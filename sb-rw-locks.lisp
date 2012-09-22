;;;; FRLocks and BRLocks for SBCL
;;;;
;;;; frlock is a "fast read lock", which allows readers to gain unlocked access
;;;; to values, and provides post-read verification. Readers which intersected
;;;; with writers need to retry. frlock is very efficient when there are many
;;;; readers and writes are both fast and relatively scarce. It is, however,
;;;; unsuitable when readers and writers need exclusion, such as with SBCL's
;;;; current hash-table implementation.
;;;;
;;;; brlock is a "big read lock", which provides for mutual exlusion between
;;;; readers and writers. It is not as fast for readers as frlock, but more
;;;; appropriate if writes are not as fast.
;;;;
;;;; This implementation isn't quite as polished as it should be yet, and
;;;; not very tested either. Use at own risk.

;;;; Copyright (c) 2012 Nikodemus Siivola <nikodemus@sb-studio.net>
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defpackage :sb-rw-locks
  (:use :cl :sb-thread :sb-ext :sb-int :sb-sys)
  (:export
   #:make-frlock
   #:frlock
   #:frlock-p
   #:frlock-name
   #:frlock-write
   #:frlock-read
   #:frlock-read-begin
   #:frlock-read-end
   #:frlock-write-lock
   #:frlock-write-unlock

   #:make-brlock
   #:brlock
   #:brlock-p
   #:brlock-name
   #:brlock-write-lock
   #:brlock-write-unlock
   #:brlock-read-lock
   #:brlock-read-unlock))

(in-package :sb-rw-locks)

(defstruct (frlock (:constructor make-frlock (&key name))
                   (:copier nil))
  (mutex (make-mutex :name "FRLock mutex") :type mutex :read-only t)
  (pre-epoch 0 :type sb-ext:word)
  (post-epoch 0 :type sb-ext:word)
  (name nil))

(declaim (inline frlock-read-begin))
(defun frlock-read-begin (frlock)
  "Start a read sequence on FRLOCK. Returns a read-token to be validated
later. Using FRLOCK-READ instead is recommended."
  (barrier (:read))
  (frlock-post-epoch frlock))

(declaim (inline frlock-read-end))
(defun frlock-read-end (frlock)
  "Ends a read sequence on FRLOCK. Returns a token. If this token is EQL to
the read-token returned by FRLOCK-READ-BEGIN, the values read under the FRLOCK
are consistent and can be used: if the values differ, the values are
inconsistent and the read must be restated. Using FRLOCK-READ instead is
recommended."
  (barrier (:read))
  (frlock-pre-epoch frlock))

(defmacro frlock-read ((frlock) &body value-forms)
  "Evaluates VALUE-FORMS under FRLOCK till it obtains a consistent
set, and returns that as multiple values."
  (once-only ((frlock frlock))
    (with-unique-names (mark)
      (let ((syms (make-gensym-list (length value-forms))))
        `(loop
           (let ((,mark (frlock-read-begin ,frlock))
                 ,@(mapcar 'list syms value-forms))
             (declare (word ,mark))
             (barrier (:compiler))
             (when (eql ,mark (frlock-read-end ,frlock))
               (return (values ,@syms)))))))))

(declaim (inline frlock-write-lock))
(defun frlock-write-lock (frlock &key (wait-p nil) timeout)
  "Acquires FRLOCK for writing, invalidating existing and future read-tokens
for the duration. Returns T on success, and NIL if the lock wasn't acquired
due to eg. a timeout. Using FRLOCK-WRITE instead is recommended."
  (when (grab-mutex (frlock-mutex frlock) :waitp wait-p :timeout timeout)
    (setf (frlock-pre-epoch frlock)
          (logand most-positive-word (1+ (frlock-pre-epoch frlock))))
    (barrier (:write))
    t))

(declaim (inline frlock-write-unlock))
(defun frlock-write-unlock (frlock)
  "Releases FRLOCK after writing, allowing valid read-tokens to be acquired again.
Signals an error if the current thread doesn't hold FRLOCK for writing. Using FRLOCK-WRITE
instead is recommended."
  (setf (frlock-post-epoch frlock)
        (logand most-positive-word (1+ (frlock-post-epoch frlock))))
  (release-mutex (frlock-mutex frlock) :if-not-owner :error)
  (barrier (:write)))

(defmacro frlock-write ((frlock &key (wait-p t) timeout) &body body)
  "Executes BODY while holding FRLOCK for writing."
  (once-only ((frlock frlock))
    (with-unique-names (got-it)
      `(without-interrupts
         (let (,got-it)
           (unwind-protect
                (when (setf ,got-it (allow-with-interrupts
                                      (frlock-write-lock ,frlock :timeout ,timeout
                                                                 :wait-p ,wait-p)))
                  (with-local-interrupts ,@body))
             (when ,got-it
               (frlock-write-unlock ,frlock))))))))

(defstruct (brlock (:constructor make-brlock (&key name))
                   (:copier nil))
  (mutex (make-mutex :name "BRLock mutex") :type mutex :read-only t)
  (reader-count 0 :type word)
  (name nil))

(defun brlock-write-lock (brlock &key (wait-p t) timeout)
  "Acquires BRLOCK for writing. Waits until all readers have released the lock.
Returns T if the lock was acquired succesfully, NIL otherwise. Using
WITH-BRLOCK-WRITE instead is recommended. WARNING: There is no sanity checking to
verify that the current thread doesn't already hold the BRLOCK for reading:
recursive read -> write lock acquisition will deadlock."
  (when (grab-mutex (brlock-mutex brlock) :waitp wait-p :timeout timeout)
    (or (zerop (brlock-reader-count brlock))
        (unless (and wait-p
                     (wait-for (zerop (brlock-reader-count brlock)) :timeout timeout))
          (release-mutex (brlock-mutex brlock))
          nil)
        t)))

(defun brlock-write-unlock (brlock)
  "Releases BRLOCK from writing. Using WITH-BRLCK-WRITE instead is recommended."
  (setf (brlock-name brlock) nil)
  (release-mutex (brlock-mutex brlock)))

(defmacro with-brlock-write ((brlock &key (wait-p t) timeout) &body body)
  "Acquires BRLOCK for writing for the duration of BODY."
  (once-only ((brlock brlock))
    (with-unique-names (got-it)
      `(without-interrupts
         (let (,got-it)
           (unwind-protect
                (when (setf ,got-it (allow-with-interrupts (brlock-write-lock ,brlock
                                                                              :timeout ,timeout
                                                                              :wait-p ,wait-p)))
                  (with-local-interrupts ,@body))
             (when ,got-it
               (brlock-write-unlock ,brlock))))))))

(defun brlock-read-lock (brlock &key (wait-p t) timeout)
  "Acquires BRLOCK for reading. WARNING: There is no sanity checking to
verify that the current thread doesn't already hold the BRLOCK for reading:
recursive read lock acquisition will deadlock if there are writers waiting to
gain the lock."
  (loop with mutex = (brlock-mutex brlock)
        do (atomic-incf (brlock-reader-count brlock))
           (cond ((mutex-owner mutex)
                  (atomic-decf (brlock-reader-count brlock))
                  (unless wait-p
                    (return nil)))
                 (t
                  (return t)))
           (or (wait-for (not (mutex-owner mutex)) :timeout timeout)
               (return nil))))

(defun brlock-read-unlock (brlock)
  "Releases BRLOCK from reading. WARNING: There is no sanity checking to
verify that the current thread holds the BRLOCK for reading in the first place."
  (atomic-decf (brlock-reader-count brlock)))

(defmacro with-brlock-read ((brlock &key (wait-p t) timeout) &body body)
  "Acquires BRLOCK for reading for the duration of BODY."
  (once-only ((brlock brlock))
    (with-unique-names (got-it)
      `(without-interrupts
         (let (,got-it)
           (unwind-protect
                (when (setf ,got-it (allow-with-interrupts (brlock-read-lock ,brlock
                                                                             :timeout ,timeout
                                                                             :wait-p ,wait-p)))
                  (with-local-interrupts ,@body))
             (when ,got-it
               (brlock-read-unlock ,brlock))))))))

#+nil
(progn
  (defun test-brlocks ()
    (let ((rw (make-brlock))
          (a 0)
          (b 0)
          (c 0)
          (n-readers 100)
          (reader-i 10000)
          (n-writers 10)
          (writer-i 1000)
          (run! nil)
          (w-e! nil)
          (r-e! nil))
      (mapc #'join-thread
            (nconc
             (loop repeat n-readers
                   collect (make-thread
                            (lambda ()
                              (loop until run! do (thread-yield))
                              (handler-case
                                  (loop repeat reader-i
                                        do (with-brlock-read (rw)
                                             (assert (eql c (+ a b)))
                                             (sleep 0.0001)))
                                (error (e)
                                  (setf r-e! e))))))
             (loop repeat n-writers
                   collect (make-thread
                            (lambda ()
                              (loop until run! do (thread-yield))
                              (handler-case
                                  (loop repeat writer-i
                                        do (assert
                                            (with-brlock-write (rw)
                                              (setf a (random 10000)
                                                    b (random 10000)
                                                    c (+ a b))))
                                           (sleep (random 0.001)))
                                (error (e)
                                  (setf w-e! e))))))
             (progn
               (setf run! t)
               nil)))
      (list w-e! r-e!)))

  (defun test-frlocks ()
    (let ((rw (make-frlock))
          (a 0)
          (b 0)
          (c 0)
          (n-readers 100)
          (reader-i 1000000)
          (n-writers 10)
          (writer-i 10000)
          (run! nil)
          (w-e! nil)
          (r-e! nil))
      (mapc #'join-thread
            (nconc
             (loop repeat n-readers
                   collect (make-thread
                            (lambda ()
                              (loop until run! do (thread-yield))
                              (handler-case
                                  (loop repeat reader-i
                                        do (multiple-value-bind (a b c)
                                               (frlock-read (rw) a b c)
                                             (assert (eql c (+ a b)))))
                                (error (e)
                                  (setf r-e! e))))))
             (loop repeat n-writers
                   collect (make-thread
                            (lambda ()
                              (loop until run! do (thread-yield))
                              (handler-case
                                  (loop repeat writer-i
                                        do (frlock-write (rw)
                                             (setf a (random 10000)
                                                   b (random 10000)
                                                   c (+ a b)))
                                           (sleep (random 0.0001)))
                                (error (e)
                                  (setf w-e! e))))))
             (progn
               (setf run! t)
               nil)))
      (list w-e! r-e!))))

#+nil
(loop repeat 1
      for f = (print (cons :frlock (time (test-frlocks))))
      for b = (print (cons :brlock (time (test-brlocks))))
      while (and (every #'null (cdr f))
                 (every #'null (cdr b))))
