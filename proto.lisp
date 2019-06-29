; BINFIX by V.Cerovski 2015,7

(in-package :binfix)

(defparameter *binfix*
  '((|;|    infix     (progn))
    (:==    def       defmacro)
    (:=     def       defun)
    (:-     def       defmethod)
    ( =.    infix     (setq))
    (.=     infix     (setf))
    (->     def-lambda)
    ($      infix     ())
    (symbol-macrolet  let= symbol-macrolet)
    (let    let=      let)
    (let*   let=      let*)
    (labels flet=     labels)
    (=..    var-bind  multiple-value-bind)
    (..=    var-bind  destructuring-bind)
    (.x.    unreduc   .x. values)
    (:.     infix     (cons))
    (||     infix     (or))
    (&&     infix     (and))
    (==     infix     (eql))
    (=c=    infix     (char=))
    ( <     infix     (<))
    (in     infix     (member))
    ( !     infix     (aref))))

(defun binfix (e &optional (ops *binfix*))
  (cond ((atom e) e)
        ((null ops) (if (cdr e) e (car e)))
        (t (let* ((op (car ops))
                  (op.rhs (member (pop op) e)))
             (if (null op.rhs)
               (binfix e (cdr ops))
               (let ((lhs (ldiff e op.rhs)))
                 (macroexpand-1
                   `(,@op ,lhs ,(cdr op.rhs)))))))))

(defmacro infix (op lhs rhs)
  `(,@op ,(binfix lhs) ,(binfix rhs)))

(defun semicolon (s ch)
  (declare (ignore ch))
  (if (char= #\; (peek-char nil s))
    (loop until (char= #\Newline (read-char s nil #\Newline t))
          finally (return (values)))
    (values (intern ";"))))

(defvar *timing* 0)

(defmacro binfix-reader ()
 '(lambda (s ch) (declare (ignore ch))
    (let ((time (get-internal-real-time))
          (semicolon (get-macro-character #\;)))
      (unwind-protect
        (progn (set-macro-character #\; #'semicolon)
               (values (binfix (read-delimited-list #\} s t)))) ;;values b/c of clisp
        (set-macro-character #\; semicolon)
        (incf *timing* (- (get-internal-real-time) time))))))

(set-macro-character #\{ (binfix-reader))
(set-macro-character #\} (get-macro-character #\) ))

#+ecl
(defmacro use (&rest phases)
  "Helper macro for defining binfix interface in ECL."
  `(eval-when ,(or phases '(:load-toplevel :compile-toplevel :execute))
     (set-macro-character #\{ (binfix-reader))
     (set-macro-character #\} (get-macro-character #\) nil))))
