; BINFIX by V.Cerovski 2015,6

(in-package :binfix)

(defparameter *binfix*
  '((|;| progn)
    (:== def defmacro)
    (:=  def defun)
    (:-  def defmethod)
    ( =. setq)
    (.=  setf)
    (->  def lambda)
    ($)
    (labels flet= labels)
    (symbol-macrolet  let= symbol-macrolet)
    (let  let= let)
    (let* let= let*)
    (=..  var-bind multiple-value-bind)
    (.x.  unreduc .x. values)
    (:.   cons)
    (||   or)
    (&&   and)
    (==   eql)
    (=c=  char=)
    (in   member)
    ( !   aref)))

(defun binfix (e &optional (ops *binfix*))
  (cond ((atom e) e)
        ((null ops) (if (cdr e) e (car e)))
        (t (let* ((op (car ops))
                  (op.rhs (member (pop op) e)))
             (if (null op.rhs)
               (binfix e (cdr ops))
               (let ((lhs (ldiff e op.rhs)))
                 `(,@op
                    ,(if (eql (car op) 'def)
                       lhs
                       (binfix lhs (cdr ops)))
                    ,(if (eql (car op) 'unreduc)
                       (cdr op.rhs)
                       (binfix (cdr op.rhs) ops)))))))))

(defun semicolon (s ch)
  (declare (ignore ch))
  (if (char= #\; (peek-char nil s))
    (loop until (char= #\Newline (read-char s nil #\Newline t))
          finally (return (values)))
    #+(or sbcl ccl)          (intern ";")
    #+(or clisp ecl) (values (intern ";"))))

(defvar *timing* 0)

(set-macro-character #\{
  (lambda (s ch) (declare (ignore ch))
    (let ((time (get-internal-real-time))
          (semicolon (get-macro-character #\;)))
      (unwind-protect
        (progn (set-macro-character #\; #'semicolon)
               (binfix (read-delimited-list #\} s t)))
        (set-macro-character #\; semicolon)
        (incf *timing* (- (get-internal-real-time) time))))))

(set-macro-character #\} (get-macro-character #\) ))

