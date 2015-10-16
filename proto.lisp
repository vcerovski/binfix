; BINFIX by V.Cerovski 2015

(in-package :binfix)

(defparameter *binfix*
  '(( &  progn)
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
                  (i (position (pop op) e)))
             (if (null i)
               (binfix e (cdr ops))
              `(,@op
                ,(if (eql (car op) 'def)
                    (subseq e 0 i)
                    (binfix (subseq e 0 i) (cdr ops)))
                ,(binfix (subseq e (1+ i)) ops)))))))

(set-macro-character #\{
  (lambda (s ch) (declare (ignore ch))
    (binfix (read-delimited-list #\} s t))))

(set-macro-character #\} (get-macro-character #\) ))

