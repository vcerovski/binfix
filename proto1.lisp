; BINFIX by V.Cerovski 2015

(in-package :binfix)

(defmacro def (what args body)
  `(,what ,@(if {what == 'lambda}
              `(,(if {args && atom args} `(,args) args))
               (if (atom args) `(,args ()) `(,(car args),(cdr args))))
          ,body))

{let= let lhs body &aux vars :==
  loop while {cadr body == '=}
     do (push `(,(car body),(caddr body)) vars)
        {body =. cdddr body}
     finally (return (let ((let `(,let ,(nreverse vars) ,@body)))
                       (if lhs `(,@lhs ,let) let)))}

;BOOTSTRAP PHASE 2 DONE. (DEFs and LETs in proto BINFIX defined)

