; BINFIX by V.Cerovski 2015

(in-package :binfix)

(defmacro def (what args body)
  `(,what ,@(if {what == 'lambda}
              `(,(if {args && atom args} `(,args) args))
               (if (atom args) `(,args ()) `(,(car args),(cdr args))))
          ,body))

{let= let nill body &aux vars :==     ;nill b/c of GCL
  loop while {cadr body == '=}
     do (push `(,(car body),(caddr body)) vars)
        {body =. cdddr body}
     finally (return `(,let ,(nreverse vars) ,@body))}

;BOOTSTRAP PHASE 2 DONE. (DEFs and LETs in proto BINFIX defined)

