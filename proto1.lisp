; BINFIX by V.Cerovski 2015

(in-package :binfix)

{defmacro def (what args body)
  `(,what ,@(if {what == 'lambda}
              `(,(if {args && atom args} `(,args) args))
               (if (atom args) `(,args ()) `(,(car args),(cdr args))))
          ,body);

 let= let lhs body &aux vars :==
  loop while {cadr body == '=}
     do {push `(,(car body),(caddr body)) vars;
         body =. cdddr body}
     finally (return (let ((let `(,let ,(nreverse vars) ,@body)))
                       (if lhs `(,@lhs ,let) let)));

 flet= flet lhs body &aux funs :==
  loop for r = {'= in body} while r
       for (name . lambda) = (ldiff body r)
       do {push `(,name ,lambda ,(cadr r)) funs;
           body =. cddr r}
       finally (return (let ((flet `(,flet ,(reverse funs) ,@body)))
                         (if lhs `(,@lhs ,flet) flet)));

 unreduc op op-lisp lhs rhs :==
   labels
     unreduce e &optional args arg =
       (cond {null e      $ nreverse {binfix (nreverse arg) :. args}}
             {car e == op $ unreduce (cdr e) {binfix (nreverse arg) :. args}}
             {t           $ unreduce (cdr e) args {car e :. arg}})
   `(,op-lisp ,@(unreduce rhs `(,lhs)));

 var-bind op lhs rhs :== `(,op,lhs,@rhs)}

;BOOTSTRAP PHASE 2 DONE. (DEFs and LETs in proto BINFIX defined)
;PROTO BINFIX DEFINED.

