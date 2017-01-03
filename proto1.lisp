; BINFIX by V.Cerovski 2015,7

(in-package :binfix)

{defmacro def (what args body)
  `(,what ,@(if (atom args)
               `(,args ())
               `(,(car args),(cdr args)))
          ,(binfix body));

 def-lambda args body :==
  `(lambda ,(if (consp args) args `(,args))
     ,(binfix body));

 let= let lhs body &aux vars :==
  loop while {cadr body == '=}
     do {push `(,(car body),(caddr body)) vars;
         body =. cdddr body}
     finally (return (let ((let `(,let ,(nreverse vars) ,(binfix body))))
                       (if lhs (binfix `(,@lhs ,let)) let)));

 flet= flet lhs body &aux funs :==
  loop for r = {'= in body} while r
       for (name . lambda) = (ldiff body r)
       do {push `(,name ,lambda ,(cadr r)) funs;
           body =. cddr r}
       finally {return let flet = `(,flet ,(reverse funs) ,(binfix body))
                         if lhs (binfix `(,@lhs ,flet)) flet};

 unreduc op op-lisp lhs rhs :==
   labels
     unreduce e &optional args arg =
       (cond {null e      $ nreverse {binfix (nreverse arg) :. args}}
             {car e == op $ unreduce (cdr e) {binfix (nreverse arg) :. args}}
             {t           $ unreduce (cdr e) args {car e :. arg}})
   `(,op-lisp ,@(unreduce rhs `(,(binfix lhs))));

 var-bind op lhs rhs :== `(,op ,lhs ,(car rhs) ,(binfix (cdr rhs)))}

;BOOTSTRAP PHASE 2 DONE. (DEFs and LETs in proto BINFIX defined)
;PROTO BINFIX DEFINED.

