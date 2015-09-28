; BINFIX by V.Cerovski 2015

(in-package :binfix)

{=let e &optional binds decl :=
  if (null e) (=let '(()) binds decl)
    let s = (car e)
      (cond {symbolp s && cadr e == '= $
              =let (cdddr e) `((,s,(caddr e)),@binds) decl}
            {symbolp s && caddr e == '= $
              =let (cddddr e) `((,s,(cadddr e)),@binds) `((type,(cadr e),s),@decl)}
            (t `(,(nreverse binds)
                 ,@(if decl `((declare,@decl)))
                 ,@(if {symbolp s && cdr e} `(,e) e)))) &

 interleave &rest r :==
   let body = (reverse (pop r))
     {loop while (cdr r) do
         {let ab = (pop r) ; cannot use loop for clause here b/c of ecl
              {car body .= list (car body) (pop ab)}
              (push (pop ab) body)} &
      when r {car body .= car body :. r} &
      funcall {b -> if (atom (car b)) b ; funcall only b/c sbcl complains.
                        (append (car b) (cdr b))}
              (reverse body)} &

 keyword-to-S-expr k :=
   let* str = (subseq (format () "~S" k) 1)
     (read-from-string
       (if {str ! 0 =c= #\| } ; ecl does not compile |}
         (format () "(~A)" (subseq str 1 {1- $ length str}))
         str)) &

 &symbolp s :== `{string ,s ! 0 =c= #\& } & ; ecl does not compile #\&}

 collect-&parts l &optional arg types :=
   if (null l) {reverse arg :. types && `((declare ,@(reverse types)))}
     let s = (pop l)
       (cond {listp s || &symbolp s $ collect-&parts l {s :. arg} types}
             {symbolp s $
               let n = (car l)
                 (when (keywordp n)
                   {push `(type,(keyword-to-S-expr n),s) types &
                    pop l &
                    n =. car l})
                 (if {n == '=}
                   (collect-&parts (cddr l) `((,s,(cadr l)),@arg) types)
                   (collect-&parts l `(,s,@arg) types))}
             {t $ error "BINFIX: cannot collect-&parts of ~S" l}) &

 lambda-list l &optional arg types :=
   if (null l) {nreverse arg :. types && `((declare ,@(nreverse types)))}
     let s = (pop l)
       (cond {symbolp s $
               cond {keywordp (car l) $
                      if {cadr l == '=}
                        (collect-&parts `(&optional,s,@l) arg types)
                        (lambda-list (cdr l) `(,s,@arg) `((type,(keyword-to-S-expr (car l)),s),@types))}
                    {&symbolp s $ collect-&parts l `(,s,@arg) types}
                    {car l =='= $ collect-&parts `(&optional,s,@l) arg types}
                    {         t $ lambda-list l `(,s,@arg) types}}
             {listp s $
               let ll = (lambda-list s)
                 (lambda-list l {car ll :. reverse arg} (revappend (cdadr ll) types))}
             {t $ error "BINFIX: lambda-list expects symbol or list, not ~S" s}) &


 =flet e &optional binds name lambdal decl :=
   cond {null e      $ `(,(reverse binds),@(car decl),@{name :. reverse lambdal})}
        {null name   $ =flet (cdr e) binds (car e) lambdal ()}
        {car e ==':= $ =flet (cdr e) binds name lambdal '(())}
        {decl && listp (car e) && caar e == 'declare
                     $ =flet (cdr e) binds name lambdal `((,(car e),@(car decl)))}
        {car e == 'declare
                     $ =flet (cddr e) binds name lambdal `(((declare,(cadr e)),@(car decl)))}
        {decl        $ =flet (cdr e) `((,name
                                         ,@(lambda-list (reverse lambdal))
                                          ,@(car decl)
                                           ,(car e))
                                       ,@binds) () () ()}
        {t           $ =flet (cdr e) binds name {car e :. lambdal} ()} &

 method-lambda-list l &optional arg :=
   if (null l)
     (list (nreverse arg))
     (if {cdr l && keywordp (cadr l)}
        (method-lambda-list (cddr l) `((,(car l),(keyword-to-S-expr (cadr l))),@arg))
        (method-lambda-list  (cdr l) `(,(car l),@arg))) &

 *binfix* =. mapcar {op &aux (o (car op)) -> append (if (listp o) o `(,o,o)) (cdr op)}
   `(((&  progn)      :unreduce )
     ((let            ,#'=let));-----------------------LET constructs
     ((let*           ,#'=let))
     ((flet           ,#'=flet))
     ((labels         ,#'=flet))
     ((macrolet       ,#'=flet))
     ((symbol-macrolet,#'=let))
     ((:== defmacro)  :def )
     ((:= defun)      :def )
     ((:- defmethod)  :defm )
     ((loop           ,#'identity));-------------------OPS W/UNCHANGED RHS
     ((? interleave)  :unreduce);----------------------$pliter
     (($ ())          :split)
     ((.=   setf)) ;-----------------------------------ASSIGNMENT
     ((+=   incf))
     ((-=   decf))
     (( =.  setq))
     ((.=.  set))
     ( mapc ) ;----------------------------------------MAPPING
     ((@.   mapcar)   :rhs-args)
     ((@n   mapcan)   :rhs-args)
     ((@..  maplist)  :rhs-args)
     ((@.n  mapcon)   :rhs-args)
     ((:->  function) :lhs-lambda);--------------------LAMBDA/FUNCALL
     ((->   lambda)   :lhs-lambda)
     ((@@   apply)    :rhs-args )
     ((@    funcall)  :rhs-args :left-assoc :also-postfix )
     ((.x.  values)   :unreduce :also-prefix)
     ((=..  multiple-value-bind) :allows-decl );-------DESTRUCTURING
     ((..=  destructuring-bind) :allows-decl )
     ((:. cons));--------------------------------------CONSING
     ((|| or)       :unreduce );-----------------------LOGICAL OPS
     ( or           :unreduce :also-prefix )
     ((&& and)      :unreduce )
     ( and          :unreduce :also-prefix )
     ( <            :unreduce :also-prefix );----------COMPARISONS/PREDICATES
     ( >            :unreduce :also-prefix )
     ( <=           :unreduce :also-prefix )
     ( >=           :unreduce :also-prefix )
     ((=== equalp))
     ( equalp )
     ( equal )
     ((==  eql)     :also-prefix)           ; :also-prefix depreciated.
     ( eql          :also-prefix )
     ((=s= string=))
     ((=c= char=)   :unreduce )
     ( =            :unreduce :also-prefix )
     ( /=           :unreduce :also-prefix )
     ( eq )
     ( subtypep )
     ((in member));------------------------------------END OF COMPARISONS/PREDICATES
     ;================= :lower  binding user defined ops go here =================
     ;================= :higher binding user defined ops go here =================
     ( coerce )
     ( cons         :also-prefix )          ; could be also represented with .
     ( elt )
     ( svref )
     ((!! aref))
     ( logior       :unreduce );-----------------------BIT ARITHMETICS
     ( logand       :unreduce )
     ((<< ash))
     ( mod );------------------------------------------ARITHMETICS
     ( min          :also-prefix :unreduce )
     ( max          :also-prefix :unreduce )
     ( +            :also-prefix :unreduce )
     ( -            :also-unary  :unreduce )
     ( floor )
     ( ceiling )
     ( truncate )
     ( /            :also-unary )
     ( *            :also-prefix :unreduce )
     ((** expt))
     ((! aref)      :rhs-args)) &

 binfix e &optional (ops *binfix*) :=
  labels ((singleton (x)
            (declare (inline))
            (if {consp x && null (cdr x)} (car x) x))
          (unreduce (e op &optional args arg)
            (cond {null e      $ reverse {binfix (reverse arg) ops :. args}}
                  {car e == op $ unreduce (cdr e) op {binfix (reverse arg) ops :. args}}
                  {t           $ unreduce (cdr e) op args {car e :. arg}}))
          (declare-then-binfix (rhs ops &optional decls rest)
            (cond {null rest && stringp (car rhs) $
                     declare-then-binfix (cdr rhs) ops {car rhs :. decls} t}
                  {consp (car rhs) && caar rhs == 'declare $
                     declare-then-binfix (cdr rhs) ops {car rhs :. decls} t}
                  {car rhs == 'declare $
                     declare-then-binfix (cddr rhs) ops `((declare,(cadr rhs)),@decls) t}
                  {t `(,@(nreverse decls) ,(if (cdr rhs) (binfix rhs ops) (car rhs)))})))
  {if {atom e || null ops} e
    let* i = (position (caar ops) e)
      {if (null i) (binfix e (cdr ops))
         let lhs = (subseq e 0 i)
             rhs = (subseq e (1+ i))
             op = (caar ops)
             op-lisp = (cadar ops)
             op-prop = (cddar ops)
          (cond {null rhs $
                   if {:also-postfix in op-prop}
                      `(,op-lisp,@(binfix lhs ops))
                       (error "BINFIX: missing r.h.s. of ~S (~S)~@
                               with l.h.s:~%~S" op op-lisp lhs)}
                {functionp op-lisp $
                   if (zerop i)
                      {op :. funcall op-lisp rhs}
                      (binfix `(,@lhs,{op :. funcall op-lisp rhs}))}
                {:lhs-lambda in op-prop $
                   `(,op-lisp ,@(lambda-list lhs)
                              ,@(declare-then-binfix rhs ops))}
                {:unreduce in op-prop && position op rhs $ ;position necessary...
                    mapcar #'singleton (unreduce rhs op `(,(binfix lhs (cdr ops)),op-lisp))}
                {zerop i $ cond {:also-unary  in op-prop $ `(,op-lisp ,(singleton (binfix rhs ops)))}
                                {:also-prefix in op-prop $ `(,op-lisp ,@(binfix rhs ops))}
                                {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                           with r.h.s:~%~S" op op-lisp rhs}}
                {:def in op-prop $ `(,op-lisp ,(car e)
                                     ,@(lambda-list (cdr lhs))
                                     ,@(declare-then-binfix rhs ops))}
                {:defm in op-prop $`(,op-lisp ,(car e)
                                     ,@(method-lambda-list (cdr lhs))
                                     ,@(declare-then-binfix rhs ops))}
                {:left-assoc in op-prop && position op rhs $
                   let* j = (position op rhs)
                       lrhs = (subseq rhs 0 j)
                       rrhs = (subseq rhs j)
                      (binfix`((,op-lisp ,(singleton (binfix  lhs (cdr ops)))
                                         ,(singleton (binfix lrhs (cdr ops)))) ,@rrhs) ops)}
                {:allows-decl in op-prop $
                   `(,op-lisp ,lhs ,(car rhs) ,@(declare-then-binfix (cdr rhs) ops))}
                {:split in op-prop $
                   `(,(if (= i 1) (car e) (binfix lhs (cdr ops)))
                     ,{when rhs
                         let e = (binfix rhs ops)
                            (if (cdr e) e (car e))})}
                (t `(,op-lisp
                     ,(if (= i 1) (car e) (binfix lhs (cdr ops)))
                     ,@(cond {null (cdr rhs) $ rhs}
                             {:rhs-args in op-prop $ if {op in rhs} `(,(binfix rhs ops)) rhs}
                             {t `(,(binfix rhs ops))}))))}}}

;===== BINFIX defined =====
#|
(when t ;--------TIMING ONLY CODE
  (defparameter +timing+ 0)
  (declaim (type integer +timing+))

  #+sbcl {get-time-usec := sec usec =.. (sb-ext:get-time-of-day) sec * 1000000 + usec}
  #-sbcl {get-time-usec := 0}

  (set-macro-character #\{
     {s ch -> (declare (ignore ch))
              let start = (get-time-usec)
                 prog1 {binfix $ read-delimited-list #\} s t}
                       {+timing+ += (get-time-usec) - start}})
) ;--------TIMING ONLY CODE
|#

