; BINFIX by V.Cerovski 2015

(in-package :binfix)

{singleton x := if {consp x && null (cdr x)} (car x) x;

 keyword-type-spec k :=
   let S = {singleton $ read-from-string
                          (concatenate 'string "(" (symbol-name k) ")")
                          () :eof}
     (if {symbolp S && not (keywordp S) || listp S} S
        (error "Incorrect BINFIX keyword-type specifier ~S" k));

 &lambdap s :== `{,s in lambda-list-keywords};

 collect-&parts l &optional arg types :=
   if (null l) {reverse arg :. types && `((declare ,@(reverse types)))}
     let s = (pop l)
       (cond {listp s || &lambdap s $ collect-&parts l {s :. arg} types}
             {symbolp s $
               let n = (car l)
                 (when (keywordp n)
                   {push `(type,(keyword-type-spec n),s) types;
                    pop l;
                    n =. car l})
                 (if {n == '=}
                   (collect-&parts (cddr l) `((,s,(cadr l)),@arg) types)
                   (collect-&parts l `(,s,@arg) types))}
             {t $ error "BINFIX: cannot collect-&parts of ~S" l});

 lambda-list l &optional arg types :=
   if (null l) {nreverse arg :. types && `((declare ,@(nreverse types)))}
     let s = (pop l)
       (cond {symbolp s $
               cond {keywordp (car l) $
                      if {cadr l == '=}
                        (collect-&parts `(&optional,s,@l) arg types)
                        (lambda-list (cdr l) `(,s,@arg) `((type,(keyword-type-spec (car l)),s),@types))}
                    {s =='&whole $ lambda-list (cdr l) `(,(car l),s,@arg) types}
                    { &lambdap s $ collect-&parts l `(,s,@arg) types}
                    {car l == '= $ collect-&parts `(&optional,s,@l) arg types}
                    {          t $ lambda-list l `(,s,@arg) types}}
             {listp s $
               let ll = (lambda-list s)
                 (lambda-list l {car ll :. arg} (revappend (cdadr ll) types))}
             {t $ error "BINFIX lambda-list expects symbol or list, not ~S" s});

 method-lambda-list l &optional args :=
   if (null l) (list (nreverse args))
     let s = (pop l)
       (cond {symbolp s $
               cond {keywordp (car l) $
                      if {cadr l == '=}
                        (collect-&parts `(&optional,s,@l) args)
                        (method-lambda-list (cdr l) {`(,s,(keyword-type-spec (car l))) :. args})}
                    {&lambdap s  $ collect-&parts l {s :. args}}
                    {car l =='=  $ collect-&parts `(&optional,s,@l) args}
                    {car l =='== $ method-lambda-list (cddr l) {`(,s (eql,(cadr l))) :. args}}
                    {         t  $ method-lambda-list l {s :. args}}}
             {listp s $ method-lambda-list l {s :. args}}
             {t $ error "BINFIX method-lambda-list expects symbol or list, not ~S" s});

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
        {t           $ =flet (cdr e) binds name {car e :. lambdal} ()};

 decls e &optional decls doc :=
  let s = (car e)
    (cond {               s == 'declare $ decls (cddr e) {cadr e :. decls} doc}
          {listp s && car s == 'declare $ decls (cdr e) (revappend (cdr s) decls) doc}
          {t $ `(,@doc ,@{decls && `((declare ,@(reverse decls)))}) .x. e});

 doc-decls e &optional decls :=
   if {stringp (car e) && cdr e}
      (decls (cdr e) decls `(,(car e)))
      (decls e decls);

 vbinds e &optional vars decls :=
   cond {null e $ reverse vars .x. reverse decls}
        {symbolp (car e) && not (keywordp (car e)) $
            if (keywordp (cadr e))
              (vbinds (cddr e)
                      {car e :. vars}
                      {`(type ,(keyword-type-spec (cadr e)),(car e)) :. decls})
              (vbinds (cdr e)
                      {car e :. vars}
                      decls)}
        {t $ error "BINFIX: symbol expected, not ~S in~@
                   ~S" (car e) (reverse vars)};

 lbinds e &optional binds decls :=
   let s = (car e)
     (cond {symbolp s && cadr e == '=
              $ lbinds (cdddr e) `((,s,(caddr e)) ,@binds)  decls}
           {symbolp s && keywordp (cadr e) && caddr e == '=
              $ lbinds (cddddr e)
                      `((,s,(cadddr e)),@binds)
                      `((type,(keyword-type-spec (cadr e)),s),@decls)}
           {t $ reverse binds :. {decl body =.. (decls e decls)
                                   `(,@decl ,@{body && `(,{singleton $ binfix body})})}});


 *binfix* =.
   `(( &               progn      :unreduce)
     ( let             let        :rhs-lbinds);;------------LET constructs
     ( let*            let*       :rhs-lbinds)
     ( flet            ,#'=flet)
     ( labels          ,#'=flet)
     ( macrolet        ,#'=flet)
     ( symbol-macrolet symbol-macrolet :rhs-lbinds)
     ( :==  defmacro   :def)
     ( :=   defun      :def)
     ( :-   defmethod  :defm)
     ( block    block     :prefix);;------------------------PREFIX FORMS
     ( tagbody  tagbody   :prefix)
     ( catch    catch     :prefix)
     ( progn    progn     :prefix)
     ( cond     cond      :prefix);;------------------------COND/CASE FORMS
     ( case     case      :prefix)
     ( ccase    ccase     :prefix)
     ( ecase    ecase     :prefix)
     ( typecase typecase  :prefix)
     (etypecase etypecase :prefix)
     (ctypecase ctypecase :prefix)
     ( if       if        :prefix)
     ( loop ,#'identity);;----------------------------------OPS W/UNCHANGED RHS
     (  ?   ()         :split);;----------------------------$pliters
     (  $   ()         :split)
     ( .=   setf) ;;----------------------------------------ASSIGNMENT
     ( +=   incf)
     ( -=   decf)
     (  =.  setq)
     ( .=.  set)
     ( setq setq  :rhs-sbinds)
     ( set  set   :rhs-sbinds)
     (psetq psetq :rhs-sbinds)
     ( setf setf  :rhs-ebinds)
     (psetf psetf :rhs-ebinds)
     ( mapc mapc) ;;----------------------------------------MAPPING
     ( @.   mapcar     :rhs-args)
     ( @n   mapcan     :rhs-args)
     ( @..  maplist    :rhs-args)
     ( @.n  mapcon     :rhs-args)
     ( :->  function   :lhs-lambda);;-----------------------LAMBDA/FUNCALL
     ( ->   lambda     :lhs-lambda)
     ( @@   apply      :rhs-args)
     ( @    funcall    :rhs-args :left-assoc :also-postfix)
     ( .x.  values     :unreduce :also-prefix)
     ( =..  multiple-value-bind  :syms=expr);;--------------DESTRUCTURING
     ( ..=  destructuring-bind   :lambda/expr)
     ( :.   cons);;-----------------------------------------CONSING
     ( ||       or     :unreduce);;-------------------------LOGICAL OPS
     ( or       or     :unreduce :also-prefix)
     ( &&       and    :unreduce)
     ( and      and    :unreduce :also-prefix)
     ( <        <      :unreduce :also-prefix);;------------COMPARISONS/PREDICATES
     ( >        >      :unreduce :also-prefix)
     ( <=       <=     :unreduce :also-prefix)
     ( >=       >=     :unreduce :also-prefix)
     ( ===      equalp)
     ( equalp   equalp)
     ( equal    equal)
     ( ==       eql    :also-prefix)          ;; :also-prefix depreciated.
     ( eql      eql    :also-prefix)
     ( =s=      string=)
     ( =c=      char=  :unreduce)
     (  =        =     :unreduce :also-prefix)
     ( /=       /=     :unreduce :also-prefix)
     ( eq       eq)
     ( subtypep subtypep)
     ( in       member);;-----------------------------------END OF COMPARISONS/PREDICATES
     ;;================ :lower  binding user defined ops go here =================
     ;;================ :higher binding user defined ops go here =================
     ( coerce   coerce)
     ( cons     cons    :also-prefix)
     ( elt      elt)
     ( svref    svref)
     ( !!       aref)
     ( logior   logior  :unreduce);;------------------------BIT ARITHMETICS
     ( logand   logand  :unreduce)
     ( <<       ash)
     ( mod      mod);;--------------------------------------ARITHMETICS
     ( min      min     :also-prefix :unreduce)
     ( max      max     :also-prefix :unreduce)
     (  +        +      :also-prefix :unreduce)
     (  -        -      :also-unary  :unreduce)
     ( floor    floor)
     ( ceiling  ceiling)
     ( truncate truncate)
     (  /        /      :also-unary)
     (  *        *      :also-prefix :unreduce)
     ( **       expt)
     (  !       aref    :rhs-args));


 binfix e &optional (ops *binfix*) :=
   labels
          unreduce e op &optional args arg =
            (cond {null e      $ reverse {binfix (reverse arg) ops :. args}}
                  {car e == op $ unreduce (cdr e) op {binfix (reverse arg) ops :. args}}
                  {t           $ unreduce (cdr e) op args {car e :. arg}})

     binfix+ e &optional (ops ops) =
       (if {'; in e}
          (singleton (mapcar #'singleton (unreduce e ';)))
         `(,(singleton (binfix e ops))))

          declare-then-binfix rhs ops &optional decls rest =
            (cond {null rest && stringp (car rhs) $
                     declare-then-binfix (cdr rhs) ops {car rhs :. decls} t}
                  {consp (car rhs) && caar rhs == 'declare $
                     declare-then-binfix (cdr rhs) ops {car rhs :. decls} t}
                  {car rhs == 'declare $
                     declare-then-binfix (cddr rhs) ops `((declare,(cadr rhs)),@decls) t}
                  {t `(,@(nreverse decls) ,(if (cdr rhs) (binfix rhs ops) (car rhs)))})

     decl*-binfix+ rhs &optional (ops ops) decls =
       {decl* body =.. (decls rhs decls)
         `(,@decl* ,@(binfix+ body ops))}

    sbinds e &optional converted s current =
     {symbol-macrolet
       join-to-converted = `(,(singleton (binfix (reverse current) ops)),s,@converted)
         (cond {null e      $ cddr $ reverse join-to-converted}
               {cadr e =='= $ sbinds (cddr e) join-to-converted (car e)}
               {t           $ sbinds (cdr e)  converted s {car e :. current}})}

    e-binds e &optional binds lhs rhs =
      {labels b-eval-rev e = (singleton
                               (if {consp e && > (length e) 1}
                                  {binfix $ singleton $ nreverse e}
                                  e))
              bind lhs rhs = {b-eval-rev rhs :. b-eval-rev lhs :. binds}
        (cond {null e     $ if {lhs && rhs}
                              {nreverse (bind lhs rhs) .x. nil}
                              {nreverse binds .x. append (nreverse lhs) (nreverse rhs) e}}
              {car e =='= $ if (null rhs)
                              (e-binds (cddr e) binds lhs `(,(cadr e))) 
                              (e-binds (cddr e) (bind lhs (last rhs)) (butlast rhs) `(,(cadr e)))}
              {car e =='; $ if {lhs && rhs}
                              {e-binds (cdr e) (bind lhs rhs)}
                              (error "BINFIX expression(s) bind(s), missing = in:~@
                                      ~A" (append (nreverse lhs) (nreverse rhs)))}
              {rhs        $ e-binds (cdr e) binds           lhs {car e :. rhs}}
              {t          $ e-binds (cdr e) binds {car e :. lhs}          rhs})}

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
                {:rhs-lbinds in op-prop $ singleton (binfix `(,@lhs (,op-lisp ,@(lbinds rhs))) ops)}
                {:syms=expr  in op-prop $
                   vars decls =.. (vbinds lhs)
                      `(,op-lisp ,vars ,(car rhs)
                                 ,@{decls && `((declare ,@decls))}
                                 ,@(decl*-binfix+ (cdr rhs) ops))}
                {:rhs-sbinds in op-prop $
                   singleton (binfix `(,@lhs (,op-lisp ,@(sbinds rhs))) ops)}
                {:rhs-ebinds in op-prop $
                   binds r =.. (e-binds rhs)
                     (singleton (binfix `(,@lhs (,op-lisp ,@binds) ,@r) ops))}
                {functionp op-lisp $
                   if (zerop i)
                      {op :. funcall op-lisp rhs}
                      (binfix `(,@lhs,{op :. funcall op-lisp rhs}))}
                {:lhs-lambda in op-prop $
                   `(,op-lisp ,@(lambda-list lhs)
                              ,@(declare-then-binfix rhs ops))}
                {:unreduce in op-prop && position op rhs $ ;;position necessary...
                    mapcar #'singleton (unreduce rhs op `(,(binfix lhs (cdr ops)),op-lisp))}
                {zerop i $ cond {:also-unary  in op-prop $ `(,op-lisp ,(singleton (binfix rhs ops)))}
                                {:also-prefix in op-prop || :prefix in op-prop
                                                         $ `(,op-lisp ,@(if {'; in rhs}
                                                                          (binfix+ rhs)
                                                                          (binfix rhs)))}
                                {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                            with r.h.s:~%~S" op op-lisp rhs}}
                {:def in op-prop $ `(,op-lisp ,(car e)
                                     ,@(lambda-list (cdr lhs))
                                     ,@(declare-then-binfix rhs ops))}
                {:defm in op-prop $
                   `(,op-lisp ,(pop lhs) ,@(cond {consp (car lhs) && null (cdar lhs) $ pop lhs}
                                                 {keywordp (car lhs) $ list (pop lhs)})
                      ,@(method-lambda-list lhs)
                      ,@(declare-then-binfix rhs ops))}
                {:left-assoc in op-prop && position op rhs $
                   let* j = (position op rhs)
                       lrhs = (subseq rhs 0 j)
                       rrhs = (subseq rhs j)
                      (binfix`((,op-lisp ,(singleton (binfix  lhs (cdr ops)))
                                         ,(singleton (binfix lrhs (cdr ops)))) ,@rrhs) ops)}
                {:lambda/expr in op-prop $
                   destructuring-bind (llist &rest decls) (lambda-list lhs)
                      `(,op-lisp ,llist ,(car rhs) ,@decls
                                 ,@(declare-then-binfix (cdr rhs) ops))}
                {:split in op-prop $
                   `(,(if (= i 1) (car e) (binfix lhs (cdr ops)))
                     ,{when rhs
                         let e = (binfix rhs ops)
                            (if (cdr e) e (car e))})}
                {:prefix in op-prop $ binfix `(,@lhs ,(binfix `(,op,@rhs) ops))}
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

