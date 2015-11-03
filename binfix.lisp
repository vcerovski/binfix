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
   if (null l) {nreverse arg .x. types}
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
             {t $ error "BINFIX lambda-list cannot collect-&parts of ~S" l});

 lambda-list l &optional arg types :=
   if (null l) {nreverse arg .x. types}
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
               ll decls =.. (lambda-list s)
                 (lambda-list l {ll :. arg} (append decls types))}
             {t $ error "BINFIX lambda-list expects symbol or list, not ~S" s});

 method-lambda-list l &optional args :=
   if (null l) {nreverse args .x. ()}
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

 lbinds e &optional binds s current decls :=
   labels make-bind s e = `(,s ,(singleton (binfix (reverse e))))
     (cond {car e == 'declare || consp (car e) && caar e == 'declare
              $ decls e =.. (decls e decls)
                 {cdr (reverse {make-bind s current :. binds}) :. decls .x. e}}
           {null e
              $ let current = (reverse current)
                  {decls e =.. (decls (cdr current) decls)
                    {cdr (reverse {{s :. car current :.()} :. binds}) :. decls .x. e}}}
           {car e == ';
              $ if {cadr e == 'declare || consp (cadr e) && caadr e == 'declare}
                  (lbinds (cdr e) binds s current decls)
                  {decls e =.. (decls (cdr e) decls)
                    {cdr (reverse {make-bind s current :. binds}) :. decls .x. e}}}
           {cadr e == '=
              $ lbinds (cddr e)
                       {make-bind s current :. binds} (car e) ()
                       decls}
           {keywordp (cadr e) && caddr e == '=
              $ lbinds (cdddr e)
                       {make-bind s current :. binds} (car e) ()
                      `((type,(keyword-type-spec (cadr e)),(car e)),@decls)}
           {t $ lbinds (cdr e)
                       binds s {car e :. current}
                       decls});

 fbinds e &optional binds name llist body :=
   symbol-macrolet
     finish =
       {decl* r =.. (decls (if name {name :. revappend llist (nreverse body)}
                                            {revappend llist (nreverse body)}))
         {`(,(nreverse binds) ,@decl*) .x. r}}
   {labels
     bind n ll d b =
       {ll ldecl* =.. (lambda-list (nreverse ll))
         {decl* body =.. (decls (nreverse b) ldecl*)
           {`(,n ,ll ,@decl* ,@d ,(singleton (binfix body))) :. binds}}}
   (cond {null e
            $ if body
                {decl* r =.. (decls (nreverse body))
                  {`(,(nreverse (bind name llist decl* `(,(pop r))))) .x. r}}
                finish}
         {car e == ':=
            $ if body
                {decl* r =.. (decls (nreverse body))
                  (fbinds (cddr e)
                          (bind name llist decl* `(,(pop r)))
                          (pop r)
                          (nreverse r)
                         `(,(cadr e)))}
                (fbinds (cddr e) binds name llist `(,(cadr e)))}
         {car e == ';
            $ if body
                (fbinds (cdr e) (bind name llist () body))
                finish}
         {body  $ fbinds (cdr e) binds name llist {car e :. body}}
         {llist $ fbinds (cdr e) binds name {car e :. llist} body}
         {name  $ fbinds (cdr e) binds name `(,(car e))}
         {t     $ fbinds (cdr e) binds (car e)})};


 *binfix* =.
   `(( &               progn           :unreduce)
     ( let             let             :rhs-lbinds);;-------LET constructs
     ( let*            let*            :rhs-lbinds)
     ( flet            flet            :rhs-fbinds)
     ( labels          labels          :rhs-fbinds)
     ( macrolet        macrolet        :rhs-fbinds)
     ( symbol-macrolet symbol-macrolet :rhs-lbinds)
     ( :==             defmacro        :def)
     ( :=              defun           :def)
     ( :-              defmethod       :defm)
     ( block    block     :prefix);;------------------------PREFIX FORMS
     ( tagbody  tagbody   :prefix)
     ( catch    catch     :prefix)
     ( prog2    prog2     :prefix)
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

     decl*-binfix+ rhs &optional (ops ops) decls =
       {decl* body =.. (decls rhs decls)
         `(,@decl* ,@(binfix+ body ops))}

     doc*-decl*-binfix+ rhs &optional (ops ops) decls =
       {doc*-decl* body =.. (doc-decls rhs decls)
         `(,@doc*-decl* ,@(binfix+ body ops))}

     sbinds e &optional converted s current =
       {symbol-macrolet
         convert = `(,(singleton (binfix (reverse current) ops)),s,@converted)
           (cond {null e      $ cddr $ reverse convert}
                 {cadr e =='= $ sbinds (cddr e) convert (car e)}
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
                {:rhs-lbinds in op-prop $
                   binds-decls* expr =.. (lbinds rhs)
                     (singleton (binfix `(,@lhs (,op-lisp ,@binds-decls* ,@(binfix+ expr))) ops))}
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
                {:rhs-fbinds in op-prop $
                   binds-decls* expr =.. (fbinds rhs)
                     (singleton (binfix `(,@lhs (,op-lisp ,@binds-decls* ,@(binfix+ expr))) ops))}
                {functionp op-lisp $
                   if (zerop i)
                      {op :. funcall op-lisp rhs}
                      (binfix `(,@lhs,{op :. funcall op-lisp rhs}))}
                {:lhs-lambda in op-prop $
                   ll decls =.. (lambda-list lhs)
                      `(,op-lisp ,ll ,@(decl*-binfix+ rhs ops decls))}
                {:unreduce in op-prop && position op rhs $ ;;position necessary...
                    mapcar #'singleton (unreduce rhs op `(,(binfix lhs (cdr ops)),op-lisp))}
                {zerop i $ cond {:also-unary  in op-prop $ `(,op-lisp ,(singleton (binfix rhs ops)))}
                                {:also-prefix in op-prop || :prefix in op-prop
                                                         $ `(,op-lisp ,@(if {'; in rhs}
                                                                          (binfix+ rhs)
                                                                          (binfix rhs)))}
                                {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                            with r.h.s:~%~S" op op-lisp rhs}}
                {:def in op-prop $ ll decls =.. (lambda-list (cdr lhs))
                                    `(,op-lisp ,(car lhs) ,ll
                                               ,@(doc*-decl*-binfix+ rhs ops decls))}
                {:defm in op-prop $
                   `(,op-lisp ,(pop lhs) ,@(cond {consp (car lhs) && null (cdar lhs) $ pop lhs}
                                                 {keywordp (car lhs) $ list (pop lhs)})
                              ,@{ll decls =.. (method-lambda-list lhs)
                                  `(,ll ,@(doc*-decl*-binfix+ rhs ops decls))})}
                {:left-assoc in op-prop && position op rhs $
                   let* j = (position op rhs)
                       lrhs = (subseq rhs 0 j)
                       rrhs = (subseq rhs j)
                      (binfix`((,op-lisp ,(singleton (binfix  lhs (cdr ops)))
                                         ,(singleton (binfix lrhs (cdr ops)))) ,@rrhs) ops)}
                {:lambda/expr in op-prop $
                   llist decls =.. (lambda-list lhs)
                     `(,op-lisp ,llist ,(car rhs)
                                ,@(decl*-binfix+ (cdr rhs) ops decls))}
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

