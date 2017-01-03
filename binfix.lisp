; BINFIX by V.Cerovski 2015,7

(in-package :binfix)

{singleton x := if {consp x && null (cdr x)} (car x) x;

 keyword-type-spec k :=
   let S = {singleton $ read-from-string
                          (concatenate 'string "(" (symbol-name k) ")")
                          () :eof}
     if {symbolp S && not (keywordp S) || listp S} S
        (error "Incorrect BINFIX keyword-type specifier ~S" k);

 &lambdap s :== `{,s in lambda-list-keywords};

 declare* decl* &optional (decl 'declare) :==
   `{,decl* && list {',decl :. nreverse ,decl*}};

 collect-&parts l &optional arg types :=
   if (null l) {nreverse arg .x. declare* types}
     let s = (pop l)
        cond {listp s || &lambdap s $ collect-&parts l {s :. arg} types}
             {symbolp s $
               let n = (car l)
                 {when (keywordp n)
                   {push `(type,(keyword-type-spec n),s) types;
                    pop l;
                    n =. car l};
                  if {n == '=}
                   (collect-&parts (cddr l) `((,s,(cadr l)),@arg) types)
                   (collect-&parts l `(,s,@arg) types)}}
             {t $ error "BINFIX lambda-list cannot collect-&parts of ~S" l};

 lambda-list l &optional arg types :=
   if (null l) {nreverse arg .x. declare* types}
     let s = (pop l)
        cond {symbolp s $
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
                 lambda-list l {ll :. arg} (append (cdar decls) types)}
             {t $ error "BINFIX lambda-list expects symbol or list instead of ~S~@
                         ~S" l (nreverse arg)};

 method-lambda-list l &optional args :=
   if (null l) {nreverse args .x. ()}
     let s = (pop l)
        cond {symbolp s $
               cond {keywordp (car l) $
                      if {cadr l == '=}
                        (collect-&parts `(&optional,s,@l) args)
                        (method-lambda-list (cdr l) {`(,s,(keyword-type-spec (car l))) :. args})}
                    {&lambdap s  $ collect-&parts l {s :. args}}
                    {car l =='=  $ collect-&parts `(&optional,s,@l) args}
                    {car l =='== $ method-lambda-list (cddr l) {`(,s (eql,(cadr l))) :. args}}
                    {         t  $ method-lambda-list l {s :. args}}}
             {listp s $ method-lambda-list l {s :. args}}
             {t $ error "BINFIX method-lambda-list expects symbol or list, not ~S" s};

 struct x &optional defs types name opts slots doc :=
    cond {null x || car x == ';
            $ `(defstruct ,(if opts `(,name,@(nreverse opts)) name)
                                  ,@{doc && `(,doc)} ,@(nreverse slots)) :. defs
               .x. types .x. cdr x}
         {null name
            $ struct (cdr x) defs types (car x)}
         {stringp (car x)
            $ if doc
                (error "BINFIX def struct ~A has two doc-strings,~%~S~%and~%~S" name doc (car x))
                (struct (cdr x) defs types name opts slots (car x))}
         {keywordp (car x)
            $ cond {car x == :named
                      $ struct (cdr x) defs types name
                               {:named :. opts} slots doc}
                   {car x == :constructor
                      $ struct (cdddr x) defs types name
                              `((:constructor,(cadr x),(lambda-list (caddr x))),@opts) slots doc}
                   {t $ struct (cddr x) defs types name
                               {`(,(car x),(cadr x)) :. opts} slots doc}}
         {cadr x == '=
            $ if {fourth x in '(:type :read-only)}
                (struct (nthcdr 5 x) defs types name opts
                        {`(,(car x),(caddr x),(fourth x),(fifth x)) :. slots} doc)
                (struct (nthcdr 3 x) defs types name opts
                        {`(,(car x),(caddr x)) :. slots} doc)}
         {keywordp (cadr x) && caddr x == '=
            $ if {fifth x == :read-only}
                (struct (nthcdr 6 x) defs types name opts
                        {`(,(car x),(cadddr x):type,(keyword-type-spec(cadr x)),@(subseq x 4 6)) :. slots} doc)
                (struct (nthcdr 4 x) defs types name opts
                        {`(,(car x),(cadddr x):type,(keyword-type-spec(cadr x))) :. slots} doc)}
         {t $ if {cadr x == :read-only}
                (struct (cdddr x) defs types name opts
                        {subseq x 0 3 :. slots} doc)
                (struct (cdr x) defs types name opts
                        {car x :. slots} doc)};

 defparameter *def-symbol*
   '((var          . defvar)
     (parameter    . defparameter)
     (constant     . defconstant)
     (symbol-macro . define-symbol-macro));

 defparameter *def-macro*
   '((type           . deftype)
     (compiler-macro . define-compiler-macro));

 defparameter *def-function* ();

 defparameter *def-method* ();

 sbind* e &optional binds s current decls :=
   labels make-bind s e = `(,s ,(singleton (binfix (nreverse e))))
      cond {null e
              $ let* current = (nreverse current)
                     e = (pop current)
                  cdr {nreverse $ `(,s ,e) :. binds} .x. decls .x. current}
           {car e in *decls* || listp (car e) && caar e in *decls*
              $ cdr (nreverse {make-bind s current :. binds}) .x. decls .x. e}
           {car e == ';
              $ cdr (nreverse {make-bind s current :. binds}) .x. decls .x. cdr e}
           {cadr e == '=
              $ sbind* (cddr e)
                       {make-bind s current :. binds} (car e) ()
                       decls}
           {keywordp (cadr e) && caddr e == '=
              $ sbind* (cdddr e)
                       {make-bind s current :. binds} (car e) ()
                      `((type,(keyword-type-spec (cadr e)),(car e)),@decls)}
           {t $ sbind* (cdr e)
                       binds s {car e :. current}
                       decls};

 def-sbind* binds :==
   `(sbind* (cdr (if {car (last,binds) == ';}
                        ,binds
                    `(,@,binds ;))));

 defclass-body b &optional slot slots class-opts :=
   if {null b || car b == ';}
      (values `(,{cdr $ nreverse $ if slot {reverse slot :. slots} slots}
                ,@(nreverse class-opts))
              (cdr b))
      let e = (pop b)
          cond {keywordp e
                  $ cond {e == :default-initargs
                            $ let* br = {'; in b}
                                   inits = (ldiff b br)
                                defclass-body br slot slots `((:default-initargs ,@inits) ,@class-opts)}
                         {slot $ defclass-body (cdr b) {car b :. e :. slot} slots class-opts}
                         {t $ defclass-body (cdr b) () slots `((,e,(car b)) ,@class-opts)}}
               {symbolp e
                  $ defclass-body b (when e `(,e)) {reverse slot :. slots} class-opts}
               {t $ error "BINFIX def class contains ~A" e};

 defs x &optional defs types :=
   labels check-def x assgn *x* descr =
     {let def = (binfix (cdr x))
        if {assgn in cdr x}
           (defs () `((,(cdr (assoc (car x) *x*)) ,@(cdr def)) ,@defs) types)
           (error "BINFIX def ~A instead of ~A definition has~%~S" (car x) descr (cdr x))}
    cond {null x
            $ `(,@{types && nreverse types}
                ,@(nreverse defs))}
         {assoc (car x) *def-symbol*
            $ binds decl* r =.. (def-sbind* x)
                {decl* r =.. (decls r (declare* decl* declaim))
                   (defs r (revappend {let def = (cdr (assoc (car x) *def-symbol*))
                                         (mapcar {a -> def :. a} binds)}
                                      defs)
                        (if decl* {append decl* types} types))}}
         {assoc (car x) *def-macro*    $ check-def x ':== *def-macro*    "macro"}
         {assoc (car x) *def-function* $ check-def x ':=  *def-function* "function"}
         {assoc (car x) *def-method*   $ check-def x ':-  *def-method*   "method"}
         {car x == '#-sbcl{struct}
                    #+sbcl{sb-alien:struct}
            $ assgn types r =.. (struct (cdr x) defs types)
                (defs r assgn types)}
         {car x == 'class
            $ class-def r =..(defclass-body (cdddr x))
                (defs r `((defclass ,(cadr x) ,(caddr x) ,@class-def) ,@defs) types)}
         {find-if {e -> e in '(:= :== :- :type=)} x
            $ `(,(binfix x))}
         {car x == 'binfix
            $ `((defbinfix ,@(cdr x)))}
         {t $ error "BINFIX def has a trailing:~%~S" x};

 defparameter *decls* '(declare declaim);

 decls e &optional decls doc :=
  labels var*-keyword e &optional vars =
    (cond {null e           $ nil .x. nreverse vars}
          {keywordp (car e) $ keyword-type-spec (car e) :. reverse vars .x. cdr e}
          {symbolp (car e)  $ var*-keyword (cdr e) {car e :. vars}}
          {t                $ error "BINFIX declaration got ~A instead of symbol." (car e)})
  {let s = (car e)
    (cond {s in *decls*
             $ if (symbolp (cadr e))
                 {vars r =.. (var*-keyword (cdr e))
                   (decls r  ;;{vars && s :. r}
                          {if vars {`(,s,vars) :. decls} decls}
                          doc)}
                 (decls (cddr e) {`(,s,(cadr e)):. decls} doc)}
          {listp s && car s in *decls*
             $ decls (cdr e) {s :. decls} doc}
          {t $ `(,@doc ,@decls) .x. e})};

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

 lbinds e :=
   let *decls* = '(declare)
     binds decls r =.. (sbind* e)
       decls e =.. (decls r (declare* decls))
          `(,binds ,@(nreverse decls)) .x. e;

 fbinds e &optional binds name llist body :=
   symbol-macrolet
     finish =
       {decl* r =.. (decls (if name {name :. revappend llist (nreverse body)}
                                            {revappend llist (nreverse body)}))
          `(,(nreverse binds) ,@(declare* decl*)) .x. r}
   {labels
     bind n ll d b =
       {ll ldecl* =.. (lambda-list (nreverse ll))
          decl* body =.. (decls (nreverse b) ldecl*)
            `(,n ,ll ,@decl* ,@d ,(singleton (binfix body))) :. binds}
    cond {null e
            $ if body
                {decl* r =.. (decls (nreverse body))
                  `(,(nreverse (bind name llist decl* `(,(pop r))))) .x. r}
                finish}
         {car e == ':=
            $ if body
                {decl* r =.. (decls (nreverse body))
                   fbinds (cddr e)
                          (bind name llist decl* `(,(pop r)))
                          (pop r)
                          (nreverse r)
                         `(,(cadr e))}
                (fbinds (cddr e) binds name llist `(,(cadr e)))}
         {car e == ';
            $ if body
                (fbinds (cdr e) (bind name llist () body))
                finish}
         {body  $ fbinds (cdr e) binds name llist {car e :. body}}
         {llist $ fbinds (cdr e) binds name {car e :. llist} body}
         {name  $ fbinds (cdr e) binds name `(,(car e))}
         {t     $ fbinds (cdr e) binds (car e)}};


 *binfix* =.
   `((( <&              prog1)
      ( <&..            multiple-value-prog1))
     ((  &              progn           :unreduce))
     (( def             defs            :macro));;------------DEFINITIONS
     (( let             let             :rhs-lbinds);;-------LET constructs
      ( let*            let*            :rhs-lbinds)
      ( symbol-macrolet symbol-macrolet :rhs-lbinds)
      ( prog*           prog*           :rhs-lbinds)
      ( prog            prog            :rhs-lbinds))
     (( macrolet        macrolet        :rhs-fbinds)
      ( flet            flet            :rhs-fbinds)
      ( labels          labels          :rhs-fbinds))
     (( :==             defmacro        :def)
      ( :=              defun           :def)
      ( :-              defmethod       :defm)
      ( :type=          deftype         :def))
     (( block    block     :prefix);;------------------------PREFIX FORMS
      ( tagbody  tagbody   :prefix)
      ( catch    catch     :prefix)
      ( prog1    prog1     :prefix)
      ( prog2    prog2     :prefix)
      ( progn    progn     :prefix)
      ( cond     cond      :prefix);;------------------------COND/CASE FORMS
      ( case     case      :prefix)
      ( ccase    ccase     :prefix)
      ( ecase    ecase     :prefix)
      ( typecase typecase  :prefix)
      (etypecase etypecase :prefix)
      (ctypecase ctypecase :prefix))
     ((  ?   ()         :split));;----------------------------$pliters
     ((  $   ()         :split))
     (( .=   setf) ;;----------------------------------------ASSIGNMENT
      ( +=   incf)
      ( -=   decf)
      (  =.  setq)
      ( .=.  set));; DEPRECIATED
     (( setq setq  :rhs-sbinds)
      ( set  set   :rhs-sbinds)
      (psetq psetq :rhs-sbinds))
     (( setf setf  :rhs-ebinds)
      (psetf psetf :rhs-ebinds))
     ((.@    mapc       :rhs-args) ;;-------------------------MAPPING
      (..@   mapl       :rhs-args)
      ( @/   reduce     :rhs-args)
      ( @.   mapcar     :rhs-args)
      ( @..  maplist    :rhs-args)
      ( @n   mapcan     :rhs-args)
      ( @.n  mapcon     :rhs-args)
      ( @@   apply      :rhs-args)
      ( .@.  multiple-value-call  :rhs-args)
      ( @    funcall    :rhs-args :left-assoc :also-postfix))
     (( :->  function   :lhs-lambda))
     (( ->   lambda     :lhs-lambda))
     (( =..  multiple-value-bind  :syms/expr));;--------------MULTIPLE VALUES/DESTRUCTURING
     (( ..=  destructuring-bind   :lambda/expr))
     ((values values    :prefix)
      ( .x.   values    :unreduce :also-prefix));; :also-prefix depreciated
     (( loop ,#'identity   :prefix))
     (( ||       or     :unreduce);;-------------------------LOGICAL OPS
      ( or       or     :unreduce :also-prefix))
     (( &&       and    :unreduce)
      ( and      and    :unreduce :also-prefix))
     (( ===      equalp))
   ;;(( equalp   equalp)) ;; DEPRECIATED
     (( equal    equal))
     (( ==       eql))
     (( eql      eql    :also-prefix))
     (( eq       eq))
     (( subtype-of subtypep))
     (( :.       cons))
     (( in       member))
     (( th-cdr   nthcdr))
     (( =s=      string=))
     (( =c=      char=  :unreduce))
     ((  =        =     :unreduce :also-prefix))
     (( /=       /=     :unreduce :also-prefix))
     (( <        <      :unreduce :also-prefix));;------------COMPARISONS
     (( >        >      :unreduce :also-prefix))
     (( <=       <=     :unreduce :also-prefix))
     (( >=       >=     :unreduce :also-prefix))
     ;;-----------------------------------END OF COMPARISONS
     (( th-bit   logbitp))
     ;;================ :lower  binding user defined ops go here =================
     ;;================ :higher binding user defined ops go here =================
     (( coerce   coerce))
     (( !..      nth-value) ;;----------------------INDEXING 
      ( th-value nth-value))
     (( th       nth))
     (( .!       elt) 
      ( !.       svref)
      ( !!.      row-major-aref))
     (( !!       aref      :rhs-args))
     ((.!!.      bit       :rhs-args))
     ((.eqv.     bit-eqv   :rhs-args))
     ((.or.      bit-ior   :rhs-args))
     ((.xor.     bit-xor   :rhs-args))
     ((.and.     bit-and   :rhs-args))
     ((.nand.    bit-and   :rhs-args))
     ((.nor.     bit-nor   :rhs-args))
     ((.not.     bit-not   :also-unary))
     ((.orc1.    bit-orc1  :rhs-args))
     ((.orc2.    bit-orc2  :rhs-args))
     ((.andc1.   bit-andc1 :rhs-args))
     ((.andc2.   bit-andc2 :rhs-args))
     (( dpb           dpb           :rhs-args))
     (( ldb           ldb))
     (( ldb-test      ldb-test))
     (( deposit-field deposit-field :rhs-args))
     (( mask-field    mask-field))
     (( byte          byte))
     (( eqv.     logeqv    :also-unary :unreduce))
     (( or.      logior    :also-unary :unreduce))
     (( xor.     logxor    :also-unary :unreduce))
     (( and.     logand    :also-unary :unreduce))
     (( nand.    lognand))
     (( nor.     lognor))
     (( test.    logtest))
     (( orc1.    logorc1))
     (( orc2.    logorc2))
     (( andc1.   logandc1))
     (( andc2.   logandc2))
     (( <<       ash));;--------------------------------------ARITHMETICS
     (( lcm      lcm     :also-unary  :unreduce))
     (( gcd      gcd     :also-unary  :unreduce))
     (( mod      mod))
     (( rem      rem))
     (( min      min     :also-prefix :unreduce)
      ( max      max     :also-prefix :unreduce))
     ((  +        +      :also-unary  :unreduce))
     ((  -        -      :also-unary  :unreduce))
     ((  /        /      :also-unary))
     ((  *        *      :also-prefix :unreduce))
     (( **       expt))
     (( .!.      bit     :rhs-args));;------------------------ARRAY INDEXING
     ((  !       aref    :rhs-args))
     ((  ;        ;)));

 assign-properties :=
   let p = 0
      mapc {l -> {incf p;
                  mapc {s -> {get (car s) 'properties .= p :. cdr s}} l}}
           *binfix* ;

 (assign-properties);

 split e op &optional args arg :=
    cond {null e      $ nreverse $ nreverse arg :. args}
         {car e == op $ split (cdr e) op {nreverse arg :. args}}
         {t           $ split (cdr e) op args {car e :. arg}};

 find-op-in e &optional (p 1000) o.r :=
    cond {null e $ o.r}
         {symbolp (car e)
            $ let q = (get (car e) 'properties)
                 if {q && {< (car q) p
                           || = (car q) p
                              && cddr q
                              && null (intersection
                                        '(:rhs-args    :unreduce
                                          :lhs-lambda  :left-assoc
                                          :lambda/expr :macro :split
                                          :syms/expr)
                                        (cddr q))}}
                   {find-op-in (cdr e) (car q) e}
                   {find-op-in (cdr e) p o.r}}
         {t $ find-op-in (cdr e) p o.r};

 binfix e &optional (max-priority 1000) :=
   labels
     unreduce e op &optional args arg =
       (cond {null e      $ reverse {binfix (reverse arg) :. args}}
             {car e == op $ unreduce (cdr e) op {binfix (reverse arg) :. args}}
             {t           $ unreduce (cdr e) op args {car e :. arg}})

     binfix+ e =
       (if {'; in e}
          (if {'; == car (last e)}
             (binfix+ (butlast e))
             (mapcar #'singleton (unreduce e ';)))
         `(,(singleton (binfix e))))

     decl*-binfix+ rhs decls =
       {decl* body =.. (decls rhs decls)
         `(,@decl* ,@(binfix+ body))}

     doc*-decl*-binfix+ rhs decls =
       {doc*-decl* body =.. (doc-decls rhs decls)
         `(,@doc*-decl* ,@(binfix+ body))}

     sbinds e &optional converted s current =
       {symbol-macrolet
          convert = `(,(singleton (binfix (reverse current))),s,@converted)
            cond {null e      $ cddr $ reverse convert}
                 {cadr e =='= $ sbinds (cddr e) convert (car e)}
                 {t           $ sbinds (cdr e)  converted s {car e :. current}}}

     e-binds e &optional binds lhs rhs =
       {labels b-eval-rev e = (singleton
                                (if {consp e && > (length e) 1}
                                   (binfix {singleton $ nreverse e})
                                   e))
               bind lhs rhs = {b-eval-rev rhs :. b-eval-rev lhs :. binds}
          cond {null e     $ if {lhs && rhs}
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
               {t          $ e-binds (cdr e) binds {car e :. lhs}          rhs}}

  if {atom e} e
    let rhs = (find-op-in e max-priority)
      if (null rhs) e
        let* lhs = (ldiff e rhs)
             op = (pop rhs)
             op-prop = (get op 'properties)
            priority = (pop op-prop)
             op-lisp = (pop op-prop)
           cond {op == '; $ error "BINFIX: bare ; in:~% ~{ ~A~}" e}
                {null rhs $
                   if {:also-postfix in op-prop}
                      `(,op-lisp,@(binfix lhs))
                       (error "BINFIX: missing r.h.s. of ~S (~S)~@
                               with l.h.s:~%~S" op op-lisp lhs)}
                {:rhs-lbinds in op-prop $
                   binds-decls* expr =.. (lbinds rhs)
                     singleton (binfix `(,@lhs (,op-lisp ,@binds-decls* ,@(binfix+ expr))))}
                {:syms/expr  in op-prop $
                   vars decls =.. (vbinds lhs)
                      `(,op-lisp ,vars ,(car rhs)
                                 ,@{decls && `((declare ,@decls))}
                                 ,@(decl*-binfix+ (cdr rhs) ()))}
                {:rhs-sbinds in op-prop $
                   singleton (binfix `(,@lhs (,op-lisp ,@(sbinds rhs))))}
                {:rhs-ebinds in op-prop $
                   binds r =.. (e-binds rhs)
                     singleton (binfix `(,@lhs (,op-lisp ,@binds) ,@r))}
                {:rhs-fbinds in op-prop $
                   binds-decls* expr =.. (fbinds rhs)
                     singleton (binfix `(,@lhs (,op-lisp ,@binds-decls* ,@(binfix+ expr))))}
                {functionp op-lisp $
                   if (null lhs)
                      {op :. funcall op-lisp {binfix rhs priority}}
                      (binfix `(,@lhs,{op :. funcall op-lisp (binfix rhs priority)}))}
                {:lhs-lambda in op-prop $
                   ll decls =.. (lambda-list lhs)
                      `(,op-lisp ,ll ,@(decl*-binfix+ rhs decls))}
                {:macro in op-prop $
                  `(progn ,(binfix lhs) ,@(reduce #'append (mapcar op-lisp (split rhs op))))}
                {:unreduce in op-prop && position op rhs $ ;;position necessary...
                  let u = (mapcar #'singleton (unreduce rhs op `(,(binfix lhs),op-lisp)))
                     cond {lhs $ u}
                          {:also-unary  in op-prop $ `(,op-lisp (,op-lisp ,(caddr u)) ,@(cdddr u))}
                          {:also-prefix in op-prop $ `(,op-lisp (,op-lisp,@(caddr u)) ,@(cdddr u))}
                          {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                      with r.h.s:~%~S" op op-lisp rhs}}
                {null lhs $ cond{:also-unary  in op-prop $ `(,op-lisp ,(singleton (binfix rhs)))}
                                {:also-prefix in op-prop || :prefix in op-prop
                                                         $ `(,op-lisp ,@(if {'; in rhs}
                                                                          (binfix+ rhs)
                                                                          (binfix rhs)))}
                                {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                            with r.h.s:~%~S" op op-lisp rhs}}
                {:def in op-prop $ ll decls =.. (lambda-list (cdr lhs))
                                    `(,op-lisp ,(car lhs) ,ll
                                               ,@(doc*-decl*-binfix+ rhs decls))}
                {:defm in op-prop $
                   `(,op-lisp ,(pop lhs) ,@(cond {consp (car lhs) && null (cdar lhs) $ pop lhs}
                                                 {keywordp (car lhs) $ list (pop lhs)})
                              ,@{ll decls =.. (method-lambda-list lhs)
                                  `(,ll ,@(doc*-decl*-binfix+ rhs decls))})}
                {:left-assoc in op-prop && position op rhs $
                   let* j = (position op rhs)
                       lrhs = (subseq rhs 0 j)
                       rrhs = (subseq rhs j)
                       binfix`((,op-lisp ,(singleton (binfix  lhs))
                                         ,(singleton (binfix lrhs))) ,@rrhs)}
                {:lambda/expr in op-prop $
                   llist decls =.. (lambda-list lhs)
                     `(,op-lisp ,llist ,(car rhs)
                                ,@(decl*-binfix+ (cdr rhs) decls))}
                {:split in op-prop $
                   `(,(if {lhs && null (cdr lhs)} (car e) (binfix lhs))
                     ,{when rhs
                         let e = (binfix rhs)
                            (if (cdr e) e (car e))})}
                {:prefix in op-prop $ binfix `(,@lhs ,(binfix `(,op,@rhs)))}
                (t `(,op-lisp
                     ,(singleton (binfix lhs))
                     ,@(cond {null (cdr rhs) $ rhs}
                             {:rhs-args in op-prop $
                                cond {find-op-in rhs (1+ priority)
                                                $ `(,(binfix rhs))}
                                     {'; in rhs $ binfix+ rhs}
                                     {t         $ rhs}}
                             {t $ `(,(binfix rhs))})))}

;===== BINFIX defined =====
