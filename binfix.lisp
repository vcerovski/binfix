; BINFIX by V.Cerovski 2015,9

(in-package :binfix)

{singleton x := if {consp x && null (cdr x)} (car x) x;

 keyword-type-spec k :=
   let S = {singleton $ read-from-string
                          (concatenate 'string "(" (symbol-name k) ")")
                          () :eof}
     cond {symbolp S && not (keywordp S) $ S}
          {listp S $ case (car S)
                       { lambda   $ `(function ,@(cdr S))}
                       { function $ `(ftype (function ,@(cdr S)))}
                       { t        $ S }}
          {t       $ error "Incorrect BINFIX keyword-type specifier ~S" k};

 type-keyword-type s ktype :=
   let type = (keyword-type-spec ktype)
     if {symbolp type || not {car type in `(type ftype)}}
       `(type ,type ,s)
       `(    ,@type ,s);

 &lambdap s :== `{,s in lambda-list-keywords};

 declare* decl* &optional (decl 'declare) :==
   `{,decl* && list {',decl :. nreverse ,decl*}};

 collect-&parts l &optional arg types :=
   labels ?-symbol-p      s = {symbol-name s ! 0 =c= #\?}
          ?-symbol-symbol s = {intern $ subseq (symbol-name s) 1}
   if (null l) {nreverse arg .x. declare* types}
     let s = (pop l)
        cond {listp s || &lambdap s $ collect-&parts l {s :. arg} types}
             {symbolp s $
               let n = (car l)
                 {when (keywordp n)
                   {push (type-keyword-type s n) types;
                    pop l;
                    n =. car l};
                  if {n == '=}
                    (if (?-symbol-p (caddr l))
                      (collect-&parts (cdddr l) `((,s,(cadr l),(?-symbol-symbol (caddr l))),@arg) types)
                      (collect-&parts (cddr l)  `((,s,(cadr l)                            ),@arg) types))
                    (collect-&parts l `(,s,@arg) types)}}
             {t $ error "BINFIX lambda-list cannot collect-&parts of ~S" l};

 lambda-list l &optional arg types :=
   if (null l) {nreverse arg .x. declare* types}
     let s = (pop l)
        cond {symbolp s $
               cond {keywordp (car l) $
                      if {cadr l == '=}
                        (collect-&parts `(&optional,s,@l) arg types)
                        (lambda-list (cdr l) `(,s,@arg) {type-keyword-type s (car l) :. types})}
                    {s =='&whole $ lambda-list (cdr l) `(,(car l),s,@arg) types}
                    { &lambdap s $ collect-&parts l `(,s,@arg) types}
                    {car l == '= $ collect-&parts `(&optional,s,@l) arg types}
                    {          t $ lambda-list l `(,s,@arg) types}}
             {listp s $
               ll decls =.. (lambda-list s)
                 lambda-list l {ll :. arg} (append (cdar decls) types)}
             {t $ error "BINFIX lambda-list expects symbol or list instead of ~S~@
                         ~S" l (nreverse arg)};

 sym-eql s1 s2 := symbolp s1 && symbolp s2 && keywordp s1 == keywordp s2 && symbol-name s1 =s= symbol-name s2;

 semicolon-in e :== `(member '; ,e :test 'sym-eql);

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
                    {sym-eql (car l) '==
                                 $ method-lambda-list (cddr l) {`(,s (eql,(cadr l))) :. args}}
                    {         t  $ method-lambda-list l {s :. args}}}
             {listp s $ method-lambda-list l {s :. args}}
             {t $ error "BINFIX method-lambda-list expects symbol or list, not ~S" s};

 dstruct x &optional defs types name opts slots doc :=
    cond {null x || sym-eql (car x) ';
            $ `(defstruct ,(if opts `(,name,@(nreverse opts)) name)
                                  ,@{doc && `(,doc)} ,@(nreverse slots)) :. defs
               .x. types .x. cdr x}
         {null name
            $ dstruct (cdr x) defs types (car x)}
         {stringp (car x)
            $ if doc
                (error "BINFIX def struct ~A has two doc-strings,~%~S~%and~%~S" name doc (car x))
                (dstruct (cdr x) defs types name opts slots (car x))}
         {keywordp (car x)
            $ cond {car x == :named
                      $ dstruct (cdr x) defs types name
                               {:named :. opts} slots doc}
                   {car x == :constructor
                      $ dstruct (cdddr x) defs types name
                              `((:constructor,(cadr x),(lambda-list (caddr x))),@opts) slots doc}
                   {t $ dstruct (cddr x) defs types name
                               {`(,(car x),(cadr x)) :. opts} slots doc}}
         {cadr x == '=
            $ if {fourth x in '(:type :read-only)}
                (dstruct (nthcdr 5 x) defs types name opts
                        {`(,(car x),(caddr x),(fourth x),(fifth x)) :. slots} doc)
                (dstruct (nthcdr 3 x) defs types name opts
                        {`(,(car x),(caddr x)) :. slots} doc)}
         {keywordp (cadr x) && caddr x == '=
            $ if {fifth x == :read-only}
                (dstruct (nthcdr 6 x) defs types name opts
                        {`(,(car x),(cadddr x):type,(keyword-type-spec(cadr x)),@(subseq x 4 6)) :. slots} doc)
                (dstruct (nthcdr 4 x) defs types name opts
                        {`(,(car x),(cadddr x):type,(keyword-type-spec(cadr x))) :. slots} doc)}
         {t $ if {cadr x == :read-only}
                (dstruct (cdddr x) defs types name opts
                        {subseq x 0 3 :. slots} doc)
                (dstruct (cdr x) defs types name opts
                        {car x :. slots} doc)};

 defparameter *def-symbol*
   '((var          . defvar)
     (parameter    . defparameter)
     (constant     . defconstant)
     (symbol-macro . define-symbol-macro));

 defparameter *decls* '(declare declaim);

 decls e &optional decls doc :=
  labels var*-keyword e &optional vars =
    (cond {null e           $ nil .x. nreverse vars}
          {keywordp (car e) $ 'type :. keyword-type-spec (car e) :. reverse vars .x. cdr e}
          {symbolp (car e)  $ var*-keyword (cdr e) {car e :. vars}}
          {consp (car e) && caar e in '(type ftype)
                            $ `(,@(car e) ,@(reverse vars)) .x. cdr e}
          {consp (car e) && caar e == 'function
                            $ `(ftype ,(car e) ,@(reverse vars)) .x. cdr e}
          {consp (car e) && caar e == 'lambda
                            $ `(type (function ,@(cdar e)) ,@(reverse vars)) .x. cdr e}
          {t                $ error "BINFIX decl. of ~A got ~A instead of type-specifier." (nreverse vars) (car e)})
   let s = (car e)
     cond {s in *decls*
             $ if (symbolp (cadr e))
                 {vars r =.. (var*-keyword (cdr e))
                    decls r  ;;{vars && s :. r}
                          {if vars {`(,s,vars) :. decls} decls}
                          doc}
                 (decls (cddr e) {`(,s,(cadr e)):. decls} doc)}
          {listp s && car s in *decls*
             $ decls (cdr e) {s :. decls} doc}
          {t $ `(,@doc ,@decls) .x. e};

 doc-decls e &optional decls :=
   if {stringp (car e) && cdr e}
      (decls (cdr e) decls `(,(car e)))
      (decls e decls);

 sbind* e &optional binds s current decls :=
   labels make-bind s e = `(,s ,(binfix (nreverse e)))
      cond {null e
              $ let* current = (nreverse current)
                     e = (pop current)
                  cdr {nreverse $ `(,s ,e) :. binds} .x. decls .x. current}
           {car e in *decls* || listp (car e) && caar e in *decls*
              $ cdr (nreverse {make-bind s current :. binds}) .x. decls .x. e}
           {sym-eql (car e) ';
              $ cdr (nreverse {make-bind s current :. binds}) .x. decls .x. cdr e}
           {cadr e == '=
              $ sbind* (cddr e)
                       {make-bind s current :. binds} (car e) ()
                       decls}
           {keywordp (cadr e) && caddr e == '=
              $ sbind* (cdddr e)
                       {make-bind s current :. binds} (car e) ()
                       {type-keyword-type (car e) (cadr e) :. decls}}
           {t $ sbind* (cdr e)
                       binds s {car e :. current}
                       decls};

 mvbind e &optional syms decls :=
   labels errorm m = (error (format nil "BINFIX: ~A~~% Read ~~{ ~~A~~}~% Remain ~~{ ~~A~~}" m)
                            (nreverse syms) e)
   cond {null e $ errorm "Incomplete LET.  Missing = ?"}
        {car e == '=
           $ if (null syms) (errorm "No symbols to bind in LET.")
               let r = (semicolon-in (cdr e))
                 if (null r) (errorm "Incomplete LET. Missing ; ?")
                   {nreverse syms .x. binfix (ldiff (cdr e) r) .x. decls .x. cdr r}}
        {sym-eql (car e) '; $ errorm "Missing body of LET."}
        {keywordp (cadr e)
           $ mvbind (cddr e) {car e :. syms} {type-keyword-type (car e) (cadr e) :. decls}}
        {t $ mvbind (cdr e) {car e :. syms} decls};

 dbind e &optional llist :=
   cond {cadr e == '=
           $ let* r = (semicolon-in (cddr e))
                  llist = (if llist {nreverse $ car e :. llist}
                                    (car e))
                  e = (cddr e)
               {llist decls =.. (lambda-list llist)
                  if r {llist .x. binfix (ldiff e r) .x. decls .x. cdr r}
                       {llist .x.          (car e)   .x. decls .x. cdr e}}}
        {t $ dbind (cdr e) {car e :. llist}};

 def-sbind* binds :==
   `(sbind* (cdr (if (sym-eql (car (last,binds)) ';)
                        ,binds
                    `(,@,binds ;))));

 def-class b &optional slot slots class-opts :=
   if {null b || sym-eql (car b) ';}
      (values `(,{cdr $ nreverse $ if slot {reverse slot :. slots} slots}
                ,@(nreverse class-opts))
              (cdr b))
      let e = (pop b)
          cond {keywordp e
                  $ cond {e == :default-initargs
                            $ let* br = {semicolon-in b}
                                   inits = (ldiff b br)
                                def-class br slot slots `((:default-initargs ,@inits) ,@class-opts)}
                         {slot $ def-class (cdr b) {car b :. e :. slot} slots class-opts}
                         {t $ def-class (cdr b) () slots `((,e,(car b)) ,@class-opts)}}
               {symbolp e
                  $ def-class b (when e `(,e)) {reverse slot :. slots} class-opts}
               {t $ error "BINFIX def class contains ~A" e};

 mbind n ll d b :=
   ll ldecl* =.. (method-lambda-list ll)
     decl* body =.. (decls b ldecl*)
       `(,n ,ll ,@decl* ,@d ,(binfix body));

 unreduce-rhs op e &optional cdr-p form0 forms := ;; better version of collect-d=, returns also leading expr.
   labels
     last-semi e &optional last =
       (cond {null e      $ last}
             {sym-eql (car e) ';
                          $ last-semi (cdr e) e}
             {t           $ last-semi (cdr e) last})
     pair-forms forms &optional pairs =
       (if (null forms) (nreverse pairs)
          (pair-forms (cddr forms) {{car forms :. cadr forms} :. pairs}))
   let rhs = {member op e :test 'sym-eql}
     (if (null rhs)
        {pair-forms {nreverse $ e :. forms} .x. form0}
        {let* lhs = (ldiff e rhs)
              lhs-r = (last-semi lhs)
              lhs-l = (ldiff lhs lhs-r)
           (if cdr-p
              (unreduce-rhs op (cdr rhs) t form0 {cdr lhs-r :. lhs-l :. forms})
              (unreduce-rhs op (cdr rhs) t {lhs-r && lhs-l} {if lhs-r (cdr lhs-r) lhs-l :. forms}))});

 def-generic b &optional params entries :=
   cond {null b
           $ `(,@(method-lambda-list params) ,@(nreverse entries)) .x. ()}
        {null params
           $ let rest = {semicolon-in b} ;; ;-terminated method lambda list.
               if rest
                 (def-generic (cdr rest) {let h =(ldiff b rest) `(,(car h),(cdr h))})
                 (def-generic () `(,(car b),(cdr b)))}
        {stringp (car b)
           $ def-generic (cdr b) params `((:documentation,(car b)) ,@entries)}
        {car b in '(declare :generic-function-class :method-class)
           $ def-generic (cddr b) params `((,(car b),(cadr b)) ,@entries)}
        {car b in '(:argument-precedence-order :method-combination)
           $ loop for nxt = (cdr b) then (cdr nxt)
                  until {null nxt || keywordp (car nxt) || sym-eql (car nxt) ';}
                  finally (def-generic nxt params `(,(ldiff b nxt) ,@entries))}
        {':- in b
           $ `(,@(method-lambda-list params)
               ,@(nreverse entries)
               ,@(mapcar {mdef -> mbind :method (car mdef) () (cdr mdef)}
                         (unreduce-rhs :- b))) .x. ()}
      ;;{car b == '; ;; doen't work because ; is consumed at this point.
      ;;   $ `(,@(method-lambda-list params) ,@(nreverse entries)) .x. cdr b}
        {t $ error "BINFIX def generic has a trailing ~S" (ldiff b {semicolon-in b})};

 defs x &optional defs types :=
    cond {sym-eql (car x) 'generic
            $ defgen r =.. (def-generic (cdr x))
                defs r `((defgeneric ,@defgen) ,@defs) types}
         {assoc (car x) *def-symbol* :test 'sym-eql
            $ if {null (cddr x) || sym-eql (caddr x) ';} ;; It's a hack, sbind* should support it.
                (defs (cdddr x) `((,(cdr (assoc (car x) *def-symbol* :test 'sym-eql)),(cadr x)) ,@defs) types)
                {binds decl* r =.. (def-sbind* x)
                  decl* r =.. (decls r (declare* decl* declaim))
                    defs r (revappend {let def = (cdr (assoc (car x) *def-symbol* :test 'sym-eql))
                                          mapcar {a -> def :. a} binds}
                                      defs)
                         (if decl* {append decl* types} types)}}
         {sym-eql (car x) 'struct
            $ assgn types r =.. (dstruct (cdr x) defs types)
                (defs r assgn types)}
         {sym-eql (car x) 'class
            $ class-def r =..(def-class (cdddr x))
                (defs r `((defclass ,(cadr x) ,(caddr x) ,@class-def) ,@defs) types)}
         {sym-eql (car x) 'binfix
            $ `((defbinfix ,@(cdr x)))}
         {t $ if {defs || types}
                 {progn-monad
                   `(progn ,@{types && nreverse types}
                           ,@(nreverse defs))
                   (binfix x)}
                 (error "BINFIX def has a trailing:~% ~S~%" x)};

 vbinds e &optional vars decls :=
   cond {null e $ reverse vars .x. reverse decls}
        {symbolp (car e) && not (keywordp (car e)) $
            if (keywordp (cadr e))
              (vbinds (cddr e)
                      {car e :. vars}
                      {type-keyword-type (car e) (cadr e) :. decls})
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

 slots+ e &optional slots decls :=
   cond {null e $ error "BINFIX: Empty body of slots ~S." (nreverse slots)}
        {car e == :_
           $ {cadr e .x. cddr e .x. nreverse slots .x. nreverse decls}}
        {cadr e == '= ;; s = s'
           $ slots+ (cdddr e) {`(,(car e),(caddr e)) :. slots} decls}
        {keywordp (cadr e) && not {cadr e == :_} ;; so type "_" cannot be specified as :_ here!
           $ if {caddr e == '=}  ;; s type = s'
                (slots+ (cddddr e) {`(,(car e),(cadddr e)) :. slots} {type-keyword-type (car e) (cadr e) :. decls})
                (slots+ (cddr e) {car e :. slots} {type-keyword-type (car e) (cadr e) :. decls})}
        {t $ slots+ (cdr e) {car e :. slots} decls};

 slots e :=
   let *decls* = '(declare)
     s r slots decls =.. (slots+ e)
       decls e =.. (decls r (declare* decls))
          `(,slots ,s ,@(nreverse decls)) .x. e;

 fbinds e def :=
   cond {car e ==  def   $ `(,(cdr e))}
        {car e == 'progn $ mapcan {d -> fbinds d def} (cdr e)}
        {t $ error "BINFIX expects ~S, found:~%   ~S" def (car e)};

 defs-macro &rest defs :== defs defs;

 hashget table key &rest opt :== `(gethash ,key ,table ,@opt);

 *binfix* =.
   `((( <&              prog1)
      ( <&..            multiple-value-prog1))
     ((  &              progn           :progn))

     (( def                       nil                       :binfix-defs              ) ;;---------DEFINITIONS
      ;; data defs
      ( defclass                  defclass                  :progn :prefix :quote-rhs )
      ( defstruct                 defstruct                 :progn :prefix :quote-rhs )
      ( deftype                   deftype                   :progn :prefix :quote-rhs )
      ( defparameter              defparameter              :progn :prefix :quote-rhs )
      ( defvar                    defvar                    :progn :prefix :quote-rhs )
      ( defconstant               defconstant               :progn :prefix :quote-rhs )
      ;; error conditions
      ( define-condition          define-condition          :progn :prefix :quote-rhs )
      ;; setf
      ( define-setf-expander      define-setf-expander      :progn :prefix :quote-rhs )
      ( define-setf-method        define-setf-method        :progn :prefix :quote-rhs )
      ( defsetf                   defsetf                   :progn :prefix :quote-rhs )
      ;; generic functions
      ( defgeneric                defgeneric                :progn :prefix :quote-rhs )
      ( defmethod                 defmethod                 :progn :prefix :quote-rhs )
      ( define-method-combination define-method-combination :progn :prefix :quote-rhs )
      ;; functions
      ( defun                     defun                     :progn :prefix :quote-rhs )
      ;; macro functions
      ( defmacro                  defmacro                  :progn :prefix :quote-rhs )
      ( define-compiler-macro     define-compiler-macro     :progn :prefix :quote-rhs )
      ( define-symbol-macro       define-symbol-macro       :progn :prefix :quote-rhs )
      ( define-modify-macro       define-modify-macro       :progn :prefix :quote-rhs )
      ;; global declarations
      ( declaim                   declaim                   :progn :prefix :quote-rhs )
      ( proclaim                  proclaim                  :progn :prefix :quote-rhs ))

     (( :==             defmacro        :def  ((type           . deftype)
                                               (compiler-macro . define-compiler-macro)))
      ( :=              defun           :def                                            )
      ( :-              defmethod       :defm                                           )
      ( :type=          deftype         :def                                            ))

     (( cond       cond          :rhs-implicit-progn => :prefix)  ;; does not require => to have priority; :rhs-implicit-progn must be first prop.
      ( case       case          :rhs-implicit-progn => :prefix)  ;;   ... same ...
      (ccase      ccase          :rhs-implicit-progn => :prefix)  ;;   ... same ...
      (ecase      ecase          :rhs-implicit-progn => :prefix)  ;;   ... same ...
      ( typecase   typecase      :rhs-implicit-progn => :prefix)  ;;   ... same ...
      (ctypecase  ctypecase      :rhs-implicit-progn => :prefix)  ;;   ... same ...
      (etypecase  etypecase      :rhs-implicit-progn => :prefix)) ;;   ... same ...

     (( let             let             :rhs-lbinds);;-------LET constructs
      ( let*            let*            :rhs-lbinds)
      ( symbol-macrolet symbol-macrolet :rhs-lbinds)
      ( prog*           prog*           :rhs-lbinds)
      ( prog            prog            :rhs-lbinds)
      ( with-slots      with-slots      :rhs-slots )
      ( macrolet        macrolet        :rhs-mbinds)
      ( flet            flet            :rhs-fbinds)
      ( labels          labels          :rhs-fbinds))

     (( block    block     :prefix);;------------------------PREFIX FORMS
      ( tagbody  tagbody   :prefix)
      ( catch    catch     :prefix)
      ( prog1    prog1     :prefix)
      ( prog2    prog2     :prefix)
      ( progn    progn     :prefix))

     ((  ?   ()         :split))   ;; DEPRECIATED

     (( setq setq  :rhs-sbinds)
      ( set  set   :rhs-sbinds)
      (psetq psetq :rhs-sbinds))
     (( setf setf  :rhs-ebinds)
      (psetf psetf :rhs-ebinds))

     ((  $   ()         :split      :rhs-args)
      ( .$   ()         :split-left :rhs-args))

     ((.@    mapc       :rhs-args) ;;-------------------------MAPPING
      (..@   mapl       :rhs-args)
      ( @/   reduce     :rhs-args)
      ( @.   mapcar     :rhs-args)
      ( @..  maplist    :rhs-args)
      ( @n   mapcan     :rhs-args)
      ( @.n  mapcon     :rhs-args)
      ( @~   maphash)
      ( @@   apply      :rhs-args)
      ( .@.  multiple-value-call  :rhs-args)
      ( @    funcall    :rhs-args :left-assoc :also-postfix))
     (( :->  function   :lhs-lambda))
     (( ->   lambda     :lhs-lambda))
     (( =..  multiple-value-bind  :syms/expr) ;;--------------MULTIPLE VALUES/DESTRUCTURING
      ( ..=  destructuring-bind   :lambda/expr))
     ((values values    :prefix   :single)
      ( .x.   values    :unreduce :single))
     (( loop  loop      :prefix   :quote-rhs))

     (( =... multiple-value-setq   :quote-lhs)  ;;------------ASSIGNMENT 
      ( .=   setf)
      ( +=   incf)
      ( -=   decf)
      (  =.  setq)
      ( .=.  set ))

     (( ||       or     :unreduce);;-------------------------LOGICAL OPS
      ( or       or     :unreduce :also-prefix))

     (( &&       and    :unreduce)
      ( and      and    :unreduce :also-prefix))

     (( ===      equalp :single)
      ( equal    equal  :single)
      ( ==       eql    :single)
      ( eql      eql    :single)
      ( eq       eq     :single)
      ( ~~      remhash :single)
      ( subtype-of subtypep :single))

     (( :.       cons))
     (( in       member))
     (( th-cdr   nthcdr))

     (( =s=      string= :single)
      ( =c=      char=   :single :unreduce)
      (  =        =      :single :unreduce :also-prefix)
      ( /=       /=      :single :unreduce :also-prefix)
      ( <        <       :single :unreduce :also-prefix)
      ( >        >       :single :unreduce :also-prefix)
      ( <=       <=      :single :unreduce :also-prefix)
      ( >=       >=      :single :unreduce :also-prefix))
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
     ((.!!.      bit       :rhs-args))
     (( !!       aref      :rhs-args))
     (( ~!       gethash   :single :rhs-args)
      (!~~       assoc     :single)
      (~~!       rassoc    :single))

     ((.eqv.     bit-eqv   :rhs-args)
      (.or.      bit-ior   :rhs-args)
      (.xor.     bit-xor   :rhs-args)
      (.and.     bit-and   :rhs-args)
      (.nand.    bit-and   :rhs-args)
      (.nor.     bit-nor   :rhs-args)
      (.not.     bit-not   :also-unary)
      (.orc1.    bit-orc1  :rhs-args)
      (.orc2.    bit-orc2  :rhs-args)
      (.andc1.   bit-andc1 :rhs-args)
      (.andc2.   bit-andc2 :rhs-args))
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
     (( min      min     :also-prefix :unreduce :single)
      ( max      max     :also-prefix :unreduce :single))
     ((  +        +      :also-unary  :unreduce))
     ((  -        -      :also-unary  :unreduce))
     ((  /        /      :also-unary))
     ((  *        *      :also-prefix :unreduce))
     (( **       expt))
     (( .!.      bit     :rhs-args));;------------------------ARRAY INDEXING
     ((  !       aref    :rhs-args :single)
      (  _       slot-value        :single))

     ((  ;        ;))

     ((index     aref    :term)
      (index2    hashget :term :macro)));

 declaim (fixnum *no-of-bops*);
 defvar *no-of-bops* 0;

 assign-properties :=
  let p = {*no-of-bops* =. 0}
    map () {l ->{incf p;
                  mapc {prop -> {let* bop = (pop prop)
                                      lop = (pop prop)
                                   {get bop 'properties .= `(,p,lop,prop)};
                                 incf *no-of-bops*}}
                       l}}
           *binfix*;

 (assign-properties);

 defvar *init-binfix* nil;

 init-binfix :==
   when *init-binfix*
     { *binfix* =. copy-tree *init-binfix*;
       (assign-properties);
       nil };

 save-binfix :=
   unless *init-binfix*
     {*init-binfix* =. copy-tree *binfix*};

 split e op &optional args arg :=
    cond {null e      $ nreverse $ nreverse arg :. args}
         {car e == op $ split (cdr e) op {nreverse arg :. args}}
         {t           $ split (cdr e) op args {car e :. arg}};

 Bop-p s :=
   symbolp s &&
     {get s 'properties ||
      not (keywordp s) && get (find-symbol (symbol-name s) "BINFIX") 'properties};

 find-Bop s &key (terms t) :=
   symbolp s &&
     let Bop = (cond {get s 'properties $ s}
                     {not (keywordp s) $ find-symbol (symbol-name s) "BINFIX"})
       get Bop 'properties && {terms || not {:term in caddr (get Bop 'properties)}} && Bop;

 find-Bop-in e &optional (p (1+ *no-of-bops*)) last-Bop o.r :=
    cond {null e $ o.r}
         {Bop-p (car e) && find-Bop (car e) :terms nil
            $ let* Bop = (find-Bop (car e) :terms nil)
                   q = (get Bop 'properties)
                 if {q && {car q < p
                           || car q == p
                              && not {   :single in caddr q
                                      && :single in caddr (get last-Bop 'properties)
                                      && not {Bop == last-Bop}
                                      && error "BINFIX parsing ambiguity between ~S and ~S" last-Bop Bop}
                              && caddr q
                              && null (intersection
                                        '(:rhs-args    :unreduce
                                          :lhs-lambda  :left-assoc
                                          :lambda/expr :split
                                          :syms/expr)
                                        (caddr q))}}
                   {find-Bop-in (cdr e) (car q) Bop e }
                   {find-Bop-in (cdr e)  p      last-Bop o.r}}
         {t $ find-Bop-in (cdr e) p last-Bop o.r};

 progn-monad form1 &optional form2 :=
   labels
     unit form = {if {consp form && car form == 'progn}
                     form
                    `(progn ,form)}

     join form1 form2 = `(progn ,@(cdr form1) ,@(cdr form2))

     cond {null form2 $ form1}
          {null form1 $ form2}
          {t $ join (unit form1) (unit form2)};

 implicit-progn e := cddr $ binfix `(progn () ; ,@e);

 binfix e &optional (max-priority (1+ *no-of-bops*)) :=
   labels
     unreduce e op &optional args arg =
       (cond {null e             $ reverse {binfix (reverse arg) :. args}}
             {sym-eql (car e) op $ unreduce (cdr e) op {binfix (reverse arg) :. args}}
             {t                  $ unreduce (cdr e) op args {car e :. arg}})

     binfix+ e =
       (if {semicolon-in e}
          (if (sym-eql (car (last e)) ';)
             (binfix+ (butlast e))
             (unreduce e ';))
         `(,(binfix e)))

     decl*-binfix+ rhs decls =
       {decl* body =.. (decls rhs decls)
         `(,@decl* ,@(binfix+ body))}

     doc*-decl*-binfix+ rhs decls =
       {doc*-decl* body =.. (doc-decls rhs decls)
         `(,@doc*-decl* ,@(implicit-progn body))}

     sbinds e &optional converted s current =
       {symbol-macrolet
          convert = `(,(binfix (reverse current)),s,@converted)
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
               {sym-eql (car e) ';
                           $ if {lhs && rhs}
                               {e-binds (cdr e) (bind lhs rhs)}
                               (error "BINFIX expression(s) bind(s), missing = in:~@
                                      ~A" (append (nreverse lhs) (nreverse rhs)))}
               {rhs        $ e-binds (cdr e) binds           lhs {car e :. rhs}}
               {t          $ e-binds (cdr e) binds {car e :. lhs}          rhs}}

     last-expr e =
       {let i = (position '; e :from-end t :test 'sym-eql)
          if i {subseq e 0 i .x. subseq e (1+ i)}
               {nil .x. e}}

     term e =
        {cond {atom e $ e}
              {consp e && consp (cadr e) && Bop-p (caadr e)
                 $ let op-prop = (get (caadr e) 'properties) ;; not looking for B-op, just a symbol.
                     if {:term in caddr op-prop}
                        (if {:macro in caddr op-prop}
                           {term $ macroexpand-1 {cadr op-prop :. car e :. cdadr e && binfix+ (cdadr e)} :. cddr e}
                           {term $               {cadr op-prop :. car e :. cdadr e && binfix+ (cdadr e)} :. cddr e})
                        {car e :. term (cdr e)}}
              {t $ car e :. term (cdr e)}}

  if {atom e} e
    let rhs = (find-Bop-in e max-priority)
      if (null rhs) (singleton (term e))
        let* lhs = (term (ldiff e rhs))
             rhs = (term rhs)
             op = (find-Bop (pop rhs) :terms nil)
           priority op-lisp op-prop ..= (get op 'properties)
           cond {sym-eql op '; $ error "BINFIX: bare ; in:~% ~{ ~A~}" e}
                {null rhs $
                   if {:also-postfix in op-prop}
                      `(,op-lisp ,(singleton (binfix lhs)))
                       (error "BINFIX: missing r.h.s. of ~S (~S)~@
                               with l.h.s:~%~S" op op-lisp lhs)}
                {:rhs-lbinds in op-prop $
                   cond {consp (car rhs) && cadr rhs == '=
                           $ llist e decls r =.. (dbind rhs)
                               {decls expr =.. (decls r (declare* decls))
                                 (binfix `(,@lhs (destructuring-bind ,llist ,e
                                                   ,@(nreverse decls)
                                                   ,@(binfix+ expr))))}}
                        {cadr rhs == '= || keywordp (cadr rhs) && caddr rhs == '=
                           $ binds-decls* expr =.. (lbinds rhs)
                               binfix `(,@lhs (,op-lisp ,@binds-decls* ,@(binfix+ expr)))}
                        {t $ syms e decls r =.. (mvbind rhs)
                               {decls expr =.. (decls r (declare* decls))
                                 (binfix `(,@lhs (multiple-value-bind ,syms ,e
                                                   ,@(nreverse decls)
                                                   ,@(binfix+ expr))))}}}
                {:rhs-slots in op-prop $
                   slots-s-decls* expr =.. (slots rhs)
                     binfix `(,@lhs (,op-lisp ,@slots-s-decls* ,@(binfix+ expr)))}
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

                {:rhs-fbinds in op-prop || :rhs-mbinds in op-prop $
                   binfix `(,@lhs (,op-lisp
                                    ,(fbinds (car rhs) (if {:rhs-fbinds in op-prop} 'defun 'defmacro))
                                    ,@(decl*-binfix+ (cdr rhs) ())))}

                {:lhs-lambda in op-prop $
                   ll decls =.. (lambda-list lhs)
                      `(,op-lisp ,ll ,@(decl*-binfix+ rhs decls))}
                {:binfix-defs in op-prop $
                   progn-monad (binfix lhs) (defs rhs)}
                {:progn in op-prop $
                   cond {:prefix in op-prop && {:quote-rhs in op-prop || :macro in op-prop}
                           $ progn-monad (singleton (binfix lhs))
                                         {let e = {semicolon-in rhs}
                                            if (null e)
                                              `(,op-lisp ,@rhs)
                                               (progn-monad`(,op-lisp ,@(ldiff rhs e))
                                                            (binfix (cdr e)))}}
                        {t $ progn-monad (binfix lhs) ;; partial implementation.
                                        `(,op-lisp ,(binfix rhs))}}
                {:rhs-implicit-progn == car op-prop && find (cadr op-prop) rhs :test 'sym-eql $ ;; looks ahead to allow other variants of the same op
                   {rhs-split rhs-head =.. (unreduce-rhs (cadr op-prop) rhs)
                      binfix `(,@lhs
                               (,op-lisp ,@{let h = (binfix rhs-head) h && list h}
                                ,@(mapcar {spl -> binfix (car spl) :. implicit-progn (cdr spl)}
                                          rhs-split)))}}
                {:unreduce in op-prop && find op rhs :key 'find-Bop $ ;;find necessary...
                  let u = (unreduce rhs op `(,(binfix lhs),op-lisp))
                     cond {lhs $ u}
                          {:also-unary  in op-prop $ `(,op-lisp (,op-lisp ,(caddr u)) ,@(cdddr u))}
                          {:also-prefix in op-prop $ `(,op-lisp (,op-lisp,@(caddr u)) ,@(cdddr u))}
                          {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                      with r.h.s:~%~S" op op-lisp rhs}}
                {null lhs $ cond{:also-unary  in op-prop $ `(,op-lisp ,(binfix rhs))}
                                {:also-prefix in op-prop || :prefix in op-prop
                                    $ `(,op-lisp ,@(cond {:quote-rhs in op-prop $ rhs}
                                                         {semicolon-in rhs $ binfix+ rhs}
                                                         {cdr rhs   $ binfix rhs}
                                                         { t        $ rhs}))}
                                {t $ error "BINFIX: missing l.h.s. of ~S (~S)~@
                                            with r.h.s:~%~S" op op-lisp rhs}}
                {:def in op-prop $
                  prev lhs =.. (last-expr lhs)
                   let def = (cdr (assoc (car lhs) (cadr op-prop)))
                    {when def (pop lhs);
                     ll decls =.. (lambda-list (cdr lhs))
                       (progn-monad
                          (binfix prev)
                         `(,{def || op-lisp} ,(car lhs) ,ll
                                    ,@(doc*-decl*-binfix+ rhs decls)))}}
                {:defm in op-prop $
                  prev lhs =.. (last-expr lhs)
                   let def = (cdr (assoc (car lhs) (cadr op-prop)))
                    {when def (pop lhs);
                     (progn-monad
                        (binfix prev)
                       `(,{def || op-lisp} ,(pop lhs) ,@(cond {consp (car lhs) && null (cdar lhs) $ pop lhs}
                                                              {keywordp (car lhs) $ list (pop lhs)})
                                  ,@{ll decls =.. (method-lambda-list lhs)
                                      `(,ll ,@(doc*-decl*-binfix+ rhs decls))}))}}
                {:left-assoc in op-prop && find op rhs :key 'find-Bop $
                   binfix `(,op-lisp ,(binfix  lhs) ,@rhs)}
                {:lambda/expr in op-prop $
                   llist decls =.. (lambda-list lhs)
                     `(,op-lisp ,llist ,(car rhs)
                                ,@(decl*-binfix+ (cdr rhs) decls))}

                {:split in op-prop $
                   cond {:rhs-args in op-prop && semicolon-in rhs
                           $ `(,(binfix lhs) ,@(binfix+ rhs))}
                        {cdr lhs || not (Bop-p (car lhs))
                           $ `(,(binfix lhs) ,(binfix rhs))}
                        {:also-unary in third (get (find-Bop (car lhs) :terms nil) 'properties) ;; needed for handling {- $ ...}
                           $ (binfix `(,@lhs ,(binfix rhs)))}
                        {t $ error "BINFIX: missing l.h.s of ~S~@
                                    with r.h.s:~%~S" (car lhs) rhs}}

                {:split-left in op-prop $
                   if {semicolon-in rhs && :rhs-args in op-prop}
                      (binfix`(,@lhs ,@(binfix+ rhs)))
                      (binfix`(,@lhs ,(binfix rhs)))}

                {:prefix in op-prop $
                   binfix `(,@lhs ,(cond {:quote-rhs in op-prop  $ `(,op,@rhs)}
                                         {semicolon-in rhs       $ `(,op,@(binfix+ rhs))}
                                         {t $ binfix `(,op,@rhs)}))}
                (t `(,op-lisp
                     ,(if {:quote-lhs in op-prop} lhs (binfix lhs))
                     ,@(cond {null (cdr rhs) $ rhs}
                             {:rhs-args in op-prop $
                                cond {find-Bop-in rhs (1+ priority)
                                                $ `(,(binfix rhs))}
                                     {semicolon-in rhs
                                                $ binfix+ rhs}
                                     {t         $ rhs}}
                             {t $ `(,(binfix rhs))})))}

;===== BINFIX defined =====
