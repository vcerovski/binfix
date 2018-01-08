; BINFIX by V.Cerovski 2015,8

(in-package :binfix)

{declaim-fun &rest name-type :==
    loop for name = (pop name-type)
         for type = (pop name-type)
         while name collect `(ftype ,type ,name) into decl
         finally (return `(declaim ,@decl)) &

 deftype priority ()
   '(member :first :last :earlier :later :before :after :as) &

 deftype property ()
   '(member :lhs-lambda :def :defm :split :unreduce  :syms/expr :lambda/expr
            :rhs-lbinds :rhs-sbinds :rhs-ebinds :rhs-fbinds :prefix
            :also-prefix :also-unary :also-postfix :left-assoc :rhs-args
            :macro :quote-lhs :quote-rhs :progn) &

 rmbinfix op :symbol :=
   *binfix* =. delete-if {o -> null (cdr o) && caar o == op} *binfix*;
   *binfix* =. o -> delete op o :key #'car @. *binfix*;
   remprop op 'properties;
   () &

 op-position op :symbol :=
  "Returns index of *binfix* elem that contains op, or nil otherwise."
   loop for i = 0 then (1+ i)
        for o in *binfix* do
      (when {car o == op || listp (car o) && member op o :key #'car}
         (return i)) &

 declaim-fun defbinfix {symbol &optional symbol priority &rest t :-> boolean} &

 defbinfix op lisp-op = op p = :later &rest prop :=
  "DEFBINFIX op [lisp-op [priority op [property]*]]"
   let i = {ecase p;
             :first      ? 0;
             :last       ? op-position '; ;
             :earlier    ? op-position 'in + 1;
             :later      ? op-position 'coerce;
             :before :as ? op-position (pop prop);
             :after      ? op-position (pop prop) + 1};
     every {p -> etypecase p (property p)} prop;
     rmbinfix op;
     unless i (error "DEFBINFIX ~S ~S cannot find binfix op." op p);
     *binfix* =. append (subseq *binfix* 0 i)
                       `(((,op ,lisp-op ,@prop) ,@{p == :as && *binfix* .! i}))
                        (subseq *binfix* (if {p == :as} (1+ i) i));
     (assign-properties);
     t &

 lsbinfix s :stream = *standard-output* :=
    format s "  BINFIX~16t   LISP~16t~32t   Properties~@
              ==============================================================================~@
              ~{~&(~{~2t~{~s~^~,16t~}~^~%~} )~}~@
              ------------------------------------------------------------------------------~@
             " *binfix*
}
