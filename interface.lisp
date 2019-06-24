; BINFIX by V.Cerovski 2015,8

(in-package :binfix)

#+ecl(use)

{deftype priority ()
   '(member :first :last :earlier :later :before :after :as :same-as) &

 deftype property ()
   '(member :lhs-lambda :def :defm :split :unreduce  :syms/expr :lambda/expr
            :rhs-lbinds :rhs-sbinds :rhs-ebinds :rhs-fbinds :prefix
            :also-prefix :also-unary :also-postfix :left-assoc :rhs-args
            :macro :quote-lhs :quote-rhs :progn) &

 op-position op :symbol :=
  "Returns index of the first element of *binfix* that contains op, or nil otherwise."
   position-if {ops -> member op ops :key #'car} *binfix* &

 rmbinfix op :symbol :=
  "Removes binfix operation OP. Returns nil."
   let i = op-position op;
     when i
       let B-ops = *binfix* .! i;
         unless {setf *binfix* .! i = delete op B-ops :key 'car}
           setq *binfix* = delete-if 'null *binfix*;
         remprop op 'properties;
         nil &

 setbinfix op :symbol lisp-op :symbol :=
  "Set already defined binfix OP to represent lisp LISP-OP."
   ops -> {op1 -> {car op1 eq op && setf cadr op1 = lisp-op} .@ ops} .@ *binfix*;
   (assign-properties);
   nil

 declaim ({symbol &optional symbol priority &rest t :-> boolean} defbinfix) &

 defbinfix op lisp-op = op p = :later &rest prop :=
  "DEFBINFIX op [lisp-op [priority op [property]*]]"
   rmbinfix op;
   let* i = {ecase p;
             :first      ? 0;
             :last       ? op-position '; ;
             :earlier    ? op-position 'in + 1;
             :later      ? op-position 'coerce;
             :before :as ? op-position (pop prop);
             :after      ? op-position (pop prop) + 1;
             :same-as    ? {let* op1 = pop prop
                                 prop1 = get op1 'properties;
                              when prop (warn "defbinfix ~S properties ~S ignored." op prop);
                              prop =. `(,@(caddr prop1) :keys ,@(cadddr prop1));
                              op-position op1}};
     every {p -> etypecase p (property p)} prop;
     unless i (error "DEFBINFIX ~S ~S cannot find binfix op." op p);
     *binfix* =. append (subseq *binfix* 0 i)
                       `(((,op ,lisp-op ,@prop) ,@{p in '(:as :same-as) && *binfix* .! i}))
                        (subseq *binfix* (if {p in '(:as :same-as)} (1+ i) i));
     (assign-properties);
     t &

 lsbinfix s :stream = *standard-output* :=
    format s "  BINFIX~16t   LISP~16t~32t   Properties~@
              ==============================================================================~@
              ~{~&(~{~2t~{~s~^~,16t~}~^~%~} )~}~@
              ------------------------------------------------------------------------------~@
             " *binfix*
}
