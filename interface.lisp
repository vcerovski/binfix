; BINFIX by V.Cerovski 2015,9

(in-package :binfix)

#+ecl(use-binfix)

{deftype priority ()
   '(member :first :last :earlier :later :before :after :as :same-as) &

 deftype property ()
   '(member :lhs-lambda :def :defm :split :unreduce  :syms/expr :lambda/expr
            :rhs-lbinds :rhs-sbinds :rhs-ebinds :rhs-fbinds :prefix
            :also-prefix :also-unary :also-postfix :left-assoc :rhs-args
            :macro :quote-lhs :quote-rhs :progn) &

 op-position op :symbol :=
  "Returns index of the first element of *binfix* that contains op, or nil otherwise."
   position-if {ops -> member op ops :key #'car :test 'sym-eql} *binfix* &

 rmbop op :symbol :=
  "Removes binfix operation OP. Returns nil."
   let* bop = (find-Bop op)
        i = op-position bop;
     when i
       let B-ops = *binfix* .! i;
         unless {setf *binfix* .! i = delete bop B-ops :key 'car :test 'sym-eql}
           setq *binfix* = delete-if 'null *binfix*;
         remprop bop 'properties;
         nil &

 keep-Bops &rest Bops :==
  "Keep only Bops represented by symbols in argument(s) BOPS.  Without
  arguments restores all binfix Bops.  Handles also implicit dependence
  of := :== and :- on progn Bop. Returns nil."
  when {semicolon-in Bops && intersection '(:= :== :-) Bops}
     (pushnew 'progn Bops);
  `{eval-when (:load-toplevel :compile-toplevel :execute)
     progn
       (init-binfix);
       unless ,(null Bops)
         {*binfix* =. delete ()
                        {Bs -> {Bs =. delete-if {B -> unless {car B in ',Bops}
                                                        (remprop (car B) 'properties) t}
                                                Bs}
                            @. *binfix*}}
         (assign-properties)} &

 rem-Bops &rest Bops :==
  "Macro that removes Bops represented by symbols in BOPS.  Returns nil."
  `{eval-when (:load-toplevel :compile-toplevel :execute)
     progn
       (save-binfix);
       'rmbop .@ ',Bops;
       (assign-properties)} &

 set-Bop op :symbol lisp-op :symbol &rest props :==
  "Set already defined binfix OP to represent lisp LISP-OP,
  with the same properties unless properties PROPS are non-nil."
  `{eval-when (:load-toplevel :compile-toplevel :execute)
     progn
       (save-binfix);
       ops -> {op1 -> when {car op1 eq ',op}
                        {setf cadr op1 = ',lisp-op}
                        {unless ,(null props) setf cddr op1 = ',props} .@ ops}
           .@ *binfix*;
       (assign-properties)} &

 #-abcl {declaim ({symbol &optional symbol priority &rest t :-> boolean} defbinfix)}
 #-abcl &

 def-Bop Bop lisp-op = Bop p = :later &rest prop :==
  "DEFBINFIX bop [lisp-op [priority op [property]*]]
  Defines new or redefines existing Bop BOP."
   let* i = {ecase p;
             :first      => 0;
             :last       => op-position '; ;
             :earlier    => op-position 'in + 1;
             :later      => op-position 'coerce;
             :before :as => op-position (pop prop);
             :after      => op-position (pop prop) + 1;
             :same-as    => let* op1 = pop prop
                                 prop1 = get op1 'properties;
                              when prop (warn "defbinfix ~S properties ~S ignored." Bop prop);
                              prop =. caddr prop1;
                              op-position op1};
     every {p -> {etypecase p; property p}} prop;
     unless i (error "DEFBINFIX ~S ~S cannot find binfix Bop." Bop p);
     (save-binfix);
     rmbop Bop;
     *binfix* =. append (subseq *binfix* 0 i)
                       `(((,Bop ,lisp-op ,@prop) ,@{p in '(:as :same-as) && *binfix* .! i}))
                        (subseq *binfix* (if {p in '(:as :same-as)} (1+ i) i));
     (assign-properties);
     t &

 list-Bops s :stream = *standard-output* :=
    format s "  BINFIX~16t   LISP~16t~32t   Properties~@
              ==============================================================================~@
              ~{~&(~{~2t~{~(~A~)~16t~{~S~^~,16t~}~}~^~%~} )~}~@
              ------------------------------------------------------------------------------~@
             " {Bops -> {Bop -> list {cond car Bop == :.   => ":.";
                                           car Bop == ' || => "||";
                                           keywordp (car Bop) => format nil "~S" (car Bop);
                                           t => symbol-name (car Bop)}
                                     (cdr Bop)
                              @. Bops}
                      @. *binfix*}
}
