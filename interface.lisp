; BINFIX by V.Cerovski 2015

(in-package :binfix)

{declaim-fun &rest name-type :==
    loop for name = (pop name-type)
         for type = (pop name-type)
         while name collect `(ftype ,type ,name) into decl
         finally (return `(declaim ,@decl)) &

 deftype priority ()
   '(member :first :last :earlier :later :before :after :replace) &

 deftype property ()
   '(member :lhs-lambda :def :defm :split :unreduce :allows-decl :lambda/expr
            :rhs-lbinds :rhs-sbinds :rhs-ebinds
            :also-prefix :also-unary :also-postfix :left-assoc :rhs-args) &

 rmbinfix op :symbol := *binfix* =. delete op *binfix* :key #'car &

 declaim-fun defbinfix {symbol &optional {symbol || function} priority &rest t :-> boolean} &

 defbinfix op lisp-op = op p = :later &rest prop :=
  "DEFBINFIX op [lisp-op [priority op [property]*]]"
   let i = {ecase p $ :first   ? 0
                    $ :last    ? length *binfix* - 1
                    $ :earlier ? 1 + position 'in *binfix* :key #'car
                    $ :later   ? position 'coerce *binfix* :key #'car
                    $ :before  ? position (pop prop) *binfix* :key #'car
                    $ :after   ? position (pop prop) *binfix* :key #'car + 1
                    $ :replace ? {let i = (position op *binfix* :key #'car)
                                   if i {prop =. cddr (elt *binfix* i) & i}
                                        (error "DEFBINFIX: undefined ~S" op)}}
    progn
     (every {p -> etypecase p (property p)} prop)
     (rmbinfix op)
     {*binfix* =. append (subseq *binfix* 0 i)
                        `((,op ,lisp-op ,@prop))
                         (subseq *binfix* i)}
     t &

 lsbinfix s :stream = *standard-output* :=
    format s "BINFIX~16t   LISP~16t~32t   Properties~@
              ============================================================~@
             ~{~&~{~s~,16t~}~}~@
              ------------------------------------------------------------~@
             " *binfix*
}
