; BINFIX by V.Cerovski 2015,6

(defpackage #:binfix
  #-gcl(:use #:cl)
  #+gcl(:use #:lisp)
  (:export #:binfix    #:defbinfix #:rmbinfix #:lsbinfix  #:defbinfixdef
           #:->  #:==  #:=== #:=c= #:=s= #:&  #:&&  #:||  #:in   #:!!
           #:.=  #:=.  #:.=. #:..= #:=.. #:+= #:-=  #:<<  #:!    #:?
           #:$   #:**  #:@   #:@@  #:@n  #:@. #:@.. #:@.n #:.x.  #:|;|
           #:<&  #:@/  #:.@. #:.@  #:..@ #:th #:th-cdr    #:th-value
           #:def #:parameter #:var #:constant #:generic   #:symbol-macro
          #-sbcl #:struct))

#+clisp (shadowing-import '! :binfix)
  #+ecl (shadowing-import '@ :binfix)
  #+ccl (shadowing-import '@ :binfix)
 #+sbcl (shadowing-import 'var :binfix)

