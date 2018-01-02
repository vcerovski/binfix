; BINFIX by V.Cerovski 2015,6

(defpackage #:binfix
  #-gcl(:use #:cl)
  #+gcl(:use #:lisp)
  (:export #:binfix    #:defbinfix #:rmbinfix #:lsbinfix  #:defbinfixdef
           #:->  #:==  #:=== #:=c= #:=s= #:&  #:&&  #:||  #:in   #:!!  #:!!.
           #:.=  #:=.  #:.=. #:..= #:=.. #:=... #:+= #:-=  #:<<  #:!    #:?
           #:$   #:**  #:@   #:@@  #:@n  #:@. #:@.. #:@.n #:.x.  #:|;|
           #:<&  #:@/  #:.@. #:.@  #:..@ #:<&..     #:@~  #:!~   #:!~~ #:~~!
           #:th  #:th-cdr    #:th-value  #:.! #:!.  #:!.. #:.!.  #:.!!.
           #:def #:parameter #:var #:constant #:generic   #:symbol-macro
                 #:class
           #:th-bit  #:.nor.   #:or.    #:xor.    #:and.   #:nand.  #:nor.
           #:andc2.  #:eqv.    #:test.  #:orc1.   #:orc2.  #:andc1. #:.eqv.
           #:.or.    #:.xor.   #:.and.  #:.nand.  #:.not.  #:.orc1. #:.orc2.
           #:.andc1. #:.andc2. #:.eqv.  #:subtype-of
          #-sbcl #:struct))

#+clisp (shadowing-import 'symbol-macro :binfix)
#+clisp (shadowing-import '! :binfix)
  #+ecl (shadowing-import '@ :binfix)
  #+ccl (shadowing-import '@ :binfix)
 #+sbcl (shadowing-import 'var :binfix)

