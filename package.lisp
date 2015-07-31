; BINFIX by V.Cerovski 2015

(defpackage #:binfix
  #-gcl(:use #:cl)
  #+gcl(:use #:lisp)
  (:export #:binfix  #:defbinfix #:rmbinfix #:lsbinfix
           #:-> #:== #:=== #:=c= #:=s= #:&  #:&&  #:||  #:in #:!!
           #:.= #:=. #:.=. #:..= #:=.. #:+= #:-=  #:<<  #:!  #:?
           #:$  #:** #:@   #:@@  #:@n  #:@. #:@.. #:@.n #:.x.))

