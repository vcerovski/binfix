; BINFIX by V.Cerovski 2015,9

(defpackage #:binfix
  #-gcl(:use #:cl)
  #+gcl(:use #:lisp)
  (:export #:binfix #:def-Bop #:set-Bop #:rem-Bops #:list-Bops #:keep-Bops))
