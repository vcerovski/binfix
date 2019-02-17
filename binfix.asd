; BINFIX by V.Cerovski 2015,9

(asdf:defsystem #:binfix
   :description "BINFIX -- A powerful binary infix syntax for Common LISP."
   :author "Viktor Cerovski"
   :licence "GNU GPLv2"
   :version "0.26.1"
   :serial t
   :components
      ((:file "package")
       (:file "proto")
       (:file "proto1")
       (:file "binfix")
       (:file "interface")
       (:static-file "README.md")
       (:static-file "doc/index.html")
       (:static-file "doc/markdown.css")))

