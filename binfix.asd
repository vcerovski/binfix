; BINFIX by V.Cerovski 2015,9

(defsystem #:binfix
   :description "BINFIX -- A powerful binary infix syntax for Common LISP."
   :author "Viktor Cerovski"
   :licence "GNU GPLv2"
   :version "0.27"
   :serial t
   :components
      ((:file "package")
       (:file "proto")
       (:file "proto1")
       (:file "binfix")
       (:file "interface")
       (:static-file "README.md")
       (:static-file "doc/index.html")
       (:static-file "doc/markdown.css")
       (:static-file "doc/syntax-term.png")
       (:static-file "doc/syntax-gui.png"))
   :in-order-to ((test-op (test-op "binfix/5am"))))

(defsystem #:binfix/5am
   :description "5am test suite for BINFIX"
   :author "Viktor Cerovski"
   :licence "GNU GPLv2"
   :depends-on (:binfix :fiveam)
   :components ((:file "binfix-5am"))
   :perform (test-op (o s) (symbol-call :binfix/5am :run-tests)))

