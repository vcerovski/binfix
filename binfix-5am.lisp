(defpackage #:binfix/5am
  (:use #:cl #:binfix)
  #+sbcl (:shadowing-import-from #:binfix #:struct #:var)
  #+ecl (:shadowing-import-from #:binfix #:@ #:=>)
  #+ccl (:shadowing-import-from #:binfix #:@ #:=>)
  (:import-from #:fiveam
      #:def-suite #:in-suite #:test #:is #:is-true #:signals
      #:*on-error* #:*on-failure* #:run!)
  (:export #:run-tests)
)

(in-package :binfix/5am)

(def-suite binfix-tests)
(in-suite binfix-tests)

(defmacro B1 (test B-expr &rest rest)
  (declare (symbol test) (string B-expr))
  "Reading and evaluating string B-EXPR in a one-argument TEST"
  `(,test (eval (read-from-string ,B-expr)) ,@rest))

(defmacro B2 (test (pred B-expr S-expr &rest rest1) &rest rest2)
  (declare (symbol test pred) (string B-expr))
  "Reading and evaluating string B-EXPR in a two-argument TEST PRED.
   Note that B-EXPR is the 1st and S-EXPR the 2nd argument."
  `(,test (,pred ,S-expr (eval (read-from-string ,B-expr)) ,@rest1) ,@rest2))

(defmacro Berror (B-expr &rest rest)
  (declare (string B-expr))
  "Check that reading (w/o evaluation) of string B-EXPR signals error"
  `(signals error (read-from-string ,B-expr) ,@rest))

(test S-expressions
  (B2 is (equal "'{a $ b}" '(a b))                   "S-expr ops sanity check."            )
  (B2 is (equal "'{f $ g $ h x y z}"
                 '(f (g (h x y z)))  ))
  (B1 is-true  "'{1 :. 2} == '(1 . 2)}"                           )
  (B1 is-true  "'{'{f $ x * y} == '{f {x * y}} == '(f (* x y))}"  )
  (B2 is (equal
           "'{-2 :. loop for i upto 9 collect i}"
            '(cons -2 (loop for i upto 9 collect i))    ))

  (B2 is (equal "
            '{loop for i = 1 to 3
                   collect loop for j = 2 to 4
                                collect {i :. j}}"
            '(loop for i = 1 to 3
                   collect (loop for j = 2 to 4
                                 collect (cons i j)))    ))

  (B2 is (equal "
            '(cond {x > 1 $ x}
                   {x < 1 $ sin x}
                   {b $ x + y}
                   {t $ a})"
            '(cond ((> x 1) x)
                   ((< x 1) (sin x))
                   (b (+ x y))
                   (t a))                                ))
)

(test arithmetics
  (B2 is (equal  "'{1 + 2}            " '(+ 1 2)                   ) "Arithmetics sanity check.")
  (B2 is ( =     " {1 / 2}            "  1/2                       ))
  (B2 is (equal  "'{a - b - c - d}    " '(- a b c d)               ))
  (B2 is (equal  "'{- a - b - c - d}  " '(- (- a) b c d)           ))
  (B2 is (equal  "'{a + b - c + d}    " '(+ a (- b c) d)           ))
  (B2 is (equal  "'{- a * b}          " '(- (* a b))               ))
  (B2 is (equal  "'{a + b * c}        " '(+ a (* b c))             ))
  (B2 is (equal  "'{a + 1- b * c}     " '(+ a (* (1- b) c))        ))
  (B2 is (equal  "'{a * b / c * d + 1}" '(+ (/ (* a b) (* c d)) 1) ))
  (B2 is (equal  "'{a - g b - c - f d}" '(- a (g b) c (f d))       ))
)

(test functional
  (B2 is (equal  "'{x -> x + a}"       '(lambda (x) (+ x a))  ) "Lambda sanity check.")
  (B2 is (equal  "'{x y = 1 -> x + y}" '(lambda (x &optional (y 1)) (+ x y))         ))

  (B2 is (equal "'{x y :number = 1 -> x + y}"
                '(lambda (x &optional (y 1)) (declare (type number y)) (+ x y))      ))

  (B2 is (equal "'{x :number = 1 y :number = 1 -> x + y}"
                '(lambda (&optional (x 1) (y 1))
                   (declare (type number x)
                            (type number y))
                   (+ x y))  ))
  (B2 is (equal "'{x = 1 y = 1 -> declare x y :number  x + y}"
                 '(lambda (&optional (x 1) (y 1))
                    (declare (type number x y))
                    (+ x y))  ))
  (B1 is-true "
       {'{ x -> y -> z -> x * y + z  @ 2 @ 3 @ 4} equal
        '(funcall
           (funcall
             (funcall
               (lambda (x) (lambda (y) (lambda (z) (+ (* x y) z))))
               2)
             3)
           4)}"  )

  (B2 is (equal
           "'{'min @/ a b -> abs {a - b} @. a b}"
           '(reduce 'min (mapcar (lambda (a b) (abs (- a b))) a b))   ))

  (B2 is (=       "{-> 1 @}"                             1   ))
  (B2 is (equal  "'{-> 1 @}"  '(funcall (lambda () 1))       ))
  (B2 is (=     "{x -> y -> z -> x * y + z @ 2 @ 3 @ 4}" 10  ))
)

(test let-forms
  (B2 is (equal "'{let x = 1 x}"    '(let ((x 1)) x)  ) "LET-form sanity check.")
  (B1 is-true   "{1 = let x = 1 x}"                   )
  (B1 is-true   "{1 = flet f := 1 (f)}"               )
  (B2 is (equal"
            '{flet f x :integer y :number := {x / y}
                   g x :number y := {x ** y}
                f 1 2 / g 2 3}
          " '(flet ((f (x y)
                      (declare (type integer x)
                               (type number y))
                      (/ x y))
                    (g (x y)
                      (declare (type number x))
                      (expt x y)))
               (/ (f 1 2) (g 2 3)))     ))
  (B2 is (equal "
              '{flet f x := x + x;
                     g x := y * y;
                  f $ g x}
            " '(flet ((f (x) (+ x x))
                      (g (x) (* y y)))
                 (f (g x)))             ))
)

(test multiple-let
  (B2 is (equal
           "'{let a b = floor a b; a + b}"
            '(multiple-value-bind (a b) (floor a b) (+ a b))   ))
  (B2 is (equal
           "'{let a :int b = floor a b; a + b}"
            '(multiple-value-bind (a b) (floor a b)
               (declare (type int a))
               (+ a b))   ))
  (B2 is (equal
           "'{let a :int b :int = floor a b; a + b}"
            '(multiple-value-bind (a b) (floor a b)
               (declare (type int a) (type int b))
               (+ a b))   ))

  (B2 is (equal "'{let (a b) = '(1 2); list a b}"
                 '(destructuring-bind (a b) '(1 2) (list a b))      ))
  (B2 is (equal "'{let (a b) = '(1 2) list a b}"
                 '(destructuring-bind (a b) '(1 2) (list a b))      ))
  (B2 is (equal "'{let (a = 2 b = 2) = f x; list a b}"
                 '(destructuring-bind (&optional (a 2) (b 2)) (f x)
                     (list a b))                                    ))

  (Berror "'{let a b = floor a b  a + b}")
  (Berror "'{let a b   floor a b  a + b}")
  (Berror "'{let a b   floor a b; a + b}")
)

(test prefix
  (B2 is (equal  "'{progn a}"          '(progn a)              ))
  (B2 is (equal  "'{progn a;}"         '(progn a)              ))
  (B2 is (equal  "'{progn (a)}"        '(progn (a))            ))
  (B2 is (equal  "'{progn (a);}"       '(progn (a))            ))
  (B2 is (equal  "'{values a b}"       '(values a b)           ))
  (B2 is (equal  "'{values a; b}"      '(values a b)           ))
  (B2 is (equal  "'{progn a; b;}"      '(progn a b)            ))
  (B2 is (equal  "'{progn (a); b}"     '(progn (a) b)          ))
  (B2 is (equal  "'{progn (a); (b)}"   '(progn (a) (b))        ))
  (B2 is (equal  "'{progn f a; f b}"   '(progn (f a) (f b))    ))
  (B2 is (equal  "'{f progn a b}"      '(f (progn a b))        ))
  (B2 is (equal  "'{f progn f a; b}"   '(f (progn (f a) b))    ))
  (B2 is (equal  "'{x / progn f a; b}" '(/ x (progn (f a) b))  ))
  (B1 is-true    " {t == block b; return-from b t} "            )
)

(test also-prefix
  (B2 is (equal  "'{min f x y; g y x; h x}"           '(min (f x y) (g y x) (h x))          ))
  (B2 is (equal  "'{or a and b; p; c and d; pred q}"  '(or (and a b) p (and c d) (pred q))  ))
)

(test also-unary
  (B2 is (=      " { - 1 } "          -1              ))
  (B2 is (=      " {- $ 1} "          -1              ))
  (B2 is (=      " {- $ / $ 2} "      -1/2            ))
  (B2 is (equal  "'{- $ a + b - c}" '(- {a + b - c})  ))
  (B2 is (equal  "'{- $ a * b - c}" '(- {a * b - c})  ))
  (B2 is (equal  "'{x > 0 $  - $ sqrt x}"
                  '((> x 0) (- (sqrt x)))             ))
  (B2 is (equal  "'{.not. $ a .xor. b}"
                  '(bit-not (bit-xor a b))            ))
)

(test sets/binds
  (B2 is (equal
           "'{*print-case* =. :downcase}"
            '(setq *print-case* :downcase)  ))

  (B2 is (equal "'{x -> a =. x}"     '(lambda (x) (setq a x))                      ))
  (B2 is (equal "'{x -> a _'x .= x}" '(lambda (x) (setf (slot-value a 'x) x))      ))
  (B2 is (equal "'{x -> s-x a .= x}" '(lambda (x) (setf (s-x a) x))                ))

  (B2 is (equal "'{i -> a[i] += d; b[i] += d .@ ind}"
                 '(mapc (lambda (i) (incf (aref a i) d) (incf (aref b i) d)) ind)  ))

  (B2 is (equal"
            '{let x :bit = 1
                x}"
            '(let ((x 1))
               (declare (type bit x))
               x)       ))

  (B2 is (equal "'{A ! I J += B ! I K * C ! K J}"
                 '(INCF (AREF A I J) (* (AREF B I K) (AREF C K J)))  ))

  (B2 is (equal"
            '{1 + setf a ! 1 = f 1 + 2;
                       a ! 2 = 3 + f 4;
                + f 5}
          " '(+ 1
                (setf (aref a 1) (+ (f 1) 2)
                      (aref a 2) (+ 3 (f 4)))
                (f 5))  ))

  (B2 is (equal"
            '{x -> a :int b =.. (f x)
                   c d :int =.. (g x)
                     a * c / b * d
                @. h a;}
          " '(mapcar
               (lambda (x)
                 (multiple-value-bind (a b)
                   (f x)
                   (declare (type int a))
                   (multiple-value-bind (c d)
                     (g x)
                     (declare (type int d))
                     (/ (* a c) (* b d)))))
               (h a))  ))
  (B2 is (equal "
            '{let a = b c;
              let* x = y z;
              l r =.. (f g)
              p q ..= (f l)
                declare q :int
                h a x l r p q}
          " '(let ((a (b c)))
              (let* ((x (y z)))
               (multiple-value-bind (l r) (f g)
                (destructuring-bind (p q) (f l)
                  (declare (type int q))
                  (h a x l r p q)))))  ))
  (B2 is (equal "
            '{let a = b c;
              let* x = y z;
              l r ..= (f g)
              p q =.. (f l)
                declare q :int
                h a x l r p q}
          " '(let ((a (b c)))
              (let* ((x (y z)))
               (destructuring-bind (l r) (f g)
                (multiple-value-bind (p q) (f l)
                  (declare (type int q))
                  (h a x l r p q)))))  ))

  (B2 is (equal "'{with-slots a b :_ s  f a b}"
                 '(with-slots (a b) s (f a b))    ))
  (B2 is (equal "'{with-slots a :t1 b :t2 :_ s  f a b}"
                 '(with-slots (a b) s (declare (type t2 b) (type t1 a)) (f a b))    ))
  (B2 is (equal "
           '{with-slots a1 = a b1 = b :_ s1
             with-slots a2 = a b2 = b :_ s2
               f a1 b2;
               g b1 a2}
          "'(with-slots ((a1 a) (b1 b)) s1
              (with-slots ((a2 a) (b2 b)) s2
                (f a1 b2)
                (g b1 a2)))   ))
  (B2 is (equal "
            '{with-slots a1 :t1 = a b1 :t2 = b :_ s1
              with-slots a2 :t1 = a b2 :t2 = b :_ s2
                f a1 b2;
                g b1 a2}
           "'(with-slots ((a1 a) (b1 b)) s1
               (declare (type t2 b1)
                        (type t1 a1))
               (with-slots ((a2 a) (b2 b)) s2
                 (declare (type t2 b2)
                          (type t1 a2))
                 (f a1 b2)
                 (g b1 a2)))   ))
)

(test implicit-progn
  (B2 is (equal"
            '{x -> print x;
                   setf car x = f x;
                        cdr x = y -> g y @. x;
                .@ xs}
          " '(mapc
               (lambda (x)
                 (print x)
                 (setf (car x) (f x)
                       (cdr x) (mapcar (lambda (y) (g y)) x)))
               xs)  ))
  (B2 is (equal
           "'{cond (a) => (f); 1; g => 22; (f) => nil}"
            '(cond ((a) (f) 1) (g 22) ((f) nil))         ))
  (B2 is (equal "
            '{cond x > 1 => x;
                   x < 1 => print 1;
                            sin x;
                   b => let y = g y;
                          x + y ** 3;
                   t => a}
          " '(cond ((> x 1) x)
                   ((< x 1) (print 1)
                            (sin x))
                   (b (let ((y (g y)))
                         (+ x (expt y 3))))
                   (t a))                          ))
  (B2 is (equal "'{ecase f x;
                    0 1 2 => print 'a; g a;
                    3 4   => print 'b; g b;
                    6     => print 'c; h c}
                "'(ecase (f x)
                    ((0 1 2) (print 'a) (g a))
                    ((3 4)   (print 'b) (g b))
                    (6       (print 'c) (h c)))     ))
  (B2 is (equal "'{case f a; 1 a; 2 b; 3 c}"
                 '(case (f a) (1 a) (2 b) (3 c))   ))
)

(test definitions
  (B2 is (equal
           "'{def var *x* :fixnum = 1}"
           '(progn (declaim (type fixnum *x*)) (defvar *x* 1))   ))
  (B2 is (equal
           "'{def var *x* :fixnum = 1;}"
           '(progn (declaim (type fixnum *x*)) (defvar *x* 1))   ))
  (B2 is (equal
           "'{def struct s a b c; var *v* = 1}"
           '(progn (defstruct s a b c) (defvar *v* 1))           ))
  (B2 is (equal "
            '{def parameter *x* = 1 *y* = 2
              def struct point x y z
              def f x := sqrt x * sin x}
          "'(progn
              (defparameter *x* 1)
              (defparameter *y* 2)
              (defstruct point x y z)
              (defun f (x) (* (sqrt x) (sin x))))                ))
  (B2 is (equalp "
            '{def generic join a b;
               \"Generic join.\"
               a :list b :list :- append a b;
               a :t    b :list :- a :. b;
               a :list b :t    :- `(,@a ,b);
               a :t    b :t    :- list a b}
          "'(progn
              (defgeneric join (a b)
                (:documentation "Generic join.")
                (:method ((a list) (b list)) (append a b))
                (:method ((a t) (b list)) (cons a b))
                (:method ((a list) (b t)) `(,@a ,b))
                (:method ((a t) (b t)) (list a b))))            ))
)

(test B-terms
  (B2 is (equal " '{A[i]} "  '(aref a i)       )     "B-terms sanity check"    )
  (B2 is (equal "'{(a)[i]}" '(aref (a) i)      ))
  (B2 is (equal
           "'{a[i] + b[i;j] / c[i;j] - a[f k]}"
           '(+ (aref a i) (- (/ (aref b i j) (aref c i j)) (aref a (f k))))   ))
  (B2 is (equal "'{a[1;2][2;3]}"  '(aref (aref a 1 2) 2 3)                    ))

  (B2 is (equal "'{incf table[[key;0]]}"
                 '(incf (binfix::hashget table key 0))))
)

(test parsing-errors
  (Berror  "      {a; b}       ")
  (Berror  "      {a &}        ")
  (Berror  "      {a $}        ")
  (Berror  "      {$ a}        ")
  (Berror  "   {progn $ a}     ")
  (Berror  "    {min $ a}      ")
  (Berror  "      {a ->}       ")
  (Berror  "      {f :=}       ")
  (Berror  "      {f :-}       ")
  (Berror  "      {f :==}      ")
  (Berror  "      {f :type=}   ")
  (Berror  "      {:= f}       ")
  (Berror  "      {:- f}       ")
  (Berror  "     {:== f}       ")
  (Berror  "  {:type= f}       ")
  (Berror  "  {1 min 3 max 2}  ")
  (Berror  "   {1 <= 2 < 3}    ")
  (Berror  "   {a 1 =.. f x}   ")
  (Berror  "  {def atruct x y} ")
)

(test interface
  (B1 is-true   "(defbinfix % mod :after +))"       )
  (B2 is (equal "'{a % b}"     '   (mod a b)       ))
  (B2 is (equal "'{a % b + c}" '(+ (mod a b) c)    ))
)

(defun run-tests ()
 "Returns t if all tests pass, otherwise nil"
  (setq *on-error* nil
        *on-failure* nil)
  (run! 'binfix-tests))
