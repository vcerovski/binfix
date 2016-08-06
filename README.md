<link href="markdown.css" rel="stylesheet" type="text/css"></link>

# BINFIX

Viktor Cerovski, Aug 2016.

<a name="Introduction"></a>
## Introduction

BINFIX (blend from "Binary Infix") is a poweful infix syntax notation for
S-expressions of Common LISP ranging from simple arithmetic and logical
forms to whole programs.

It is in experimental phase with a few important new features still to come.
One of them, available from v0.16, is use of a single `;` symbol as a
form-separating symbol in [implicit-progn](#LET ; progn example), [expression
terminator](#SETF expr-termination) for SETFs, or as end of [LET binds
symbol](#LET ; examples) or [local functions definition](#Local functions).
There is also `def`, for [defining things](#def).

The most recent one is the same priority OPs (since v0.20).

Once the rest of them have been implemented, BINFIX will go to RC and then to
reference 1.0 version.

-----------------------
## Content

* [Installation](#Instalation)
* [Examples](#Examples)
    * [Arithmetic and logical expressions](#Arithmetic and logical expressions)
    * [Consing](#Consing)
    * [Lambdas, definitions and type annotations](#Lambdas, definitions and type annotations)
        * [lambda](#lambda)
        * [Mappings](#Maps)
        * [defun](#defun)
        * [&optional](#&optional)
        * [Local functions](#Local functions)
        * [defmethod](#defmethod)
        * [defmacro](#defmacro)
        * [def](#def)
        * [Type annotations, declarations and definitions](#types)
    * [LETs](#LETs)
    * [SETs](#SETs)
    * [Implicit `progn`](#Implicit progn)
    * [`$`plitter](#`$`plitter)
    * [Multiple-choice forms](#Multiple-choice forms)
    * [Destructuring, multiple values](#Destructuring, multiple values)
    * [Loops](#Loops)
* [Indexing](#Indexing)
* [Mappings](#Mappings)
* [Working with bits](#Bits)
* [Support for macros](#Support for macros)
* [More involved examples](#More involved examples)
    * [ordinal](#ordinal)
    * [join](#join)
    * [values-bind](#values-bind)
    * [for](#for)
* [Implementation](#Implementation)
    * [proto-BINFIX](#proto-BINFIX)
* [Appendix](#Appendix)
    * [Operation properties](#Operation properties)
    * [List of all operations](#List of all operations)

-----------------------
<a name="Instalation"></a>
## Instalation

[Quicklisp](https://www.quicklisp.org/) makes the
downloading/installation/loading trivial:

    (ql:quickload :binfix)

After loading the package, the next step is to allow use of its symbols

    (use-package :binfix)

BINFIX is developed using
[SBCL](https://en.wikipedia.org/wiki/Steel_Bank_Common_Lisp), and checked to
work fine with [CLISP](https://en.wikipedia.org/wiki/CLISP),
and [Clozure CL](https://en.wikipedia.org/wiki/Clozure_CL),
while with [ECL](https://en.wikipedia.org/wiki/Embeddable_Common_Lisp) there
have been some problems with loading and testing recently, so for the
time being BINFIX is not running on ECL.
<!-- passes tests when hand-loaded but does not go through the package system yet. -->

BINFIX shadows `!` and `symbol-macrol` in CLISP , `@` in Clozure CL and ECL, as
well as `var` (`sb-debug:var`) in SBCL.

The latest version is available at [gihub](https://github.com/vcerovski/binfix),
and can be obtained by

    git clone https://github.com/vcerovski/binfix

<a name="Examples"></a>
## Examples

Generally, quoting a BINFIX expression in REPL will produce the corresponding
S-expression.

For easier comparison of input and output forms in following examples, LISP
printer is first `setq` (operation `=.`) to lowercase output with

    {*print-case* =. :downcase}

=> `:downcase`

BINFIX is a free-form notation (just like S-expr), i.e any number of empty
spaces (including tabs and newlines) between tokens is treated the same as a
single white space.

<a name="Arithmetic and logical expressions"></a>
### Arithmetic and logical expressions

Classic math stuff:

    {2 * 3 + 4}

=> `10`

    '{a * {b + c}}

=> `(* a (+ b c))`

    '{- {x + y} / x * y}

=> `(- (/ (+ x y) (* x y)))`

    '{0 < x < 1 && y >= 1 || y >= 2}

=> `(or (and (< 0 x 1) (>= y 1)) (>= y 2))`

    '{- f x - g x - h x}

=> `(- (- (f x)) (g x) (h x))`

Expressions like `{(f x y) * (g a b)}` and `{{f x y} * {g a b}}` generally
produce the same result. The inner brackets, however, can be removed:

    '{sqrt x * sin x}

=> `(* (sqrt x) (sin x))`

    '{A ! i .= B ! j + C ! k}

=> `(setf (aref a i) (+ (aref b j) (aref c k)))`

    '{a ! i j += b ! i k * c ! k j}

=> `(incf (aref a i j) (* (aref b i k) (aref c k j)))`

    '{listp A && car A == 'x && cdr A || A}

=> `(or (and (listp a) (eql (car a) 'x) (cdr x)) a)`

<a name="Consing"></a>
### Consing

Operation `:.` stands for `cons`. For instance,

    {-2 :. loop for i to 9 collect i}

=> `(-2 0 1 2 3 4 5 6 7 8 9)`

with the familiar behaviour:

    {1 :. 2 :. 3 equal '(1 2 . 3)}

=> `t`

    {1 :. 2 :. 3 :. {} equal '(1 2 3)}

=> `t`


<a name="Lambdas, definitions and type annotations"></a>
### Lambdas, definitions and type annotations

<a name="lambda"></a>
#### `lambda`

    '{x -> sqrt x * sin x}

=> `(lambda (x) (* (sqrt x) (sin x)))`

    '{x :single-float -> sqrt x * sin x}

=> `(lambda (x) (declare (type single-float x)) (* (sqrt x) (sin x)))`

    '{x y -> {x - y}/{x + y}}

=> `(lambda (x y) (/ (- x y) (+ x y)))`

Mixing of notations works as well, so each of the following

    {x y -> / (- x y) (+ x y)}
    {x y -> (- x y)/(+ x y)}
    {x y -> (/ (- x y) (+ x y))}

produces the same form.

Fancy way of writing `{2 * 3 + 4}`

    {x -> y -> z -> x * y + z @ 2 @ 3 @ 4}

=> `10`

Quoting reveals the expanded S-expr

    '{x -> y -> z -> x * y + z @ 2 @ 3 @ 4}

=>

    (funcall (funcall (funcall
      (lambda (x) (lambda (y) (lambda (z) (+ (* x y) z))))
        2) 3) 4)

Indeed, `@` is left-associative, standing for `funcall`.

More complicated types can be also explicitely given after an
argument, 

    '{x :|or symbol number| -> x :. x}

=>

    (lambda (x) (declare (type (or symbol number) x)) (cons x x))

<a name="Maps"></a>
#### `Mappings`

`mapcar` is also supported:

    '{x -> sin x * sqrt x @. (f x)}

=>

    (mapcar (lambda (x) (* (sin x) (sqrt x))) (f x))

Alternatively, it is possible to use the expression-termination symbol `;`,

    {x -> sin x * sqrt x @. f x;}

to the same effect.

`reduce` is represented by `@/`,

    '{#'max @/ x y -> abs{x - y} @. a b}

=>

    (reduce #'max (mapcar (lambda (x y) (abs (- x y))) a b))

and other maps have their `@`'s as well.


<a name="defun"></a>
#### `defun`

Factorial fun:

    '{f n :integer := if {n <= 0} 1 {n * f {1- n}}}

=>

    (defun f (n)
      (declare (type integer n))
      (if (<= n 0)
          1
          (* n (f (1- n)))))

Function documentation, local declarations, local bindings 
and comments have a straightforward syntax:

    '{g x := "Auxilary fn."
       declare (inline)
       let x*x = x * x; ;; Note binds termination via ;
         x*x / 1+ x*x}

=>

    (defun g (x)
      "Auxilary fn."
      (declare (inline))
      (let ((x*x (* x x)))
        (/ x*x (1+ x*x))))

<a name="&optional"></a>
#### `&optional` is optional

Explicitely tail-recursive version of `f`

    '{fac n m = 1 :=
       declare (integer m n)
       if {n <= 0} m
          {fac {n - 1} {n * m}}}

=>

    (defun fac (n &optional (m 1))
      (declare (integer m n))
      (if (<= n 0)
          m
          (fac (- n 1) (* n m))))

As you may by now expect, the following is also permited

    {fac n :integer m :integer = 1 :=
      if {n <= 0} m
         {fac {n - 1} {n * m}}}

<a name="Local functions"></a>
#### Local functions

Version of `fac` with a local recursive function `f`:

    {fac n :integer :=
      labels
        f n m := {if {n = 0} m
                     {f (1- n) {n * m}}}
       f n 1}

Another syntax to specify a local function is to use a single `;` as in

    {fac n :integer :=
      labels
        f n m := if {n = 0} m
                    {f (1- n) {n * m}};
       f n 1}

<!--
There is also yet another way to write the definition of `fac`, as

    {fac n :integer :=
      labels
        f n m := {if n = 0; m; f (1- n) {n * m}}
       f n 1}
-->

All three above definitions of `fac` are transformed by `binfix` to

    (defun fac (n)
      (declare (type integer n))
      (labels ((f (n m)
                 (if (= n 0)
                     m
                     (f (1- n) (* n m)))))

which can be demonstrated by simply evaluating the quoted expressions.

The same syntax is used also in the case of `flet` and `macrolet`.

<a name="defmethod"></a>
#### `defmethod`

The following two generic versions of `f`

    '{f n :integer :- if {n <= 0} 1 {n * f {1- n}}}
    '{f (n integer):- if {n <= 0} 1 {n * f {1- n}}}
<!--
    '{f n :integer :- {if n <= 0; 1;
                          n * f(1- n)}}
-->

both produce

    (defmethod f ((n integer))
      (if (<= n 0)
          1
          (* n (f (1- n)))))

`:-` supports also eql-specialization via `==` op, analogous to
the way `=` is used for optional arguments initialization, as well as an
optional method qualifier, given as the first argument after the method name,
that can be either a keyword or an atom surrounded by parens (i.e `:around`,
`(reduce)` etc.)

<a name="defmacro"></a>
#### `defmacro`

Macros are defined via `:==` operation, similar to the previous examples.
See Sec. [Support for macros](#Support for macros).

<a name="types"></a>
#### Type annotations, declarations and definitions

The examples shown so far demonstrate the possibility to type-annotate
symbols in binds and lambda-lists by an (optional) keyword representing
the type (for instance `:fixnum`, `:my-class`, `:|simple-array single-float|`,
`:|or symbol number|`, `:|{symbol or number}|`, etc.)

OPs that represent LISP forms which allow declaration(s), in BINFIX can 
have in addition to the standard `(declare ...)` form also unparenthesized
variant:

    '{f x :fixnum y = 2 :=
       declare (inline)
       declare (fixnum y)
       x + y ** 2}

=>

    (defun f (x &optional (y 2))
      (declare (type fixnum x))
      (declare (inline))
      (declare (fixnum y))
      (+ x (expt y 2)))

Operation `:->` can be used to specify function type. For example, in
SBCL 1.1.17 function `sin` has declared type that can be written as

    '{number :-> single-float -1.0 1.0 ||
                 double-float -1.0 1.0 ||
                 complex single-float  ||
                 complex double-float .x. &optional}

=>

    (function (number)
     (values
      (or (single-float -1.0 1.0)
          (double-float -1.0 1.0)
          (complex single-float)
          (complex double-float))
      &optional))

Type definitions are given using `:type=` OP, as in

    `{mod n :type= `(integer 0 (,n))}

=>

    (deftype mod (n) `(integer 0 (,n)))

<a name="def"></a>
#### `def`

Program typically consists of a number of definitions of functions,
constants, parameters, types, etc. The operation `def` is introduced
to facilitate their easy writing:

    '{def parameter *x* = 1 *y* = 2
      def struct point x y z
      def f x := sqrt x * sin x}

=>

    (progn
     nil
     (defparameter *x* 1)
     (defparameter *y* 2)
     (defstruct point x y z)
     (defun f (x) (* (sqrt x) (sin x))))

As it is clear from the example, the definitions are wrapped up in `progn`.

More detailed definitions are also straightforward to specify:

    '{def parameter
        *x* :fixnum = 1
        *y* :fixnum = 2;

      struct point "Point"
        :print-function {p s d ->
                           declare (ignore d)
                           with-slots (x y z) p
                             (format s "#<~$ ~$ ~$>" x y z)}
        :constructor create-point (x y z = 0f0)
        x :single-float = 0f0
        y :single-float = 0f0
        z :single-float = 0f0

      def f x :single-float :=
        declare (inline)
        sqrt x * sin x}

=>

    (progn
     nil
     (declaim (type fixnum *x*)
              (type fixnum *y*))
     (defparameter *x* 1)
     (defparameter *y* 2)
     (defstruct
         (point
          (:print-function
           (lambda (p s d)
             (declare (ignore d))
             (with-slots (x y z)
                 p
               (format s "#<~$ ~$ ~$>" x y z))))
          (:constructor create-point (x y &optional (z 0.0))))
       "Point"
       (x 0.0 :type single-float)
       (y 0.0 :type single-float)
       (z 0.0 :type single-float))
     (defun f (x)
       (declare (inline))
       (declare (type single-float x))
       (* (sqrt x) (sin x))))

`def`ining of symbols follows the same syntax as `let` binding, which
is covered next.

<a name="LETs"></a>
### LETs

LET symbol-binding forms (`let`, `let*` and `symbol-macrolet`) in BINFIX use
`=`  with an optional type-annotation:

    '{let x :bit = 1
          y = {2 ** 3}
          z = 4
        x + y * z}

=>

    (let ((x 1) (y (expt 2 3)) (z 4))
      (declare (type bit x))
      (+ x (* y z)))

<a name="LET ; examples"></a>
A single `;` can be used as a terminator of bindings:

    '{let x :bit = 1
          y = 2 ** 3
          z = f a;
        x + y * z}

=>

    (let ((x 1) (y (expt 2 3)) (z (f a)))
      (declare (type bit x))
      (+ x (* y z)))

<a name="LET ; progn example"></a>
Finally, a single `;` can also be used to separate forms in implicit-progn,
as in

    '{let x :bit = 1
          y = 2 ** 3
          z = f a;         ;; end of binds
        print "Let binds"; ;; 1st form
        x + y * z}         ;; 2nd form of implicit-progn

=>

    (let ((x 1) (y (expt 2 3)) (z (f a)))
      (declare (type bit x))
      (print "Let binds")
      (+ x (* y z)))

<a name="LET associativity"></a>
Nesting of `let`s without parens follows the right-associativity

    '{let a = f x;
        if a
          (g x)
          let b = h x;
            f b}

=>

    (let ((a (f x)))
      (if a
          (g x)
          (let ((b (h x)))
            (f b))))

Note the three levels of parens gone.

<a name="SETs"></a>
### SETs

In addition to `=.` and `.=` OPs representing, respectively, a single `setq`
and `setf` assignment, multiple assignments via SETs can be done using `=`,

    '{psetq x =   cos a * x + sin a * y
            y = - sin a * x + cos a * y}

=>

    (psetq x (+ (* (cos a) x) (* (sin a) y))
           y (+ (- (* (sin a) x)) (* (cos a) y)))

If it is necessary to remove repeating `sin a` and `cos a`,
it is easy to use `let`,

    {let sin = sin a
         cos = cos a;
       psetq x =   cos * x + sin * y
             y = - sin * x + cos * y}

and in the case of SETF assignments, RHS are represented with a single
expression,

    '{psetf a ! 0 = {a ! 1}
            a ! 1 = {a ! 0}}

=>

    (psetf (aref a 0) (aref a 1)
           (aref a 1) (aref a 0))

<a name="SETF expr-termination"></a>
Alternatively, it is possible to use a single `;` as an expression-termination
symbol,

    '{psetf a ! 0 = a ! 1; ;; expr. termination via single ;
            a ! 1 = a ! 0}

=>

    (psetf (aref a 0) (aref a 1)
           (aref a 1) (aref a 0))

It is also possible to mix infix SETFs with other expressions:

    '{f x + setf a = b
                 c = d;
          * h a c}

=>

    (+ (f x)
       (*
        (setf a b
              c d)
        (h a c)))

<a name="Implicit progn"></a>
### Implicit `progn`

An implicit `progn` in BINFIX is achieved with a single `;` separating the
forms forming the progn.  In all cases (`->`, `:=`, `:-` and LETs) the syntax
is following that of the [LET example above](#LET ; progn example).

As expected, other `prog`s have to be explicitly given,

    '{x -> prog2 (format t "Calculating... ")
                 {f $ x * x}
                 (format t "done.~%")}

or

    '{x -> prog2
             format t "Calculating... ";
             f {x * x};
             format t "done.~%"}

both producing the following form

    (lambda (x)
      (prog2 (format t "Calculating... ") (f (* x x)) (format t "done.~%")))

Since BINFIX is a free-form notation, the following one-liner also works:

    '{x -> prog2 format t "Calculating... "; f{x * x}; format t "done.~%"}

Binfix `<&` stands for `prog1`,

    '{x -> {f {x * x} <&
            format t "Calculation done.~%"}}

=>

    (lambda (x) (prog1 (f (* x x)) (format t "Calculation done.~%")))

<a name="`$`plitter"></a>
### `$`plitter

Infix `$` is a vanishing OP, leaving only its arguments,
effectivelly splitting the list in two parts.

    '{f $ g $ h x y z}

=> `(f (g (h x y z)))`

So its effect here is similar to `$` in Haskell. 
Or perphaps:

    '{declare $ optimize (speed 1) (safety 1)}

=> `(declare (optimize (speed 1) (safety 1)))`


`$`plitter also allows writing a shorter `cond`, as in

    (cond {p x $ f x}
          {q x $ g x}
          {r x $ h x}
          {t $ x})

compared to the equivalent

    (cond ((p x) (f x))
          ((q x) (g x))
          ((r x) (h x))
          (t x))

Another splitter is `?`, which can be used instead of `$` in the previous
example, as well as described in the next section.

<a name="Multiple-choice forms"></a>
### Multiple-choice forms (`cond`, `case`, ...)

An alternative syntax to describe multiple-choice forms is to use `?` and `;`

    {cond p x ? f x;
          q x ? g x;
          r x ? h x;
            t ? x}

See also [`ordinal` example below](#ordinal).

<a name="Destructuring, multiple values"></a>
### Destructuring, multiple values

Multiple values (`values`) are represented by `.x.`, 
`multiple-value-bind` by `=..` , and `destructuring-bind` by `..=`

    '{a (b) c ..= (f x) a + 1 .x. b + 2 .x. c + 3}

=>

    (destructuring-bind (a (b) c) (f x) (values (+ a 1) (+ b 2) (+ c 3)))

Another way to write the same expr:

    '{a (b) c ..= (f x) values a + 1; b + 2; c + 3}

`multiple-value-call` is represented by `.@.`

    '{#'list .@. 1 '(b 2) 3}

=>

    (multiple-value-call #'list 1 '(b 2) 3)

=>

    (1 (b 2) 3)

Both `..=` and `=..` can be nested,

    '{a b c =.. (f x)
      x y z =.. (g z)
      a * x + b * y + c * z}

=>

    (multiple-value-bind (a b c)
        (f x)
      (multiple-value-bind (x y z) (g z) (+ (* a x) (* b y) (* c z))))

<a name="Loops"></a>
#### Loops

Loops can be also nested without writing parens:

    '{loop for i = 1 to 3
           collect loop for j = 2 to 4
                        collect {i :. j}}

=>

    (loop for i = 1 to 3
          collect (loop for j = 2 to 4
                        collect (cons i j))) 

<a name="Mappings"></a>
### Mappings

Mappings and function applications are what `@`-ops are all about,
as summarized in the following table,

<table>
  <tr><td>  <code>@</code></td>  <td><code>funcall</code></td></tr>
  <tr><td>  <code>@.</code></td> <td><code>mapcar</code></td></tr>
  <tr><td>  <code>@..</code></td><td><code>maplist</code></td></tr>
  <tr><td>  <code>@n</code></td> <td><code>mapcan</code></td></tr>
  <tr><td>  <code>@.n</code></td><td><code>mapcon</code></td></tr>
  <tr><td> <code>.@</code></td>  <td><code>mapc</code></td></tr>
  <tr><td><code>..@</code></td>  <td><code>mapl</code></td></tr>
  <tr><td>  <code>@/</code></td> <td><code>reduce</code></td></tr>
  <tr><td>  <code>@@</code></td> <td><code>apply</code></td></tr>
  <tr><td> <code>.@.</code></td> <td><code>multiple-value-call</code></td></tr>
</table>

They all have the same priority and are right-associative, and, since
they bind weaker than `->`, are easy to string together with lambdas,
as in a map-reduce expr.

`{'max @/ x y -> abs{x - y} @. a b}`

<a name="Indexing"></a>
### Indexing

The following table summarizes BINFIX OPs for indexing, from
the weakest to the strongest binding OP:

<table>
  <tr><td><code>!..</code></td>     <td><code>nth-value</code></td></tr>
  <tr><td><code>th-value</code></td><td><code>nth-value</code></td></tr>
  <tr><td><code>.!</code></td>      <td><code>elt</code></td>      </tr>
  <tr><td><code>th</code></td>      <td><code>nth</code></td>      </tr>
  <tr><td><code>th-bit</code></td>  <td><code>logbitp</code></td>  </tr>
  <tr><td><code>th-cdr</code></td>  <td><code>nthcdr</code></td>   </tr>
  <tr><td><code>!.</code></td>      <td><code>svref</code></td>    </tr>
  <tr><td><code>!!.</code></td>     <td><code>row-major-aref</code></td></tr>
  <tr><td><code>.!!.</code></td>    <td><code>bit</code></td>      </tr>
  <tr><td><code>!!</code></td>      <td><code>aref</code></td>     </tr>
  <tr><td><code>.!.</code></td>     <td><code>bit</code></td>      </tr>
  <tr><td><code>!</code></td>       <td><code>aref</code></td>     </tr>
</table>

`!..` and `th-value` are mere synonyms and have the same priority, while `!!`
is a weaker binding `!`, allowing easier writting of expr. with arithmetic
operations with indices, like

`{a !! i + j}`

`{a !! i + j; 1- k;}`

etc.  In the same relation stand `.!.` and `.!!.`

<a name="Bits"></a>
### Working with bits

Integer bit-logical BINFIX ops are given with a `.` after the name of OP,
while bit-array version of the same OP with `.` before and after the name.
For instance, `{a or. b}` transforms to `(logior a b)`, while
`{a .or. b}` transforms to `(bit-ior a b)`.

<a name="Support for macros"></a>
### Support for macros

If BINFIX terms _only_ are inserted under backquote, everything should work
fine, 

    '{let t1 = 'x
          t2 = '{x + x}
         `{x -> ,t1 / ,t2}}

=>

    (let ((t1 'x) (t2 '(+ x x)))
      `(lambda (x) (/ ,t1 ,t2)))

Replacing, however, BINFIX operations inside a backquoted BINFIX will _not_
work.  This is currently not considered as a problem because direct call of
`binfix` will cover some important cases of macro transformations in a 
straightforward manner:

    {m x y op = '/ type = :double-float :==
       let a = (gensym)
           b = (gensym)
         binfix `(let ,a ,type = ,x
                      ,b ,type = ,y
                    {,a - ,b} ,op {,a + ,b})}

Now macro `m` works as expected:

    (macroexpand-1 '(m (f x y) {a + b}))

=>

    (let ((#:g805 (f x y)) (#:g806 (+ a b)))
      (declare (type double-float #:g806)
               (type double-float #:g805))
      (/ (- #:g805 #:g806) (+ #:g805 #:g806)))
    t

or,

    (macroexpand-1 '(m (f x y) {a + b}) * :double-float)

=>

    (let ((#:g817 (f x y)) (#:g818 (+ a b)))
      (declare (type double-float #:g817)
               (type double-float #:g818))
      (* (- #:g817 #:g818) (+ #:g817 #:g818)))
    t

See more in [implementation details](#binfix macros)

<a name="More involved examples"></a>
### More involved examples

<a name="ordinal"></a>
#### `ordinal`

Converting an integer into ordinal string in English can be defined as

    {ordinal i :integer :=
       let* a = i mod 10
            b = i mod 100
          suf = {cond
                   a = b = 1 || a = 1 && 21 <= b <= 91 ? "st";
                   a = b = 2 || a = 2 && 22 <= b <= 92 ? "nd";
                   a = b = 3 || a = 3 && 23 <= b <= 93 ? "rd";
                                                    t  ? "th"}
            format () "~D~a" i suf}

It can be also written in a more "lispy" way without parens as

    {ordinal1 i :integer :=
       let* a = i mod 10
            b = i mod 100
          suf = {cond
                   = a b 1 or = a 1 and <= b 21 91 ? "st";
                   = a b 2 or = a 2 and <= b 22 92 ? "nd";
                   = a b 3 or = a 3 and <= b 23 93 ? "rd";
                                                t  ? "th"}
            format () "~D~a" i suf}

which can be tried using `@.` (`mapcar`)

    {#'ordinal @. '(0 1 12 22 43 57 1901)}

=> `("0th" "1st" "12th" "22nd" "43rd" "57th" "1901st")`

(This example is picked up from [Rust
blog](http://blog.rust-lang.org/2015/04/17/Enums-match-mutation-and-moves.html))

<a name="join"></a>
#### `join`

APL-ish joining of things into list:

    {
      defgeneric join (a b) &

      join a :list  b :list :- append a b        &
      join a :t     b :list :- cons a b          &
      join a :list  b :t    :- append a (list b) &
      join a :t     b :t    :- list a b          &

      defbinfix '++ 'join 
    }
    ; Must close here in order to use ++

    {let e = '{2 in 'x ++ '(1 2 3) ++ '((a)) ++ -1 * 2}
        format t "~S~%=> ~S" e (eval e)}

Evaluation of the above returns `t` and prints the following

    (member 2 (join 'x (join '(1 2 3) (join '((a)) (* -1 2)))))
    => (2 3 (a) -2)

<a name="values-bind"></a>
#### `values-bind`

Macro `multiple-value-bind` with symbol `_` in variable list standing for
an ignored value can be defined as

    {values-bind v e &rest r :==
      let*  _ = ()
         vars = a -> if {a == '_} {car $ push (gensym) _} a @. v;
        `(multiple-value-bind ,vars ,e
            ,@{_ && `({declare $ ignore ,@_})}
            ,@r)}

So, for instance,

    (macroexpand-1 '(values-bind (a _) (truncate 10 3) a))

=>

    (multiple-value-bind (a #:g823) (truncate 10 3) (declare (ignore #:g823)) a)
    t

<a name="for"></a>
#### `for`

Nested BINFIX lambda lists can be used in definitions of macros, as in the
following example of a procedural for-loop macro

    {for (v :symbol from below by = 1) &rest r :==
      `(loop for,v fixnum from,from below,below ,@{by /= 1 && `(by,by)}
             do ,@r)}

Now

    (macroexpand-1 '(for (i 0 n)
                      {a ! i .= 1+ i}))

=>

    (loop for i fixnum from 0 below n
          do (setf (aref a i) (1+ i)))
    t

<a name="Implementation"></a>
## Implementation

BINFIX expression is written as a list enclosed in curly brackets `{` ... `}`
handled through LISP reader, so the usual syntax rules of LISP apply, e.g `a+b`
is a single symbol, while `a + b` is three symbols.  Lisp reader after
tokenization calls the function `binfix` which does shallow transformation of
BINFIX into S-expr representation of the expression.

BINFIX uses a simple rewrite algorithm that divides a list in two, LHS and RHS
of the lowest priority infix operator found within the list, then recursively
processes each one.

<a name="proto-BINFIX"></a>
### proto-BINFIX

Bootstraping is done beginning with proto-BINFIX,

    (defparameter *binfix*
      '(( &  progn)
        (:== def defmacro)
        (:=  def defun)
        (:-  def defmethod)
        ( =. setq)
        (.=  setf)
        (->  def lambda)
        ($)
        (labels flet= labels)
        (let  let= let)
        (let* let= let*)
        (:.   cons)
        (||   or)
        (&&   and)
        (==   eql)
        (=c=  char=)
        (in   member)
        ( !   aref)))
    
    (defun binfix (e &optional (ops *binfix*))
      (cond ((atom e) e)
            ((null ops) (if (cdr e) e (car e)))
            (t (let* ((op (car ops))
                      (i (position (pop op) e)))
                 (if (null i)
                   (binfix e (cdr ops))
                  `(,@op
                    ,(if (eql (car op) 'def)
                        (subseq e 0 i)
                        (binfix (subseq e 0 i) (cdr ops)))
                    ,(binfix (subseq e (1+ i)) ops)))))))
    
    (set-macro-character #\{
      (lambda (s ch) (declare (ignore ch))
        (binfix (read-delimited-list #\} s t))))
    
    (set-macro-character #\} (get-macro-character #\) ))

which captures the basics of BINFIX.

The next bootstrap phase defines macro `def` and, in the same 
single BINFIX expression, macros `let=` and `flet=`

    {defmacro def (what args body)
      `(,what ,@(if {what == 'lambda}
                  `(,(if {args && atom args} `(,args) args))
                   (if (atom args) `(,args ()) `(,(car args),(cdr args))))
              ,body) &

     let= let lhs body &aux vars :==
      loop while {cadr body == '=}
         do {push `(,(car body),(caddr body)) vars &
             body =. cdddr body}
         finally (return (let ((let `(,let ,(nreverse vars) ,@body)))
                           (if lhs `(,@lhs ,let) let))) &

     flet= flet lhs body &aux funs :==
      loop for r = {'= in body} while r
           for (name . lambda) = (ldiff body r)
           do {push `(,name ,lambda ,(cadr r)) funs &
               body =. cddr r}
           finally (return (let ((flet `(,flet ,(nreverse funs) ,@body)))
                             (if lhs `(,@lhs ,flet) flet)))}

which wraps up proto-BINFIX.

Since v0.15, BINFIX interns a symbol consisting of a single `;` char not
followed by `;` char, while two or more consequtive `;` are interpreted
as starting a comment.  This behavior is limited to BINFIX
expressions only, while outside of them the standard LISP rules apply.

Since v0.19, proto-BINFIX introduces `unreduc` property.

The rest is written using this syntax, and consists of handling of lambda lists
and `let`s, a longer list of OPs with properties, redefined `binfix` to
its full capability, and, finally, several interface functions for
dealing with OPs (`lsbinfix`, `defbinfix` and `rmbinfix`).

Priorities of operations in proto-BINIFIX are given only relatively, with no
numerical values and thus with no two operations of the same priority.

Since v0.20, symbol of a BINFIX operation has a list of properties stored into
the symbol property `binfix::properties`, which includes a numerically given
priority of the OP (which also considerably speeds up parsing.) The actual
value of number representing priority is supposed to be immaterial since only
relation to other OPs priority values is relevant.  Defining new same-priority
OPs should be done via `defbinfix` with `:as` option, which may change priority
values of many other OPs.

<a name="binfix macros"></a>
Since shallow transformation into standard syntax is done by function `binfix`
invoked recursively by the reader, `binfix` cannot be directly called for
arbitrary macro transformation of BINFIX into BINFIX when standard macro
helpers BACKTICK, COMA and COMA-AT are used. The reason is that `{`...`}` is
invoked before them while the correct order would be after them.
Examples of succesful combinations of backquoting and BINFIX are given
[above](#Support for macros).

<a name="Appendix"></a>
## Appendix

<a name="Operation properties"></a>
### Operation properties

`:def` -- Operation (OP) is a definition requiring LHS to has a name and lambda
list.

`:defm` -- OP is a definition requiring LHS to have a name followed by
unparenthesized method lambda list.

`:lhs-lambda` -- OP has lambda list as its LHS.

`:rhs-lbinds` -- OP has let-binds at the beginning of its LHS,<br>
[*symbol* [*keyword*] **`=`** *expr*]\* *declaration*\*

`:rhs-fbinds` -- OP has flet-binds at the beginning of its LHS, including
optional declarations.

`:rhs-sbinds` -- OP has symbol-binds as its RHS. They are let-binds without
annotations or declarations,
[*symbol* **`=`** *expr*<sup>+</sup>]<sup>+</sup>

`:rhs-ebinds` -- OP has expr-binds at the beginning of its RHS,
[*expr*<sup>+</sup> **`=`** *expr*]\*

`:unreduce` -- All appearances of OP at the current level should be unreduced,
i.e replaced with a single call with multiple arguments.

`:left-assoc` -- OP is left--associative (OPs are right-associative by default.)

`:prefix` -- OP is prefix with RHS being its arguments, given as one or more
atoms/S-expr or a single `;` separated B-expr.

`:also-prefix` -- OP can be used as prefix when LHS is missing.

`:also-unary` -- OP can be used as unary when LHS is missing.

`:also-postfix` -- OP can be used as postfix when RHS is missing.

`:lambda/expr` -- OP takes lambda-list at LHS and an expression at RHS, followed by body.

`:syms/expr` -- OP takes a list of symbols as LHS (each with an optional
[keyword-type](#types) annotation,) an expression as RHS followed
by optional declarations and a BINFIX-expression.

`#'my-fun` -- function `my-fun` will be applied to the untransformed RHS.

`:split` -- OP splits the expr at this point.

`:rhs-args` -- OP takes LHS as 1st and RHS as remaining arguments.

`:macro` -- OP is a macro.

<a name="List of all operations"></a>
### List of all operations

Command

    (lsbinfix)

prints the table of all BINFIX OPs and their properties from the weakest-
to the strongest-binding OP, with parens enclosing OP(s) of the same priority:

      BINFIX         LISP            Properties
    ==============================================================================
    ( <&             prog1 )
    ( &              progn           :unreduce )
    ( def            binfix::defs    :macro )
    ( let            let             :rhs-lbinds
      let*           let*            :rhs-lbinds
      symbol-macrolet                symbol-macrolet :rhs-lbinds
      prog*          prog*           :rhs-lbinds
      prog           prog            :rhs-lbinds )
    ( macrolet       macrolet        :rhs-fbinds
      flet           flet            :rhs-fbinds
      labels         labels          :rhs-fbinds )
    ( :==            defmacro        :def
      :=             defun           :def
      :-             defmethod       :defm
      :type=         deftype         :def )
    ( block          block           :prefix
      tagbody        tagbody         :prefix
      catch          catch           :prefix
      prog1          prog1           :prefix
      prog2          prog2           :prefix
      progn          progn           :prefix
      cond           cond            :prefix
      case           case            :prefix
      ccase          ccase           :prefix
      ecase          ecase           :prefix
      typecase       typecase        :prefix
      etypecase      etypecase       :prefix
      ctypecase      ctypecase       :prefix )
    ( loop           #<FUNCTION identity>            :prefix )
    ( ?              nil             :split )
    ( $              nil             :split )
    ( .=             setf
      +=             incf
      -=             decf
      =.             setq
      .=.            set )
    ( setq           setq            :rhs-sbinds
      set            set             :rhs-sbinds
      psetq          psetq           :rhs-sbinds )
    ( setf           setf            :rhs-ebinds
      psetf          psetf           :rhs-ebinds )
    ( .@             mapc            :rhs-args
      ..@            mapl            :rhs-args
      @/             reduce          :rhs-args
      @.             mapcar          :rhs-args
      @..            maplist         :rhs-args
      @n             mapcan          :rhs-args
      @.n            mapcon          :rhs-args
      @@             apply           :rhs-args
      .@.            multiple-value-call             :rhs-args
      @              funcall         :rhs-args       :left-assoc     :also-postfix )
    ( :->            function        :lhs-lambda )
    ( ->             lambda          :lhs-lambda )
    ( values         values          :prefix )
    ( =..            multiple-value-bind             :syms/expr )
    ( ..=            destructuring-bind              :lambda/expr )
    ( !..            nth-value
      th-value       nth-value )
    ( ||             or              :unreduce
      or             or              :unreduce       :also-prefix )
    ( &&             and             :unreduce
      and            and             :unreduce       :also-prefix )
    ( <              <               :unreduce       :also-prefix )
    ( >              >               :unreduce       :also-prefix )
    ( <=             <=              :unreduce       :also-prefix )
    ( >=             >=              :unreduce       :also-prefix )
    ( ===            equalp )
    ( equalp         equalp )
    ( equal          equal )
    ( ==             eql )
    ( eql            eql             :also-prefix )
    ( .x.            values          :unreduce       :also-prefix )
    ( :|.|           cons )
    ( =s=            string= )
    ( =c=            char=           :unreduce )
    ( =              =               :unreduce       :also-prefix )
    ( /=             /=              :unreduce       :also-prefix )
    ( eq             eq )
    ( subtypep       subtypep )
    ( in             member )
    ( coerce         coerce )
    ( .!!.           bit             :rhs-args )
    ( th-cdr         nthcdr )
    ( th             nth )
    ( .!             elt )
    ( !.             svref )
    ( !!.            row-major-aref )
    ( !!             aref            :rhs-args )
    ( th-bit         logbitp )
    ( dpb            dpb             :rhs-args )
    ( ldb            ldb )
    ( ldb-test       ldb-test )
    ( deposit-field  deposit-field   :rhs-args )
    ( mask-field     mask-field )
    ( byte           byte )
    ( eqv.           logeqv          :also-unary     :unreduce )
    ( or.            logior          :also-unary     :unreduce )
    ( xor.           logxor          :also-unary     :unreduce )
    ( and.           logand          :also-unary     :unreduce )
    ( nand.          lognand )
    ( nor.           lognor )
    ( test.          logtest )
    ( orc1.          logorc1 )
    ( orc2.          logorc2 )
    ( andc1.         logandc1 )
    ( andc2.         logandc2 )
    ( .eqv.          bit-eqv         :rhs-args )
    ( .or.           bit-ior         :rhs-args )
    ( .xor.          bit-xor         :rhs-args )
    ( .and.          bit-and         :rhs-args )
    ( .nand.         bit-and         :rhs-args )
    ( .nor.          bit-nor         :rhs-args )
    ( .not.          bit-not         :also-unary )
    ( .orc1.         bit-orc1        :rhs-args )
    ( .orc2.         bit-orc2        :rhs-args )
    ( .andc1.        bit-andc1       :rhs-args )
    ( .andc2.        bit-andc2       :rhs-args )
    ( <<             ash )
    ( lcm            lcm             :also-unary     :unreduce )
    ( gcd            gcd             :also-unary     :unreduce )
    ( mod            mod )
    ( rem            rem )
    ( min            min             :also-prefix    :unreduce
      max            max             :also-prefix    :unreduce )
    ( +              +               :also-unary     :unreduce )
    ( -              -               :also-unary     :unreduce )
    ( /              /               :also-unary )
    ( *              *               :also-prefix    :unreduce )
    ( **             expt )
    ( .!.            bit             :rhs-args )
    ( !              aref            :rhs-args )
    ( |;|            |;| )
    ------------------------------------------------------------------------------

=> `nil`

