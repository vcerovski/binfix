<link href="markdown.css" rel="stylesheet" type="text/css"></link>

# BINFIX

Viktor Cerovski, Oct 2015.

<a name="Introduction"></a>
## Introduction

BINFIX (blend from "Binary Infix") is a poweful infix syntax notation for
S-expressions of Common LISP ranging from simple arithmetic and logical
forms to whole programs.

It is in experimental phase with a few important new features still to come.
One of them is use of a single `;` symbol as [expression terminator](#SETF expr-termination),
available from v0.16.

Once they've been implemented, BINFIX will go to RC and then a reference 1.0 version.

-----------------------
## Content

* [Installation](#Instalation)
* [Examples](#Examples)
    * [Arithmetic and logical expressions](#Arithmetic and logical expressions)
    * [Consing](#Consing)
    * [Lambdas, definitions and type annotations](#Lambdas, definitions and type annotations)
        * [lambda](#lambda)
        * [defun](#defun)
        * [&optional](#&optional)
        * [Local functions](#Local functions)
        * [defmethod](#defmethod)
        * [defmacro](#defmacro)
        * [Type annotations and declarations](#type annotations)
    * [LETs](#LETs)
    * [SETs](#SETs)
    * [Implicit/Explicit `progn`](#Implicit/Explicit progn)
    * [`$`plitter](#`$`plitter)
    * [Multiple-choice forms](#Multiple-choice forms)
    * [Destructuring, multiple values](#Destructuring, multiple values)
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

[Quicklisp](https://www.quicklisp.org/) makes the downloading/installation/loading
trivial:

    (ql:quickload :binfix)

After loading the package, the next step is to allow use of its symbols

    (use-package :binfix)

BINFIX is developed using
[SBCL](https://en.wikipedia.org/wiki/Steel_Bank_Common_Lisp), and checked to
work fine with [CLISP](https://en.wikipedia.org/wiki/CLISP),
and [Clozure CL](https://en.wikipedia.org/wiki/Clozure_CL),
while with [ECL](https://en.wikipedia.org/wiki/Embeddable_Common_Lisp) BINFIX
passes tests when hand-loaded but does not go through the package system yet.

BINFIX shadows `!` in CLISP (`ext:!`) and `@` in Clozure CL and ECL.

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

    {{1 :. 2 :. 3} equal '(1 2 . 3)}

=> `t`

    {{1 :. 2 :. 3 :. {}} equal '(1 2 3)}

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

    {{x -> y -> z -> x * y + z} @ 2 @ 3 @ 4}

=> `10`

Quoting reveals the expanded S-expr

    '{{x -> y -> z -> x * y + z} @ 2 @ 3 @ 4}

=>

    (funcall (funcall (funcall
      (lambda (x) (lambda (y) (lambda (z) (+ (* x y) z))))
        2) 3) 4)

Indeed, `@` is left-associative, standing for `funcall`.

More complicated types can be also explicitely given after the
argument, 

    '{x :|or symbol number| -> x :. x}

=>

    (lambda (x) (declare (type (or symbol keyword) x)) (cons x x))


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

    '{fac n :integer :=
       labels
         f n m := {if {n = 0} m
                      {f (1- n) {n * m}}}
        (f n 1)}

=>

    (defun fac (n)
      (declare (type integer n))
      (labels ((f (n m)
                 (if (= n 0)
                     m
                     (f (1- n) (* n m)))))

The same syntax is used in the case of `flet` and `macrolet`.

<a name="defmethod"></a>
#### `defmethod`

Generic versions of `f`

    '{f n :integer :- if {n <= 0} 1 {n * f {1- n}}}
    '{f (n integer):- if {n <= 0} 1 {n * f {1- n}}}

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

<a name="type annotations"></a>
#### Type annotations and declarations

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

<a name="LETs"></a>
### LETs

LET-binding forms (`let`, `let*` and `symbol-macrolet`) in BINFIX use `=`  with
an optional type-annotation:

    '{let x :bit = 1
          y = 2
        x + y}

=>

    (let ((x 1) (y 2))
      (declare (type bit x))
      (+ x y))

`flet`/`labels` forms require name and lambda-list before `:=` symbol:

    '{flet f x := {sqrt x * sin x}
        (f 0.5)}

=>

    (flet ((f (x)
             (* (sqrt x) (sin x))))
      (f 0.5))

<a name="SETs"></a>
### SETs

In addition to `=.` and `.=` OPs representing, respectively, a single `setq`
and `setf` assignment, multiple assignments via SETs can be done using `=`,

    '{psetq x =   cos a * x + sin a * y
            y = - sin a * x + cos a * y}

=>

    (psetq x (+ (* (cos a) x) (* (sin a) y))
           y (+ (- (* (sin a) x)) (* (cos a) y)))

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

<a name="Implicit/Explicit progn"></a>
### Implicit/Explicit `progn`

Lambda's and LET's written in BINFIX have no implicit progn.  This in
particular means that if a prog is needed in the body of lambda or LET, it
should be explicitely given:

    {x -> prog2 (format t "Calculating... ")
                {f $ x * x}
                (format t "done.~%")}

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

    '{a (b) c ..= (f x) {a + 1 .x. b + 2 .x. c + 3}}

=>

    (destructuring-bind (a (b) c) (f x) (values (+ a 1) (+ b 2) (+ c 3)))

Another example:

    {{.x. 5 1 5 1} == {a b =.. (truncate 11 2) {.x. a b a b}}}

=> `t`

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

    {m x y :==
       let a = (gensym)
           b = (gensym)
         binfix `(let ,a :double-float = ,x
                      ,b :double-float = ,y
                    {{,a - ,b} / {,a + ,b}})}

Now macro `m` works as expected:

    (macroexpand-1 '(m (f x y) {a + b}))

=>

    (let ((#:g805 (f x y)) (#:g806 (+ a b)))
      (declare (type double-float #:g806)
               (type double-float #:g805))
      (/ (- #:g805 #:g806) (+ #:g805 #:g806)))
    t

See more in [implementation details](#binfix macros)

<a name="More involved examples"></a>
### More involved examples

<a name="ordinal"></a>
#### `ordinal`

Converting an integer into ordinal string in English can be defined as

    {ordinal i :integer :=
       let* a = {i mod 10}
            b = {i mod 100}
          suf = {cond
                   a = b = 1 || a = 1 && 21 <= b <= 91 ? "st";
                   a = b = 2 || a = 2 && 22 <= b <= 92 ? "nd";
                   a = b = 3 || a = 3 && 23 <= b <= 93 ? "rd";
                                                    t  ? "th"}
            format () "~D~a" i suf}

It can be also written in a more "lispy" way without parens as

    {ordinal1 i :integer :=
       let* a = {i mod 10}
            b = {i mod 100}
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
         vars = {a -> if {a == '_} {car $ push (gensym) _} a @. v}
        `(multiple-value-bind ,vars ,e
            ,@(if _ `({declare $ ignore ,@_}))
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

    (macroexpand-1 '(for (i 0 n) {a ! i .= 1+ i}))

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

The rest is written using this syntax, and consists of handling of lambda lists
and `let`s, a longer list of OPs with properties, redefined `binfix` to
its full capability, and, finally, several interface functions for
dealing with OPs (`lsbinfix`, `defbinfix` and `rmbinfix`).

Priorities of operations are given only relatively, with no numerical values and
thus with no two operations of the same priority.

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

`:defm` -- OP is a definition requiring LHS to has a name, and method lambda
list.

`:lhs-lambda` -- OP has lambda list as its LHS.

`:rhs-lbinds` -- OP has let-binds at the beginning of its LHS,<br>
[*symbol* [*keyword*] **`=`** *expr*]\* *declaration*\*

`:rhs-sbinds` -- OP has symbol-binds as its RHS. They are let-binds without
annotations or declarations,
[*symbol* **`=`** *expr*<sup>+</sup>]<sup>+</sup>

`:rhs-ebinds` -- OP has expr-binds at the beginning of its RHS,
[*expr*<sup>+</sup> **`=`** *expr*]\*

`:unreduce` -- All appearances of OP at the current level should be unreduced,
i.e replaced with a single call with multiple arguments.

`:left-assoc` -- OP is left--associative (OPs are right-associative by default.)

`:prefix` -- OP is prefix with RHS being its arguments.

`:also-prefix` -- OP can be used as prefix OP when LHS is missing.

`:also-unary` -- OP can be used as unary when LHS is missing.

`:also-postfix` -- OP can be used as postfix OP when RHS is missing.

`:lambda/expr` -- OP takes lambda-list at LHS and an expression at RHS, followed by body.

`:syms=expr` -- OP takes a list of symbols as LHS (each with an optional
[keyword-type](#type annotations) annotation), an expression as RHS followed
by optional declarations and a BINFIX-expression.

`#'my-fun` -- function `my-fun` will be applied to the untransformed RHS.

`:split` -- OP splits the expr at this point.

`:rhs-args` -- OP takes LHS as 1st and RHS as remaining arguments.

<a name="List of all operations"></a>
### List of all operations

    (lsbinfix)

prints the table of all BINFIX OPs and their properties from the weakest-
to the strongest-binding OP:

    BINFIX           LISP            Properties
    ============================================================
    &                progn           :unreduce       
    let              let             :rhs-lbinds     
    let*             let*            :rhs-lbinds     
    flet             #<FUNCTION binfix::=flet>       
    labels           #<FUNCTION binfix::=flet>       
    macrolet         #<FUNCTION binfix::=flet>       
    symbol-macrolet  symbol-macrolet :rhs-lbinds     
    :==              defmacro        :def            
    :=               defun           :def            
    :-               defmethod       :defm           
    block            block           :prefix         
    tagbody          tagbody         :prefix         
    catch            catch           :prefix         
    progn            progn           :prefix         
    cond             cond            :prefix         
    case             case            :prefix         
    ccase            ccase           :prefix         
    ecase            ecase           :prefix         
    typecase         typecase        :prefix         
    etypecase        etypecase       :prefix         
    ctypecase        ctypecase       :prefix         
    if               if              :prefix         
    loop             #<FUNCTION identity>            
    ?                binfix::interleave              :unreduce       
    $                nil             :split          
    .=               setf            
    +=               incf            
    -=               decf            
    =.               setq            
    .=.              set             
    setq             setq            :rhs-sbinds     
    set              set             :rhs-sbinds     
    psetq            psetq           :rhs-sbinds     
    setf             setf            :rhs-ebinds     
    psetf            psetf           :rhs-ebinds     
    mapc             mapc            
    @.               mapcar          :rhs-args       
    @n               mapcan          :rhs-args       
    @..              maplist         :rhs-args       
    @.n              mapcon          :rhs-args       
    :->              function        :lhs-lambda     
    ->               lambda          :lhs-lambda     
    @@               apply           :rhs-args       
    @                funcall         :rhs-args       :left-assoc     :also-postfix   
    .x.              values          :unreduce       :also-prefix    
    =..              multiple-value-bind             :syms=decl    
    ..=              destructuring-bind              :lambda/expr    
    :|.|             cons            
    ||               or              :unreduce       
    or               or              :unreduce       :also-prefix    
    &&               and             :unreduce       
    and              and             :unreduce       :also-prefix    
    <                <               :unreduce       :also-prefix    
    >                >               :unreduce       :also-prefix    
    <=               <=              :unreduce       :also-prefix    
    >=               >=              :unreduce       :also-prefix    
    ===              equalp          
    equalp           equalp          
    equal            equal           
    ==               eql             :also-prefix    
    eql              eql             :also-prefix    
    =s=              string=         
    =c=              char=           :unreduce       
    =                =               :unreduce       :also-prefix    
    /=               /=              :unreduce       :also-prefix    
    eq               eq              
    subtypep         subtypep        
    in               member          
    coerce           coerce          
    cons             cons            :also-prefix    
    elt              elt             
    svref            svref           
    !!               aref            
    logior           logior          :unreduce       
    logand           logand          :unreduce       
    <<               ash             
    mod              mod             
    min              min             :also-prefix    :unreduce       
    max              max             :also-prefix    :unreduce       
    +                +               :also-prefix    :unreduce       
    -                -               :also-unary     :unreduce       
    floor            floor           
    ceiling          ceiling         
    truncate         truncate        
    /                /               :also-unary     
    *                *               :also-prefix    :unreduce       
    **               expt            
    !                aref            :rhs-args       
    ------------------------------------------------------------

=> `nil`

