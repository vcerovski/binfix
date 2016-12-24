" BINFIX Vim syntax file
" by V. Cerovski Dec 2016
" based and dependent on the standard LISP syntax file of vim, lisp.vim

syn keyword lispKey array atom bignum bit bit-vector boolean character compiled-function complex
syn keyword lispKey cons double-float fixnum float function hash-table integer keyword list long-float
syn keyword lispKey nil null number package pathname random-state ratio rational readtable sequence
syn keyword lispKey short-float signed-byte simple-array simple-bit-vector simple-string simple-vector
syn keyword lispKey single-float standard-char stream symbol t unsigned-byte vector
syn keyword lispKey common string string-char

syn keyword lispKey :array :atom :bignum :bit :bit-vector :boolean :character :compiled-function :complex
syn keyword lispKey :cons :double-float :fixnum :float :function :hash-table :integer :keyword :list :long-float
syn keyword lispKey :nil :null :number :package :pathname :random-state :ratio :rational :readtable :sequence
syn keyword lispKey :short-float :signed-byte :simple-array :simple-bit-vector :simple-string :simple-vector
syn keyword lispKey :single-float :standard-char :stream :symbol :t :unsigned-byte :vector
syn keyword lispKey :common :string :string-char

so $VIMRUNTIME/syntax/lisp.vim

" Added   .  |  !  ?   compared to lisp.vim
if version >= 600
 setlocal iskeyword=38,42,43,45,47-58,60-62,64-90,97-122,_,.,\|,$,\?
else
 set iskeyword=38,42,43,45,47-58,60-62,64-90,97-122,_,.,\|,$,\?
endif

syn match lispParenError	")}"

syn match	lispSymbol	contained	![^()'`,"; \t{}]\+!
syn match	lispSymbol	contained	!;[^;]\v|\$!

syn region lispList	matchgroup=Delimiter start="{"   skip="|.\{-}|"	matchgroup=Delimiter end="}"  contains=@lispListCluster
syn region lispBQList	matchgroup=PreProc   start="`{"  skip="|.\{-}|"	matchgroup=PreProc   end="}"  contains=@lispListCluster

syn match lispAtom		"'{"me=e-1		contains=lispAtomMark	nextgroup=lispAtomList
syn match lispAtom		"'[^ \t(){}]\+"		contains=lispAtomMark
syn match lispAtomBarSymbol	!'|..\{-}|!		contains=lispAtomMark

syn region lispAtomList		contained	matchgroup=Special start="{"	skip="|.\{-}|" matchgroup=Special end="}"	contains=@lispAtomCluster,lispString,lispEscapeSpecial

syn keyword lispFunc	def
syn keyword lispKey  		struct	var	parameter	constant	symbol-macro
syn keyword lispKey  	declare
syn keyword lispFunc	:=	:==	:-	:->	:type=
syn keyword lispFunc	<<	**	in	:.	==	===	=s=	=c=
syn keyword lispFunc	-=	+=	.=	.=.	=.	=..	..=
syn keyword lispFunc	.x. 	\|\|	&&	&	<&	<&..	;	?	$	;
syn keyword lispFunc	->	@@	@.	@n	@	@..	@.n	.@	..@	@/	.@.
syn keyword lispFunc	!	.!	!.	.!.	.!!.	!!	!!.	!..
syn keyword lispFunc	th	th-cdr	th-bit	th-value	subtype-of
syn keyword lispFunc	 eqv.	 or.	 xor.	 and.	 nand.	 nor.	test.	 orc1.	 orc2.	 andc1.	 andc2.
syn keyword lispFunc	.eqv.	.or.	.xor.	.and.	.nand.	.nor.	.not.	.orc1.	.orc2.	.andc1.	.andc2.

syn match lispEscapeSpecial		!#|[^(){}'`,"; \t]\+|#!
syn match binfixEscapeSpecial		!#[':][^()'`,"; \t{}]\+!

syn match lispParenError	")}"

syn sync lines=1000

