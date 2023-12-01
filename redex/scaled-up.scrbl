#lang scribble/manual
@(require redex/pict
          redex/reduction-semantics
          scriblib/figure
          "nt-array.rkt"
          "typesetting.rkt")

@title{Formalization}

First we show the operational semantics, followed by the static semantics.

@section{Dynamic semantics}

Null-terminated arrays @tt{(ntarray @math{l} @math{h} @math{τ})} are
like arrays @tt{(array @math{l} @math{h} @math{τ})}. You can read and
write at any index from @math{l} up to @math{h}. The key
difference is that there is guaranteed to be a null
terminator @emph{at index @math{h} or later}.

This means two things:
@itemlist[

 @item{there is a value at index
  @math{h}. So while arrays are guaranteed
  to have @math{h - l} contiguous locations in memory,
  null-terminated arrays are guarantedd to have @math{h-l+1}.}

 @item{If you read the value at index
  @math{h} and it is @emph{not} null, there
  must be another valid memory location at location @math{
   h+1}, and hence the type could safely be changed to
  @tt{(ntarray @math{l} @math{h+1} @math{τ})}.}

 ]


To add null-terminated arrays to the language, we first add the syntax:

@figure["nt-syntax"
	"Additional syntax for null-terminated arrays"
	(render-language CoreChkC-NT)]

For the operational semantics, you could start by replaying the definitions of
all the array-like reductions.  (One minor difference is that it is safe
to dereference a pointer of type @tt{(ptr c (ntarray l 0 τ))}.)

This will make null-terminated arrays similar to arrays, but
it won't capture the type refinement that occurs when
null-terminated array occurs at its potential final position
(i.e. @math{l}).

In order to check this property, the programmer must've bound a pointer to
the end of the array to a variable in order to test for non-nullness and then
do something with the refined knowledge about what the variable points to.

So we'd like to support dynamically reasoning about programs like:

@verbatim|{
if *x {       // x : ptr (ntarray l 0 τ)
  ...x...     // x : ptr (ntarray l 1 τ)
}
}|

The substitution based model is at odds with this kind of reasoning though
since by the time this expression is evaluated, both occurrences of @tt{x}
will have been substituted with a value (some integer) and there's no way
to communicate the knowledge about x from one occurrence to the next.

So the first step is to eliminate the use of substitution.

Putting aside null-terminated arrays for a moment, here's how the model can
be revised to eliminate the use of substitution: Keep
@tt{let}-expressions around.  When a variable is encountered, retrieve
it's value from the surrounding context.  Once a @tt{let}'s body is
fully reduced, it can be eliminated.

To accomplish this, we add an evaluation context allow the reduction of
expressions under @tt{let}:

@figure["nosubst-syntax"
	"Evaluation contexts to avoid substitution"
	(render-language CoreChkC-Let)]

To implement variable references, we drop @tt{E-Let} and add
a reduction rule for eliminating a @tt{let} when fully
evaluated and a rule for referencing a variable within the
context of the @tt{let} that binds it:

@figure["nosubst-computation"
        "Let without using substitution"
        (parameterize ([judgment-form-cases '(E-Var E-Let)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢let ⊢-rewrite])                      
            (render-judgment-form ⊢let)))]

While we're at it, we can generalize @tt{let} to a @math{
 n}-ary binding form and also support mutating lvars:

@figure["let+-syntax"
	"Syntax for n-ary let and lvar assignment"
	(render-language CoreChkC-Let+)]

Semantics:

@figure["let+-computation"
        "Semantics for n-ary let and lvar assignment"
        (parameterize ([judgment-form-cases '(E-Let E-Var E-Set)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢let+ ⊢-rewrite])                      
            (render-judgment-form ⊢let+)))]


Now back to the issue of null-terminated arrays. The basic
idea is to make a special case for dereferencing a variable
@tt{(* x)}. If @tt{x} refers to a null-terminated array that
is at its boundary, i.e. @tt{(ntarray 0 @math{τ})}, and the
value at that index is non-null, then we can update the type
of @tt{x} to expand the bound. Other occurrences of @tt{x}
will now see the refined type:


@figure["nt-computation"
        "Null-terminated array dereference"
        (parameterize ([judgment-form-cases '(E-VarNT)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢nt ⊢-rewrite])                      
            (render-judgment-form ⊢nt)))]

The @tt{nt-incr} relation is just the following:

@figure["nt-incr"
        "Incrementing null-terminated array types"
        (parameterize ([judgment-form-cases '(NT-Incr)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢nt ⊢-rewrite])                      
            (render-judgment-form ⊢nt)))]

Suppose we have @math{H′ = }@render-term[CoreChkC-NT ((8 : int) (0 : int))], then here is an
example of reduction with null-terminated arrays:

@(with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢nt ⊢-rewrite])
   (begin
     (define-term H′ ((8 : int) (0 : int)))
     (render-term CoreChkC-NT
                  (⊢nt ↝ (H′ (let ((x = (1 : (ptr c (ntarray 0 int))))) in (* x))) (H′ (let ((x = (1 : (ptr c (ntarray 1 int))))) in (8 : int)))))))

Of course, this refined knowledge is not terribly useful
without a way of conditionally doing something based upon
it. If we add a standard notion of conditional expressions,
it becomes possible to write code that checks whether the
null-terminator has been reached and proceed in case it
hasn't.

@figure["if-syntax"
	"Adding conditionals"
	(render-language CoreChkC-If)]

@figure["if-computation"
        "Reductions for conditionals"
        (parameterize ([judgment-form-cases '(If-T If-F)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['= (<-rewrite "=")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢if ⊢-rewrite])                      
            (render-judgment-form ⊢if)))]

Voilà!  We can now safely run programs that operate over null-terminated
arrays of arbitrary length.

We can also add function and function pointers. Here is the
idea: we assume a global function definition environment,
much like structure definitions. Each function has a single
parameter and an expression (it's easy enough to have
multiple parameters too). There is a new kind of @tt{ω} type
which are function pointers. Functions are denoted by their
offset in the global table (so there are two address spaces:
the heap and function pointers). We add syntax for calling
functions:

@figure["fun-syntax"
	"Adding functions"
	(render-language CoreChkC-Fun)]

The semantics of function calls is to replace the call with
an expression that let bind the parameter to the argument in
the scope of the body of the function:


@figure["fun-computation"
        "Reductions for conditionals"
        (parameterize ([judgment-form-cases '(E-Fun)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['= (<-rewrite "=")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*F* *F*rewrite]
               ['add1 add1-rewrite]
               ['⊢fun ⊢-rewrite])                      
            (render-judgment-form ⊢fun)))]

You can now write a recursive @tt{strlen}-like function that takes a null-terminated
array and returns it's length.

Suppose we have the following function table @math{F′}:

@render-term[CoreChkC-Fun ((x
                            (if (* x)                                  
                                ((1 : int) + (call (0 : (ptr c (fun (ptr c (ntarray 0 int)) -> int)))
                                                   (x + (1 : int))))
                                (0 : int))))]

Then:
@render-term[CoreChkC-Fun (call (0 : (ptr c (fun (ptr c (ntarray 0 int)) -> int))) (1 : (ptr c (ntarray 0 int))))]
will count the number of non-null values that are in the heap, starting from the
beginning.

While this lets us write and use @tt{strlen}-like functions,
it won't help clients of @tt{strlen} because there's no way
to signal that the length returned by @tt{strlen} can be used as the bound
in the arguments type.  However, I think all of that is in reach: we need to
add support for offsets in null-checks, i.e. special case @tt{(* (x + n))}
and write @tt{strlen} so that it returns a pointer to the beginning of the
null-terminated array it was given, but at the appropriately updated type.

@section{Static semantics}

TBD.



