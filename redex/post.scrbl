#lang scribble/manual
@(require redex/pict
          scriblib/figure
          "post.rkt"
          "typesetting.rkt")

@title{POST formalism}

@(require scribble-abbrevs/latex)
@appendix

This appendix provides the formal semantics as presented in
the POST paper.

The only significant difference is array bounds have been
augmented to include both a lower and upper bound rather
than just an upper as done in POST'19.

@figure["syntax"
	"Syntax of Core Checked C"
	(render-language CoreChkC)]

The reduction relation is equivalent to what is in the POST
paper and aims to be as close as possible in style, but it
uses metafunctions in some places to express some of the
disjunctive premises in the paper.

@figure["other-style"
        "Semantics, computation rules"
        (parameterize ([judgment-form-cases ↝-cases])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢ ⊢-rewrite])
            
          
            (render-judgment-form ⊢)))]

The context-based reduction relation:

@figure["context"
        "Reduction in context"
        (parameterize ([judgment-form-cases ⟶-cases])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢ ⊢-rewrite])                      
            (render-judgment-form ⊢)))]


@figure["typing"
        "Typing judgment"
        (parameterize ([judgment-form-cases typing-rules])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['*H* *H*rewrite]               
               ['add1 add1-rewrite]
               ['⊢ ⊢-rewrite])                      
            (render-judgment-form ⊢)))]