#lang scribble/manual
@(require redex/pict
          scriblib/figure
          "compiled-check.rkt"
          "typesetting.rkt")

@title{Compiling Checks}

Yiyun's idea:

@figure["cc-syntax"
	"Syntax of Compiled Checked C"
	(render-language CoreChkC^)]

@figure["cc-computation"
        "Semantics, computation rules"
        (parameterize ([judgment-form-cases '(E-Bounds X-Bounds)])
          (with-compound-rewriters
              (['+ +-rewrite]
               ['< (<-rewrite "<")]
               ['>= (<-rewrite "≥")]
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢^ ⊢-rewrite])                      
            (render-judgment-form ⊢^)))]

@figure["cc-typing"
        "Type-based transformation"
        (parameterize ([judgment-form-cases '(T-Index^)])
          (with-compound-rewriters
              (['+ +-rewrite]               
               ['length length-rewrite]
               ['*D* *D*rewrite]
               ['add1 add1-rewrite]
               ['⊢^ ⊢-rewrite])                      
            (render-judgment-form ⊢^)))]