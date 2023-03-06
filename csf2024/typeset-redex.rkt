#lang racket

(require redex/pict)
(require "../redex/nt-array.rkt")
(render-language CoreChkC+ "syntax.pdf")
(render-judgment-form ⊢ty "types.pdf")

