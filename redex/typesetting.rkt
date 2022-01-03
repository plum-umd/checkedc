#lang racket
(provide (all-defined-out))
(require redex/pict redex/reduction-semantics)
(define-language L
  (D H F ::= dummy-non-terminal))

;; Typesetting helpers

(define ↝-cases
  '(E-Binop E-Cast E-Deref E-Assign E-Amper E-Malloc
            E-Let E-Unchecked X-DerefOOB X-AssignOOB
            X-DerefNull X-AssignNull X-AmperNull X-BinopNull))

(define typing-rules
  '(T-Var T-VConst T-Let T-Base T-PtrC T-Amper T-BinopInt T-Malloc
          T-Unchecked T-Cast T-Deref T-Index T-Assign T-IndAssign))

(define ⟶-cases
  '(C-Exp C-Halt))

(define (⊢-rewrite lws)
  (match lws
    [(list _ _
           (app lw-e '↝)
           (app lw-e (list _ h1 e1 _))
           (app lw-e (list _ h2 e2 _)) _)
     (list "" h1 "; " e1 " ↝ " h2 "; " e2 "")]

    [(list _ _
           (app lw-e '⟶)
           (app lw-e (list _ h1 e1 c _))
           (app lw-e (list _ h2 e2 _)) _)
     (list "" h1 "; " e1 " ⟶ " c h2 "; " e2 "")]

    [(list _ _
           (app lw-e 'ty)
           (app lw-e (list _ g s m e _))
           t
           _)
     (list "" g ", " s " ⊢" m " " e " : " t "")]

    [(list _ _
           (app lw-e '>>)
           (app lw-e (list _ g s m e _))
           (app lw-e (list _ e^ t _))
           _)
     (list "" g ", " s " ⊢" m " " e " >> " e^ " : " t "")]
       
    #;
    [(list _ _
           (app lw-e 'subst)
           (app lw-e (list _ e x v _))
           (app lw-e e′ #;(app lw-e (list _ e′ _)))
           _)
     (writeln e′)
     #;(writeln rhs)
     (list "" "[" v "/" x "]" e " = " e′ "")]
       
    [(list _ _ n lhs (app lw-e "#t") _)
     (list "" n lhs "")]
    [(list _ _ n lhs rhs _)
     (list "" n " " lhs " = " rhs "")]))
   
(define (length-rewrite lws)
  (match lws
    [(list _ _ (app lw-e (list-rest _ _ (app lw-e (list _ fs d _)) _)) _)
     (list "|" fs d "|")]
    [(list _ _ e _)
     (list "|" e "|")]))

(define (*D*rewrite lws)
  (list (render-term L D)))
(define (*H*rewrite lws)
  (list (render-term L H)))

(define (*F*rewrite lws)
  (list (render-term L F)))


(define ((<-rewrite s) lws)
  (match lws
    [(list _ _ a b _ ...)
     (list "" a (string-append " " s " ") b "")]))
   
(define (+-rewrite lws)
  (match lws
    [(list _ _ a b _ ...)
     (list "" a " + " b "")]))

(define (--rewrite lws)
  (match lws
    [(list _ _ a b _ ...)
     (list "" a " - " b "")]))

(define (add1-rewrite lws)
  (match lws
    [(list _ _ a _ ...)
     (list "" a "+1")]))

(define (max-rewrite lws)
  (match lws
    [(list _ _ a b _ ...)
     (list (render-term L max) "(" a ", " b ")")]))
   
(define (↝rewrite lws)
  (match lws
    [(list _ _ h1 e1 h2 r _ ...)
     (list ""
           h1 "; " e1 " ↝ " h2 "; " r "")]))

(define (⟶rewrite lws)
  (match lws
    [(list _ _ h1 e1 m h2 e2 _ ...)
     (list ""
           h1 "; " e1 " "
           "⟶" m " "
           h2 "; " e2 "")]))
