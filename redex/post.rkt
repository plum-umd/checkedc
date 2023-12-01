#lang racket
(provide (all-defined-out))
(require redex/reduction-semantics)

;; Redex model of Achieving Safety Incrementally with Checked C,
;; by Ruef, Lampropoulos, Sweet, Tarditi, & Hicks, POST'19.
;; http://www.cs.umd.edu/~mwh/papers/checkedc-incr.pdf


(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *D* (make-parameter (term ()))) ; struct table
(define *H* (make-parameter (term ()))) ; global heap (for type system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax

(define-language CoreChkC
  (m ::= c u)
  (τ ::= int (ptr m ω))
  (ω ::= τ (struct T) (array l h τ))
  (e ::= (n : τ) x (let x = e in e) (malloc ω) (cast τ e)
     (e + e) (& e → f) (* e) (* e = e) (unchecked e))
  (n k ::= natural)
  (l h ::= integer)
  (D ((T fs) ...))
  (fs ((τ f) (τ f) ...))
  (x f T ::= variable-not-otherwise-mentioned)
  (H ::= ((n : τ) ...))
  (r ::= e ε)
  (ε ::= Null Bounds)
  (E ::= hole (let x = E in e) (E + e) ((n : τ) + E)
     (& E → f) (cast τ E) (* E) (* E = e) (* (n : τ) = E) (unchecked E))

  ;; static
  (Γ ::= ((x : τ) ...))
  (σ ::= ((n : τ) ...)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operational Semantics

(define ~~>
  (reduction-relation
   CoreChkC #:domain (H r)
   (--> (H e) (H_′ r_′) (judgment-holds (⊢↝ (H e) (H_′ r_′))))))

(define (---> m)
  (reduction-relation
   CoreChkC
   #:domain (H r)
   (--> (H e) (H_′ r)
        (judgment-holds (⊢⟶ (H e ,m) (H_′ r))))))

(define-judgment-form CoreChkC
  #:contract (⊢↝ (H e) (H r))
  #:mode     (⊢↝ I O)
  [(⊢↝ (H ((n_1 : τ_1) + (n_2 : τ_2))) (H (n_3 : τ_3)))
   (where n_3 ,(+ (term n_1) (term n_2)))
   (where τ_3 (⊢binop-type τ_1 n_1 n_2))
   E-Binop]

  [(⊢↝ (H (cast τ (n : τ_′))) (H (n : τ)))
   E-Cast]

  [(⊢↝ (H (* (n : τ))) (H (n_1 : τ_1)))
   (where #t (⊢deref-ok? τ))
   (where #t (⊢heap-defined? H n))
   (where (n_1 : τ_1) (⊢heap-lookup H n))
   E-Deref]

  [(⊢↝ (H (* (n : τ) = (n_1 : τ_1))) (H_′ (n_1 : τ_1)))
   (where #t (⊢heap-defined? H n))
   (where #t (⊢deref-ok? τ))
   (where H_′ (⊢heap-update H n (n_1 : τ_1)))
   E-Assign]

  [(⊢↝ (H (& (n : τ) → f_i)) (H (n_0 : τ_0)))
   (where (n_0 : τ_0) (⊢& τ f_i n))
   E-Amper]

  [(⊢↝ (H (malloc ω)) (H_′ (n_1 : (ptr c ω))))
   (where (τ_1 τ_2 ...) (⊢types ,(*D*) ω))
   (where ((n : τ) ...) H)
   (where H_′ ((n : τ) ... (0 : τ_1) (0 : τ_2) ...))
   (where n_1 ,(add1 (length (term H))))
   E-Malloc]

  [(⊢↝ (H (let x = (n : τ) in e)) (H e_′))
   (where e_′ (⊢subst e x (n : τ)))
   E-Let]

  [(⊢↝ (H (unchecked (n : τ))) (H (n : τ)))
   E-Unchecked]

  [(⊢↝ (H (* (n : τ))) (H Bounds))
   (where (ptr c (array l h τ_1)) τ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-DerefOOB]

  [(⊢↝ (H (* (n : τ) = (n_1 : τ_1))) (H Bounds))
   (where (ptr c (array l h τ_1)) τ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-AssignOOB]

  [(⊢↝ (H (* (0 : τ))) (H Null))
   (where (ptr c ω) τ)
   X-DerefNull]

  [(⊢↝ (H (* (0 : τ) = (n_1 : τ_′))) (H Null))
   (where (ptr c ω) τ)
   X-AssignNull]

  [(⊢↝ (H (& (0 : τ) → f)) (H Null))
   (where (ptr c (struct T)) τ)
   X-AmperNull]

  [(⊢↝ (H ((0 : τ) + (n : τ_′))) (H Null))
   (where (ptr c (array l h τ_1)) τ)
   X-BinopNull])


(define-judgment-form CoreChkC
  #:contract (⊢⟶ (H e m) (H r))
  #:mode     (⊢⟶ I O)
  [(where (in-hole E e_0) e)
   (⊢↝ (H e_0) (H_′ e_0′))
   (where e_′ (in-hole E e_0′))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------ C-Exp
   (⊢⟶ (H e m) (H_′ e_′))]

  [(where (in-hole E e_0) e)
   (⊢↝ (H e_0) (H_′ ε))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------- C-Halt
   (⊢⟶ (H e m) (H_′ ε))])

(define-metafunction CoreChkC
  ⊢binop-type : τ n n -> τ or #f
  [(⊢binop-type (ptr c (array l h τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (name τ int) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m (struct T))) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr u (array l h _))) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m int)) n_1 n_2) τ]
  [(⊢binop-type _ _ _) #f])

(define-metafunction CoreChkC
  ⊢heap-defined? : H n -> #t or #f
  [(⊢heap-defined? H n)
   ,(< 0 (term n) (add1 (length (term H))))])

(define-metafunction CoreChkC
  ⊢heap-lookup : H n -> (n : τ)
  [(⊢heap-lookup H n)
   ,(list-ref (term H) (sub1 (term n)))])

(define-metafunction CoreChkC
  ⊢heap-update : H n (n : τ) -> H
  [(⊢heap-update H n (n_1 : τ_1))
   ,(list-set (term H) (sub1 (term n)) (term (n_1 : τ_1)))])

(define-metafunction CoreChkC
  ⊢heap-from : H n -> H
  [(⊢heap-from H n) ,(drop (term H) (sub1 (term n)))])

(define-metafunction CoreChkC
  ⊢struct-lookup : D T -> fs
  [(⊢struct-lookup ((T fs) _ ...) T) fs]
  [(⊢struct-lookup (_ (T_′ fs) ...) T)
   (⊢struct-lookup ((T_′ fs) ...) T)])

(define-metafunction CoreChkC
  ⊢deref-ok? : τ -> #t or #f
  [(⊢deref-ok? int) #t]
  [(⊢deref-ok? (ptr u ω)) #t]
  [(⊢deref-ok? (ptr c int)) #t]
  [(⊢deref-ok? (ptr c (struct T))) #t]
  [(⊢deref-ok? (ptr c (array l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢deref-ok? _) #f])

(define-metafunction CoreChkC
  ⊢types : D ω -> (τ ...)
  [(⊢types D τ) (τ)]
  [(⊢types D (array l h τ))
   ,(make-list (- (term h) (term l)) (term τ))]
  [(⊢types D (struct T))
   (τ ...)
   (where ((τ f) ...) (⊢struct-lookup D T))])

;; fixes a minor bug in paper: should be τ_0 f_0; ...; τ_k f_k, 0 <= i <= k,
;; i.e. 0-based counting, not 1-based
(define-metafunction CoreChkC
  ⊢& : τ f n -> (n : τ) or #f
  [(⊢& (ptr m (struct T)) f_i n)
   (n_i : τ_i′)
   (where ((τ_0 f_0) ... (τ_i f_i) _ ...) (⊢struct-lookup ,(*D*) T))
   (where n_i ,(+ (term n) (length (term ((τ_0 f_0) ...)))))
   (where τ_i′ (ptr m τ_i))
   (side-condition (or (eq? (term m) 'u) (not (= 0 (term n)))))]
  [(⊢& _ _ _) #f])

(define-metafunction CoreChkC
  ⊢check-mode : m m -> #t or #f
  [(⊢check-mode u _) #t]
  [(⊢check-mode m m) #t]
  [(⊢check-mode _ _) #f])

(define-metafunction CoreChkC
  ⊢mode : E -> m
  [(⊢mode hole) c]
  [(⊢mode (unchecked E)) u]
  [(⊢mode (let x = E in e)) (⊢mode E)]
  [(⊢mode (E + e))          (⊢mode E)]
  [(⊢mode ((n : τ) + E))    (⊢mode E)]
  [(⊢mode (& E → f))        (⊢mode E)]
  [(⊢mode (cast τ E))       (⊢mode E)]
  [(⊢mode (* E))            (⊢mode E)]
  [(⊢mode (* E = e))        (⊢mode E)]
  [(⊢mode (* (n : τ) = E))  (⊢mode E)])

(define-metafunction CoreChkC
  ⊢subst : e x (n : τ) -> e
  [(⊢subst x x (n : τ)) (n : τ)]
  [(⊢subst (let x = e_1 in e_2) x (n : τ))
   (let x = (⊢subst e_1 x (n : τ)) in e_2)]
  [(⊢subst (let x_′ = e_1 in e_2) x (n : τ))
   (let x_′ = (⊢subst e_1 x (n : τ)) in (⊢subst e_2 x (n : τ)))]
  [(⊢subst (cast τ_′ e) x (n : τ))
   (cast τ_′ (⊢subst e x (n : τ)))]
  [(⊢subst (e_1 + e_2) x (n : τ))
   ((⊢subst e_1 x (n : τ)) + (⊢subst e_2 x (n : τ)))]
  [(⊢subst (& e → f) x (n : τ))
   (& (⊢subst e x (n : τ)) → f)]
  [(⊢subst (* e) x (n : τ))
   (* (⊢subst e x (n : τ)))]
  [(⊢subst (* e_1 = e_2) x (n : τ))
   (* (⊢subst e_1 x (n : τ)) = (⊢subst e_2 x (n : τ)))]
  [(⊢subst (unchecked e) x (n : τ))
   (unchecked (⊢subst e x (n : τ)))]
  [(⊢subst e _ _) e])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Typing

(define-judgment-form CoreChkC
  #:contract (⊢ty Γ σ m e τ)
  #:mode     (⊢ty I I I I O)
  [(where τ (⊢ty-env-lookup Γ x))
   ------------- T-Var
   (⊢ty Γ σ m x τ)]

  [(where (_ ... (n : τ) _ ...) σ)
   ------------- T-VConst
   (⊢ty Γ σ m (n : τ) τ)]

  [(⊢ty Γ σ m e_1 τ_1)
   (where ((x_′ : τ_′) ...) Γ)
   (⊢ty ((x : τ_1) (x_′ : τ_′) ...) σ m e_2 τ)
   ------------- T-Let
   (⊢ty Γ σ m (let x = e_1 in e_2) τ)]

  [(where #t (⊢base? n τ))
   ------------- T-Base
   (⊢ty Γ σ m (n : τ) τ)]

  [(where (ptr c ω) τ)
   (where (τ_0 ..._1) (⊢types ,(*D*) ω))
   (where #t (⊢heap-defined? ,(*H*) n))
   (where  ((n_1 : τ_1) ..._1 _ ...) (⊢heap-from ,(*H*) n))
   (where ((n_′ : τ_′) ...) σ)
   (⊢ty Γ ((n : τ) (n_′ : τ_′) ...) m (n_1 : τ_1) τ_0) ...
   ------------- T-PtrC
   (⊢ty Γ σ m (n : τ) τ)]

  [(⊢ty Γ σ m e (ptr m (struct T)))
   (where (_ ... (τ_f f) _ ...) (⊢struct-lookup ,(*D*) T))
   ------------- T-Amper
   (⊢ty Γ σ m (& e → f) (ptr m τ_f))]

  [(⊢ty Γ σ m e_1 int)
   (⊢ty Γ σ m e_2 int)
   ------------- T-BinopInt
   (⊢ty Γ σ m (e_1 + e_2) int)]

  [(where (τ_1 τ_2 ...) (⊢types ,(*D*) ω))
   ------------- T-Malloc
   (⊢ty Γ σ m (malloc ω) (ptr c ω))]

  [(⊢ty Γ σ u e τ)
   ------------- T-Unchecked
   (⊢ty Γ σ m (unchecked e) τ)]

  [(⊢ty Γ σ m e τ_′)
   (where #t (⊢cast-ok? m τ))
   ------------- T-Cast
   (⊢ty Γ σ m (cast τ e) τ)]

  [(⊢ty Γ σ m e (ptr m_′ ω))
   (where τ (⊢deref-type ω))
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-Deref
   (⊢ty Γ σ m (* e) τ)]

  [(⊢ty Γ σ m e_1 (ptr m_′ (array l h τ)))
   (⊢ty Γ σ m e_2 int)
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-Index
   (⊢ty Γ σ m (* (e_1 + e_2)) τ)]

  [(⊢ty Γ σ m e_1 (ptr m_′ ω))
   (⊢ty Γ σ m e_2 τ)
   (where τ (⊢deref-type ω))
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-Assign
   (⊢ty Γ σ m (* e_1 = e_2) τ)]

  [(⊢ty Γ σ m e_1 (ptr m_′ (array l h τ)))
   (⊢ty Γ σ m e_2 int)
   (⊢ty Γ σ m e_3 τ)
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-IndAssign
   (⊢ty Γ σ m (* (e_1 + e_2) = e_3) τ)])

(define-metafunction CoreChkC
  ⊢ty-env-lookup : Γ x -> τ
  [(⊢ty-env-lookup ((x : τ) _ ...) x) τ]
  [(⊢ty-env-lookup (_ (x_′ : τ_′) ...) x)
   (⊢ty-env-lookup ((x_′ : τ_′) ...) x)])

(define-metafunction CoreChkC
  ⊢base? : n τ -> #t or #f
  [(⊢base? n int) #t]
  [(⊢base? n (ptr u ω)) #t]
  [(⊢base? 0 τ) #t]
  [(⊢base? n (ptr c (array 0 0 τ_′))) #t]
  [(⊢base? _ _) #f])

(define-metafunction CoreChkC
  ⊢cast-ok? : m τ -> #t or #f
  [(⊢cast-ok? u τ) #t]
  [(⊢cast-ok? c int) #t]
  [(⊢cast-ok? c (ptr u ω)) #t]
  [(⊢cast-ok? _ _) #f])

(define-metafunction CoreChkC
  ⊢deref-type : ω -> τ
  [(⊢deref-type τ) τ]
  [(⊢deref-type (array l h τ)) τ])

(define-metafunction CoreChkC
  ⊢mode-ok? : m m -> #t or #f
  [(⊢mode-ok? u u) #t]
  [(⊢mode-ok? c _) #t]
  [(⊢mode-ok? _ _) #f])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(module+ test
  (parameterize ((*D* (term ((foo ((int x) (int y)))))) ; a struct defn
                 (*H* (term ((5 : int))))) ; a heap for the type system tests

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; ↝

    ;; E-BinOp
    (test--> ~~>
             (term (() ((3 : int) + (4 : int))))
             (term (() (7 : int))))
    (test--> ~~>
             (term (() ((3 : (ptr c (array 0 5 int))) + (4 : int))))
             (term (() (7 : (ptr c (array -4 1 int))))))
    (test--> ~~> ; going off the end in checked mode
             (term (() ((3 : (ptr c (array 0 5 int))) + (7 : int))))
             (term (() (10 : (ptr c (array -7 -2 int))))))
    (test--> ~~> ; ptr arith on null in unchecked mode
             (term (() ((0 : (ptr u (array 0 5 int))) + (4 : int))))
             (term (() (4 : (ptr u (array 0 5 int))))))

    ;; E-Cast
    (test--> ~~>
             (term (() (cast (ptr c (array 0 5 int)) (0 : int))))
             (term (() (0 : (ptr c (array 0 5 int))))))

    ;; E-Deref
    (test--> ~~>
             (term (((7 : int)) (* (1 : int))))
             (term (((7 : int)) (7 : int))))
    (test--> ~~> ; dereferencing a valid checked ptr to an array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 1 int))))))
             (term (((7 : int)) (7 : int))))
    (test--> ~~> ; dereferencing an unchecked ptr to a nullary array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 0 int))))))
             (term (((7 : int)) (7 : int))))
    (test--> ~~>
             (term (((5 : int)) (* (1 : (ptr u (array 1 0 int))))))
             (term (((5 : int)) (5 : int))))
    (test--> ~~>
             (term (((7 : int)) (* (1 : (ptr u (array 0 -2 int))))))
             (term (((7 : int)) (7 : int))))

    ;; E-Assign
    (test--> ~~>
             (term (((7 : int)) (* (1 : int) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~> ; assigning a valid checked ptr to an array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 1 int))) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~> ; assigning an unchecked ptr to a nullary array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 0 int))) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~>
             (term (((7 : int)) (* (1 : (ptr u (array 7 0 int))) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~>
             (term (((7 : int)) (* (1 : (ptr u (array -1 -7 int))) = (2 : int))))
             (term (((2 : int)) (2 : int))))

    ;; E-Amper
    (test--> ~~>
             (term (() (& (4 : (ptr u (struct foo))) → x)))
             (term (() (4 : (ptr u int)))))
    (test--> ~~>
             (term (() (& (4 : (ptr c (struct foo))) → x)))
             (term (() (4 : (ptr c int)))))
    (test--> ~~>
             (term (() (& (4 : (ptr c (struct foo))) → y)))
             (term (() (5 : (ptr c int)))))

    ;; E-Malloc
    (test--> ~~>
             (term (() (malloc int)))
             (term (((0 : int)) (1 : (ptr c int)))))
    (test--> ~~>
             (term (() (malloc (array 0 3 int))))
             (term (((0 : int) (0 : int) (0 : int))
                    (1 : (ptr c (array 0 3 int))))))

    (test--> ~~>
             (term (() (malloc (struct foo))))
             (term (((0 : int) (0 : int)) (1 : (ptr c (struct foo))))))

    (test--> ~~> ; alloc'ing a nullary array gets stuck
             (term (() (malloc (array 0 0 int)))))

    ;; E-Let
    (test--> ~~>
             (term (() (let x = (5 : int) in x)))
             (term (() (5 : int))))

    ;; E-Unchecked
    (test--> ~~>
             (term (() (unchecked (7 : int))))
             (term (() (7 : int))))

    ;; X-DerefOOB
    (test--> ~~> ; dereferencing a checked ptr to a nullary array
             (term (((7 : int)) (* (1 : (ptr c (array -1 0 int))))))
             (term (((7 : int)) Bounds)))
    (test--> ~~>
             (term (((7 : int)) (* (1 : (ptr c (array 2 2 int))))))
             (term (((7 : int)) Bounds)))
    (test--> ~~>
             (term (((7 : int)) (* (1 : (ptr c (array -2 -2 int))))))
             (term (((7 : int)) Bounds)))

    ;; X-AssignOOB
    (test--> ~~>
             (term (() (* (1 : (ptr c (array 0 0 int))) = (7 : int))))
             (term (() Bounds)))
    (test--> ~~>
             (term (() (* (1 : (ptr c (array 9 0 int))) = (7 : int))))
             (term (() Bounds)))
    (test--> ~~>
             (term (() (* (1 : (ptr c (array -1 -10 int))) = (7 : int))))
             (term (() Bounds)))

    ;; X-DerefNull
    (test--> ~~> ; dereferencing a checked ptr to a nullary array
             (term (((7 : int)) (* (0 : (ptr c (array 0 1 int))))))
             (term (((7 : int)) Null)))

    ;; X-AssignNull
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 0 1 int))) = (7 : int))))
             (term (() Null)))

    ;; X-AmperNull
    (test--> ~~>
             (term (() (& (0 : (ptr c (struct foo))) → f)))
             (term (() Null)))

    ;; X-BinopNull
    (test--> ~~> ; ptr arith on null in checked mode
             (term (() ((0 : (ptr c (array 0 5 int))) + (4 : int))))
             (term (() Null)))

    ;; X-AssignOOB and X-AssignNull overlap
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 0 0 int))) = (7 : int))))
             (term (() Bounds))
             (term (() Null)))

    ;; X-DerefOOB and X-DerefNull overlap
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 0 0 int))))))
             (term (() Bounds))
             (term (() Null)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; ⟶
    (test-->>
     (---> 'c)
     (term (()
            (let p = (malloc (array 0 3 int)) in
              (let _ = (* (1 : (ptr c int)) = (6 : int)) in
                (let _ = (* (2 : (ptr c int)) = (7 : int)) in
                  (let _ = (* (3 : (ptr c int)) = (8 : int)) in
                    p))))))
     (term (((6 : int) (7 : int) (8 : int))
            (1 : (ptr c (array 0 3 int))))))

    (test-->>
     (---> 'c)
     (term (()
            (let p = (malloc (array 0 3 int)) in
              (let _ = (* p = (6 : int)) in
                (let p = (p + (1 : int)) in
                  (let _ = (* p = (7 : int)) in
                    (let p = (p + (1 : int)) in
                      (let _ = (* p = (8 : int)) in
                        (let p = (p + (1 : int)) in
                          p)))))))))
     (term (((6 : int) (7 : int) (8 : int))
            (4 : (ptr c (array -3 0 int))))))

    (test-->>
     (---> 'c)
     (term (()
            (let p = (malloc (struct foo)) in
              (let _ = (* (& p → x) = (7 : int)) in
                (let _ = (* (& p → y) = (8 : int)) in
                  p)))))
     (term (((7 : int) (8 : int))
            (1 : (ptr c (struct foo))))))

    (test-->>
     (---> 'c)
     (term (() ; Bounds
            (let p = (malloc (array 0 3 int)) in
              (* (p + (4 : int)) = (7 : int)))))
     (term (((0 : int) (0 : int) (0 : int))
            Bounds)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Subst
    (test-equal (term (⊢subst x x (0 : int))) (term (0 : int)))
    (test-equal (term (⊢subst y x (0 : int))) (term y))
    (test-equal (term (⊢subst (let x = x in x) x (0 : int)))
                (term (let x = (0 : int) in x)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Structures
    (define-term DT
      ((foo ((int x) (int y)))
       (bar ((int q)))))

    (test-equal (term (⊢struct-lookup DT foo)) (term ((int x) (int y))))
    (test-equal (term (⊢struct-lookup DT bar)) (term ((int q))))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; E-Amper helper
    (test-equal (term (⊢& (ptr u (struct foo)) x 5)) (term (5 : (ptr u int))))
    (test-equal (term (⊢& (ptr u (struct foo)) y 5)) (term (6 : (ptr u int))))
    (test-equal (term (⊢& (ptr c (struct foo)) x 5)) (term (5 : (ptr c int))))
    (test-equal (term (⊢& (ptr c (struct foo)) y 5)) (term (6 : (ptr c int))))
    (test-equal (term (⊢& (ptr c (struct foo)) x 0)) #f)
    (test-equal (term (⊢& (ptr c (struct foo)) y 0)) #f)


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Malloc helper
    (test-equal (term (⊢types DT int)) (term (int)))
    (test-equal (term (⊢types DT (array 0 3 int))) (term (int int int)))
    (test-equal (term (⊢types DT (struct foo))) (term (int int)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Heaps
    ;; Heaps are represented as a list addressed by position counting from 1.
    ;; Allocation appends elements at the end of the list.
    (test-equal (term (⊢heap-lookup ((7 : int)) 1)) (term (7 : int)))
    (test-equal (term (⊢heap-lookup ((4 : int) (7 : int)) 1)) (term (4 : int)))
    (test-equal (term (⊢heap-lookup ((4 : int) (7 : int)) 2)) (term (7 : int)))

    (test-equal (term (⊢heap-defined? ((7 : int)) 0)) #f)
    (test-equal (term (⊢heap-defined? ((7 : int)) 1)) #t)
    (test-equal (term (⊢heap-defined? ((7 : int)) 2)) #f)
    (test-equal (term (⊢heap-defined? ((4 : int) (7 : int)) 2)) #t)
    (test-equal (term (⊢heap-defined? ((4 : int) (7 : int)) 3)) #f)

    (test-equal (term (⊢heap-update ((7 : int)) 1 (9 : int)))
                (term ((9 : int))))
    (test-equal (term (⊢heap-update ((4 : int) (7 : int)) 1 (9 : int)))
                (term ((9 : int) (7 : int))))
    (test-equal (term (⊢heap-update ((4 : int) (7 : int)) 2 (9 : int)))
                (term ((4 : int) (9 : int))))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Type system

    (test-judgment-holds (⊢ty ((x : int)) () c x int))
    (test-judgment-holds (⊢ty () ((5 : int)) c (5 : int) int))
    (test-judgment-holds (⊢ty () ((5 : int)) c (let x = (5 : int) in x) int))
    (test-judgment-holds (⊢ty () () c (0 : int) int))
    (test-judgment-holds (⊢ty () () c (4 : int) int))
    (test-judgment-holds (⊢ty () () c (0 : (ptr c int)) (ptr c int)))
    (test-judgment-holds (⊢ty () () c (1 : (ptr c (array 0 0 int)))
                              (ptr c (array 0 0 int))))
    (test-judgment-holds (⊢ty () () c (1 : (ptr u (array 0 5 int)))
                              (ptr u (array 0 5 int))))

    (test-equal (judgment-holds (⊢ty () () c (1 : (ptr c (array 0 5 int))) τ) τ)
                '())
    (test-judgment-holds (⊢ty () () c (1 : (ptr c int)) (ptr c int))) ; T-PtrC
    (test-judgment-holds (⊢ty () () c (& (malloc (struct foo)) → x)
                              (ptr c int)))
    (test-judgment-holds (⊢ty () () c ((1 : int) + (2 : int)) int))
    (test-judgment-holds (⊢ty () () c (malloc int) (ptr c int)))
    (test-equal (judgment-holds (⊢ty () () c (malloc (array 0 0 int)) τ) τ)
                '())
    (test-judgment-holds (⊢ty () () c (cast int (0 : (ptr c (array 0 5 int)))) int))
    (test-judgment-holds ; unchecked cast to ptr type succeeds
     (⊢ty () () c (cast (ptr u int) (5 : int)) (ptr u int)))

    (test-equal (judgment-holds ; checked cast to ptr type fails
                 (⊢ty () () c (cast (ptr c int) (5 : int)) τ) τ)
                '())
    (test-judgment-holds ; unchecking checked cast
     (⊢ty () () c (unchecked (cast (ptr c int) (5 : int))) (ptr c int)))
    (test-judgment-holds
     (⊢ty () () c (* (malloc (array 0 3 int))) int))
    (test-judgment-holds
     (⊢ty () () c (* ((malloc (array 0 3 int)) + (1 : int))) int))
    (test-judgment-holds
     (⊢ty () () c (* (malloc (array 0 3 int)) = (5 : int)) int))
    (test-judgment-holds
     (⊢ty () () c (* ((malloc (array 0 3 int)) + (1 : int)) = (5 : int)) int))))
