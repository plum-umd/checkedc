#lang racket
(provide (all-defined-out))
(require redex/reduction-semantics)

;; Redex model of Achieving Safety Incrementally with Checked C, 
;; by Ruef, Lampropoulos, Sweet, Tarditi, & Hicks, POST'19.
;; http://www.cs.umd.edu/~mwh/papers/checkedc-incr.pdf

;; This is written in a monolithic-style where there is a single judgment
;; "⊢" that takes a relation name and input and ouput (in order to be
;; extensible).

(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *D* (make-parameter (term ()))) ; struct table
(define *H* (make-parameter (term ()))) ; global heap (for type system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax

(define-language CoreChkC
  (m ::= c u)
  (τ ::= int (ptr m ω))
  (ω ::= τ (struct T) (array n τ))
  (e ::= (n : τ) x (let x = e in e) (malloc ω) (cast τ e)
     ((n : τ) +-checked e) (e + e) (& e → f) (* e) (* e = e) (*-checked (n : τ) = e) (unchecked e))
  (n l k ::= natural)
  (D ((T fs) ...))
  (fs ((τ f) (τ f) ...))
  (x f T ::= variable-not-otherwise-mentioned)
  (H ::= ((n : τ) ...))
  (r ::= e ε)
  (ε ::= Null Bounds)  
  (E ::= hole (let x = E in e) (E + e) ((n : τ) +-checked E)
     (& E → f) (cast τ E) (* E) (* E = e) (*-checked (n : τ) = E) (unchecked E))

  ;; static
  (Γ ::= ((x : τ) ...))
  (σ ::= ((n : τ) ...)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Semantics

(define-judgment-form CoreChkC
  #:contract (⊢ any any any)
  #:mode     (⊢ I   I   O)
  [(⊢ ↝ (H ((n_1 : τ_1) +-checked (n_2 : τ_2))) (H (n_3 : τ_3)))
   (where n_3 ,(+ (term n_1) (term n_2)))
   (⊢ binop-type-checked (τ_1 n_1 n_2) τ_3)
   E-BinopChecked]

  [(⊢ ↝ (H ((n_1 : τ_1) + e_2)) (H ((n_1 : τ_1) +-checked e_2)) )
   (⊢ binop-null-ok? (τ_1 n_1) #t)
   E-Binop]

  [(⊢ ↝ (H (cast τ (n : τ_′))) (H (n : τ)))
   E-Cast]

  [(⊢ ↝ (H (* (n : τ))) (H (n_1 : τ_2)))
   (⊢ deref-ok? τ #t)
   (⊢ heap-defined? (H n) #t)
   (⊢ ptype (,(*D*) τ) τ_2)
   (⊢ heap-lookup (H n) (n_1 : τ_1))
   E-Deref]

  [(⊢ ↝ (H (* (n : τ) = e)) (H (*-checked (n : τ) = e)))
   (⊢ assign-null-ok? (n τ) #t)
   (⊢ deref-ok? τ #t)
   E-Assign]

  [(⊢ ↝ (H (*-checked (n : τ) = (n_1 : τ_1))) (H_′ (n_1 : τ_1)))
   (⊢ heap-defined? (H n) #t)
   ;; (⊢ deref-ok? τ #t)
   (⊢ heap-update (H n (n_1 : τ_1)) H_′)
   E-AssignChecked]

  [(⊢ ↝ (H (& (n : τ) → f_i)) (H (n_0 : τ_0)))
   (⊢ & (τ f_i n) (n_0 : τ_0))
   E-Amper]

  [(⊢ ↝ (H (malloc ω)) (H_′ (n_1 : (ptr c ω))))
   (⊢ types (,(*D*) ω) (τ_1 τ_2 ...))
   (where ((n : τ) ...) H)
   (where H_′ ((n : τ) ... (0 : τ_1) (0 : τ_2) ...))
   (where n_1 ,(add1 (length (term H))))
   E-Malloc]

  [(⊢ ↝ (H (let x = (n : τ) in e)) (H e_′))
   (⊢ subst (e x (n : τ)) e_′)
   E-Let]

  [(⊢ ↝ (H (unchecked (n : τ))) (H (n : τ)))
   E-Unchecked]

  [(⊢ ↝ (H (* (n : τ))) (H Bounds))
   (side-condition ,(positive? (term n)))
   (where (ptr c (array 0 τ_1)) τ)
   X-DerefOOB]

  [(⊢ ↝ (H (* (n : τ) = e)) (H Bounds))
   (side-condition ,(positive? (term n)))
   (where (ptr c (array 0 τ_1)) τ)
   X-AssignOOB]

  [(⊢ ↝ (H (* (0 : τ))) (H Null))
   (where (ptr c ω) τ)
   X-DerefNull]

  [(⊢ ↝ (H (* (0 : τ) = e)) (H Null))
   (where (ptr c ω) τ)
   X-AssignNull]

  [(⊢ ↝ (H (& (0 : τ) → f)) (H Null))
   (where (ptr c (struct T)) τ)
   X-AmperNull]

  [(⊢ ↝ (H ((0 : τ) + e_2)) (H Null))
   (where (ptr c (array l τ_1)) τ)
   X-BinopNull]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; ⟶  
  [(where (in-hole E e_0) e)
   (⊢ ↝ (H e_0) (H_′ e_0′))
   (where e_′ (in-hole E e_0′))
   (⊢ mode E m_′)
   (⊢ check-mode (m m_′) #t)   
   ------ C-Exp
   (⊢ ⟶ (H e m) (H_′ e_′))]
  
  [(where (in-hole E e_0) e)
   (⊢ ↝ (H e_0) (H_′ ε))
   (⊢ mode E m_′)
   (⊢ check-mode (m m_′) #t)
   ------- C-Halt
   (⊢ ⟶ (H e m) (H_′ ε))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; binop-type-checked : (τ n n) × τ  
  [(⊢ binop-type-checked ((ptr c (array l τ)) n_1 n_2) (ptr c (array n_3 τ)))
   (where n_3 ,(max (term 0) (- (term l) (term n_2))))
   BTC-0]
  
  [(⊢ binop-type-checked ((name τ int) n_1 n_2) τ) BTC-1]
  [(⊢ binop-type-checked ((name τ (ptr m (struct T))) n_1 n_2) τ) BTC-2]
  [(⊢ binop-type-checked ((name τ (ptr u (array l _))) n_1 n_2) τ) BTC-3]
  [(⊢ binop-type-checked ((name τ (ptr m int)) n_1 n_2) τ) BTC-4]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; assign-null-ok? : (n τ) x bool
  
  [(⊢ assign-null-ok? (n (ptr c ω)) #t)
   (side-condition ,(positive? (term n)))]
  [(⊢ assign-null-ok? (n (ptr u ω)) #t)]
  [(⊢ assign-null-ok? (n int) #t)]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; binop-null-ok? : (τ n) × bool
  [(⊢ binop-null-ok? ((ptr c (array l τ)) n_1) #t)
   (side-condition ,(not (= 0 (term n_1))))
   BT-0] ; fn 8
  
  [(⊢ binop-null-ok? ((name τ int) n_1) #t) BT-1]
  [(⊢ binop-null-ok? ((name τ (ptr m (struct T))) n_1) #t) BT-2]
  [(⊢ binop-null-ok? ((name τ (ptr u (array l _))) n_1) #t) BT-3]
  [(⊢ binop-null-ok? ((name τ (ptr m int)) n_1) #t) BT-4]
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; heap-defined? : (H n) × #t
  [(⊢ heap-defined? (H n) #t)
   (side-condition ,(< 0 (term n) (add1 (length (term H)))))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; heap-lookup : (H n) × (n : τ)
  [(⊢ heap-lookup (H n) ,(list-ref (term H) (sub1 (term n))))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; heap-update : (H n (n : τ)) × H
  [(⊢ heap-update (H n (n_1 : τ_1))
      ,(list-set (term H) (sub1 (term n)) (term (n_1 : τ_1))))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
  ;; heap-from : (H n) × H
  [(⊢ heap-from (H n) ,(drop (term H) (sub1 (term n))))]
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; struct-lookup : (D T) × fs
  [(⊢ struct-lookup (((T fs) _ ...) T) fs)]  
  [(⊢ struct-lookup (((T_!_1 _) (T_′ fs) ...) T_1) fs_1)
   (⊢ struct-lookup (((T_′ fs) ...) T_1) fs_1)]
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  
  ;; deref-ok? : τ × #t
  [(⊢ deref-ok? int #t)]
  [(⊢ deref-ok? (ptr u ω) #t)]
  [(⊢ deref-ok? (ptr c τ) #t)]
  [(⊢ deref-ok? (ptr c (struct T)) #t)]
  [(⊢ deref-ok? (ptr c (array n τ)) #t)
   (side-condition ,(not (= 0 (term n))))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; types : (D ω) × (τ ...)
  [(⊢ types (D τ) (τ))]
  [(⊢ types (D (array l τ)) ,(make-list (term l) (term τ)))]
  [(⊢ types (D (struct T)) (τ ...))
   (⊢ struct-lookup (D T) ((τ f) ...))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; & : (τ f n) × (n : τ)
  
  ;; fixes a minor bug in paper: should be τ_0 f_0; ...; τ_k f_k, 0 <= i <= k,
  ;; i.e. 0-based counting, not 1-based

  [(⊢ & ((ptr m (struct T)) f_i n) (n_i : τ_i′))
   (⊢ struct-lookup (,(*D*) T) ((τ_0 f_0) ... (τ_i f_i) _ ...))
   (where n_i ,(+ (term n) (length (term ((τ_0 f_0) ...)))))
   (where τ_i′ (ptr m τ_i))
   (side-condition ,(or (eq? (term m) 'u) (not (= 0 (term n)))))]
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; check-mode: (m m) × #t
  [(⊢ check-mode (u _) #t)]
  [(⊢ check-mode (m m) #t)]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; mode
  [(⊢ mode hole c)]
  [(⊢ mode (unchecked E) u)]
  [(⊢ mode (let x = E in e) m) (⊢ mode E m)]
  [(⊢ mode (E + e) m)          (⊢ mode E m)]
  [(⊢ mode ((n : τ) +-checked E) m)    (⊢ mode E m)]
  [(⊢ mode (& E → f) m)        (⊢ mode E m)]
  [(⊢ mode (cast τ E) m)       (⊢ mode E m)]
  [(⊢ mode (* E) m)            (⊢ mode E m)]
  [(⊢ mode (* E = e) m)        (⊢ mode E m)]
  [(⊢ mode (*-checked (n : τ) = E) m)  (⊢ mode E m)]


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; subst : (e x (n : τ)) × e
  
  [(⊢ subst ((n : τ) x _) (n : τ))]
  [(⊢ subst (x x (n : τ)) (n : τ))]
  [(⊢ subst ((name x_1 x_!_1) x_!_1 _) x_1)]
  [(⊢ subst ((let x = e_1 in e_2) x (n : τ)) (let x = e_1′ in e_2))
   (⊢ subst (e_1 x (n : τ)) e_1′)]
  [(⊢ subst ((let (name x_′ x_!_1) = e_1 in e_2) (name x_1 x_!_1) (n : τ))
      (let x_′ = e_1′ in e_2′))
   (⊢ subst (e_1 x_1 (n : τ)) e_1′)
   (⊢ subst (e_2 x_1 (n : τ)) e_2′)]
  [(⊢ subst ((malloc ω) x _) (malloc ω))]
  [(⊢ subst ((cast τ e) x (n : τ_′)) (cast τ e_′))
   (⊢ subst (e x (n : τ_′)) e_′)]

  [(⊢ subst ((e_1 + e_2) x (n : τ))
      (e_1′ + e_2′))
   (⊢ subst (e_1 x (n : τ)) e_1′)
   (⊢ subst (e_2 x (n : τ)) e_2′)]

  [(⊢ subst (((n_1 : τ_1) +-checked e_2) x (n : τ))
      ((n_1 : τ_1) +-checked e_2′))
   (⊢ subst (e_2 x (n : τ)) e_2′)]

  [(⊢ subst ((& e → f) x (n : τ))
      (& e_′ → f))
   (⊢ subst (e x (n : τ)) e_′)]
  [(⊢ subst ((* e) x (n : τ)) (* e_′))
   (⊢ subst (e x (n : τ)) e_′)]
  [(⊢ subst ((* e_1 = e_2) x (n : τ))
      (* e_1′ = e_2′))
   (⊢ subst (e_1 x (n : τ)) e_1′)
   (⊢ subst (e_2 x (n : τ)) e_2′)]
  [(⊢ subst ((*-checked (n_1 : τ_1) = e_2) x (n : τ))
      (*-checked (n_1 : τ_1) = e_2′))
   (⊢ subst (e_2 x (n : τ)) e_2′)]
  [(⊢ subst ((unchecked e) x (n : τ))
      (unchecked e_′))
   (⊢ subst (e x (n : τ)) e_′)]


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Typing
  [(⊢ ty-env-lookup (Γ x) τ)
   ------------- T-Var
   (⊢ ty (Γ σ m x) τ)]
  
  [(where (_ ... (n : τ) _ ...) σ)
   ------------- T-VConst
   (⊢ ty (Γ σ m (n : τ)) τ)]
  
  [(⊢ ty (Γ σ m e_1) τ_1)
   (where ((x_′ : τ_′) ...) Γ)
   (⊢ ty (((x : τ_1) (x_′ : τ_′) ...) σ m e_2) τ)
   ------------- T-Let
   (⊢ ty (Γ σ m (let x = e_1 in e_2)) τ)]
  
  [(⊢ base? (n τ) #t)
   ------------- T-Base
   (⊢ ty (Γ σ m (n : τ)) τ)]

  [(where (ptr c ω) τ)
   (⊢ types (,(*D*) ω) (τ_0 ..._1))
   (⊢ heap-defined? (,(*H*) n) #t)
   (⊢ heap-from (,(*H*) n) ((n_1 : τ_1) ..._1 _ ...))
   (where ((n_′ : τ_′) ...) σ)
   (⊢ ty (Γ ((n : τ) (n_′ : τ_′) ...) m (n_1 : τ_1)) τ_0) ...
   ------------- T-PtrC
   (⊢ ty (Γ σ m (n : τ)) τ)]
 
  [(⊢ ty (Γ σ m e) (ptr m (struct T)))
   (⊢ struct-lookup (,(*D*) T) (_ ... (τ_f f) _ ...))
   ------------- T-Amper
   (⊢ ty (Γ σ m (& e → f)) (ptr m τ_f))]

  [(⊢ ty (Γ σ m e_1) int)
   (⊢ ty (Γ σ m e_2) int)
   ------------- T-BinopInt
   (⊢ ty (Γ σ m (e_1 + e_2)) int)]

  [(⊢ ty (Γ σ m e_1) int)
   (⊢ ty (Γ σ m e_2) int)
   ------------- T-BinopCheckedInt
   (⊢ ty (Γ σ m (e_1 +-checked e_2)) int)]

  [(⊢ types (,(*D*) ω) (τ_1 τ_2 ...))
   ------------- T-Malloc
   (⊢ ty (Γ σ m (malloc ω)) (ptr c ω))]

  [(⊢ ty (Γ σ u e)  τ)
   ------------- T-Unchecked
   (⊢ ty (Γ σ m (unchecked e)) τ)]

  [(⊢ ty (Γ σ m e) τ_′)
   (⊢ cast-ok? (m τ) #t)
   ------------- T-Cast
   (⊢ ty (Γ σ m (cast τ e)) τ)]

  [(⊢ ty (Γ σ m e) (ptr m_′ ω))
   (⊢ deref-type ω τ)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-Deref
   (⊢ ty (Γ σ m (* e)) τ)]

  [(⊢ ty (Γ σ m e_1) (ptr m_′ (array n τ)))
   (⊢ ty (Γ σ m e_2) int)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-Index
   (⊢ ty (Γ σ m (* (e_1 + e_2))) τ)]

  [(⊢ ty (Γ σ m (n_1 : τ_1)) (ptr m_′ (array n τ)))
   (⊢ binop-null-ok? (n_1 τ_1) #t)
   (⊢ ty (Γ σ m e_2) int)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-IndexChecked
   (⊢ ty (Γ σ m (* ((n_1 : τ_1) +-checked e_2))) τ)]

  [(⊢ ty (Γ σ m e_1) (ptr m_′ ω))
   (⊢ ty (Γ σ m e_2) τ)
   (⊢ deref-type ω τ)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-Assign
   (⊢ ty (Γ σ m (* e_1 = e_2)) τ)]

  [(⊢ ty (Γ σ m (n_1 : τ_1)) τ_1)
   (⊢ assign-null-ok? (n_1 τ_1) #t)
   (⊢ deref-ok? τ_1 #t)
   (where (ptr m_′ ω) τ_1)
   (⊢ ty (Γ σ m e_2) τ)
   (⊢ deref-type ω τ)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-CheckedAssign
   (⊢ ty (Γ σ m (*-checked (n_1 : τ_1) = e_2)) τ)]

  [(⊢ ty (Γ σ m e_1) (ptr m_′ (array n τ)))
   (⊢ ty (Γ σ m e_2) int)
   (⊢ ty (Γ σ m e_3) τ)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-IndAssign
   (⊢ ty (Γ σ m (* (e_1 + e_2) = e_3)) τ)]

  [(⊢ ty (Γ σ m (n_1 : τ_1)) (ptr m_′ (array n τ)))
   (⊢ binop-null-ok? (n_1 τ_1) #t)
   (⊢ ty (Γ σ m e_2) int)
   (⊢ ty (Γ σ m e_3) τ)
   (⊢ mode-ok? (m_′ m) #t)
   ------------- T-CheckedIndAssign
   (⊢ ty (Γ σ m (* ((n_1 : τ_1) +-checked e_2) = e_3)) τ)]
  
  ;; ty-env-lookup : (Γ x) × τ
  [(⊢ ty-env-lookup (((x : τ) _ ...) x) τ)]
  [(⊢ ty-env-lookup (((x_!_1 : _) (x_′ : τ_′) ...) (name x x_!_1)) τ)   
   (⊢ ty-env-lookup (((x_′ : τ_′) ...) x) τ)]

  ;; base? : (n τ) × #t
  [(⊢ base? (n int) #t)]
  [(⊢ base? (n (ptr u ω)) #t)]
  [(⊢ base? (0 τ) #t)]
  [(⊢ base? (n (ptr c (array 0 τ_′))) #t)]

  ;; cast-ok? : (m τ) × #t
  [(⊢ cast-ok? (u τ) #t)]
  [(⊢ cast-ok? (c int) #t)]
  [(⊢ cast-ok? (c (ptr u ω)) #t)]

  ;; deref-type τ × τ
  [(⊢ deref-type τ τ)]
  [(⊢ deref-type (array n τ) τ)]

  ;; ptype : (D τ) × τ
  [(⊢ ptype (D int) int)]
  [(⊢ ptype (D (ptr m τ)) τ)]
  [(⊢ ptype (D (ptr m (array n τ))) τ)]
  [(⊢ ptype (D (ptr m (struct T))) τ_1)
   (⊢ struct-lookup (D T) ((τ_1 f_1) (τ_2 f_2) ...) )]  

  ;; mode-ok? : (m m) × #t
  [(⊢ mode-ok? (u u) #t)]
  [(⊢ mode-ok? (c _) #t)])

(define ~~>
  (reduction-relation
   CoreChkC #:domain (H r)
   (--> (H e) (H_′ r_′) (judgment-holds (⊢ ↝ (H e) (H_′ r_′))))))

(define (---> m)
  (reduction-relation
   CoreChkC
   #:domain (H r)
   (--> (H e) (H_′ r)
        (judgment-holds (⊢ ⟶ (H e ,m) (H_′ r))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(module+ test
  (parameterize ((*D* (term ((foo ((int x) (int y)))))) ; a struct defn
                 (*H* (term ((5 : int))))) ; a heap for the type system tests
  
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; ↝
    
    ;; E-BinOpChecked
    (test--> ~~>
             (term (() ((3 : int) +-checked (4 : int))))
             (term (() (7 : int))))
    (test--> ~~>
             (term (() ((3 : (ptr c (array 5 int))) +-checked (4 : int))))
             (term (() (7 : (ptr c (array 1 int))))))
    (test--> ~~> ; going off the end in checked mode
             (term (() ((3 : (ptr c (array 5 int))) +-checked (7 : int))))
             (term (() (10 : (ptr c (array 0 int))))))
    (test--> ~~> ; ptr arith on null in unchecked mode
             (term (() ((0 : (ptr u (array 5 int))) +-checked (4 : int))))
             (term (() (4 : (ptr u (array 5 int))))))


    ;; E-BinOp
    (test--> ~~>
             (term (() ((3 : int) + (4 : int))))
             (term (() ((3 : int) +-checked (4 : int)))))
    (test--> ~~>
             (term (() ((3 : (ptr c (array 5 int))) + (4 : int))))
             (term (() ((3 : (ptr c (array 5 int))) +-checked (4 : int)))))
    (test--> ~~> ; going off the end in checked mode
             (term (() ((3 : (ptr c (array 5 int))) + (7 : int))))
             (term (() ((3 : (ptr c (array 5 int))) +-checked (7 : int)))))
    (test--> ~~> ; ptr arith on null in unchecked mode
             (term (() ((0 : (ptr u (array 5 int))) + (4 : int))))
             (term (() ((0 : (ptr u (array 5 int))) +-checked (4 : int)))))

    ;; E-Cast
    (test--> ~~>
             (term (() (cast (ptr c (array 5 int)) (0 : int))))
             (term (() (0 : (ptr c (array 5 int))))))

    ;; E-Deref
    (test--> ~~>
             (term (((7 : int)) (* (1 : int))))
             (term (((7 : int)) (7 : int))))
    (test--> ~~> ; dereferencing a valid checked ptr to an array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 1 int))))))
             (term (((7 : int)) (7 : int))))
    (test--> ~~> ; dereferencing an unchecked ptr to a nullary array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 int))))))
             (term (((7 : int)) (7 : int))))

    ;; E-Assign

    (test--> ~~>
             (term (((7 : int)) (* (1 : int) = (2 : int))))
             (term (((7 : int)) (*-checked (1 : int) = (2 : int)))))
    (test--> ~~> ; assigning a valid checked ptr to an array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 1 int))) = (2 : int))))
             (term (((7 : int)) (*-checked (1 : (ptr u (array 1 int))) = (2 : int)))))
    (test--> ~~> ; assigning an unchecked ptr to a nullary array, steps
             (term (((7 : int)) (* (1 : (ptr u (array 0 int))) = (2 : int))))
             (term (((7 : int)) (*-checked (1 : (ptr u (array 0 int))) = (2 : int)))))

    ;; E-AssignChecked
    (test--> ~~>
             (term (((7 : int)) (*-checked (1 : int) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~> ; assigning a valid checked ptr to an array, steps
             (term (((7 : int)) (*-checked (1 : (ptr u (array 1 int))) = (2 : int))))
             (term (((2 : int)) (2 : int))))
    (test--> ~~> ; assigning an unchecked ptr to a nullary array, steps
             (term (((7 : int)) (*-checked (1 : (ptr u (array 0 int))) = (2 : int))))
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
             (term (() (malloc (array 3 int))))
             (term (((0 : int) (0 : int) (0 : int))
                    (1 : (ptr c (array 3 int))))))

    (test--> ~~>
             (term (() (malloc (struct foo))))
             (term (((0 : int) (0 : int)) (1 : (ptr c (struct foo))))))

    (test--> ~~> ; alloc'ing a nullary array gets stuck
             (term (() (malloc (array 0 int)))))

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
             (term (((7 : int)) (* (1 : (ptr c (array 0 int))))))
             (term (((7 : int)) Bounds)))

    ;; X-AssignOOB
    (test--> ~~>
             (term (() (* (1 : (ptr c (array 0 int))) = (7 : int))))
             (term (() Bounds)))

    ;; X-DerefNull
    (test--> ~~> ; dereferencing a checked ptr to a nullary array
             (term (((7 : int)) (* (0 : (ptr c (array 1 int))))))
             (term (((7 : int)) Null)))

    ;; X-AssignNull
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 1 int))) = (7 : int))))
             (term (() Null)))

    ;; X-AmperNull
    (test--> ~~>
             (term (() (& (0 : (ptr c (struct foo))) → f)))
             (term (() Null)))

    ;; X-BinopNull
    (test--> ~~> ; ptr arith on null in checked mode
             (term (() ((0 : (ptr c (array 5 int))) + (4 : int))))
             (term (() Null)))

    ;; X-AssignOOB and X-AssignNull overlap
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 0 int))) = (7 : int))))
             (term (() Bounds))
             (term (() Null)))

    ;; X-DerefOOB and X-DerefNull overlap
    (test--> ~~>
             (term (() (* (0 : (ptr c (array 0 int))))))
             (term (() Bounds))
             (term (() Null)))

    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; ⟶
    (test-->>
     (---> 'c)
     (term (()
            (let p = (malloc (array 3 int)) in
              (let _ = (* (1 : (ptr c int)) = (6 : int)) in
                (let _ = (* (2 : (ptr c int)) = (7 : int)) in
                  (let _ = (* (3 : (ptr c int)) = (8 : int)) in
                    p))))))
     (term (((6 : int) (7 : int) (8 : int))
            (1 : (ptr c (array 3 int))))))
    
    (test-->>
     (---> 'c)
     (term (()
            (let p = (malloc (array 3 int)) in
              (let _ = (* p = (6 : int)) in
                (let p = (p + (1 : int)) in
                  (let _ = (* p = (7 : int)) in
                    (let p = (p + (1 : int)) in
                      (let _ = (* p = (8 : int)) in
                        (let p = (p + (1 : int)) in
                          p)))))))))
     (term (((6 : int) (7 : int) (8 : int))
            (4 : (ptr c (array 0 int))))))

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
            (let p = (malloc (array 3 int)) in
              (* (p + (4 : int)) = (7 : int)))))
     (term (((0 : int) (0 : int) (0 : int))
            Bounds)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Subst
    (test-judgment-holds (⊢ subst (x x (0 : int)) (0 : int)))
    (test-judgment-holds (⊢ subst (y x (0 : int)) y))
    (test-judgment-holds (⊢ subst ((let x = x in x) x (0 : int))
                            (let x = (0 : int) in x)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Structures
    (define-term DT
      ((foo ((int x) (int y)))
       (bar ((int q)))))

    (test-judgment-holds (⊢ struct-lookup (DT foo) ((int x) (int y))))
    (test-judgment-holds (⊢ struct-lookup (DT bar) ((int q))))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; E-Amper helper
    (test-judgment-holds (⊢ & ((ptr u (struct foo)) x 5) (5 : (ptr u int))))
    (test-judgment-holds (⊢ & ((ptr u (struct foo)) y 5) (6 : (ptr u int))))
    (test-judgment-holds (⊢ & ((ptr c (struct foo)) x 5) (5 : (ptr c int))))
    (test-judgment-holds (⊢ & ((ptr c (struct foo)) y 5) (6 : (ptr c int))))
    (test-equal (judgment-holds (⊢ & ((ptr c (struct foo)) x 0) any) any) '())
    (test-equal (judgment-holds (⊢ & ((ptr c (struct foo)) y 0) any) any) '())


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Malloc helper
    (test-judgment-holds (⊢ types (DT int) (int)))
    (test-judgment-holds (⊢ types (DT (array 3 int)) (int int int)))
    (test-judgment-holds (⊢ types (DT (struct foo)) (int int)))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Heaps    
    ;; Heaps are represented as a list addressed by position counting from 1.
    ;; Allocation appends elements at the end of the list.
    (test-judgment-holds (⊢ heap-lookup (((7 : int)) 1) (7 : int)))
    (test-judgment-holds (⊢ heap-lookup (((4 : int) (7 : int)) 1) (4 : int)))
    (test-judgment-holds (⊢ heap-lookup (((4 : int) (7 : int)) 2) (7 : int)))

    (test-equal (judgment-holds (⊢ heap-defined? (((7 : int)) 0) #t)) #f)
    (test-judgment-holds (⊢ heap-defined? (((7 : int)) 1) #t))
    (test-equal (judgment-holds (⊢ heap-defined? (((7 : int)) 2) #t)) #f)
    (test-judgment-holds (⊢ heap-defined? (((4 : int) (7 : int)) 2) #t))
    (test-equal (judgment-holds (⊢ heap-defined? (((4 : int) (7 : int)) 3) #t)) #f)

    (test-judgment-holds (⊢ heap-update (((7 : int)) 1 (9 : int))
                            ((9 : int))))
    (test-judgment-holds (⊢ heap-update (((4 : int) (7 : int)) 1 (9 : int))
                            ((9 : int) (7 : int))))
    (test-judgment-holds (⊢ heap-update (((4 : int) (7 : int)) 2 (9 : int))
                            ((4 : int) (9 : int))))
    

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Type system
    
    (test-judgment-holds (⊢ ty (((x : int)) () c x) int))
    (test-judgment-holds (⊢ ty (() ((5 : int)) c (5 : int)) int))
    (test-judgment-holds (⊢ ty (() ((5 : int)) c (let x = (5 : int) in x)) int))
    (test-judgment-holds (⊢ ty (() () c (0 : int)) int))
    (test-judgment-holds (⊢ ty (() () c (4 : int)) int))
    (test-judgment-holds (⊢ ty (() () c (0 : (ptr c int))) (ptr c int)))
    (test-judgment-holds (⊢ ty (() () c (1 : (ptr c (array 0 int))))
                            (ptr c (array 0 int))))
    (test-judgment-holds (⊢ ty (() () c (1 : (ptr u (array 5 int))))
                            (ptr u (array 5 int))))
    (test-equal (judgment-holds (⊢ ty (() () c (1 : (ptr c (array 5 int)))) τ) τ)
                '())
    (test-judgment-holds (⊢ ty (() () c (1 : (ptr c int))) (ptr c int))) ; T-PtrC
    (test-judgment-holds (⊢ ty (() () c (& (malloc (struct foo)) → x))
                            (ptr c int)))    
    (test-judgment-holds (⊢ ty (() () c ((1 : int) + (2 : int))) int))
    (test-judgment-holds (⊢ ty (() () c ((1 : int) +-checked (2 : int))) int))
    (test-judgment-holds (⊢ ty (() () c (malloc int)) (ptr c int)))
    (test-equal (judgment-holds (⊢ ty (() () c (malloc (array 0 int))) τ) τ)
                '())
   
    (test-judgment-holds (⊢ ty (() () c (cast int (0 : (ptr c (array 5 int))))) int))
    (test-judgment-holds ; unchecked cast to ptr type succeeds
     (⊢ ty (() () c (cast (ptr u int) (5 : int))) (ptr u int)))
    
    (test-equal (judgment-holds ; checked cast to ptr type fails
                 (⊢ ty (() () c (cast (ptr c int) (5 : int))) τ) τ)
                '())
    (test-equal (judgment-holds ; additional check is needed for typing +-checked
                 (⊢ ty (() () c (*((0 : (ptr c (array 4 int))) +-checked (5 : int)))) τ) τ)
                '())
    (test-judgment-holds ; unchecking checked cast
     (⊢ ty (() () c (unchecked (cast (ptr c int) (5 : int)))) (ptr c int)))
    (test-judgment-holds
     (⊢ ty (() () c (* (malloc (array 3 int)))) int))
    (test-judgment-holds
     (⊢ ty (() () c (* ((malloc (array 3 int)) + (1 : int)))) int))
    (test-judgment-holds
     (⊢ ty (() () c (* (malloc (array 3 int)) = (5 : int))) int))
    (test-judgment-holds
     (⊢ ty (() () c (* ((malloc (array 3 int)) + (1 : int)) = (5 : int))) int))))
