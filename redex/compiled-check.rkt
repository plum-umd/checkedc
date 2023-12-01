#lang racket
(provide (all-defined-out))
(require "post-2.rkt")
(require redex/reduction-semantics)
(require rackcheck)
(require rackunit)

#|
;; Run in the interactions window to see an example reduction

(require redex)

(define (example e)
  (traces (--->^ 'c)
          (first (judgment-holds (⊢^ >> (() () c ,e) (e′ τ)) ((n) e′)))))

(define (run)
  (example (term (let p = (malloc (array 3 int)) in
                      (* (p + (2 : int))))))
  (example (term (let p = (malloc (array 3 int)) in
                      (* (p + (100 : int)))))))
|#

;; Is this ok? or should I reuse *D* and *H*?
(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *eD* (make-parameter (term ()))) ; struct table
(define *eH* (make-parameter (term ()))) ; global heap (for type system)


;; Syntax
(define-extended-language CoreChkC^ CoreChkC
  ;; (eτ ::= int (ptr eω))
  ;; (eω ::= eτ (struct T) (array eτ))
  (ee ::=  n x (let x = ee in ee) (malloc n)
      (ee + ee) (* ee) (* ee = ee) (enull ee)
      ;; generalize n to ee for dependent types
      (ebounds n ee)
      (ebounds-0 n ee))
  (eH ::= (n ...))
  (er ::= ee ε)
  (eE ::= hole (let x = eE in ee) (eE + ee) (n + eE)
      (* eE) (* eE = ee) (* n = eE)
      (enull eE)
      (ebounds n eE)
      (ebounds-0 n eE)))



(define-extended-judgment-form CoreChkC^ ⊢
  #:mode (⊢^ I I O)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Semantics

  ;; ↝^S corresponds to a step in the source
  ;; ↝^C corresponds to a step related to explicit checks

  [(⊢^ ↝^S (eH (n_1 + n_2)) (eH n_3))
   (where n_3 ,(+ (term n_1) (term n_2)))
   eE-Binop]

  [(⊢^ ↝^S (eH (* n)) (eH n_1))
   (⊢^ eheap-defined? (eH n) #t)
   (⊢^ eheap-lookup (eH n) n_1)
   eE-Deref]

  [(⊢^ ↝^S (eH (* n  = n_1)) (eH_′ n_1))
   (⊢^ eheap-defined? (eH n) #t)
   (⊢^ eheap-update (eH n n_1) eH_′)
   eE-Assign]

  [(⊢^ ↝^S (eH (malloc n_1)) (eH_′ n_2))
   (where (n ...) eH)
   (where eH_′ ,(append (term (n ...)) (build-list (term n_1) (const 0))))
   (where n_2 ,(add1 (length (term eH))))
   eE-Malloc]

  [(⊢^ ↝^S (eH (let x = n in ee)) (eH ee_′))
   (⊢^ esubst (ee x n) ee_′)
   eE-Let]

  [(⊢^ ↝^C (eH (ebounds n_1 n_2)) (eH n_2))
   (side-condition ,(< (term n_2) (term n_1)))
   eE-Bounds]

  [(⊢^ ↝^C (eH (ebounds n_1 n_2)) (eH Bounds))
   (side-condition ,(>= (term n_2) (term n_1)))
   eX-Bounds]

  ;; ebounds-0 no longer needed?
  ;; no, we need when there is * e when e is an array
  [(⊢^ ↝^C (eH (ebounds-0 n n_1)) (eH n_1))
   (side-condition ,(positive? (term n)))
   eE-Bounds-0]

  [(⊢^ ↝^C (eH (ebounds-0 n n_1)) (eH Bounds))
   (side-condition ,(zero? (term n)))
   eX-Bounds-0]

  [(⊢^ ↝^C (eH (enull n)) (eH n))
   (side-condition ,(positive? (term n)))
   eE-Null]

  [(⊢^ ↝^C (eH (enull n)) (eH Null))
   (side-condition ,(zero? (term n)))
   eX-Null]


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; ⟶^C
  [(where (in-hole eE ee_0) ee)
   (⊢^ ↝^C (eH ee_0) (eH_′ ee_0′))
   (where ee_′ (in-hole eE ee_0′))
   ------ C-Exp
   (⊢^ ⟶^C (eH ee) (eH_′ ee_′))]

  [(where (in-hole eE ee_0) ee)
   (⊢^ ↝^C (eH ee_0) (eH_′ ε))
   ------- C-Halt
   (⊢^ ⟶^C (eH ee) (eH_′ ε))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; ⟶^S
  [(where (in-hole eE ee_0) ee)
   (⊢^ ↝^S (eH ee_0) (eH_′ ee_0′))
   (where ee_′ (in-hole eE ee_0′))
   ------ S-Exp
   (⊢^ ⟶^S (eH ee) (eH_′ ee_′))]

  ;; TODO: semantics


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; eheap-lookup : (eH n) × (n : eτ)
  [(⊢^ eheap-lookup (eH n) ,(list-ref (term eH) (sub1 (term n))))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; eheap-update  : (eH n (n : eτ)) × H
  [(⊢^ eheap-update (eH n n_1)
       ,(list-set (term eH) (sub1 (term n)) (term n_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; eheap-defined? : (eH n) × #t
  [(⊢^ eheap-defined? (eH n) #t)
   (side-condition ,(< 0 (term n) (add1 (length (term eH)))))]

  ;; not needed anymore
  ;; [(⊢ ebinop-type ((ptr c (array τ)) n_1 n_2) (ptr c (array τ)))
  ;;  (where n_3 ,(max (term 0) (- (term l) (term n_2))))
  ;;  (side-condition ,(not (= 0 (term n_1))))
  ;;  BT-0]


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; sizeof : (D ω) × n
  [(⊢^ sizeof (D ω) n)
   (⊢^ types (D ω) (τ_0 τ_1 ...))
   (where n ,(length (term (τ_0 τ_1 ...))))]




  [(⊢^ eerase-H  ((n : τ) ...) (n ...))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Subst

  [(⊢^ esubst (n x _) n)]
  [(⊢^ esubst (x x n) n)]
  [(⊢^ esubst ((name x_1 x_!_1) x_!_1 _) x_1)]
  [(⊢^ esubst ((let x = ee_1 in ee_2) x n) (let x = ee_1′ in ee_2))
   (⊢^ esubst (ee_1 x n) ee_1′)]
  [(⊢^ esubst ((let (name x_′ x_!_1) = ee_1 in ee_2) (name x_1 x_!_1) n)
       (let x_′ = ee_1′ in ee_2′))
   (⊢^ esubst (ee_1 x_1 n) ee_1′)
   (⊢^ esubst (ee_2 x_1 n) ee_2′)]
  [(⊢^ esubst ((malloc n) x _) (malloc n))]

  [(⊢^ esubst ((ee_1 + ee_2) x n)
       (ee_1′ + ee_2′))
   (⊢^ esubst (ee_1 x n) ee_1′)
   (⊢^ esubst (ee_2 x n) ee_2′)]

  [(⊢^ esubst ((* ee) x n) (* ee_′))
   (⊢^ esubst (ee x n) ee_′)]
  [(⊢^ esubst ((* ee_1 = ee_2) x n)
       (* ee_1′ = ee_2′))
   (⊢^ esubst (ee_1 x n) ee_1′)
   (⊢^ esubst (ee_2 x n) ee_2′)]

  [(⊢^ esubst ((enull ee_1) x n) (enull ee_1′))
   (⊢^ esubst (ee_1 x n) ee_1′)]
  [(⊢^ esubst ((ebounds n_0 ee_1) x n_1) (ebounds n_0 ee_1′))
   (⊢^ esubst (ee_1 x n_1) ee_1′)]

  [(⊢^ esubst ((ebounds-0 n_0 ee_1) x n_1) (ebounds-0 n_0 ee_1′))
   (⊢^ esubst (ee_1 x n_1) ee_1′)]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Type-based transformation, without heap consistency
  ;; ≻ : (Γ e) × (e^ τ)
  [(⊢^ ty-env-lookup (Γ x) τ)
   ------------- eT-Var′
   (⊢^ ≻ (Γ x) (x τ))]

  [------------- eT-VConst′
   (⊢^ ≻ (Γ (n : τ)) (n τ))]

  [(⊢^ ≻ (Γ e_1) (ee_1 τ_1))
   (where ((x_′ : τ_′) ...) Γ)
   (⊢^ ≻ (((x : τ_1) (x_′ : τ_′) ...) e_2) (ee_2 τ))
   ------------- eT-Let′
   (⊢^ ≻ (Γ (let x = e_1 in e_2)) ((let x = ee_1 in ee_2) τ))]

  [(⊢^ ≻ (Γ e) (ee (ptr m (struct T))))
   (⊢^ struct-lookup (,(*D*) T) ((τ_0 f_0) ... (τ_f f) _ ...))
   (where n ,(length (term (τ_0 ...))))
   (⊢^ enull-check-maybe (m ee) ee_0)
   ------------- eT-Amper′
   (⊢^ ≻ (Γ (& e → f)) ((ee_0 + n) (ptr m τ_f)))]

  [(⊢^ ≻ (Γ e_1) (ee_1 int))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   ------------- eT-BinopInt′
   (⊢^ ≻ (Γ (e_1 + e_2)) ((ee_1 + ee_2) int))]

  [(⊢^ ≻ (Γ (n_1 : τ_1)) (ee_1 int))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   ------------- eT-BinopCheckedInt′
   (⊢^ ≻ (Γ ((n_1 : τ_1) +-checked e_2)) ((ee_1 + ee_2) int))]


  [(⊢^ types (,(*D*) ω) (τ_1 τ_2 ...))
   (⊢^ sizeof (,(*D*) ω) n)
   ------------- eT-Malloc′
   (⊢^ ≻ (Γ (malloc ω)) ((malloc n) (ptr c ω)))]


  [(⊢^ ≻ (Γ e)  (ee τ))
   ------------- eT-Unchecked′
   (⊢^ ≻ (Γ (unchecked e)) (ee τ))]

  [(⊢^ ≻ (Γ e) (ee τ_′))
   ------------- eT-Cast′
   (⊢^ ≻ (Γ (cast τ e)) (ee τ))]

  [(⊢^ ≻ (Γ e) (ee (ptr m_′ ω)))
   (⊢^ deref-type ω τ)
   (⊢^ enull-check-maybe (m_′ ee) ee_0)
   (⊢^ ebounds-check-maybe-ω (m_′ ω ee_0) ee_1)
   ------------- eT-Deref′
   (⊢^ ≻ (Γ (* e)) ((* ee_1) τ))]

  [(⊢^ ≻ (Γ e_1) (ee_1 (ptr m_′ (array n τ))))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   (⊢^ enull-check-maybe (m_′ ee_1) ee_3)
   (⊢^ ebounds-check-maybe (m_′ n ee_2) ee_4)
   (⊢^ enull-check-maybe (m_′ (ee_3 + ee_4)) ee_5)
   ------------- eT-Index′
   (⊢^ ≻ (Γ (* (e_1 + e_2))) ((* ee_5) τ))]

  [(⊢^ ≻ (Γ (n_1 : τ_1)) (ee_1 (ptr m_′ (array n τ))))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   (⊢^ ebounds-check-maybe (m_′ n ee_2) ee_3)
   (⊢^ enull-check-maybe (m_′ (ee_1 + ee_3)) ee_4)
   ------------- eT-IndexChecked′
   (⊢^ ≻ (Γ (* ((n_1 : τ_1) +-checked e_2))) ((* ee_4) τ))]

  [(⊢^ ≻ (Γ e_1) (ee_1 (ptr m_′ ω)))
   (⊢^ ≻ (Γ e_2) (ee_2 τ))
   (⊢^ deref-type ω τ)
   (⊢^ enull-check-maybe (m_′ ee_1) ee_3)
   (⊢^ ebounds-check-maybe-ω (m_′ ω ee_3) ee_4)
   ------------- eT-Assign′
   (⊢^ ≻ (Γ (* e_1 = e_2)) ((* ee_4 = ee_2) τ))]

  [(⊢^ ≻ (Γ (n_1 : τ_1)) (ee_1 τ_1))
   ;; (side-condition ,(positive? (term n_1)))
   (⊢^ deref-ok? τ_1 #t)
   (where (ptr m_′ ω) τ_1)
   (⊢^ ≻ (Γ e_2) (ee_2 τ))
   (⊢^ deref-type ω τ)
   ------------- eT-CheckedAssign′
   (⊢^ ≻ (Γ (*-checked (n_1 : τ_1) = e_2)) ((* ee_1 = ee_2) τ))]

  [(⊢^ ≻ (Γ e_1) (ee_1 (ptr m_′ (array n τ))))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   (⊢^ ≻ (Γ e_3) (ee_3 τ))
   (⊢^ enull-check-maybe (m_′ ee_1) ee_4)
   (⊢^ ebounds-check-maybe (m_′ n ee_2) ee_5)
   (⊢^ enull-check-maybe (m_′ (ee_4 + ee_5)) ee_6)
   ------------- eT-IndAssign′
   (⊢^ ≻ (Γ (* (e_1 + e_2) = e_3)) ((* ee_6 = ee_3) τ))]


  [(⊢^ ≻ (Γ (n_1 : τ_1)) (ee_1 (ptr m_′ (array n τ))))
   (⊢^ ≻ (Γ e_2) (ee_2 int))
   (⊢^ ≻ (Γ e_3) (ee_3 τ))
   (⊢^ ebounds-check-maybe (m_′ n ee_2) ee_5)
   (⊢^ enull-check-maybe (m_′ (ee_1 + ee_5)) ee_6)
   ------------- eT-CheckedIndAssign′
   (⊢^ ≻ (Γ (* ((n_1 : τ_1) +-checked e_2) = e_3)) ((* ee_6 = ee_3) τ))]


  [(⊢^ ebounds-check-maybe (c n ee) (ebounds n ee))]
  [(⊢^ ebounds-check-maybe (u n ee) ee)]

  [(⊢^ ebounds-check-maybe-ω (u ω ee) ee)]
  [(⊢^ ebounds-check-maybe-ω (c τ ee) ee)]
  [(⊢^ ebounds-check-maybe-ω (c (struct T) ee) ee)]
  ;; note that we could statically determine whether n is 0
  [(⊢^ ebounds-check-maybe-ω (c (array n τ) ee) (ebounds-0 n ee))]

  [(⊢^ enull-check-maybe (c ee) (enull ee))]
  [(⊢^ enull-check-maybe (u ee) ee)])

(define/match (checked-ptr-type? ty)
  [(`(ptr c ,_)) #t]
  [(_) #f])

(define/match (unchecked-ptr-type? ty)
  [(`(ptr u ,_)) #t]
  [(_) #f])

(define/match (empty-array-ptr-type? ty)
  [(`(ptr ,_ (array 0 ,_))) #t]
  [(_) #f])


;; Reduction relations
;;; Why is _ necessary?
(define (~~>^ m)
  (match m
    ['S 
     (reduction-relation
      CoreChkC^ #:domain (eH er)
      (--> (eH ee) (eH_′ er_′) (judgment-holds (⊢^ ↝^S (eH ee) (eH_′ er_′)))))]
    ['C
     (reduction-relation
      CoreChkC^ #:domain (eH er)
      (--> (eH ee) (eH_′ er_′) (judgment-holds (⊢^ ↝^C (eH ee) (eH_′ er_′)))))]))

(define (--->^ m)
  (match m
    ['S 
     (reduction-relation
      CoreChkC^
      #:domain (eH er)
      (--> (eH ee) (eH_′ er)
           (judgment-holds (⊢^ ⟶^S (eH ee) (eH_′ er)))))]
    ['C
     (reduction-relation
      CoreChkC^
      #:domain (eH er)
      (--> (eH ee) (eH_′ er)
           (judgment-holds (⊢^ ⟶^C (eH ee) (eH_′ er)))))]))


;; union of 'S and 'C
(define --->^^
  (reduction-relation
      CoreChkC^
      #:domain (eH er)
      (--> (eH ee) (eH_′ er)
           (judgment-holds (⊢^ ⟶^C (eH ee) (eH_′ er))))
      (--> (eH ee) (eH_′ er)
           (judgment-holds (⊢^ ⟶^S (eH ee) (eH_′ er))))))

;; (parameterize ((*eD* (term ((foo ((int x) (int y)))))) ; a struct defn
;;                (*eH* (term ((5 : int)))))
;;   (judgment-holds (⊢^ eptype (,(*eD*) (ptr int)) int))
;;   (judgment-holds (⊢^ eptype (,(*eD*) (ptr (struct foo))) int)))


;; Tests


(define/contract (mk-stop-when n)
  (-> natural? any)
  (let* ((counter n)
                    (decrement! (lambda () (begin (set! counter (sub1 counter)) #f))))
               (lambda (_)
                 (if (= counter 0)
                     #t
                     (decrement!)))))

(define expr?
  (redex-match CoreChkC^ e))

(define (has-unchecked-redex? t)
  (ormap
   (λ (m)
     (match (judgment-holds (⊢ mode ,(bind-exp (first (match-bindings m))) m) m)
       ['(u) #t]
       [_ #f]))
   (redex-match CoreChkC^ (in-hole E e) t)))


(define (context-mode t)
  (first (judgment-holds (⊢ mode ,t m) m)))

(define (error? t)
  (redex-match CoreChkC^ ε t))

(define (value? t)
  (redex-match CoreChkC^ (n : τ) t))

(define (erased-expr? t)
  (redex-match CoreChkC^ ee t))

(define (ptype t)
  (first (judgment-holds (⊢^ ptype (,(*D*) ,t) τ) τ)))

(define (type? t)
  (redex-match CoreChkC^ ω t))

(define (heap? t)
  (redex-match CoreChkC^ H t))

(define (≻-well-typed? t)
  (judgment-holds (⊢^ ≻ (() ,t) (ee τ)) τ))

(define (well-typed? e)
  (judgment-holds (⊢ ty (() () c ,e) τ) τ))

;; (define (erased-heap? t)
;;   (redex-match CoreChkC^ H t))

(define/contract (erase-heap t)
  (-> heap? any)
  (match (judgment-holds (⊢^ eerase-H ,t eH) eH)
    [(list eH) eH]
    [(list eH eH0 ...) (error "impossible: erase-heap is not functional")]
    [_ (error "heap erasure failed")]))

;; (define (≻-well-typed? t)
;;   (judgment-holds (⊢^ ≻ (() ,t) (ee τ)) τ))

(define (erase-term G t)
  (first (judgment-holds (⊢^ ≻ (,G ,t) (ee τ)) ee)))

(define (compile e)
  (let ([r (judgment-holds
                  (⊢^ ≻ (() ,e) (ee τ)) ee)])
    (match r
      [(list e) e]
      [(list e0 e1 ...) (error "impossible: compile is not functional")]
      [(list) (error (string-append "compilation fails: " (format "~a" e)))])))

(define (reduce-source* H e)
  (apply-reduction-relation*
   (---> 'u)
   (term (,H ,e))
   #:all? #t))

(define (reduce-source-all-the-way H e)
  (match
      (apply-reduction-relation*
       (---> 'u)
       (term (,H ,e)))
    [(list c) (list c)]
    [(list) (list)]
    [_ (error "impossible: reduction is non-deterministic")]))


(define (run-checks* eH0 ee0)
  (match (apply-reduction-relation*
    (--->^ 'C)
    (term (,eH0 ,ee0)))
    [(list (list eH1 ee1))
     (list eH1 ee1)]
    [(list a b ...) (error "impossible: check reduction is non-deterministic")]))

(define/match (source-target-rel H-e eH-ee)
  [((list H e) (list eH ee))
   (and (equal? eH (erase-heap H))
        (let ([compiled-e (parameterize
                              ([*H* H])
                            (compile e))])
          (equal? (second (run-checks* eH compiled-e))
                  ee)))])

;; (let ([c (term ((1 : int) (* (1 : (ptr c (array 1 int))))))]
;;       [ec (term ((1) (* (ebounds-0 1 (enull 1)))))]))



;; --->^C* followed by a single --->^S
;; maybe it's possible to define this as a reduction-relation?
;; I feel like I'm reinventing the wheels
(define (reduce-target-maybe eH0 ee0)
  (match (run-checks* eH0 ee0)
    [(list eH1 ee1)
     (match (apply-reduction-relation
             (--->^ 'S)
             (term (,eH1 ,ee1)))
       [(list) (if (and (equal? eH1 eH0)
                        (equal? ee0 ee1))
                   #f
                   (list eH1 ee1))]
       [(list (list eH2 ee2))
        (list eH2 ee2)]
       [(list a b ...)
        (error "impossible: reduction is non-deterministic")])]))

(define (reduce-target* eH0 ee0)
  (define (go eH ee xs)
    (let ([r (reduce-target-maybe eH ee)])
      (match r
        [#f xs]
        [(list eH ee)
         (go eH ee (cons (list eH ee) xs))])))
  (go eH0 ee0 '()))

(define (simulation H e)
  ;; (displayln e)
  (let ([ee (parameterize ([*H* H]) (compile e))]
        [eH (erase-heap H)])
    (let ([es (reduce-source-all-the-way H e)]
          [ees (reduce-target* eH ee)])
      (match es
        [(list (list H e))
         (if (error? e)
             (begin
               ;; (print (first ees))
               ;; (print (list H e))
               ;; (print (equal? (first ees) (list H e)))
               (and (pair? ees) (equal? (first ees) (list (erase-heap H) e))))
             (source-target-rel (list H e)
                                (if (null? ees) (list eH ee) (first ees))))]
        [(list)
         (null? ees)])
      ;; (if (null? es)
      ;;     (null? ees)
          

      ;;     ;; (begin
      ;;     ;;   (displayln (last es))
      ;;     ;;   (displayln (last ees)))
      ;;     )
      )))

;;; justifications of the fixes
;; (define test-expr '(* ((malloc (array 4 (ptr c int))) + (4 : int)) = (malloc int)))

;; test-expr
;; (compile test-expr)

;; (define test-expr '(* ))

;; (define test-expr2
;;   '(((0 : (ptr c (array 9 int)))
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int)
;;     (0 : int))
;;    (* (* (1 : (ptr c (ptr c (array 9 int)))) = (2 : (ptr c (array 9 int)))))))

;; (define test-expr-3 '((cast int (12 : int)) + (* (malloc (array 3 int)))))
;; (define test-expr-4 '(let x_9 = (malloc int) in (* (* (15 : (ptr c (array 2 (ptr u (array 13 (ptr c (array 13 int))))))) = (1 : (ptr u (array 13 (ptr c (array 13 int)))))))))

;; (define test-expr-5 '(* (let x_7 = (7 : int) in (let x_5 = (malloc (array 13 (ptr u int))) in (6 : (ptr u int)))) = (unchecked (* ((5 : (ptr c (array 10 int))) + (1 : int)) = (20 : int)))))

;; (define test-expr-6 '(unchecked (* (malloc (ptr u (ptr c (ptr c (array 0 int))))))))

;; (define test-expr-7 '(* (13 : (ptr c (array 13 int))) = (* ((11 : (ptr c (array 12 int))) + (5 : int)) = (8 : int))))


;; ;; short circuiting for +
;; (define test-expr-8 '(* ((* ((malloc (array 20 (ptr c (array 18 int)))) + (16 : int))) + (* (13 : (ptr u int)) = (5 : int)))))


;; (define test-expr-9 '(* ((cast (ptr c (array 18 (ptr u (array 4 int)))) (12 : int)) + (* ((4 : (ptr u (array 0 int))) + (16 : int)) = (13 : int))) = (10 : (ptr u (array 4 int)))))


;; (define test-expr-10 '(* (* (* (* (malloc (array 19 (ptr u (ptr c (array 15 (ptr u int))))))) = (* ((12 : (ptr c (array 16 (ptr c (array 15 (ptr u int)))))) + (10 : int))))) = (* (& (16 : (ptr c (struct bar))) → z))))

;; (define test-expr-11 '(* (* (malloc (array 19 (ptr u (ptr c (array 15 (ptr u int))))))) = (* ((12 : (ptr c (array 16 (ptr c (array 15 (ptr u int)))))) + (10 : int)))))


;; (define test-expr-12 '(* (cast (ptr c (ptr c (ptr c (ptr c (array 18 int))))) (& (* ((malloc (array 18 (ptr c (struct foo)))) + (12 : int))) → y)) = (* ((* (* ((19 : (ptr c (array 14 (ptr c (array 20 (ptr u (array 6 (ptr c (ptr c (ptr c (array 18 int))))))))))) + (6 : int)) = (malloc (array 20 (ptr u (array 6 (ptr c (ptr c (ptr c (array 18 int))))))))) = (unchecked (19 : (ptr u (array 6 (ptr c (ptr c (ptr c (array 18 int))))))))) + (* ((19 : (ptr c (array 15 int))) + (cast int (9 : (ptr c int)))))) = (* (* ((malloc (array 13 (ptr u (ptr c (ptr c (ptr c (array 18 int))))))) + (4 : int))) = (* ((5 : (ptr u (array 12 (ptr c (ptr c (ptr c (array 18 int))))))) + (11 : int)))))))

;; (define test-expr-13 '(& (* ((malloc (array 18 (ptr c (struct foo)))) + (12 : int))) → y))

;; (define test-expr-14 '(* ((0 : (ptr c (array 19 int))) + (* (* ((* (0 : (ptr c (array 15 (ptr c (array 0 (ptr c (array 16 int))))))) = (2 : (ptr c (array 0 (ptr c (array 16 int)))))) + (* ((0 : (ptr c (array 19 int))) + (12 : int)) = (7 : int))) = (0 : (ptr c (array 16 int)))) = (let x_0 = (cast (ptr u (ptr c (ptr c (array 0 (ptr c int))))) (0 : (ptr c (ptr u int)))) in (* (malloc int) = (9 : int))))) = (* ((* ((* (0 : (ptr c (array 12 (ptr c (array 8 (ptr c (array 8 int)))))))) + (cast int (0 : (ptr c (array 8 (ptr c (array 9 int)))))))) + (cast int (unchecked (2 : (ptr u (ptr u (array 1 int))))))) = (let x_7 = (* (malloc (array 17 (ptr u (ptr u (array 10 (ptr c (ptr c (array 16 int))))))))) in (* ((malloc (array 9 int)) + (0 : int)))))))


(define test-expr-15 '(* (let x_1 = (* (malloc (ptr c (array 15 (ptr c int))))) in (unchecked (9 : (ptr c (array 0 int))))) = (* ((let x_5 = (8 : (ptr u (ptr c (array 12 (ptr c (array 17 int)))))) in (15 : (ptr u (array 9 int)))) + (* (17 : (ptr u (array 14 int))))) = (* ((malloc (array 4 int)) + (11 : int)) = (17 : int)))))

(define test-expr-16 '(* (* (malloc (ptr c (array 0 int)))) = (* (malloc int) = (3 : int))))
;;; H and D are both paramterized
;; (define (simulation old-H t)
;;   (match (judgment-holds
;;           (⊢^ ≻ (() ,t) (ee τ)) (ee τ))
;;     [(list (list erased-term erased-type))
;;      (match (list
;;              (apply-reduction-relation
;;               (---> 'u)
;;               (term (,old-H ,t)))
;;              (apply-reduction-relation*
;;               --->^
;;               #:all? #t
;;               ;; the number is arbitraily chosen
;;               ;; should take a constant amount of reductions
;;               ;; 4 is a good estimate
;;               ;; if 4 is not enough we can bump it up
;;               #:stop-when (mk-stop-when 4)
;;               (term (,(erase-heap old-H) ,erased-term))))

;;        [(list (list (list H e)) erased-configs)
;;         ;; (print erased-configs)
;;         ;; (print "before")
;;         ;; (print e)

;;         ;; note: e might be Null
;;         (let ((ee_0 (if (expr? e)
;;                      (first (judgment-holds
;;                              (⊢^ ≻ (() ,e) (ee_0 _)) ee_0))
;;                      e)))
;;           ;; (print erased-configs)
;;           ;; (print ee_0)
;;           ;; (print (erase-heap H))
;;           (ormap (match-lambda [(list eH ee)
;;                                 ;; (print ee)
;;                                 ;; (print eH)
;;                                 ;; (if (not (equal? ee ee_0))
;;                                 ;;     (print ee)
;;                                 ;;     (print ee_0))
;;                                 (and (equal?
;;                                       ee
;;                                       ee_0)
;;                                      (equal? (erase-heap H) eH))])
;;                  ;; one step in the source language might correspond to zero step in the target
;;                  `((,(erase-heap old-H) ,erased-term) ,@erased-configs)))
;;         ]
;;        ['(() ()) 'stuck]
;;        [x x]
;;        )
;;      ;; (list erased-term erased-type)
;;      ]
;;     ['() 'not-well-typed]
;;     [_ 'ambiguous-type ]))



;; (apply-reduction-relation*
;;  --->^
;;  (term (()
;;         (* ( (enull (malloc 3 (array int))) + (ebounds 3 (0 : int))) = (5 : int))))
;;  #:stop-when (mk-stop-when 10)
;;  #:all? #t)

(define (sizeof t)
  ;; caveat: sizeof judgment does not work for array 0
  ;; (-> type? natural?)
  (let ([mb-sz (judgment-holds (⊢^ sizeof (,(*D*) ,t) n) n)])
    ;; (print mb-sz)
    (if (null? mb-sz)
        0
        (first mb-sz))))

;;; a simple heap generator which creates heaps that include int or array int
;;; the heap has size sz
;;; gen: : generator
;;; gen- : ordinary function


;;; this could be made more sophisticated
;;; instead of generating a list of types, we can generate a list of generators
;;; e.g. suppose the heap looks like

;; (define (gen:heap-types sz)
;;   (if (equal? sz 0)
;;       (gen:const '())
;;       (gen:bind
;;        ;; never malloc empty
;;        (if (equal? sz 1)
;;            (gen:const 1)
;;            (gen:integer-in 1 sz))
;;        (lambda (sz-0)
;;          (gen:bind
;;           (gen:word-type sz-0)
;;           (lambda (ty)
;;             (gen:bind
;;              (gen:heap-types (- sz sz-0))
;;              (lambda (tys)
;;                (gen:const (cons ty tys))))))))))


;; (define (gen:list-n g n)
;;   (if (equal? n 0)
;;       (gen:const '())
;;       (gen:bind
;;        (gen:list-n g (- n 1))
;;        (lambda (xs)
;;          (gen:bind
;;           g
;;           (lambda (x)
;;             (gen:const (cons x xs))))))))

;; (define/contract (gen-heap heap-types)
;;   (-> (listof type?) gen?)
;;   (let ([heap-sz (for/sum ([tp heap-types]) (sizeof tp))])
;;     (gen:list-n
;;      ;; keep the integer literals close to the range of heap-sz
;;      ;; so there is a high chance of hitting a memory location
;;      ;; while dereferencing
;;      ;; this will make heap corruption more likely to happen
;;      (gen:map (gen:integer-in 0 (* 2 heap-sz))
;;               (lambda (x) `(,x : int)))
;;      heap-sz)
;;     ;; (for/fold ([heap '()]
;;     ;;            #:result (reverse heap)))
;;     ))

(define gen:mode
  (gen:one-of '(c u)))

;;; this function is used to get an integer that's slightly
;;; larger than the heap size so the values don't get too far
;;; from the maximum
(define (slightly-bigger heap-sz)
  (+ heap-sz (ceiling (/ heap-sz 5)) 20))

(define (gen:type type-sz H G)
  (gen:frequency
   (cat-maybes
           `((,type-sz . ,(gen:word-type (sub1 type-sz) H G))
             ;; struct base case
             ,(gen:array-type type-sz H G)))))


;;; don't -1 when calling gen:type
(define (gen:word-type type-sz H G)
  (let ([heap-sz (length H)])
    (gen:frequency (cat-maybes `(,(gen:ptr type-sz H G)

                      ;; (5 . ,(gen:const `(ptr c int)))
                      ;; (5 . ,(gen:let
                      ;;        ([i (gen:integer-in
                      ;;             0
                      ;;             (slightly-bigger heap-sz))]
                      ;;         [m gen:mode])
                      ;;        `(ptr c (array ,i int))) )
                      (1 . ,(gen:const `int)))))))

(define (gen:ptr type-sz H G)
  (if (= type-sz 0)
      #f
      (cons type-sz
            (gen:let ([ty (gen:type type-sz H G)]
                      [m gen:mode])
                     `(ptr ,m ,ty)))))


(define (gen:array-type type-sz H G)
  (if (zero? type-sz)
      #f
      (cons type-sz
            (gen:let
             ([n (gen:integer-in 0 (slightly-bigger (length H)))]
              [ty (gen:word-type (sub1 type-sz) H G)])
             `(array ,n ,ty)))))


;; (define (gen:int-heap sz)
;;   (let ((g (gen:integer-in 0 (* sz 2))))
;;     (gen:list-n
;;      (gen:map
;;       g
;;       (lambda (x) `(,x : int)))
;;      sz)))


;;; using parameter as if it is a reader monad
;;; 'u 'c 'w. the last mode trusts the annotations
;; (define generator-mode (make-parameter 'w))


(define (gen:expr mode expr-sz H G ty)
  (let ((heap-sz (length H)))
    (if (equal? expr-sz 0)
        ;; base case
        (gen:int-base mode heap-sz G ty)

        ;; inductive cases
        ;; bug of rackcheck. needs more than 1
        (gen:frequency
         (cat-maybes
          `((1 . ,(gen:int-base mode heap-sz G ty))
            ,(gen:binopint mode expr-sz H G ty)
            ,(gen:unchecked mode expr-sz H G ty)
            ,(gen:cast mode expr-sz H G ty)
            ,(gen:deref mode expr-sz H G ty)
            ,(gen:index mode expr-sz H G ty)
            ,(gen:amper mode expr-sz H G ty)
            ,(gen:assign mode expr-sz H G ty)
            ,(gen:indassign mode expr-sz H G ty)
            ,(gen:let-expr mode expr-sz H G ty)
            ))))))

(define (gen:let-expr mode expr-sz H G ty)
  (cons expr-sz
        ;; fix the type size to be 4
        (gen:let ([ty′ (gen:word-type 4 H G)]
             [e1 (gen:expr mode (sub1 expr-sz) H G ty′)]
             ;; TODO. how should binders be generated?
             [x (gen:map (gen:integer-in 0 10)
                         (λ (i) (string->symbol (string-append "x_" (number->string i)))))]
             [e2 (gen:expr mode (sub1 expr-sz) H (cons `(,x : ,ty′) G)
                           ty)])
                 `(let ,x = ,e1 in ,e2))))

(define (gen:cast mode expr-sz H G ty)
  ;; TODO: what size should the gen-type take?
  (if (and (equal? mode 'c) (checked-ptr-type? ty))
      #f
      (cons expr-sz
            (gen:let [(ty′ (gen:word-type 2 H G))
                      (e (gen:expr mode (sub1 expr-sz) H G ty′))]
                     (list 'cast ty e)))))

(define (gen:deref mode expr-sz H G ty)
  (cons expr-sz
        (gen:let ([n (gen:integer-in 0 (slightly-bigger (length H)))]
                  [omega-ty (gen:one-of (list `(array ,n ,ty) ty))]
                  [m (if (equal? mode 'c)
                         (gen:const 'c)
                         (gen:one-of '(c u)))]
                  [e (gen:expr mode (sub1 expr-sz) H G `(ptr ,m ,omega-ty))])
                 `(* ,e))))


(define (gen:index mode expr-sz H G ty)
  (cons expr-sz
        (gen:let ([n (gen:integer-in 0 (slightly-bigger (length H)))]
                  ;; [omega-ty (gen:one-of (list `(array ,n ,ty) ty))]
                  [m (if (equal? mode 'c)
                         (gen:const 'c)
                         (gen:one-of '(c u)))]
                  [e1 (gen:expr mode (sub1 expr-sz) H G `(ptr ,m (array ,n ,ty)))]
                  [e2 (gen:expr mode (sub1 expr-sz) H G 'int)])
                 `(* (,e1 + ,e2)))))

(define (gen:binopint mode expr-sz H G ty)
  (let ([expr-sz′ (sub1 expr-sz)])
    (match ty
      ['int (cons expr-sz
                  (gen:let ([e0 (gen:expr mode expr-sz′ H G 'int)]
                       [e1 (gen:expr mode expr-sz′ H G 'int)])
                      (list e0 '+ e1)))]
      [_ #f])))

(define (gen:assign mode expr-sz H G ty)
  (cons expr-sz
        (gen:let ([n (gen:integer-in 0 (slightly-bigger (length H)))]
                  [omega-ty (gen:one-of (list `(array ,n ,ty) ty))]
                  [m (if (equal? mode 'c)
                         (gen:const 'c)
                         (gen:one-of '(c u)))]
                  [e1 (gen:expr mode (sub1 expr-sz) H G `(ptr ,m ,omega-ty))]
                  [e2 (gen:expr mode (sub1 expr-sz) H G ty)])
                 `(* ,e1 = ,e2))))

(define (gen:indassign mode expr-sz H G ty)
  (cons expr-sz
        (gen:let ([n (gen:integer-in 0 (slightly-bigger (length H)))]
                  [omega-ty (gen:const `(array ,n ,ty))]
                  [m (if (equal? mode 'c)
                         (gen:const 'c)
                         (gen:one-of '(c u)))]
                  [e1 (gen:expr mode (sub1 expr-sz) H G `(ptr ,m ,omega-ty))]
                  [e2 (gen:expr mode (sub1 expr-sz) H G 'int)]
                  [e3 (gen:expr mode (sub1 expr-sz) H G ty)])
                 `(* (,e1 + ,e2) = ,e3))))

(define (gen:unchecked mode expr-sz H G ty)
  ;; unchecked is a no-op so we don't really want that
  (if (not (equal? mode 'u))
      (cons (ceiling (/ expr-sz 10))
            ;; would fail if we surround the entire then branch in parameterize
            ;; might be a bug of rackcheck
            (gen:map (gen:expr (if (equal? mode 'c) 'u mode)  (sub1 expr-sz) H G ty)
                     (λ (e) (list 'unchecked e))))
      #f))


;;; removes #f from the list
(define/contract (cat-maybes xs)
  (-> any/c (non-empty-listof any/c))
  (filter values xs))

(define (gen:int-base mode heap-sz G ty)
;; (print (gen:literal heap-sz ty))
;;    (print "before")
;;    (print (gen:malloc  ty))
;;    (print "after")
  (gen:frequency

       (cat-maybes
        (list (gen:literal mode heap-sz ty)
              (gen:malloc ty)
              (gen:var G ty)))))

(define (gen:var G ty)
  (let ([G
         (for/fold ([xs '()]
                    [seen (set)]
                    #:result xs)
                   ([var-type G])
           (match var-type
             [`(,x : ,ty′)
              (values
               (if (and (not (set-member? seen x))
                        (equal? ty ty′ ) )
                   (cons x xs)
                   xs)
               (set-add seen x))]))])
    (if (null? G)
        #f
        ;; make it more unlikely for let to go wasted
        (cons 4 (gen:one-of G)))))

(define/match (gen:malloc ty)
  [(`(ptr c ,omega-ty))
   (if (zero? (sizeof omega-ty))
       #f
       `(1 . ,(gen:const `(malloc ,omega-ty))))]
  [(_) #f])

;; (define (gen:integer-in-eq lo hi)
;;   (if (= lo hi)
;;       (gen:const lo)
;;       (gen:integer-in lo hi)))


;;; not really necessary to examine the heap
;;; fix this only if coverage is bad
(define (gen:literal mode heap-sz ty)
  ;; (print "before")
  ;; (print heap-sz)
  (if (equal? mode 'w)
      (cons 1 (gen:let
        ([i (gen:integer-in 0 (slightly-bigger heap-sz))])
        (list i ': ty)))
      ;; don't generate literals unless the mode is 'w
      (if (or (equal? ty 'int)
              (unchecked-ptr-type? ty)
              (empty-array-ptr-type? ty))
          (cons 1 (gen:let
                   ([i (gen:integer-in 0 (slightly-bigger heap-sz))])
                   (list i ': ty)))
          (cons 1 (gen:const (list 0 ': ty)))
          )))


(define (gen:amper mode expr-sz H G ty)
  (match ty
    [`(ptr ,m0 ,omega-ty)
     (if (or (equal? mode 'w) (equal? m0 mode))
         (let ([candidates (massage-D (*D*) omega-ty)])
           (and (pair? candidates)     ;; use pair? to check if list is non-empty
                (cons expr-sz (gen:let
                               (;; [m (if (equal? (generator-mode) 'w)
                                ;;        gen:mode
                                ;;        (gen:const (generator-mode)))]
                                [candidate (gen:one-of candidates)]  ; (T f)
                                [e (gen:expr mode (sub1 expr-sz) H G `(ptr ,m0 (struct ,(first candidate))))])
                               `(& ,e → ,(second candidate))))))
         #f)]
    [_ #f]))

;;; ((T fs) ...)
;;; pushing T into fs so we end up with (T τ f)
(define (massage-D D ty)
  (append-map (match-lambda
         [(list T fs)
          (filter-map
           (match-lambda
             [(list τ f)
              (and
               (equal? τ ty)
               (list T f))])
               fs)])
              D))


(module+ test



  ;; desperation/debug tests
  (test-match CoreChkC^ er (term ϵ))
  (test-match CoreChkC^ ε (term Bounds))
  (test-match CoreChkC^ ee (term 1))
  (test-match CoreChkC^ ee (term (1 + 1)))
  (test-match CoreChkC^ (eH ee) (term (()  2)))
  (test-match CoreChkC^ (eH ee) (term (()  (1 + 1))))
  (test-match CoreChkC^ (eH ee) (term (()  (ebounds 3 4))))
  (test-match CoreChkC^ er (term Bounds))
  (test-match CoreChkC^ ee (term (* (enull (ebounds-0 3 (enull (malloc 3)))) = 5)))
  (test-match CoreChkC^ er (term 7 ))
  (test-match CoreChkC^ (eH er) (term (()  7 )))

  (test-judgment-holds (⊢^ ↝^S ((7) (* 1)) ((7) 7)))
  (test-judgment-holds (⊢^  eheap-update ((7) 1 11) (11)))

  ;; two base cases
  (test--> (~~>^ 'C)
           (term (() (ebounds 3 2)))
           (term (() 2)))
  (test--> (~~>^ 'C)
           (term (() (ebounds 2 2)))
           (term (() Bounds)))

  (test--> (~~>^ 'C)
           (term (() (enull 0)))
           (term (() Null)))


  (test--> (--->^ 'C)
           (term (() (ebounds 3 2)))
           (term (() 2)))
  (test--> (--->^ 'C)
           (term (() (ebounds 2 2)))
           (term (() Bounds)))

  ;; eE-BinOp
  (test--> (~~>^ 'S)
           (term (() (3 + 4)))
           (term (() 7)))
  (test--> (~~>^ 'S)
           (term (() (3 + 7)))
           (term (() 10)))


  ;; eE-Deref
  (test--> (~~>^ 'S)
           (term ((7) (* 1)))
           (term ((7) 7)))


  ;; eE-Assign
  (test--> (~~>^ 'S)
           (term ((7) (* 1 = 2)))
           (term ((2) 2)))

  (test--> (~~>^ 'S)
           (term ((7) (malloc 1)))
           (term ((7 0) 2)))

  (test--> (~~>^ 'S)
           (term ((7) (malloc 4)))
           (term ((7 0 0 0 0) 2)))

  ;; eE-Malloc
  (test--> (~~>^ 'S)
           (term (() (malloc 1)))
           (term ((0) 1)))
  (test--> (~~>^ 'S)
           (term (() (malloc 3)))
           (term ((0 0 0)
                  1)))

  (test--> (~~>^ 'S)                       ;
           (term (() (malloc 2)))
           (term ((0 0) 1 )))

  ;; eE-Let
  (test--> (~~>^ 'S)
           (term (() (let x = 5 in x)))
           (term (() 5)))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; ⟶^
  (test-->>
   (--->^ 'S)
   (term (()
          (let p = (malloc 3) in
               (let _ = (* 1 = 6) in
                    (let _ = (* 2 = 7) in
                         (let _ = (* 3 = 8) in
                              p))))))
   (term ((6 7 8)
          1)))


  (test-->>
   --->^^ 
   (term (()
          (* (enull (ebounds-0 3 (enull (malloc 3)))) = 5)))
   (term ((5 0 0)
          5)))

  (test-->>∃
   (--->^ 'C)
   (term (()
          (* (enull (ebounds 3 2)))))
   (term (()
          (* (enull 2)))))



  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Subst
  (test-judgment-holds (⊢^ esubst (x x 0) 0))
  (test-judgment-holds (⊢^ esubst (y x 0) y))
  (test-judgment-holds (⊢^ esubst ((let x = x in x) x 0)
                          (let x = 0 in x)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Heaps
  ;; Heaps are represented as a list addressed by position counting from 1.
  ;; Allocation appends elements at the end of the list.
  (test-judgment-holds (⊢^ eheap-lookup ((7) 1) 7))
  (test-judgment-holds (⊢^ eheap-lookup ((4 7) 1) 4))
  (test-judgment-holds (⊢^ eheap-lookup ((4 7) 2) 7))

  (test-equal (judgment-holds (⊢^ eheap-defined? ((7) 0) #t)) #f)
  (test-judgment-holds (⊢^ eheap-defined? ((7) 1) #t))
  (test-equal (judgment-holds (⊢^ eheap-defined? ((7) 2) #t)) #f)
  (test-judgment-holds (⊢^ eheap-defined? ((4 7) 2) #t))
  (test-equal (judgment-holds (⊢^ eheap-defined? ((4 7) 3) #t)) #f)

  (test-judgment-holds (⊢^ eheap-update ((7) 1 9) (9)))
  (test-judgment-holds (⊢^ eheap-update ((4 7) 1 9)
                          (9 7)))
  (test-judgment-holds (⊢^ eheap-update ((4 7) 2 9)
                          (4 9)))


  (test-judgment-holds (⊢^ eerase-H ((4 : int) (7 : int)) (4 7)))
  (test-judgment-holds (⊢^ eerase-H ((4 : int) (7 : int)) eH))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Type-Based Compilation
  (parameterize ((*D* (term ((foo ((int x) (int y)))))))
    (test-judgment-holds (⊢^ ≻ (((x : int)) x) (x int)))
    (test-judgment-holds (⊢^ ≻ (() (5 : int)) (5 int)))

    (test-judgment-holds (⊢^ ≻ (() (let x = (5 : int) in x)) ((let x = 5 in x) int)))

    (test-judgment-holds (⊢^ ≻ (() (0 : int)) (0 int)))

    (test-judgment-holds (⊢^ ≻ (() (4 : int)) (4 int)))
    (test-judgment-holds (⊢^ ≻ (() (0 : (ptr c int))) (0 (ptr c int))))

    (test-judgment-holds (⊢^ ≻ (() (1 : (ptr c (array 0 int))))
                             (1 (ptr c (array 0 int)))))

    (test-judgment-holds (⊢^ ≻ (() (1 : (ptr u (array 5 int))))
                             (1 (ptr u (array 5 int)))))

    (test-equal (judgment-holds (⊢^ ≻ (() (1 : (ptr c (array 5 int)))) τ) τ)
                '())

    ;; passes only when wrapped around by parameterize!
    (test-judgment-holds (⊢^ ≻ (() (1 : (ptr c int))) (1 (ptr c int))))

    (test-judgment-holds (⊢^ ≻ (() (malloc (struct foo)))
                             ((malloc 2) (ptr c (struct foo)))))
    
    (test-judgment-holds (⊢^ ≻ (() (& (malloc (struct foo)) → x))
                             (((enull (malloc 2)) + 0) (ptr c int))))

    (test-judgment-holds (⊢^ ≻ (() (& (malloc (struct foo)) → y))
                             (((enull (malloc 2)) + 1) (ptr c int))))

    (test-judgment-holds (⊢^ ≻ (() ((1 : int) + (2 : int))) ((1 + 2) int)))

    (test-judgment-holds (⊢^ ≻ (() (malloc int)) ((malloc 1) (ptr c int))))
    (test-equal (judgment-holds (⊢ ty (() () c (malloc (array 0 int))) τ) τ)
                '())

    (test-judgment-holds (⊢^ ≻ (() (cast int (0 : (ptr c (array 5 int)))))
                             (0 int)))
    (test-judgment-holds ; unchecked cast to ptr type succeeds
     (⊢^ ≻ (() (cast (ptr u int) (5 : int))) (5 (ptr u int))))

    (test-equal (judgment-holds ; checked cast to ptr type fails
                 (⊢^ ≻ (() (cast (ptr c int) (5 : int))) τ) τ)
                '())

    (test-judgment-holds ; unchecking checked cast
     (⊢^ ≻ (() (unchecked (cast (ptr c int) (5 : int)))) (5 (ptr c int))))

    ;; deref
    (test-judgment-holds ; could be optimized
     (⊢^ ≻ (() (* (malloc (array 3 int))))
         ((* (ebounds-0 3 (enull (malloc 3) ))) int)))

    (test-judgment-holds
     (⊢^ ≻ (() (* ((malloc (array 3 int)) + (1 : int))))
         ((* (enull ((enull (malloc 3)) + (ebounds 3 1)))) int)))

    (test-judgment-holds
     (⊢^ ≻ (() (* (malloc (array 3 int)) = (5 : int)))
         ((* (ebounds-0 3 (enull (malloc 3)) ) = 5) int)))

    (test-judgment-holds
     (⊢^ ≻ (() (* ((malloc (array 3 int)) + (1 : int)) = (5 : int)))
         ((* (enull ((enull (malloc 3))  + (ebounds 3 1))) = 5) int))))


  ;; simulation
  (parameterize ([*D* (term ((foo ((int x) (int y)))
                             (bar ((int z)))))]
                 [*H* (term ())])
    ;; seed: 548098816
    (let ([mode 'w])
      (check-property
       (make-config
        #:tests 1000
        #:seed 1885204480
        ;; #:seed 416654848
        #:deadline (+ (current-inexact-milliseconds) (* 200 1000)))
       ;; shrinking won't terminate unless we disable it explicitly
       (property ([sz (gen:no-shrink (gen:integer-in 0 4))]
                  [ty-sz (gen:no-shrink (gen:integer-in 0 3))]
                  [ty (gen:no-shrink (gen:word-type ty-sz '() '()))]
                  [e (gen:no-shrink (gen:expr mode sz '() '() ty))])
                 (check-match (judgment-holds (⊢^ ≻ (() ,e) (ee τ)) (ee τ))
                              (list (list (? erased-expr?) (? type?) )))
                 (check-true (simulation (*H*) e))))))


  ;; checking that our generator only generates well-typed terms
  (parameterize ([*D* (term ((foo ((int x) (int y)))
                                          (bar ((int z)))))]
                 [*H* (term ())])
    (let ([mode 'c])
      (check-property
       (make-config
        #:tests 1000
        #:deadline (+ (current-inexact-milliseconds) (* 200 1000)))
       ;; shrinking won't terminate unless we disable it explicitly
       (property ([sz (gen:no-shrink (gen:integer-in 0 4))]
                  [ty-sz (gen:no-shrink (gen:integer-in 0 3))]
                  [ty (gen:no-shrink (gen:word-type ty-sz '() '()))]
                  [e (gen:no-shrink (gen:expr mode sz '() '() ty))])
                 (check-match (judgment-holds (⊢ ty (() () ,mode ,e) τ) τ)
                              (list (? type?) ))))))


  ;; progress
  (parameterize ([*D* (term ((foo ((int x) (int y)))
                                          (bar ((int z)))))]
                 [*H* (term ())])
    (let ([mode 'c])
      (check-property
       (make-config
        #:tests 1000
        #:deadline (+ (current-inexact-milliseconds) (* 200 1000)))
       
       ;; shrinking won't terminate unless we disable it explicitly
       (property ([sz (gen:no-shrink (gen:integer-in 0 4))]
                  [ty-sz (gen:no-shrink (gen:integer-in 0 3))]
                  [ty (gen:no-shrink (gen:word-type ty-sz '() '()))]
                  [e (gen:no-shrink (gen:expr mode sz '() '() ty))])
                 (label! (if (value? e)
                             "value"
                             "non-value"))
                 (when (not (or (value? e) (has-unchecked-redex? e)))
                   (check-match
                    (apply-reduction-relation
                     (---> 'c)
                     (term (,(*H*) ,e)))
                    (list e0 e1 ...)))))))
  )
