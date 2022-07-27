#lang racket
(require rackunit)
(provide (all-defined-out))
(require redex/reduction-semantics)
;; (require racket/control)

(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *D* (make-parameter (term ()))) ; struct table
(define *Hs* (make-parameter (term ()))) ; global heap (for type system)
(define *Fs* (make-parameter (term ()))) ; global function definition table
(define *eF* (make-parameter (term ()))) ; global erased function definition table

(define *debug* (make-parameter (term #f))) ; debug flag

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This extends the POST model in a few ways
;; - let variable lookup that avoids substitution
;; - n-ary let
;; - null-terminated arrays that use the let lookup to update array bounds
;; - standard conditional form that can be used to safely check terminator
;; - function pointers and calls


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax

(define-language CoreChkC+
  (m ::= c t u)
  (τ ::= int (ptr m ω))
  (ω ::= τ (struct T)
     (array le he τ)
     (ntarray le he τ)
     ;; NEW:
     (fun (x ...) τ (τ ...)))

  ;; NEW
  ;; normalized types
  (vτ ::= int (ptr m vω))
  (vω ::= vτ (struct T)
     (array l h vτ)
     (ntarray l h vτ)
     ;; NEw:
     (fun (x ...) τ (τ ...)))

  (e ::= (n : τ) x (let x = e in e) (malloc m ω) (cast τ e)
     (e + e) (& e → f) (* e) (* e = e)
     ;; NEW checked expr
     (unchecked (x ...) e) (checked (x ...) e)
     (if e e e)
     (strlen e)
     (dyn-bound-cast τ e)
     (call e e ...))

  ;; erased expressions
  (ee ::=  i eS)

  ;; NEW:
  (le he ::= l ls)
  (ls hs ::= (x + l))

  ;;NEW functions
  (Fs ::= (F F))
  (F ::= ((defun ((x : τ) ... e) : τ) ...))

  (n k ::= natural)
  (l h i ::= integer)
  (D ((T fs) ...))
  (fs ((vτ f) (vτ f) ...))
  (x eff f T ::= variable-not-otherwise-mentioned)

  (Hs ::= (H H))
  (H ::= ((n : vτ) ...))

  (eHs ::= (eH eH))
  (eH ::= (n ...))
  (eFs ::= (eF eF))
  (eF ::= ((defun ee x ... ee) ...))
  ;;NEW functions
  (r ::= e ε)
  (er ::= ee ε)
  (ε ::= Null Bounds)
  (E ::= hole (let x = E in e) (let x = (n : vτ) in E) (E + e) ((n : vτ) + E)
     (& E → f) (dyn-bound-cast Eτ e) (dyn-bound-cast vτ E) (cast Eτ e) (cast vτ E) (* E) (* E = e) (* (n : vτ) = E)
     (unchecked (x ...) E) (checked (x ...) E)
     (if E e e)
     (strlen E)
     (malloc m Eω)
     (n : Eτ)
     ;;New for functions
     (call E e ...)
     (call (n : vτ) (n : vτ) ... E e ...))

  (Eω ::= (array hole he τ)
       (array l hole τ)
       (array l h Eτ)
       (ntarray hole he τ)
       (ntarray l hole τ)
       (ntarray l h Eτ)
       Eτ)

  (Eτ ::= (ptr m Eω))

  ;; A Potential Redex (pr) is a term of the form matching the
  ;; premises of the ⊢→ basic reduction relation.
  (pr ::=
      (let x = (n : vτ) in (in-hole E (x + i)))
      (let x = (n : vτ) in (in-hole E (strlen x)))
      (let x = (n : vτ) in (n_2 : vτ_2))
      (let x = (n : vτ) in (in-hole E x))
      (let x = (n : vτ) in (in-hole E (* x)))
      (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x)))
      (* (n : vτ))
      (* (n : vτ) = (n_1 : vτ_1))
      (strlen (n : vτ))
      (call (n_1 : vτ_1) (n_args : vτ_args) ...)
      (dyn-bound-cast vτ (n : vτ_′))
      ((n_1 : vτ_1) + (n_2 : vτ_2))
      (cast vτ (n : vτ_′))
      (& (n : vτ) → f_i)
      (malloc m vω)
      (unchecked (x ...) (n : vτ))
      ;; NEW checked expr
      (checked (x ...) (n : vτ))
      (if (n : vτ) e_1 e_2))

 ;; result
  (eE ::= hole
      (eE + ee) (i + eE)
      (x = eE)
      (eE - ee) (i - eE)
      (star-l eE) (star-r eE)
      (star-l eE = ee) (star-r eE)
      (star-l i = eE) (star-r i = eE)
      (eE <=? ee)
      (i <=? eE)
      (if eE ee ee)
      (strlen eE)
      (let x = eE in ee)
      (let x = i in eE)

      ;;New for functions
      (call eE ee ...)
      (call ee ee ... eE ee ...))


  ;; erased serious terms
 (eS ::= x (malloc-l ee) (malloc-r ee)
      (ee + ee) (ee - ee)
      (star-l ee) (star-r ee)
      (star-l ee = ee) (star-r ee = ee)
      (x = ee)
      (ee <=? ee)
      (if ee ee ee)
      (let x = ee in ee)
      (strlen-l ee) (strlen-r ee)
      (call-l ee ee ...)
      (call-r ee ee ...)
      ;; exceptions
      (enull) (ebounds))


;; TODO: star-l and star-r
  (eK ::= hole
      pop
      (malloc-l [])
      (malloc-r [])
      ([] + ee) (i + [])
      (x = [])
      ([] - ee) (i - [])
      (star-l []) (star-r [])
      (star-l [] = ee) (star-r [] = ee)
      (star-l i = []) (star-r i = [])
      ([] <=? ee)
      (i <=? [])
      (if [] ee ee)
      (strlen-l [])
      (strlen-r [])
      (let x = [] in ee)
      ;;New for functions
      (call-l [] ee ...)
      (call-l ee ee ... [] ee ...)
      (call-r [] ee ...)
      (call-r ee ee ... [] ee ...))


  (eΣ ::= ((x_!_0 i_0) ...))

  ;; auxiliary type for compilation
  (cE ::= (compatible-closure-context ee))



  ;; static
  (Γ ::= ((x = maybe-e : τ) ...))
  (maybe-e ::= e none)
  (σ ::= ((n : τ) ...))

  ;; map from a checked array to the variable that stores its upper bound
  (ρ ::= ((x_!_0 (x_!_1 x_!_2)) ...))

  ;; only as a helper
  ;; (boolean ::= #t #f)

  #:binding-forms
  (let x = ee in ee_body #:refers-to x)
  (let x = e in e_body #:refers-to x)
  ; ':' can't appear twice. yet another redex bug?
  ; modified to allow let*-like behavior
  (defun ((x : τ) #:...bind (args x (shadow args x)) e_body #:refers-to args) _ τ_res #:refers-to args)
  (defun x ... ee #:refers-to (shadow x ...))
  (eH ((x i) ...) ee #:refers-to (shadow x ...) eH))

(default-language CoreChkC+)


(define ~~>
  (reduction-relation
   CoreChkC+ #:domain (Hs r)
   (--> (Hs e) (Hs_′ r_′) (judgment-holds (⊢↝ (Hs e) (Hs_′ r_′))))))

(define (---> m) ;; top
  (reduction-relation
   CoreChkC+
   #:domain (Hs r)
   (--> (Hs e) (Hs_′ r)
        (judgment-holds (⊢⟶ (Hs e ,m) (Hs_′ r))))))

(define --->cu
  (reduction-relation
   CoreChkC+
   #:domain (Hs r)
   (-->
    (Hs (in-hole E pr))
    (Hs_′ (in-hole E e_′))
    (judgment-holds (⊢↝/name (Hs pr) (Hs_′ e_′ any_name)))
    (computed-name (term any_name)))

   (-->
    (Hs (in-hole E pr))
    (Hs_′ ε)
    (judgment-holds (⊢↝/name (Hs pr) (Hs_′ ε any_name)))
    (computed-name (term any_name)))))

(define-judgment-form CoreChkC+
  #:contract (⊢↝/name (Hs e) (Hs r any))
  #:mode     (⊢↝/name I O)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; New rules

  [(⊢↝/name (Hs (let x = (n_0 : vτ_0) in (in-hole E (x + i_0))))
       (Hs (let x = (n_0 : vτ_0) in (in-hole E i_1))
          E-VarTy))
   (where i_1 ,(+ (term n_0) (term i_0)))
   E-VarTy]

  [(⊢↝/name (Hs (let x = (n_0 : vτ_0)  in (n_2 : vτ_2))) (Hs (n_2 : vτ_2) E-Let))
   E-Let]

  [(⊢↝/name (Hs (let x = (n : vτ) in (name e (in-hole E x)))) (Hs (let x = (n : vτ) in (in-hole E (n : vτ))) E-VarNonNT))
   (where #t (⊢non-nt-deref-or-strlen? vτ e))
   E-VarNonNT]

  [(⊢↝/name (Hs (let x = (n : vτ_1) in (in-hole E (* x)))) (Hs (let x = (n : vτ_2) in (in-hole E (n_′ : vτ_′))) E-VarNT-Incr))
   (where (ptr m _) vτ_1)
   (where H (⊢heap-by-mode Hs m))
   (where (n_′ : vτ_′) (⊢heap-lookup H n))
   (where #f ,(zero? (term n_′)))
   (where vτ_2 (⊢nt-incr vτ_1))
   E-VarNT-Incr]

  [(⊢↝/name (Hs (let x = (n : vτ_1) in (in-hole E (* x)))) (Hs (let x = (n : vτ_1) in (in-hole E (* (n : vτ_1)))) E-VarNT-Sub))
   (where (ptr m _) vτ_1)
   (where H (⊢heap-by-mode Hs m))
   (side-condition ,(let ([i (term (⊢heap-lookup H n))])
                      (or (not i)
                          (zero? (first i)))))
   E-VarNT-Sub]

  ;; this are just like their array counterparts
  [(⊢↝/name (Hs (* (n : vτ))) (Hs Bounds X-NTDerefOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   X-NTDerefOOB]

  [(⊢↝/name (Hs (* (n : vτ) = (n_1 : vτ_1))) (Hs Bounds X-NTAssignOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-NTAssignOOB]

  [(⊢↝/name (Hs ((0 : vτ) + (n : vτ_′))) (Hs Null X-BinopNTNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   X-BinopNTNull]

  ;; file a bug report on microsoft/checkedc?
  [(⊢↝/name (Hs (strlen (0 : vτ))) (Hs Null X-StrNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   X-StrNull]

  [(⊢↝/name (Hs (strlen (n : vτ))) (Hs Bounds X-StrOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   X-StrOOB]

  [(⊢↝/name (Hs (strlen (n : vτ))) (Hs (n_1 : int) E-Str))
   (where (ptr m (ntarray l h vτ_1)) vτ)
   (where H (⊢heap-by-mode Hs m))
   (where n_1 (⊢strlen n H))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   E-Str]

  [(⊢↝/name (Hs (call (n_1 : vτ_1) (n_args : vτ_args) ..._1))  (Hs (⊢build-call-stack e (x (n_args : vτ_args)) ...) E-Fun))
   (where (ptr m (fun _ _ _)) vτ_1) 
   (where (defun ((x : τ_2′) ..._1 e) : τ) (⊢fun-lookup (⊢fheap-by-mode m) n_1)) ;; defun no vτ_1
   E-Fun]

  [(⊢↝/name (Hs (dyn-bound-cast vτ (n : vτ_′))) (Hs (n : vτ_′) E-DynCast)) ;; note that the annotation does not change
   (where #t (⊢bounds-within vτ vτ_′)) ;; only need the ntarray/array subsumption cases
   E-DynCast]

  [(⊢↝/name (Hs (dyn-bound-cast vτ (n : vτ_′))) (Hs Bounds X-DynCast))
   (where #f (⊢bounds-within vτ vτ_′))
   X-DynCast]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Old rules
  [(⊢↝/name (Hs ((n_1 : vτ_1) + (n_2 : vτ_2))) (Hs (n_3 : vτ_3) E-Binop))
   (where n_3 ,(+ (term n_1) (term n_2)))
   (where vτ_3 (⊢binop-type vτ_1 n_1 n_2))
   E-Binop]

  [(⊢↝/name (Hs (cast vτ (n : vτ_′))) (Hs (n : vτ) E-Cast))
   E-Cast]

  [(⊢↝/name (Hs (* (n : vτ))) (Hs (n_1 : vτ_1) E-Deref))
   (where #t (⊢deref-ok? vτ))
   (where (ptr m _) vτ)
   (where H (⊢heap-by-mode Hs m))
   (where (n_1 : _) (⊢heap-lookup H n))
   (where vτ_1 (⊢deref-type-dyn ,(*D*) vτ))
   E-Deref]

  ;; the type stored on the heap musn't change
  ;; the type attached to n_1 can stay as the evaluation result because it's all on the stack
  [(⊢↝/name (Hs (* (n : vτ) = (n_1 : vτ_1))) (Hs_′ (n_1 : vτ_1) E-Assign))
   (where #t (⊢assign-ok? vτ))
   (where (ptr m _) vτ)
   (where H (⊢heap-by-mode Hs m))
   (where H_′ (⊢heap-update H n n_1))
   (where Hs_′ (⊢update-heap-by-mode Hs H_′ m))
   E-Assign]

  [(⊢↝/name (Hs (& (n : vτ) → f_i)) (Hs (n_0 : vτ_0) E-Amper))
   (where (n_0 : vτ_0) (⊢& vτ f_i n))
   E-Amper]

  [(⊢↝/name (Hs (malloc m vω)) (Hs_′ (n_1 : (ptr c vω)) E-Malloc))
   (where (vτ_1 ...) (⊢types ,(*D*) vω))
   (where H (⊢heap-by-mode Hs m))
   (where ((n : vτ) ...) H)
   (where H_′ ((n : vτ) ... (0 : vτ_1) ...))
   (where Hs_′ (⊢update-heap-by-mode Hs H_′ m))
   (where n_1 ,(add1 (length (term H))))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(positive? (term (⊢sizeof vω))))
   E-Malloc]

  [(⊢↝/name (Hs (malloc m vω)) (Hs (0 : (ptr c vω)) E-MallocZero))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(not (positive? (term (⊢sizeof vω)))))
   E-MallocZero]

  [(⊢↝/name (Hs (unchecked (n : vτ))) (Hs (n : vτ) E-Unchecked))
   E-Unchecked]

  [(⊢↝/name (Hs (* (n : vτ))) (Hs Bounds X-DerefOOB))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-DerefOOB]

  [(⊢↝/name (Hs (* (n : vτ) = (n_1 : vτ_1))) (Hs Bounds X-AssignOOB))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-AssignOOB]

  [(⊢↝/name (Hs (* (0 : vτ))) (Hs Null X-DerefNull))
   (where (ptr c vω) vτ)
   X-DerefNull]

  [(⊢↝/name (Hs (* (0 : vτ) = (n_1 : vτ_′))) (Hs Null X-AssignNull))
   (where (ptr c vω) vτ)
   X-AssignNull]

  [(⊢↝/name (Hs (& (0 : vτ) → f)) (Hs Null X-AmperNull))
   (where (ptr c (struct T)) vτ)
   X-AmperNull]

  [(⊢↝/name (Hs ((0 : vτ) + (n : vτ_′))) (Hs Null X-BinopNull))
   (where (ptr c (array l h vτ_1)) vτ)
   X-BinopNull]

  [(⊢↝/name (Hs (if (n : vτ) e_1 e_2)) (Hs e_1 If-T))
   (side-condition ,(< (term 0) (term n)))
   If-T]
  [(⊢↝/name (Hs (if (n : vτ) e_1 e_2)) (Hs e_2 If-F))
   (side-condition ,(= (term 0) (term n)))
   If-F]

  [(⊢↝/name (Hs (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
       (Hs (let x = (n : (ptr c (ntarray l h_′ vτ))) in (in-hole E (n_1 : int))) E-VarNTstr))
   (where n_1 (⊢strlen n (⊢heap-by-mode Hs c)))
   (where h_′ ,(max (term h) (term n_1)))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   E-VarNTstr]

  [(⊢↝/name (Hs (let x = (0 : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
       (Hs Null E-VarNTNull))
   E-VarNTNull]

  [(⊢↝/name (Hs (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
            (Hs Bounds E-VarNTOOB))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   E-VarNTOOB])


(define-judgment-form CoreChkC+
  #:contract (⊢↝ (Hs e) (Hs r))
  #:mode     (⊢↝ I O)
  [(⊢↝ (Hs e) (Hs_′ r))
   (⊢↝/name (Hs e) (Hs_′ r any))])

(define-judgment-form CoreChkC+
  #:contract (⊢⟶ (Hs e m) (Hs r))
  #:mode     (⊢⟶ I O)
  [(where (in-hole E e_0) e) 
   (⊢↝ (Hs e_0) (Hs_′ e_0′))
   (where e_′ (in-hole E e_0′))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------ C-Exp
   (⊢⟶ (Hs e m) (Hs_′ e_′))]

  [(where (in-hole E e_0) e)
   (⊢↝ (Hs e_0) (Hs_′ ε))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------- C-Halt
   (⊢⟶ (Hs e m) (Hs_′ ε))])




(define-metafunction CoreChkC+
  ⊢join-type : Γ τ τ -> τ or #f
  [(⊢join-type Γ (ptr c (ntarray le_0 he_0 τ)) (ptr c (ntarray le_1 he_1 τ)))
   (ptr c (ntarray le_2 he_2 τ))
   (where le_0′ (⊢sub-bound Γ le_0))
   (where le_1′ (⊢sub-bound Γ le_1))
   (where he_0′ (⊢sub-bound Γ he_0))
   (where he_1′ (⊢sub-bound Γ he_1))
   (where le_2  (⊢join-lower le_0′ le_1′))
   (where he_2  (⊢join-upper he_0′ he_1′))]
  [(⊢join-type Γ (ptr c (array le_0 he_0 τ)) (ptr c (array le_1 he_1 τ)))
   (ptr c (array le_2 he_2 τ))
   (where le_0′ (⊢sub-bound Γ le_0))
   (where le_1′ (⊢sub-bound Γ le_1))
   (where he_0′ (⊢sub-bound Γ he_0))
   (where he_1′ (⊢sub-bound Γ he_1))
   (where le_2  (⊢join-lower le_0′ le_1′))
   (where he_2  (⊢join-upper he_0′ he_1′))]
  [(⊢join-type _ τ τ) τ]
  [(⊢join-type _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢join-lower : le le -> le or #f
  [(⊢join-lower (x + i_0) (x + i_1))
   (x + i_2)
   (where i_2 ,(max (term i_0) (term i_1)))]
  [(⊢join-lower i_0 i_1)
   i_2
   (where i_2 ,(max (term i_0) (term i_1)))]
  [(⊢join-lower _ _) #f])

(define-metafunction CoreChkC+
  ⊢join-upper : he he -> he or #f
  [(⊢join-upper (x + i_0) (x + i_1))
   (x + i_2)
   (where i_2 ,(min (term i_0) (term i_1)))]
  [(⊢join-upper i_0 i_1)
   i_2
   (where i_2 ,(min (term i_0) (term i_1)))]
  [(⊢join-upper _ _)
   #f])

;; only performs substitution when the definition is a constant int
(define-metafunction CoreChkC+
  ⊢sub-bound : Γ le -> le
  [(⊢sub-bound _ l) l]
  [(⊢sub-bound (_ ... (x = (i : int) : _) _ ...) (x + l))
   ,(+ (term i) (term l))]
  [(⊢sub-bound _ le) le])




;; bounds-within : to-type from-type
;; dyn-bound-cast to-type (n : from-type)
(define-metafunction CoreChkC+
  ⊢bounds-within : vτ vτ -> #t or #f
  [(⊢bounds-within (ptr c (ntarray l_1 h_1 τ_1)) (ptr c (ntarray l_2 h_2 τ_2)))
   #t
   (side-condition (and (>= (term l_1) (term l_2))
                        (<= (term h_1) (term h_2))))
   or
   #f]
  [(⊢bounds-within (ptr c (array l_1 h_1 τ_1)) (ptr c (array l_2 h_2 τ_2)))
   #t
   (side-condition (and (>= (term l_1) (term l_2))
                        (<= (term h_1) (term h_2))))
   or
   #f]
  ;; is this default case ok?
  [(⊢bounds-within _ _)
   #t])

;; once we generalize to arbitrary bound expressions
;; should take the more generalized τ instead of vτ

(define-metafunction CoreChkC+
  ⊢binop-type : τ n n -> τ or #f
  [(⊢binop-type (ptr c (array l h τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (name τ int) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m (struct T))) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m int)) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr u (ntarray l h _))) n_1 n_2) τ]

  ;;  there's a lot of repetition in these rules
  ;; can we design a helper metafunction that encapsulates the common parts?
  [(⊢binop-type (ptr c (ntarray l h τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (array (x + l) h τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (+ (term x) (term l)) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (array l (x + h) τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (+ (term x) (term h)) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (ntarray (x + l) h τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (+ (term x) (term l)) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (ntarray l (x + h) τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (+ (term x) (term h)) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (name τ (ptr u (array le he _))) n_1 n_2)   τ]
  [(⊢binop-type (name τ (ptr u (ntarray le he _))) n_1 n_2) τ]
  [(⊢binop-type _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢heap-defined? : H n vω -> #t or #f
  [(⊢heap-defined? H n (array i_0 _ _))
   ,(< 0 (+ (term n) (term i_0)) (add1 (length (term H))))]
  [(⊢heap-defined? H n (ntarray i_0 _ _))
   ,(< 0 (+ (term n) (term i_0)) (add1 (length (term H))))]
  [(⊢heap-defined? H n vω)
   ,(< 0 (term n) (add1 (length (term H))))])


(define-metafunction CoreChkC+
  ⊢update-heap-by-mode : Hs H m -> Hs
  [(⊢update-heap-by-mode Hs H c) (H ,(list-ref (term Hs) 1))]
  [(⊢update-heap-by-mode Hs H t) (,(list-ref (term Hs) 0) H)]
  [(⊢update-heap-by-mode Hs H u) (,(list-ref (term Hs) 0) H)])

(define-metafunction CoreChkC+
  ⊢heap-by-mode : Hs m -> H
  [(⊢heap-by-mode Hs c) ,(list-ref (term Hs) 0)]
  [(⊢heap-by-mode Hs t) ,(list-ref (term Hs) 1)]
  [(⊢heap-by-mode Hs u) ,(list-ref (term Hs) 1)])

(define-metafunction CoreChkC+
  ⊢fheap-by-mode : m -> F
  [(⊢fheap-by-mode c) ,(list-ref (*Fs*) 0)]
  [(⊢fheap-by-mode t) ,(list-ref (*Fs*) 1)]
  [(⊢fheap-by-mode u) ,(list-ref (*Fs*) 1)])


(define-metafunction CoreChkC+
  ⊢heap-lookup : H n -> (n : τ) or #f
  [(⊢heap-lookup H n)
   ,(and (<= (term n) (length (term H)))
         (positive? (term n))
         (list-ref (term H) (sub1 (term n))))])

;(define-metafunction CoreChkC+
;  ⊢fun-lookup : F n -> (defun e ((x : τ) ... e) : τ) or #f
;  [(⊢fun-lookup ((defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) _ ...) n)
;          (defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 )]
;  [(⊢fun-lookup (_ (defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)
;          (⊢fun-lookup ((defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)]
;  )
(define-metafunction CoreChkC+
  ⊢fun-lookup : F n -> (defun ((x : τ) ... e) : τ) or #f
  [(⊢fun-lookup F n)
   ,(and (<= (term n) (length (term F)))
         (positive? (term n))
         (list-ref (term F) (sub1 (term n))))])


(define-metafunction CoreChkC+
  ⊢efun-lookup : eF n -> (defun x ... ee) or #f
  [(⊢efun-lookup eF n)
   ,(and (<= (term n) (length (term eF)))
         (positive? (term n))
         (list-ref (term eF) (sub1 (term n))))])

(define-metafunction CoreChkC+
  ⊢eheap-lookup : eH n -> n or #f
  [(⊢eheap-lookup eH i)
   ,(and (<= (term i) (length (term eH)))
         (positive? (term i))
         (list-ref (term eH) (sub1 (term i))))])

(define-metafunction CoreChkC+
  ⊢heap-update : H n n -> H or #f
  [(⊢heap-update H n n_1)
   ,(list-set (term H) (sub1 (term n)) (term (n_1 : vτ_1)))
   (where n_H ,(length (term H)))
   (side-condition (>= (term n_H) (term n)))
   (side-condition (>= (term n) 1))
   (where (_ : vτ_1) (⊢heap-lookup H n))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢eheap-update : eH n n -> eH
  [(⊢eheap-update eH n n_1)
   ,(list-set (term eH) (sub1 (term n)) (term n_1))])

(define-metafunction CoreChkC+
  ⊢heap-from : H n vω -> H
  [(⊢heap-from H n (ntarray l _ _)) ,(drop (term H) (+ (term l) (sub1 (term n))))]
  [(⊢heap-from H n (array l _ _)) ,(drop (term H) (+ (term l) (sub1 (term n))))]
  [(⊢heap-from H n _) ,(drop (term H) (sub1 (term n)))])

(define-metafunction CoreChkC+
  ⊢struct-lookup : D T -> fs
  [(⊢struct-lookup ((T fs) _ ...) T) fs]
  [(⊢struct-lookup (_ (T_′ fs) ...) T)
   (⊢struct-lookup ((T_′ fs) ...) T)])

(define-metafunction CoreChkC+
  ⊢deref-ok? : τ -> #t or #f
  [(⊢deref-ok? int) #t]
  [(⊢deref-ok? (ptr u ω)) #t]
  [(⊢deref-ok? (ptr c τ)) #t]
  [(⊢deref-ok? (ptr c (struct T))) #t]
  [(⊢deref-ok? (ptr c (fun _ _ _))) #t]
  [(⊢deref-ok? (ptr c (array l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢deref-ok? (ptr c (ntarray l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (<= 0 (term h))))]
  [(⊢deref-ok? _) #f])

(define-metafunction CoreChkC+
  ⊢assign-ok? : τ -> #t or #f
  [(⊢assign-ok? int) #t]
  [(⊢assign-ok? (ptr u ω)) #t]
  [(⊢assign-ok? (ptr c τ)) #t]
  [(⊢assign-ok? (ptr c (struct T))) #t]
  [(⊢assign-ok? (ptr c (fun _ _ _))) #t]
  [(⊢assign-ok? (ptr c (array l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢assign-ok? (ptr c (ntarray l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢assign-ok? _) #f])

(define-metafunction CoreChkC+
  ⊢bound-le? : le le -> #t or #f
  [(⊢bound-le? l_1 l_2) #t
   (side-condition (<= (term l_1) (term l_2)))]
  [(⊢bound-le? (x + l_1) (x + l_2)) #t
   (side-condition (<= (term l_1) (term l_2)))]
  [(⊢bound-le? _ _) #f])


(define-metafunction CoreChkC+
  ⊢types : D ω -> (τ ...)
  [(⊢types D τ) (τ)]
  [(⊢types D (array l h τ))
   ,(make-list (term n) (term τ))
   (where n ,(- (term h) (term l)))
   or
   ()]
  [(⊢types D (struct T))
   (τ ...)
   (where ((τ f) ...) (⊢struct-lookup D T))]
  ;; used when malloc'ing we do one more then the length
  [(⊢types D (ntarray l h τ))
   ,(make-list (term n) (term τ))
   (where n ,( + 1 (- (term h) (term l))))
   or
   ()])

;; fixes a minor bug in paper: should be τ_0 f_0; ...; τ_k f_k, 0 <= i <= k,
;; i.e. 0-based counting, not 1-based
(define-metafunction CoreChkC+
  ⊢& : τ f n -> (n : τ) or #f
  [(⊢& (ptr m (struct T)) f_i n)
   (n_i : τ_i′)
   (where ((τ_0 f_0) ... (τ_i f_i) _ ...) (⊢struct-lookup ,(*D*) T))
   (where n_i ,(+ (term n) (length (term ((τ_0 f_0) ...)))))
   (where τ_i′ (ptr m τ_i))
   (side-condition (or (eq? (term m) 'u) (not (= 0 (term n)))))]
  [(⊢& _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢check-mode : m m -> #t or #f
  [(⊢check-mode u _) #t]
  [(⊢check-mode m m) #t]
  [(⊢check-mode _ _) #f])

;; need to include the extra cases for type-level redex
(define-metafunction CoreChkC+
  ⊢mode : E -> m
  [(⊢mode hole) c]
  [(⊢mode (unchecked E)) u]
  [(⊢mode (let x = E in e)) (⊢mode E)]
  [(⊢mode (let x = (n : vτ) in E)) (⊢mode E)]
  [(⊢mode (E + e))          (⊢mode E)]
  [(⊢mode ((n : vτ) + E))    (⊢mode E)]
  [(⊢mode (& E → f))        (⊢mode E)]
  [(⊢mode (cast τ E))       (⊢mode E)]
  [(⊢mode (dyn-bound-cast τ E))       (⊢mode E)]
  [(⊢mode (* E))            (⊢mode E)]
  [(⊢mode (* E = e))        (⊢mode E)]
  [(⊢mode (* (n : τ) = E))  (⊢mode E)]
  [(⊢mode (x = E))          (⊢mode E)]
  [(⊢mode (if E e_1 e_2))   (⊢mode E)]
  ;;NEW
  [(⊢mode (call (n_0 : vτ) (n_1 : vτ2) ... E e ...))
   (⊢mode E)]
  [(⊢mode (strlen E))
   (⊢mode E)])

(define-metafunction CoreChkC+
  ⊢not-in : (x ...) x -> #t or #f
  [(⊢not-in (_ ... x _ ...) x) #f]
  [(⊢not-in _ _) #t])

;; fixed to handle all types
(define-metafunction CoreChkC+
  ⊢nt-incr : (ptr c (ntarray le he τ)) -> (ptr c (ntarray le he τ))
  ;; does it make sense to use le?
  [(⊢nt-incr (ptr c (ntarray le 0 τ))) (ptr c (ntarray le 1 τ))]
  [(⊢nt-incr τ) τ])


(define-metafunction CoreChkC+
  ⊢is-literal? : e -> #t or #f
  [(⊢is-literal? (n : _)) #t]
  [(⊢is-literal? _) #f])

(define-metafunction CoreChkC+
  ⊢bounds-sub : ω n -> ω or #f
  [(⊢bounds-sub (ntarray le he τ) n)
   (ntarray (⊢bound-sub le n) (⊢bound-sub he n) τ)]
  [(⊢bounds-sub (array le he τ) n)
   (array (⊢bound-sub le n) (⊢bound-sub he n) τ)]
  [(⊢bounds-sub _ n) #f])

(define-metafunction CoreChkC+
  ⊢bound-sub : le n -> le
  [(⊢bound-sub l n) ,(- (term l) (term n))]
  [(⊢bound-sub (x + l) n) (x + ,(- (term l) (term n)))])

(define-metafunction CoreChkC+
  ⊢is-array-or-nt-array? : ω -> #t or #f
  [(⊢is-array-or-nt-array? (ptr m (ntarray le he τ)))
   #t]
  [(⊢is-array-or-nt-array? (ptr m (array le he τ)))
   #t]
  [(⊢is-array-or-nt-array? _)
   #f])

(define-metafunction CoreChkC+
  ⊢extend-ρ′ : ((x : τ) ...) ρ -> (cE ρ)
  [(⊢extend-ρ′ () ρ) (hole ρ)]
  [(⊢extend-ρ′ ((x : τ) (x_0 : τ_0) ...) ρ)
   ((in-hole cE_1 cE_0) ρ_1)
   (where (cE_0 ρ_0) (⊢extend-ρ′ ((x_0 : τ_0) ...) ρ))
   (where (cE_1 ρ_1) (⊢extend-ρ x τ ρ_0))])

(define-metafunction CoreChkC+
  ⊢extend-ρ : x τ ρ -> (cE ρ)
  [(⊢extend-ρ x (ptr m (ntarray le he τ)) ((x_0 (x_lo0 x_hi0)) ...))
   ((let x_lo = le in
        (let x_hi = he in
             hole))
    ((x (x_lo x_hi)) (x_0 (x_lo0 x_hi0)) ...))
   (where (x_lo x_hi) ,(variables-not-in (term (x le he τ (x_0 (x_lo0 x_hi0)) ...)) '(x_lo x_hi)))]
  [(⊢extend-ρ x _ ρ)
   (hole ρ)]
  )



(define-metafunction CoreChkC+
  ⊢extend-Γ : (x = maybe-e : τ) Γ -> Γ
  [(⊢extend-Γ (x_0 = maybe-e_0 : τ_0) ((x_1 = maybe-e_1 : τ_1) ...))
   ((x_0 = maybe-e_0 : τ_0) (x_1 = maybe-e_1 : τ_1) ...)])

(define-metafunction CoreChkC+
  ⊢checked-strlen-var? : Γ e -> #t or #f
  [(⊢checked-strlen-var? Γ (strlen x))
   #t
   (where (_ (ptr c _)) (⊢ty-env-lookup Γ x))]
  [(⊢checked-strlen-var? _ _) #f])

(define-metafunction CoreChkC+
  ⊢nt-ptr? : τ -> #t or #f
  [(⊢nt-ptr? (ptr m (ntarray le he τ))) #t]
  [(⊢nt-ptr? _) #f])

(define-metafunction CoreChkC+
  ⊢non-nt-deref-or-strlen? : τ e -> #t or #f
  [(⊢non-nt-deref-or-strlen? (ptr u _) _) #t]
  [(⊢non-nt-deref-or-strlen? (ptr m (ntarray le he τ)) (in-hole E (* x))) #f]
  [(⊢non-nt-deref-or-strlen? (ptr m (ntarray le he τ))
  ;; only match strlen x instead of let ... = strlen x because we are
  ;; dealing with operational semantics
                             (in-hole E (strlen x))) #f]
  [(⊢non-nt-deref-or-strlen? _ _) #t])

(define-metafunction CoreChkC+
  ⊢strlen : n H -> n or #f
  [(⊢strlen n H)
   0
   (where (0 : _) (⊢heap-lookup H n))]
  [(⊢strlen n H)
   ,(add1 (term (⊢strlen ,(add1 (term n)) H)))
   (where (n_0 : _) (⊢heap-lookup H n))
   (side-condition (not (zero? (term n_0))))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢estrlen : n eH -> n or #f
  [(⊢estrlen n eH)
   0
   (where 0 (⊢eheap-lookup eH n))]
  [(⊢estrlen n eH)
   ,(let ([r (term (⊢estrlen ,(add1 (term n)) eH))])
      (and r (add1 r)))
   (where n_0 (⊢eheap-lookup eH n))
   (side-condition (not (zero? (term n_0))))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢malloc-type-wf : ω -> #t or #f
  [(⊢malloc-type-wf int) #t]
  [(⊢malloc-type-wf (ptr _ ω)) (⊢malloc-type-wf ω)]
  [(⊢malloc-type-wf (struct T)) #t]
  [(⊢malloc-type-wf (array 0 he τ)) (⊢malloc-type-wf τ)]
  [(⊢malloc-type-wf (ntarray 0 he τ)) (⊢malloc-type-wf τ)]
  [(⊢malloc-type-wf _) #f])

(define-metafunction CoreChkC+
  ⊢build-call-stack : e (x (n : vτ)) ...  -> e
  [(⊢build-call-stack e)
   e]
  [(⊢build-call-stack e (x_0 (n_0 : vτ_0)) (x_1 (n_1 : vτ_1)) ...)
   (let x_0 = (n_0 : vτ_0) in (⊢build-call-stack e (x_1 (n_1 : vτ_1)) ...))])

(define-metafunction CoreChkC+
  ⊢ebuild-call-stack : ee (x i) ...  -> ee
  [(⊢ebuild-call-stack ee)
   ee]
  [(⊢ebuild-call-stack ee (x_0 i_0) (x_1 i_1) ...)
   (let x_0 = i_0 in (⊢ebuild-call-stack ee (x_1 i_1) ...))])

(define-metafunction CoreChkC+
  ⊢sizeof : ω -> ee or #f
  [(⊢sizeof τ) 1]
  [(⊢sizeof (struct T)) ,(length (term (⊢struct-lookup ,(*D*) T)))]
  [(⊢sizeof (array 0 he _)) he]
  [(⊢sizeof (ntarray 0 (x + i) _)) (x + ,(+ 1 (term i)))]
  [(⊢sizeof (ntarray 0 i _)) ,(+ 1 (term i))]
  [(⊢sizeof _) ,(raise 'impossible)])

(define-metafunction CoreChkC+
  ⊢base? : n τ -> #t or #f
  [(⊢base? n int) #t]
  [(⊢base? n (ptr u ω)) #t]
  [(⊢base? 0 τ) #t]
  [(⊢base? n (ptr c (array 0 0 τ_′))) #t]
  [(⊢base? n (ptr c (ntarray 0 0 τ_′))) #t]
  [(⊢base? _ _) #f])

(define-metafunction CoreChkC+
  ⊢deref-type-dyn : D τ -> τ
  [(⊢deref-type-dyn _ int) int]
  [(⊢deref-type-dyn _ (ptr m τ)) τ]
  [(⊢deref-type-dyn _ (ptr m (ntarray _ _ τ))) τ]
  [(⊢deref-type-dyn _ (ptr m (array _ _ τ))) τ]
  [(⊢deref-type-dyn _ (ptr m (fun _ τ _))) τ]
  [(⊢deref-type-dyn D (ptr m (struct T)))
   τ_1
   (where ((τ_1 _) _ ...) (⊢struct-lookup D T))])

(define-metafunction CoreChkC+
  ⊢deref-type : ω -> τ
  [(⊢deref-type τ) τ]
  [(⊢deref-type (array le he τ)) τ]
  [(⊢deref-type (ntarray le he τ)) τ])



(module+ test
  (test--> (---> 'c)
             (term ((() ()) (let x = (1 : int) in x)))
             (term ((() ()) (let x = (1 : int) in (1 : int)))))
  (test--> (---> 'c)
             (term ((() ()) (let x = (1 : int) in (1 : int))))
             (term ((() ()) (1 : int))))
  (test-->> (---> 'c)
             (term ((() ()) (let x = (1 : int) in x)))
             (term ((() ()) (1 : int))))
    ;; shadowing. explicitly spelling out the steps to prevent non-deterministic semantics
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in (x + (let x = (4 : int) in x)))))
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x))))))
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x)))))
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int)))))))
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int))))))
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (4 : int))))))
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in ((1 : int) + (4 : int)))))
           (term ((() ()) (let x = (1 : int) in (5 : int)))))
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in (5 : int))))
           (term ((() ()) (5 : int))))
  (test-->> (---> 'c)
             (term ((() ()) (let x = (1 : int) in
                            (let y = (2 : int) in (x + y)))))
             (term ((() ()) (3 : int))))

  (test-->> (---> 'c)
             (term ((() ()) (let x = (1 : int) in
                            (let y = (2 : (ptr c (ntarray 0 0 int))) in (x + y)))))
             (term ((() ()) (3 : int))))

  ;; strlen non-NT case
  (test-->> (---> 'c)
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (strlen (2 : (ptr c (ntarray 0 0 int))))))
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (3 : int))))

  (test-->> (---> 'c)
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen (x + (1 : int))))))
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))) Bounds)))

;; E-VarNTstr
  (test--> (---> 'c)
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen x))))
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (let x = (2 : (ptr c (ntarray 0 3 int))) in (3 : int)))))

  ;; make sure the bound always expands
  (test--> (---> 'c)
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (strlen x))))
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (3 : int)))))
 
  (test-->> (---> 'c)
            (term ((((8 : int) (0 : int)) ((8 : int) (0 : int)))
                   (let x = (1 : int) in
                        (let y = (2 : (ptr c (ntarray 0 0 int))) in (* y)))))
            (term ((((8 : int) (0 : int)) ((8 : int) (0 : int))) (0 : int))))

   (test-->> (---> 'c)
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   (strlen (0 : (ptr c (ntarray 0 0 int))))))
            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
                   Null)))



  ;; E-VarTy
  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in
                          (malloc c (array (x + 0) (x + 0) int)))))
           (term ((() ()) (let x = (1 : int) in
                          (malloc c (array 1 (x + 0) int))))))


  (test--> (---> 'c)
           (term ((() ()) (malloc c (array 0 -7 int))))
           (term ((() ()) (0 : (ptr c (array 0 -7 int))))))

  (test--> (---> 'c)
           (term ((() ()) (malloc c (array 0 0 int))))
           (term ((() ()) (0 : (ptr c (array 0 0 int))))))

  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))

  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))

  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y))))
           (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in (0 : (ptr c (array 1 0 int))))))))

  (test-->> (---> 'c)
            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term ((() ()) (0 : (ptr c (array 1 0 int))))))

  ;; E-Malloc (cases where it gets stuck)
  (test-->> (---> 'c)
            (term ((() ()) (malloc c (array 2 3 int))))
            (term ((() ()) (malloc c (array 2 3 int)))))

  (test-->> (---> 'c)
            (term ((() ()) (malloc c (array 0 3 int))))
            (term ((((0 : int) (0 : int) (0 : int)) ()) (1 : (ptr c (array 0 3 int))))))

  ;; E-Malloc (empty)
  (test-->> (---> 'c)
            (term ((() ()) (malloc c (array 0 -1 int))))
            (term ((() ()) (0 : (ptr c (array 0 -1 int))))))

  (test-->> (---> 'c)
            (term ((((1 : int)) ()) (malloc c (array 0 0 int))))
            (term ((((1 : int)) ()) (0 : (ptr c (array 0 0 int))))))


  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array (x + 0) 0 int))) in
                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int)))))))
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int))))))))

   (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int)))))))
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc c (array 0 (z + 0) int))))))))

  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc c (array 0 (z + 0) int)))))))
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc c (array 0 (z + 0) int))))))))

  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc c (array 0 (z + 0) int)))))))
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc c (array 0 4 int))))))))

  (test-->> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc c (array 0 4 int)))))))
            (term ((((0 : int) (0 : int) (0 : int) (0 : int)) ()) (1 : (ptr c (array 0 4 int))))))

  (test--> (---> 'c)
            (term ((() ()) (let x = (1 : int) in
                           (* ((malloc c (array 0 (x + 0) int)) + x)))))
            (term ((() ()) (let x = (1 : int) in
                           (* ((malloc c (array 0 1 int)) + x))))))

  (test--> (---> 'c)
           (term ((() ()) (let x = (1 : int) in
                          (* ((malloc c (array 0 1 int)) + x)))))
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x))))))

    (test--> (---> 'c)
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))

  (test--> (---> 'c)
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))

  (test--> (---> 'c)
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int))))))
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* (2 : (ptr c (array -1 0 int))))))))

  (test--> (---> 'c)
           (term ((((0 : int)) ()) (let x = (1 : int) in
                                   (* (2 : (ptr c (array -1 0 int)))))))
           (term ((((0 : int)) ()) Bounds)))

  )

(module+ test
  (parameterize ((*Fs* (term (((defun  ((x : int) (x + (1 : int))) : int)      ; (fun (x ...) τ (τ ...)))
                             (defun ((y : int) (y + (2 : int))) : int)      ; (+2) at position 1
                             (defun ((p : int) (q : int) (p + q)) : int)
                             )
                             ((defun ((x : int) (x + (1 : int))) : int)      ; (+1) at position 0
                             (defun ((y : int) (y + (2 : int))) : int)      ; (+2) at position 1
                             (defun ((p : int) (q : int) (p + q)) : int)
                             )))))        ; (+)  at position 2
    (test--> (---> 'c)
           (term ((() ()) (call (1 : (ptr c (fun () int (int)))) (4 : int))))
           (term ((() ()) (let y = (4 : int) in (y + (1 : int))))))
    (test--> (---> 'c)
           (term ((() ()) (call (3 : (ptr c (fun () int (int int)))) (4 : int) (5 : int))))
           (term ((() ()) (let p = (4 : int) in (let q = (5 : int) in (p + q))))))
    )

   (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                          (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (cast (ptr c (ntarray 0 0 int)) (x + (1 : int)))))
                                       (0 : int))) : int))
                               ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                          (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (cast (ptr t (ntarray 0 0 int)) (x + (1 : int)))))
                                       (0 : int))) : int))))))

    (test-->> (---> 'c)
           (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
                  (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
           (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
                  (3 : int))))
     )

 (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                       (0 : int))) : int))
                            ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call (1 : (ptr t (fun () int ((ptr t (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                       (0 : int))) : int))))))
    (test-->>
     (---> 'c)

     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (3 : int)))))

   ;; arity
  (parameterize ((*Fs* (term (((defun ((x : int)
                               (x + (1 : int))) : int))
                              ((defun ((x : int)
                               (x + (1 : int))) : int))))))
    (test-->>
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (call (1 : (ptr c (fun () int (int)))) (2 : int) (2 : int) )))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (call (1 : (ptr c (fun () int (int)))) (2 : int) (2 : int) ))))
    (test-->>
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (call (1 : (ptr c (fun () int (int)))) (2 : int) )))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (3 : int)))))

  (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                       (0 : int))) : int))
                              ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call  (1 : (ptr t (fun () int ((ptr t (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                       (0 : int))) : int))))))
    (test-->
     (---> 'c)

     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (call  (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 0 int))) in
                 (if (* x)
                     ((1 : int) +
                                (call  (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                            (x + (1 : int))))
                     (0 : int))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 0 int))) in
                 (if (* x)
                     ((1 : int) +
                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                            (x + (1 : int))))
                     (0 : int)))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 (if (1 : int)
                     ((1 : int) +
                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                            (x + (1 : int))))
                     (0 : int))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 (if (1 : int)
                     ((1 : int) +
                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                            (x + (1 : int))))
                     (0 : int)))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        (x + (1 : int))))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        (x + (1 : int)))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int))))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int)))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        (2 : (ptr c (ntarray -1 0 int)))))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                        (2 : (ptr c (ntarray -1 0 int))))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
                       (if (* x)
                                   ((1 : int) +
                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                   (0 : int))))))))

    (test-->
     (---> 'c)
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
                       (if (* x)
                                   ((1 : int) +
                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                   (0 : int)))))))
     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 1 int))) in
                       (if (1 : int)
                                   ((1 : int) +
                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
                                          (x + (1 : int))))
                                       (0 : int))))))))
    )
)


(print "tests pass")
