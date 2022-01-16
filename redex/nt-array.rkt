#lang racket
(require rackunit)
(provide (all-defined-out))
(require redex/reduction-semantics)
;; (require racket/control)

(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *D* (make-parameter (term ()))) ; struct table
(define *H* (make-parameter (term ()))) ; global heap (for type system)
(define *F* (make-parameter (term ()))) ; global function definition table
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
  (m ::= c u)
  (τ ::= int (ptr m ω))
  (ω ::= τ (struct T)
     ;; CHANGED:
     (array le he τ)
     ;; NEW:
     (ntarray le he τ))

  ;; NEW
  ;; normalized types
  (vτ ::= int (ptr m vω))
  (vω ::= vτ (struct T)
     (array l h vτ)
     (ntarray l h vτ))

  (e ::= (n : τ) x (let x = e in e) (malloc ω) (cast τ e)
     (e + e) (& e → f) (* e) (* e = e) (unchecked e)
     ;; NEW:
     (if e e e)
     (strlen e)
     (dyn-bound-cast τ e)
     ;; NEW functions
     (call n e ...))

  ;; erased expressions
  (ee ::=  i eS)

  ;; NEW:
  (le he ::= l ls)
  (ls hs ::= (x + l))

  ;;NEW functions
  (F ::= ((defun ((x : τ) ... e) : τ) ...))

  (n k ::= natural)
  (l h i ::= integer)
  (D ((T fs) ...))
  (fs ((vτ f) (vτ f) ...))
  (x eff f T ::= variable-not-otherwise-mentioned)
  (H ::= ((n : vτ) ...))
  (eH ::= (n ...))
  ;;NEW functions
  (eF ::= ((defun x ... ee) ...))
  (r ::= e ε)
  (er ::= ee ε)
  (ε ::= Null Bounds)
  (E ::= hole (let x = E in e) (let x = (n : vτ) in E) (E + e) ((n : vτ) + E)
     (& E → f) (dyn-bound-cast Eτ e) (dyn-bound-cast vτ E) (cast Eτ e) (cast vτ E) (* E) (* E = e) (* (n : vτ) = E) (unchecked E)
     ;; NEW:
     (if E e e)
     (strlen E)
     (malloc Eω)
     (n : Eτ)
     ;;New for functions
     (call n (n : vτ) ... E e ...))

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
      (call n_1 (n_args : vτ_args) ...)
      (dyn-bound-cast vτ (n : vτ_′))
      ((n_1 : vτ_1) + (n_2 : vτ_2))
      (cast vτ (n : vτ_′))
      (& (n : vτ) → f_i)
      (malloc vω)
      (unchecked (n : vτ))
      (if (n : vτ) e_1 e_2))

  (eE ::= hole
      (eE + ee) (i + eE)
      (x = eE)
      (eE - ee) (i - eE)
      (* eE) (* eE = ee) (* i = eE)
      (eE <=? ee)
      (i <=? eE)
      (if eE ee ee)
      (strlen eE)
      (let x = eE in ee)
      (let x = i in eE)

      ;;New for functions
      (call n n ... eE ee ...))


  ;; erased serious terms
  (eS ::= x (malloc ee)
      (ee + ee) (ee - ee) (* ee) (* ee = ee)
      (x = ee)
      (ee <=? ee)
      (if ee ee ee)
      (let x = ee in ee)
      (strlen ee)
      (call n ee ...)
      ;; exceptions
      (enull) (ebounds))



  (eK ::= hole
      pop
      (malloc [])
      ([] + ee) (i + [])
      (x = [])
      ([] - ee) (i - [])
      (* []) (* [] = ee) (* i = [])
      ([] <=? ee)
      (i <=? [])
      (if [] ee ee)
      (strlen [])
      (let x = [] in ee)
      ;;New for functions
      (call n n ... [] ee ...))


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operational Semantics

(define --->^
  (reduction-relation
   CoreChkC+ #:domain (eH ee) #:codomain (eH er)
   (--> (eH (in-hole eE (i_0 + i_1)))
        (eH (in-hole eE ,(+ (term i_0) (term i_1))))
        eE-Add)

   (--> (eH (in-hole eE (i_0 <=? i_1)))
        (eH (in-hole eE ,(if (<= (term i_0) (term i_1)) 1 0)))
        eE-Leq)

   (--> (eH (in-hole eE (i_0 - i_1)))
        (eH (in-hole eE ,(- (term i_0) (term i_1))))
        eE-Subtract)

   ;; apparently negative values (a.k.a bounds) should never appear on the heap
   (--> (eH (in-hole eE (* n)))
        (eH (in-hole eE n_0))
        (where n_0 (⊢eheap-lookup eH n))
        eE-Def)

   ;; don't forget the underscore!!!!!
   (--> (eH (in-hole eE (* n = n_0)))
        (eH_′ (in-hole eE n_0))
        (where eH_′ (⊢eheap-update eH n n_0))
        eE-Assign)

   (--> (eH (in-hole eE (let x = i_0 in
                                (in-hole eE_′ (x = i_1)))))
        (eH (in-hole eE (let x = i_1 in
                                (in-hole eE_′ i_1))))
        eE-Set)

   (--> (eH (in-hole eE (malloc n_1)))
        (eH_′ (in-hole eE n_2))
        (side-condition (positive? (term n_1)))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where n_2 ,(add1 (length (term eH))))
        eE-Malloc)

   (--> (eH (in-hole eE (malloc i_1)))
        (eH (in-hole eE 0))
        (side-condition (not (positive? (term i_1))))
        eE-MallocZero)

   (--> (eH (in-hole eE (let x = i_0 in i_1)))
        (eH (in-hole eE i_1))
        eE-Let)

   (--> (eH (in-hole eE (let x = i_0 in (in-hole eE_′ x))))
        (eH (in-hole eE (let x = i_0 in (in-hole eE_′ i_0))))
        eE-Var)

   (--> (eH (in-hole eE (if i ee _)))
        (eH (in-hole eE ee))
        (side-condition (not (zero? (term i))))
        eE-IfT)

   (--> (eH (in-hole eE (if 0 _ ee)))
        (eH (in-hole eE ee))
        eE-IfF)

   (--> (eH (in-hole eE (strlen i)))
        (eH (in-hole eE i_0))
        (where i_0 (⊢estrlen i eH))
        eE-Str)

   (--> (eH (in-hole eE (call i i_1 ..._1)))
        (eH (in-hole eE (⊢ebuild-call-stack ee (x i_1) ...)))
        (where (defun x ..._1 ee) (⊢efun-lookup ,(*eF*) i))
        eE-Fun)

   (--> (eH (in-hole eE (enull)))
        (eH Null)
        eX-Null)

   (--> (eH (in-hole eE (ebounds)))
        (eH Bounds)
        eX-Bounds)))

(define --->^CEK
  (reduction-relation
   CoreChkC+ 
   (--> (eH eΣ (i_0 + i_1) (eK ...))
        (eH eΣ ,(+ (term i_0) (term i_1)) (eK ...))
        eE-Add)

   (--> (eH eΣ (i_0 <=? i_1) (eK ...))
        (eH eΣ ,(if (<= (term i_0) (term i_1)) 1 0) (eK ...))
        eE-Leq)

   (--> (eH eΣ (i_0 - i_1) (eK ...))
        (eH eΣ ,(- (term i_0) (term i_1)) (eK ...))
        eE-Subtract)

   (--> (eH eΣ (* n) (eK ...))
        (eH eΣ n_0 (eK ...))
        (where n_0 (⊢eheap-lookup eH n))
        eE-Def)

   (--> (eH eΣ (* n = n_0) (eK ...))
        (eH_′ eΣ n_0 (eK ...))
        (where eH_′ (⊢eheap-update eH n n_0))
        eE-Assign)

   (--> (eH ((x_0 i_0) ... (x _) (x_2 i_2) ...) (x = i_1) (eK ...))
        (eH ((x_0 i_0) ... (x i_1) (x_2 i_2) ...) i_1 (eK ...))
        eE-Set)

   (--> (eH eΣ (malloc n_1) (eK ...))
        (eH_′ eΣ n_2 (eK ...))
        (side-condition (positive? (term n_1)))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where n_2 ,(add1 (length (term eH))))
        eE-Malloc)

   (--> (eH eΣ (malloc i_1) (eK ...))
        (eH eΣ 0 (eK ...))
        (side-condition (not (positive? (term i_1))))
        eE-MallocZero)

   (--> (eH ((x i) ...) (let x_0 = i_0 in ee) (eK ...))
        (eH ((x_0 i_0) (x i) ...) ee (pop eK ...))
        eE-Let)

   (--> (eH (name eΣ (_ ... (x i) _ ...)) x (eK ...))
        (eH eΣ i (eK ...))
        eE-Var)

   (--> (eH eΣ (if i ee _) (eK ...))
        (eH eΣ ee (eK ...))
        (side-condition (not (zero? (term i))))
        eE-IfT)

   (--> (eH eΣ (if 0 _ ee) (eK ...))
        (eH eΣ ee (eK ...))
        eE-IfF)

   (--> (eH eΣ (strlen i) (eK ...))
        (eH eΣ i_0 (eK ...))
        (where i_0 (⊢estrlen i eH))
        eE-Str)

   (--> (eH eΣ (call i i_1 ..._1) (eK ...))
        (eH eΣ (⊢ebuild-call-stack ee (x i_1) ...) (eK ...))
        (where (defun x ..._1 ee) (⊢efun-lookup ,(*eF*) i))
        eE-Fun)

   (--> (eH eΣ (enull) (eK ...))
        (eH () Null ())
        eX-Null)

   (--> (eH eΣ (ebounds) (eK ...))
        (eH () Bounds ())
        eX-Bounds)

   ;; eval
   (--> (eH eΣ (if eS ee_0 ee_1) (eK ...))
        (eH eΣ eS ((if [] ee_0 ee_1) eK ...))
        eE-If-Eval)

   (--> (eH eΣ i ((if [] ee_0 ee_1) eK ...))
        (eH eΣ (if i ee_0 ee_1) (eK ...))
        eE-If-Cont)

   (--> (eH eΣ i ((strlen []) eK ...))
        (eH eΣ (strlen i) (eK ...))
        eE-Strlen-Cont)

   (--> (eH eΣ (strlen eS) (eK ...))
        (eH eΣ eS ((strlen []) eK ...))
        eE-Strlen-Eval)

   (--> (eH eΣ i ((malloc []) eK ...))
        (eH eΣ (malloc i) (eK ...))
        eE-Malloc-Cont)

   (--> (eH eΣ (malloc eS) (eK ...))
        (eH eΣ eS ((malloc []) eK ...))
        eE-Malloc-Eval)


   (--> (eH eΣ (let x = eS in ee) (eK ...))
        (eH eΣ eS ((let x = [] in ee) eK ...))
        eE-Let-Eval0)

   (--> (eH eΣ i ((let x = [] in ee) eK ...))
        (eH eΣ (let x = i in ee) (eK ...))
        eE-Let-Cont0)


   (--> (eH ((x i) (x_0 i_0) ...) i_1 (pop eK ...))
        (eH ((x_0 i_0) ...) i_1 (eK ...))
        eE-Pop-Cont)

   (--> (eH eΣ (call n_fun n_args ... eS ee_args ...) (eK ...))
        (eH eΣ eS ((call n_fun n_args ... [] ee_args ...) eK ...))
        eE-Fun-Eval)

   (--> (eH eΣ n ((call n_fun n_args ... [] ee_args ...) eK ...))
        (eH eΣ (call n_fun n_args ... n ee_args ...) (eK ...))
        eE-Fun-Cont)

   (--> (eH eΣ (eS <=? ee) (eK ...))
        (eH eΣ eS (([] <=? ee) eK ...))
        eE-Leq-Eval0)

   (--> (eH eΣ i (([] <=? ee) eK ...))
        (eH eΣ (i <=? ee) (eK ...))
        eE-Leq-Cont0)

   (--> (eH eΣ (i <=? eS) (eK ...))
        (eH eΣ eS ((i <=? []) eK ...))
        eE-Leq-Eval1)

   (--> (eH eΣ i_0 ((i <=? []) eK ...))
        (eH eΣ (i <=? i_0) (eK ...))
        eE-Leq-Cont1)

   (--> (eH eΣ (* eS = ee) (eK ...))
        (eH eΣ eS ((* [] = ee) eK ...))
        eE-Assign-Eval0)

   (--> (eH eΣ i ((* [] = ee) eK ...))
        (eH eΣ (* i = ee) (eK ...))
        eE-Assign-Cont0)

   (--> (eH eΣ (* i = eS) (eK ...))
        (eH eΣ eS ((* i = []) eK ...))
        eE-Assign-Eval1)

   (--> (eH eΣ i_0 ((* i = []) eK ...))
        (eH eΣ (* i = i_0) (eK ...))
        eE-Assign-Cont1)

   (--> (eH eΣ (* eS) (eK ...))
        (eH eΣ eS ((* []) eK ...))
        eE-Def-Eval)

   (--> (eH eΣ i ((* []) eK ...))
        (eH eΣ (* i) (eK ...))
        eE-Def-Cont)

   (--> (eH eΣ (x = eS) (eK ...))
        (eH eΣ eS ((x = []) eK ...))
        eE-Set-Eval)

   (--> (eH eΣ i ((x = []) eK ...))
        (eH eΣ i (x = i) (eK ...))
        eE-Set-Cont)

   (--> (eH eΣ (eS + ee) (eK ...))
        (eH eΣ eS (([] + ee) eK ...))
        eE-Add-Eval0)

   (--> (eH eΣ i (([] + ee) eK ...))
        (eH eΣ (i + ee) (eK ...))
        eE-Add-Cont0)

   (--> (eH eΣ (i + eS) (eK ...))
        (eH eΣ eS ((i + []) eK ...))
        eE-Add-Eval1)

   (--> (eH eΣ i_0 ((i + []) eK ...))
        (eH eΣ (i + i_0) (eK ...))
        eE-Add-Cont1)

   (--> (eH eΣ (eS - ee) (eK ...))
        (eH eΣ eS (([] - ee) eK ...))
        eE-Subtract-Eval0)

   (--> (eH eΣ i (([] - ee) eK ...))
        (eH eΣ (i - ee) (eK ...))
        eE-Subtract-Cont0)

   (--> (eH eΣ (i - eS) (eK ...))
        (eH eΣ eS ((i - []) eK ...))
        eE-Subtract-Eval1)

   (--> (eH eΣ i_0 ((i - []) eK ...))
        (eH eΣ (i - i_0) (eK ...))
        eE-Subtract-Cont1)))


(define ~~>
  (reduction-relation
   CoreChkC+ #:domain (H r)
   (--> (H e) (H_′ r_′) (judgment-holds (⊢↝ (H e) (H_′ r_′))))))

(define (---> m)
  (reduction-relation
   CoreChkC+
   #:domain (H r)
   (--> (H e) (H_′ r)
        (judgment-holds (⊢⟶ (H e ,m) (H_′ r))))))

(define --->cu
  (reduction-relation
   CoreChkC+
   #:domain (H r)
   (-->
    (H (in-hole E pr))
    (H_′ (in-hole E e_′))
    (judgment-holds (⊢↝/name (H pr) (H_′ e_′ any_name)))
    (computed-name (term any_name)))

   (-->
    (H (in-hole E pr))
    (H_′ ε)
    (judgment-holds (⊢↝/name (H pr) (H_′ ε any_name)))
    (computed-name (term any_name)))))

(define-judgment-form CoreChkC+
  #:contract (⊢↝/name (H e) (H r any))
  #:mode     (⊢↝/name I O)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; New rules

  [(⊢↝/name (H (let x = (n_0 : vτ_0) in (in-hole E (x + i_0))))
       (H (let x = (n_0 : vτ_0) in (in-hole E i_1))
          S-VarTy))
   (where i_1 ,(+ (term n_0) (term i_0)))
   S-VarTy]

  ;; popping the stack
  [(⊢↝/name (H (let x = (n_0 : vτ_0)  in (n_2 : vτ_2))) (H (n_2 : vτ_2) S-Let))
   S-Let]

  ;; The non-nt-deref-or-strlen? precondition ensures the if (* x) case is prioritized
  ;; over the normal variable substitution case 
  [(⊢↝/name (H (let x = (n : vτ) in (name e (in-hole E x)))) (H (let x = (n : vτ) in (in-hole E (n : vτ))) S-VarNonNT))
   (where #t (⊢non-nt-deref-or-strlen? vτ e))
   S-VarNonNT]

  ;; S-IfNTT
  [(⊢↝/name (H (let x = (n : vτ_1) in (in-hole E (* x)))) (H (let x = (n : vτ_2) in (in-hole E (n_′ : vτ_′))) S-VarNT-Incr))
   (where (n_′ : vτ_′) (⊢heap-lookup H n))
   (where #f ,(zero? (term n_′)))
   (where vτ_2 (⊢nt-incr vτ_1))
   S-VarNT-Incr]

  [(⊢↝/name (H (let x = (n : vτ_1) in (in-hole E (* x)))) (H (let x = (n : vτ_1) in (in-hole E (* (n : vτ_1)))) S-VarNT-Sub))
   (side-condition ,(let ([i (term (⊢heap-lookup H n))])
                      (or (not i)
                          (zero? (first i)))))
   S-VarNT-Sub]

  ;; this are just like their array counterparts
  [(⊢↝/name (H (* (n : vτ))) (H Bounds S-DefNtArrayBound))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   S-DefNtArrayBound]

  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H Bounds S-AssignNtArrayBound))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   S-AssignNtArrayBound]

  [(⊢↝/name (H ((0 : vτ) + (n : vτ_′))) (H Null S-AddNtArrNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   S-AddNtArrNull]

  ;; file a bug report on microsoft/checkedc?
  [(⊢↝/name (H (strlen (0 : vτ))) (H Null S-StrNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   S-StrNull]

  [(⊢↝/name (H (strlen (n : vτ))) (H Bounds S-StrBound))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   S-StrBound]

  ;; The Redex model supports non-widening strlen
  [(⊢↝/name (H (strlen (n : vτ))) (H (n_1 : int) S-Str))
   (where n_1 (⊢strlen n H))
   (where (ptr _ (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   S-Str]

  [(⊢↝/name (H (call n_1 (n_args : vτ_args) ..._1))  (H (⊢build-call-stack e (x (n_args : vτ_args)) ...) S-Fun))
   (where (defun ((x : τ_2′) ..._1 e) : τ) (⊢fun-lookup ,(*F*) n_1))
   S-Fun]

  [(⊢↝/name (H (dyn-bound-cast vτ (n : vτ_′))) (H (n : vτ_′) S-DynCast)) ;; note that the annotation does not change
   (where #t (⊢bounds-within vτ vτ_′)) ;; only need the ntarray/array subsumption cases
   S-DynCast]

  [(⊢↝/name (H (dyn-bound-cast vτ (n : vτ_′))) (H Bounds S-DynCastBound))
   (where #f (⊢bounds-within vτ vτ_′))
   S-DynCastBound]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Old rules
  [(⊢↝/name (H ((n_1 : vτ_1) + (n_2 : vτ_2))) (H (n_3 : vτ_3) S-Add))
   (where n_3 ,(+ (term n_1) (term n_2)))
   (where vτ_3 (⊢binop-type vτ_1 n_1 n_2))
   S-Add]

  [(⊢↝/name (H (cast vτ (n : vτ_′))) (H (n : vτ) S-Cast))
   S-Cast]

  [(⊢↝/name (H (* (n : vτ))) (H (n_1 : vτ_1) S-Def))
   (where #t (⊢deref-ok? vτ))
   (where (n_1 : _) (⊢heap-lookup H n))
   (where vτ_1 (⊢deref-type-dyn ,(*D*) vτ))
   S-Def]

  ;; the type stored on the heap musn't change
  ;; the type attached to n_1 can stay as the evaluation result because it's all on the stack
  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H_′ (n_1 : vτ_1) S-Assign))
   (where #t (⊢assign-ok? vτ))
   (where H_′ (⊢heap-update H n n_1))
   S-Assign]

  [(⊢↝/name (H (& (n : vτ) → f_i)) (H (n_0 : vτ_0) S-Struct))
   (where (n_0 : vτ_0) (⊢& vτ f_i n))
   S-Struct]

  [(⊢↝/name (H (malloc vω)) (H_′ (n_1 : (ptr c vω)) S-Malloc))
   (where (vτ_1 ...) (⊢types ,(*D*) vω))
   (where ((n : vτ) ...) H)
   (where H_′ ((n : vτ) ... (0 : vτ_1) ...))
   (where n_1 ,(add1 (length (term H))))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(positive? (term (⊢sizeof vω))))
   S-Malloc]

  [(⊢↝/name (H (malloc vω)) (H (0 : (ptr c vω)) S-MallocZero))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(not (positive? (term (⊢sizeof vω)))))
   S-MallocZero]

  [(⊢↝/name (H (unchecked (n : vτ))) (H (n : vτ) S-Unchecked))
   S-Unchecked]

  ;; array and nt-array combined in a single rule
  [(⊢↝/name (H (* (n : vτ))) (H Bounds S-DefBound))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   S-DefBound]

  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H Bounds S-AssignBound))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   S-AssignBound]

  [(⊢↝/name (H (* (0 : vτ))) (H Null S-DefNull))
   (where (ptr c vω) vτ)
   S-DefNull]

  [(⊢↝/name (H (* (0 : vτ) = (n_1 : vτ_′))) (H Null S-AssignNull))
   (where (ptr c vω) vτ)
   S-AssignNull]

  [(⊢↝/name (H (& (0 : vτ) → f)) (H Null S-StructNull))
   (where (ptr c (struct T)) vτ)
   S-StructNull]

  [(⊢↝/name (H ((0 : vτ) + (n : vτ_′))) (H Null S-AddNull))
   (where (ptr c (array l h vτ_1)) vτ)
   S-AddNull]

  [(⊢↝/name (H (if (n : vτ) e_1 e_2)) (H e_1 S-IfT))
   (side-condition ,(< (term 0) (term n)))
   S-IfT]
  [(⊢↝/name (H (if (n : vτ) e_1 e_2)) (H e_2 S-IfF))
   (side-condition ,(= (term 0) (term n)))
   S-IfF]

  [(⊢↝/name (H (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
            (H (let x = (n : (ptr c (ntarray l h_′ vτ))) in (in-hole E (n_1 : int))) S-StrWiden))
   (where n_1 (⊢strlen n H))
   (where h_′ ,(max (term h) (term n_1)))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   S-StrWiden]

  ;; extra rules for prioritizing if (* x) over plain if
  [(⊢↝/name (H (let x = (0 : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
       (H Null S-VarNTNull))
   S-VarNTNull]

  [(⊢↝/name (H (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
            (H Bounds S-VarNTBound))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   S-VarNTBound])


(define-judgment-form CoreChkC+
  #:contract (⊢↝ (H e) (H r))
  #:mode     (⊢↝ I O)
  [(⊢↝ (H e) (H_′ r))
   (⊢↝/name (H e) (H_′ r any))])

(define-judgment-form CoreChkC+
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
  ⊢heap-lookup : H n -> (n : τ) or #f
  [(⊢heap-lookup H n)
   ,(and (<= (term n) (length (term H)))
         (positive? (term n))
         (list-ref (term H) (sub1 (term n))))])

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
  [(⊢mode (call n (n_0 : vτ) ... E e ...))
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



(module+ test
  (test--> (---> 'c)
             (term (() (let x = (1 : int) in x)))
             (term (() (let x = (1 : int) in (1 : int)))))
  (test--> (---> 'c)
             (term (() (let x = (1 : int) in (1 : int))))
             (term (() (1 : int))))
  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in x)))
             (term (() (1 : int))))

  (test-->> (---> 'c)
            (term (() (let x = (1 : int)  in (let y = (2 : int) in (x + y)))))
             (term (() (3 : int))))


  ;; shadowing. explicitly spelling out the steps to prevent non-deterministic semantics
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in (x + (let x = (4 : int) in x)))))
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x))))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x)))))
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int)))))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int))))))
           (term (() (let x = (1 : int) in ((1 : int) + (4 : int))))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (4 : int)))))
           (term (() (let x = (1 : int) in (5 : int)))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in (5 : int))))
           (term (() (5 : int))))



  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in
                            (let y = (2 : int) in (x + y)))))
             (term (() (3 : int))))

  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in
                            (let y = (2 : (ptr c (ntarray 0 0 int))) in (x + y)))))
             (term (() (3 : int))))

  ;; strlen non-NT case
  (test-->> (---> 'c)
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (strlen (2 : (ptr c (ntarray 0 0 int))))))
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) (3 : int))))


  (test-->> (---> 'c)
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen (x + (1 : int))))))
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) Bounds)))

  ;; S-VarNTstr
  (test--> (---> 'c)
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen x))))
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (let x = (2 : (ptr c (ntarray 0 3 int))) in (3 : int)))))

  ;; make sure the bound always expands
  (test--> (---> 'c)
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (strlen x))))
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (3 : int)))))

  (test-->> (---> 'c)
            (term (((8 : int) (0 : int))
                   (let x = (1 : int) in
                        (let y = (2 : (ptr c (ntarray 0 0 int))) in (* y)))))
            (term (((8 : int) (0 : int)) (0 : int))))


  (test-->> (---> 'c)
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   (strlen (0 : (ptr c (ntarray 0 0 int))))))
            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
                   Null)))



  ;; S-VarTy
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in
                          (malloc (array (x + 0) (x + 0) int)))))
           (term (() (let x = (1 : int) in
                          (malloc (array 1 (x + 0) int))))))


  (test--> (---> 'c)
           (term (() (malloc (array 0 -7 int))))
           (term (() (0 : (ptr c (array 0 -7 int))))))

  (test--> (---> 'c)
           (term (() (malloc (array 0 0 int))))
           (term (() (0 : (ptr c (array 0 0 int))))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y))))
           (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in (0 : (ptr c (array 1 0 int))))))))

  (test-->> (---> 'c)
            (term (() (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
            (term (() (0 : (ptr c (array 1 0 int))))))

  ;; S-Malloc (cases where it gets stuck)
  (test-->> (---> 'c)
            (term (() (malloc (array 2 3 int))))
            (term (() (malloc (array 2 3 int)))))

  (test-->> (---> 'c)
            (term (() (malloc (array 0 3 int))))
            (term (((0 : int) (0 : int) (0 : int)) (1 : (ptr c (array 0 3 int))))))

  ;; S-Malloc (empty)
  (test-->> (---> 'c)
            (term (() (malloc (array 0 -1 int))))
            (term (() (0 : (ptr c (array 0 -1 int))))))

  (test-->> (---> 'c)
            (term (((1 : int)) (malloc (array 0 0 int))))
            (term (((1 : int)) (0 : (ptr c (array 0 0 int))))))


  (test--> (---> 'c)
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array (x + 0) 0 int))) in
                                (let z = (cast int y) in (malloc (array 0 (z + 0) int)))))))
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int y) in (malloc (array 0 (z + 0) int))))))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int y) in (malloc (array 0 (z + 0) int)))))))
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc (array 0 (z + 0) int))))))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc (array 0 (z + 0) int)))))))
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc (array 0 (z + 0) int))))))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc (array 0 (z + 0) int)))))))
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc (array 0 4 int))))))))

  (test-->> (---> 'c)
            (term (() (let x = (1 : int) in
                           (let y = (4 : (ptr c (array 1 0 int))) in
                                (let z = (4 : int) in (malloc (array 0 4 int)))))))
            (term (((0 : int) (0 : int) (0 : int) (0 : int)) (1 : (ptr c (array 0 4 int))))))

  (test--> (---> 'c)
            (term (() (let x = (1 : int) in
                           (* ((malloc (array 0 (x + 0) int)) + x)))))
            (term (() (let x = (1 : int) in
                           (* ((malloc (array 0 1 int)) + x))))))

  (test--> (---> 'c)
           (term (() (let x = (1 : int) in
                          (* ((malloc (array 0 1 int)) + x)))))
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x))))))

  (test--> (---> 'c)
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))

  (test--> (---> 'c)
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))

  (test--> (---> 'c)
           (term (((0 : int)) (let x = (1 : int) in
                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int))))))
           (term (((0 : int)) (let x = (1 : int) in
                                   (* (2 : (ptr c (array -1 0 int))))))))

  (test--> (---> 'c)
           (term (((0 : int)) (let x = (1 : int) in
                                   (* (2 : (ptr c (array -1 0 int)))))))
           (term (((0 : int)) Bounds))))

;;Test functions

(module+ test
  (parameterize ((*F* (term ((defun ((x : int) (x + (1 : int))) : int)      ; (+1) at position 0
                             (defun ((y : int) (y + (2 : int))) : int)      ; (+2) at position 1
                             (defun ((p : int) (q : int) (p + q)) : int)
                             ))))        ; (+)  at position 2
    (test--> (---> 'c) (term (() (call 1 (4 : int))))
           (term (() (let y = (4 : int) in (y + (1 : int))))))
    (test--> (---> 'c)
             (term (() (call 3 (4 : int) (5 : int))))
     (term (() (let p = (4 : int) in (let q = (5 : int) in (p + q)))))))

  (parameterize ((*F* (term ((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                    ;; need the cast for it to typecheck
                                    ;; evaluation should go through even without
                                              (call 1
                                          (cast (ptr c (ntarray 0 0 int)) (x + (1 : int)))))
                                       (0 : int))) : int)))))
    (test-->>
     (---> 'c)

     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (1 : (ptr c (ntarray 0 0 int))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (3 : int)))))

  ;; still works with messed up annotations
  (parameterize ((*F* (term ((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call 1
                                          (x + (1 : int))))
                                       (0 : int))) : int)))))
    (test-->>
     (---> 'c)

     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (1 : (ptr c (ntarray 0 0 int))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (3 : int)))))

  ;; arity
  (parameterize ((*F* (term ((defun ((x : int)
                               (x + (1 : int))) : int)))))
    (test-->>
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (2 : int) (2 : int) )))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (2 : int) (2 : int) ))))
    (test-->>
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (2 : int) )))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (3 : int)))))

  ;; determinism
  (parameterize ((*F* (term ((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                               (if (* x)
                                   ((1 : int) +
                                              (call 1
                                          (x + (1 : int))))
                                       (0 : int))) : int)))))
    (test-->
     (---> 'c)

     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (call 1 (1 : (ptr c (ntarray 0 0 int))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 0 int))) in
                 (if (* x)
                     ((1 : int) +
                                (call 1
                            (x + (1 : int))))
                     (0 : int))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 0 int))) in
                 (if (* x)
                     ((1 : int) +
                                (call 1
                            (x + (1 : int))))
                     (0 : int)))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 (if (1 : int)
                     ((1 : int) +
                                (call 1
                            (x + (1 : int))))
                     (0 : int))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 (if (1 : int)
                     ((1 : int) +
                                (call 1
                            (x + (1 : int))))
                     (0 : int)))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        (x + (1 : int))))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        (x + (1 : int)))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int))))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int)))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        (2 : (ptr c (ntarray -1 0 int)))))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                            (call 1
                        (2 : (ptr c (ntarray -1 0 int))))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
                       (if (* x)
                                   ((1 : int) +
                                              (call 1
                                          (x + (1 : int))))
                                   (0 : int))))))))

    (test-->
     (---> 'c)
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
                       (if (* x)
                                   ((1 : int) +
                                              (call 1
                                          (x + (1 : int))))
                                   (0 : int)))))))
     (term (((1 : int) (1 : int) (1 : int) (0 : int))
            (let x = (1 : (ptr c (ntarray 0 1 int))) in
                 ((1 : int) +
                  (let x = (2 : (ptr c (ntarray -1 1 int))) in
                       (if (1 : int)
                                   ((1 : int) +
                                              (call 1
                                          (x + (1 : int))))
                                       (0 : int))))))))))



(module+ test
  (test-equal (term (⊢types () (ntarray 0 0 int))) (term (int)))
  (test-equal (term (⊢types () (ntarray 0 1 int))) (term (int int)))

  (test--> ~~>
           (term (((8 : int) (0 : int))
                  (let x = (1 : (ptr c (ntarray 0 0 int))) in (* x))))
           (term (((8 : int) (0 : int))
                  (let x = (1 : (ptr c (ntarray 0 1 int))) in (8 : int)))))

  (test-->>∃ ~~>
             (term (((8 : int) (0 : int))
                    (let x = (1 : (ptr c (ntarray 0 0 int))) in (* x))))
             (curry (default-equiv)
                    (term (((8 : int) (0 : int))
                           (let x = (1 : (ptr c (ntarray 0 1 int))) in (8 : int))))))

  (test-->> (---> 'c)
            (term (((8 : int) (0 : int))
                   (let x = (1 : (ptr c (ntarray 0 0 int))) in
                        (if (* x)
                            (let y = (x + (1 : int)) in
                                 (* y))
                            (1 : int)))))
            (term (((8 : int) (0 : int)) (0 : int))))
  (test-->> (---> 'c)
            (term (((8 : int) (0 : int))
                   (if (5 : int) (2 : int) (3 : int))))
            (term (((8 : int) (0 : int)) (2 : int)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subtype

(define-judgment-form CoreChkC+
  #:contract (⊢subtype τ τ)
  #:mode (⊢subtype I I)

  [
   -------------- Sub-Nt
   (⊢subtype (ptr c (nt-array l h τ)) (ptr c (array l h τ)))]

  [
   ------------- Sub-Refl
   (⊢subtype τ τ)]

  [
   ------------- Sub-Ptr
   (⊢subtype (ptr c τ) (ptr c (array 0 1 τ)))]

   [
   ------------- Sub-Arr
   (⊢subtype (ptr c (array 0 1 τ)) (ptr c τ))]

  [
   (where #t (⊢bound-le? le le_1))
   (where #t (⊢bound-le? he_1 he))
   ------------- Sub-SubsumeNT
   (⊢subtype (ptr c (ntarray le he τ)) (ptr c (ntarray le_1 he_1 τ)))]

  [
   (where #t (⊢bound-le? le le_1))
   (where #t (⊢bound-le? he_1 he))
   ------------- Sub-Subsume
   (⊢subtype (ptr c (array le he τ)) (ptr c (array le_1 he_1 τ)))]

  ;; Again to match Coq developement, might remove
  ;; something wrong syntactically here
  [(where ((τ_f f) _ ...) (⊢struct-lookup ,(*D*) T))
   (⊢subtype τ_f τ)
   ------------- Sub-struct-array-field
   (⊢subtype (ptr c (struct T)) (ptr c τ))])

;;tests for subtyping
(module+ test
  (parameterize ((*D* (term ((foo ((int x) (int y)))))))
;; tests for subtyping
  (test-judgment-holds
   (⊢subtype int int))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray 0 6 int)) (ptr c (ntarray 0 6 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray 0 6 int)) (ptr c (ntarray 0 2 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 6 int)) (ptr c (array 0 2 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 6 int)) (ptr c (array 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array -1 6 int)) (ptr c (array 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray -1 6 int)) (ptr c (ntarray 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c int) (ptr c (array 0 1 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 1 int)) (ptr c int)))
  (test-judgment-holds
   (⊢subtype (ptr c (struct foo)) (ptr c int)))
 

;; bound-le? function
  (test-equal (term (⊢bound-le? 3 7)) #t)
  (test-equal (term (⊢bound-le? (x + 7) (x + 8))) #t)
  (test-equal (term (⊢bound-le? 3 3)) #t)
  (test-equal (term (⊢bound-le? 13 7)) #f)
  (test-equal (term (⊢bound-le? (x + 5) (y + 1))) #f)
  (test-equal (term (⊢bound-le? (x + 5) (x + 1))) #f)))

(define-judgment-form CoreChkC+
  #:contract (⊢Fwf>>> Γ σ ρ m F eF)
  #:mode     (⊢Fwf>>> I I I I I O)
  [------------- WF-FUN-NIL
   (⊢Fwf>>> Γ σ ρ m () ())]
  [(⊢Fwf>>> Γ σ ρ m ((defun ((x_0 : τ_0) ... e_0) : τ_res0) ...) ((defun x_1 ... ee_1) ...))
   (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ_res e ee)
   ------------- WF-FUN-CONS
   (⊢Fwf>>> Γ σ ρ m ((defun ((x : τ) ... e) : τ_res) (defun ((x_0 : τ_0) ... e_0) : τ_res0) ...)
            ((defun x ... ee) (defun x_1 ... ee_1) ...))])

(define-judgment-form CoreChkC+
  #:contract (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ e ee)
  #:mode     (⊢fwf>>> I I I I I             I I O)
  [(⊢awf Γ ((x : τ) ...))
   (where (cE ρ_′) (⊢extend-ρ′ ((x : τ) ...) ρ))
   (⊢ty>>> ((x = none : τ) ... ) σ ρ_′ m e ee τ_res)
   ------------- WF-FUN
   (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ_res e (in-hole cE ee))])

;; Typing
(define-judgment-form CoreChkC+
  #:contract (⊢ty>>> Γ σ ρ m e ee τ)
  #:mode     (⊢ty>>> I I I I I O O)

  [(⊢ty>>> Γ σ ρ m x x (ptr m_′ (ntarray le he τ)))
   (where τ_2 (⊢nt-incr (ptr m_′ (ntarray le he τ))))
   (⊢ty>>> (⊢extend-Γ (x = none : τ_2) Γ)  σ ρ m e_1 ee_1 τ_1)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_3)
   (where τ_4 (⊢join-type Γ τ_1 τ_3))
   ------------- T-IfNT
   (⊢ty>>> Γ σ ρ m (if (* x) e_1 e_2)
           (if (⊢widen-bounds-deref ρ x (ptr m_′ (ntarray le he τ)) (* (if x x (enull))))
               ee_1 ee_2) τ_4)]
  ;; TODO: add join
  [(⊢ty>>> Γ σ ρ m e ee τ)
   (where #f (⊢nt-ptr-deref? Γ e))
   (⊢ty>>> Γ σ ρ m e_1 ee_1 τ_1)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_2)
   (where τ_3 (⊢join-type Γ τ_1 τ_2))
   ------------- T-IfNonNT
   (⊢ty>>> Γ σ ρ m (if e e_1 e_2) (if ee ee_1 ee_2) τ_3)]

  [(where (_ τ) (⊢ty-env-lookup Γ x))
   (⊢wf Γ τ)
   ------------- T-Var
   (⊢ty>>> Γ σ ρ m x x τ)]

  ;; POST rules
  [(where (_ ... (n : τ) _ ...) σ)
   ------------- T-VConst
   (⊢ty>>> Γ σ ρ m (n : τ) n τ)]

  ;; NOTE: this rule is only for function elimination
  ;; the well-formdness judgment handles the introduction
  [(where (defun ((x : τ_2) ..._1 e) : τ) (⊢fun-lookup ,(*F*) n_1))
   (where (τ_2′ ... τ_res) (⊢instantiate-fun-args τ (x τ_2 e_2) ...))
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_2′′) ...
   (⊢subtype τ_2′′  τ_2′) ...
   ------------- T-VCall
   (⊢ty>>> Γ σ ρ m (call n_1 e_2 ..._1) (call n_1 ee_2 ...) τ_res)]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 τ_1)
   (where (cE ρ_′) (⊢extend-ρ x τ_1 ρ))
   (⊢ty>>> (⊢extend-Γ (x = e_1 : τ_1) Γ) σ ρ_′ m e_2 ee_2 τ)
   (where #f (⊢checked-strlen-var? Γ e_1))
   ------------- T-LetNonStr
   (⊢ty>>> Γ σ ρ m (let x = e_1 in e_2)
           (let x = ee_1 in (in-hole cE ee_2)) (⊢instantiate-type x e_1 τ))]

  [(where (maybe-e (ptr m_′ (ntarray le he τ_1))) (⊢ty-env-lookup Γ x_2))
   (⊢ty>>> (⊢extend-Γ (x_2 = maybe-e : (ptr m (ntarray le (x_1 + 0) τ_1)))
                   (⊢extend-Γ (x_1 = (strlen x_2) : int) Γ))
           σ ρ m e ee τ)
   (where (_ x_high) (⊢bound-var-lookup ρ x_2))
   (where eff ,(variable-not-in (term (x_high x_1 ee)) 'eff_strlen))
   (where τ_2 (⊢instantiate-type x_1 (strlen x_2) τ))
   ------------- T-LetStr
   ;; no need to extend ρ here because x_1 is an integer, not an array pointer
   (⊢ty>>> Γ σ ρ m (let x_1 = (strlen x_2) in e)
           (let x_1 = (strlen (⊢insert-check #f ρ x_2 x_2 (ptr m_′ (ntarray le he τ_1))))
                in (⊢insert-strlen-widening m_′ x_1 x_high ee))
        τ_2)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr m_′ (ntarray le he τ)))
   ------------- T-Str
   (⊢ty>>> Γ σ ρ m (strlen e)
        (⊢widen-bounds-strlen ρ e
                              (ptr m_′ (ntarray le he τ))
                              (strlen (⊢insert-check #f ρ e ee (ptr m_′ (ntarray le he τ)))))
        int)]

  [(where #t (⊢base? n τ))
   ------------- T-Base
   (⊢ty>>> Γ σ ρ m (n : τ) n τ)]

  ;; TODO: add proper subtyping
  [(where (ptr c vω) τ)
   (where (τ_0 ..._1) (⊢types ,(*D*) vω))
   (where #t (⊢heap-defined? ,(*H*) n vω))
   (where ((n_1 : τ_1) ..._1 _ ...) (⊢heap-from ,(*H*) n vω))
   (where ((n_′ : τ_′) ...) σ)
   (⊢ty>>> Γ ((n : τ) (n_′ : τ_′) ...) ρ m (n_1 : τ_1) n_1 τ_0) ...
   ------------- T-PtrC
   (⊢ty>>> Γ σ ρ m (n : τ) n τ)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr m_′ (struct T)))
   (where ((τ_0 f_0) ... (τ_f f) _ ...) (⊢struct-lookup ,(*D*) T))
   (where n ,(length (term (τ_0 ...))))
   ------------- T-Amper
   (⊢ty>>> Γ σ ρ m (& e → f) ((⊢insert-null-check′ ρ ee (ptr m_′ (struct T)))  + n) (ptr m_′ τ_f))]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 int)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   ------------- T-BinopInt
   (⊢ty>>> Γ σ ρ m (e_1 + e_2) (ee_1 + ee_2) int)]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr m_′ ω))
   (where ω_′ (⊢bounds-sub ω n))
   (⊢ty>>> Γ σ ρ m (n : τ) n int)
   ------------- T-BinopInd
   (⊢ty>>> Γ σ ρ m (e_1 + (n : τ)) ((⊢insert-null-check′ ρ ee_1 (ptr m_′ ω)) + n) (ptr m_′ ω_′))]

  [(⊢wf Γ (ptr c ω))
   (where #t (⊢malloc-type-wf ω))
   ------------- T-Mac
   (⊢ty>>> Γ σ ρ m (malloc ω) (malloc (⊢sizeof ω)) (ptr c ω))]

  [(⊢ty>>> Γ σ ρ u e ee τ)
   ------------- T-Unchecked
   (⊢ty>>> Γ σ ρ m (unchecked e) ee τ)]

  [(⊢ty>>> Γ σ ρ m e ee τ_′)
   (where #t (⊢dyn-bound-cast-ok? τ_′ τ))
   (where x_e ,(gensym 'x_e))
   (where ee_′ (⊢insert-bounds-check-dyn ρ x_e e τ_′ τ))
   ------------- T-DynCast
   (⊢ty>>> Γ σ ρ m (dyn-bound-cast τ e) (let x_e = ee in ee_′) τ)]

  [(⊢ty>>> Γ σ ρ m e ee τ_′)
   (where #t (⊢cast-ok? m τ_′ τ))
   ------------- T-Cast
   (⊢ty>>> Γ σ ρ m (cast τ e) ee τ)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr m_′ ω))
   (where τ (⊢deref-type ω))
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-Def
   (⊢ty>>> Γ σ ρ m (* e) (⊢widen-bounds-deref ρ e (ptr m_′ ω)
                                           (* (⊢insert-check #f ρ e ee (ptr m_′ ω)))) τ)]

  
  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr m_′ ω))
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   (where #t (⊢mode-ok? m_′ m))
   (where #f (⊢is-literal? e_2))
   (where #f (⊢is-array-or-nt-array? ω)) ; this used to be #f; I have no idea why
   (where τ (⊢deref-type ω))
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e_1 ω))
   (where (x_ee x_ee1 x_ee2)
          ,(variables-not-in (term (ee_1 ee_2 ρ ω)) '(x x x)))
   ------------- T-Ind
   (⊢ty>>> Γ σ ρ m
           (* (e_1 + e_2))
           (* (let x_ee1 = ee_1 in
                   (let x_ee2 = ee_2 in
                        (let x_ee = ((if x_ee1 x_ee1 (enull)) + x_ee2) in
                             (if x_ee
                                 (if (1 <=? (ee_lo - x_ee2))
                                     (ebounds)
                                     (if ((ee_hi - x_ee2) <=? (⊢array-upper-shift #f ω))
                                         (ebounds)
                                         x_ee))
                                 (enull)))))) τ)]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr m_′ ω))
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ)
   (where τ (⊢deref-type ω))
   (where (x_e1 x_e2) ,(variables-not-in (term (ee_1 ee_2 ω τ)) '(x_e1 x_e2)))
   (where #t (⊢mode-ok? m_′ m))
   ------------- T-Assign
   ;; TODO: rewrite without helper functions
   (⊢ty>>> Γ σ ρ m (* e_1 = e_2)
           (let x_e1 = ee_1 in
                (let x_e2 = ee_2 in
                     (* (⊢insert-check #t ρ e_1 x_e1 (ptr m_′ ω)) = x_e2))) τ)]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr m_′ ω))
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   (⊢ty>>> Γ σ ρ m e_3 ee_3 τ)
   (where #t (⊢mode-ok? m_′ m))
   (where #f (⊢is-literal? e_2))
   (where #f (⊢is-array-or-nt-array? ω))
   (where τ (⊢deref-type ω))
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e_1 ω))
   (where (x_ee1 x_ee2 x_ee3 x_ee),(variables-not-in (term (ee_1 ee_2 ρ ω)) '(x x x x)))
   ------------- T-IndAssign
   (⊢ty>>> Γ σ ρ m (* (e_1 + e_2) = e_3)
           (* (let x_ee1 = ee_1 in
                   (let x_ee2 = ee_2 in
                        (let x_ee3 = ee_3 in
                             (let x_ee = ((if x_ee1 x_ee1 (enull)) + x_ee2) in
                                  (if x_ee
                                      (if (1 <=? (ee_lo - x_ee2))
                                          (ebounds)
                                          (if ((ee_hi - x_ee2) <=? (⊢array-upper-shift #t ω))
                                              (ebounds)
                                              (* x_ee = ee_3)))
                                      (enull))))))) τ)])





;; typing rule that ignores the compiled expression
;; we need this in order to run the old tests
(define-judgment-form CoreChkC+
  #:contract (⊢ty Γ σ m e τ)
  #:mode     (⊢ty I I I I O)
  [(⊢ty>>> Γ σ () m e _ τ)
   -------------
   (⊢ty Γ σ m e τ)])

(define-judgment-form CoreChkC+
  #:contract (⊢awf Γ ((x : τ) ...))
  #:mode     (⊢awf I I)

  [------------- WFA-NIL
   (⊢awf Γ ())]

  [(⊢wf Γ τ_0)
   (⊢awf (⊢extend-Γ (x_0 = none : τ_0) Γ) ((x_1 : τ_1) ...))
   ------------- WFA-CONS
   (⊢awf Γ ((x_0 : τ_0) (x_1 : τ_1) ...))])

(define-judgment-form CoreChkC+
  #:contract (⊢bwf Γ le)
  #:mode     (⊢bwf I I)

  ;; well-formed bounds
  [------------- WFB-INT
   (⊢bwf Γ l)]

  [(where (_ int) (⊢ty-env-lookup Γ x))
   ------------- WFB-VAR
   (⊢bwf Γ (x + l))])

(define-judgment-form CoreChkC+
  #:contract (⊢wf Γ τ)
  #:mode     (⊢wf I I)

  [------------- WF-INT
   (⊢wf Γ int)]

  [(⊢wf Γ τ)
   (⊢bwf Γ le)
   (⊢bwf Γ he)
    ------------- WF-ARPTR
   (⊢wf Γ (ptr m (array le he τ)))]

  [(⊢wf Γ τ)
   (⊢bwf Γ le)
   (⊢bwf Γ he)
    ------------- WF-NTARPTR
   (⊢wf Γ (ptr m (ntarray le he τ)))]

  [------------- WF-STRCT
   (⊢wf Γ (ptr m (struct T)))]

  [(⊢wf Γ τ)
    ------------- WF-TPTR
   (⊢wf Γ (ptr m τ))])

;; do we need to widen bounds with unchecked pointers? probably yes

;; the boolean flag indicates whether we are assigning or not


(define-metafunction CoreChkC+
  ⊢insert-strlen-widening : m x x ee -> ee
  [(⊢insert-strlen-widening u _ _ ee) ee]
  [(⊢insert-strlen-widening c x_new x_hi ee)
   (let eff = (if (x_new <=? x_hi)
                  0
                  (x_hi = x_new))
        in ee)
   (where eff ,(variable-not-in (term (x_hi x_new ee)) 'eff_strlen))])

(define-metafunction CoreChkC+
  ⊢insert-check : boolean ρ e ee (ptr m ω) -> ee
  [(⊢insert-check boolean ρ e ee (ptr m ω))
   (in-hole cE_1 ee_1)
   (where x_e ,(variable-not-in (term (e ee ω)) 'x_e))
   (where cE (let x_e = ee in hole))
   (where (cE_0 ee_0) (⊢insert-bounds-check boolean ρ e cE x_e (ptr m ω)))
   (where (cE_1 ee_1) (⊢insert-null-check cE_0 ee_0 x_e (ptr m ω)))])


(define-metafunction CoreChkC+
  ⊢insert-null-check′ : ρ ee (ptr m ω) -> ee
  [(⊢insert-null-check′ ρ ee (ptr m ω))
   (in-hole cE_0 ee_0)
   (where x_e ,(variable-not-in (term (ρ ee ω)) 'x_e))
   (where cE (let x_e = ee in hole))
   (where (cE_0 ee_0) (⊢insert-null-check cE x_e x_e (ptr m ω)))])


(define-metafunction CoreChkC+
  ⊢insert-bounds-check-dyn : ρ x e (ptr m ω) (ptr m ω) -> ee
  [(⊢insert-bounds-check-dyn ρ x_e e (ptr m ω) (ptr m (_ le he _)))
   (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
        (let x_hi = ee_hi in
             (if (x_lo <=? le)
                 (if (he <=? x_hi)
                     x_e
                     (ebounds))
                 (ebounds))))
   (where c m)
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω))
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi)))
   or
   x_e])


(define-metafunction CoreChkC+
  ⊢insert-bounds-check : boolean ρ e cE x (ptr m ω) -> (cE ee)
  [(⊢insert-bounds-check boolean ρ e cE x_e (ptr m ω))
   ((in-hole
     cE
     (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
          (let x_hi = ee_hi in
               hole)))
    (if (1 <=? x_lo)
        (ebounds)
        (if (x_hi <=? (⊢array-upper-shift boolean ω))
            (ebounds)
            x_e)))
   (where c m)
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω))
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi)))
   or
   (cE x_e)])

(define-metafunction CoreChkC+
  ⊢insert-null-check : cE ee x (ptr m ω) -> (cE ee)
  [(⊢insert-null-check cE ee x_e (ptr m ω))
   (cE
    (if x_e
        ee
        (enull)))
   (where c m)
   or
   (cE x_e)])

(define-metafunction CoreChkC+
  ⊢array-upper-shift : boolean ω -> -1 or 0
  [(⊢array-upper-shift #f (ntarray _ _ _)) -1]
  [(⊢array-upper-shift _ _) 0])


(define-metafunction CoreChkC+
  ⊢get-accurate-bounds : ρ e ω -> (ee ee) or #f
  [(⊢get-accurate-bounds ρ e ω)
   (x_lo x_hi)
   (where x e)
   (where (x_lo x_hi) (⊢bound-var-lookup ρ x))
   or
   (⊢array-bounds ω)])


(define-metafunction CoreChkC+
  ⊢array-bounds : ω -> (ee ee) or #f
  [(⊢array-bounds (ntarray le he _))
   (le he)]
  [(⊢array-bounds (array le he _))
   (le he)]
  [(⊢array-bounds _)
   #f])


(define-metafunction CoreChkC+
  ⊢bound-var-lookup : ρ x -> (x x) or #f
  [(⊢bound-var-lookup ((x (x_lo x_hi)) _ ...) x)
   (x_lo x_hi)]
  [(⊢bound-var-lookup (_ (x_′ (x_lo′ x_hi′)) ...) x)
   (⊢bound-var-lookup ((x_′ (x_lo′ x_hi′)) ...) x)]
  [(⊢bound-var-lookup _ _) #f])


(define-metafunction CoreChkC+
  ⊢widen-bounds-deref : ρ e τ ee -> ee
  [(⊢widen-bounds-deref ρ e τ ee)
   (let x_derefed = ee in
        (if x_derefed
            (if x_hi
                x_derefed
                (let eff = (x_hi = 1) in x_derefed))
            x_derefed))
   (where (ptr c (ntarray _ _ _)) τ)
   (where #t (⊢nt-ptr? τ))
   (where x e)                          ; ee represents the compiled version of (* e_0 ...)
   (where (_ x_hi) (⊢bound-var-lookup ρ x)) ; e represents e_0 only
   (where (eff x_derefed) ,(variables-not-in (term (τ e ee ρ)) '(eff_ifnt x_derefed)))
   or
   ee])


(define-metafunction CoreChkC+
  ⊢widen-bounds-strlen : ρ e τ ee -> ee
  [(⊢widen-bounds-strlen ρ e τ ee)
   (let x_ee = ee in
        (if (x_ee <=? x_hi)
            x_ee
            (x_hi = x_ee)))
   (where #t (⊢nt-ptr? τ))
   (where x e)                          ; ee represents the compiled version of (strlen e_0 ...)
   (where (_ x_hi) (⊢bound-var-lookup ρ x)) ; e represents e_0 only
   (where (x_ee) ,(variables-not-in (term (τ e ee ρ)) '(x_ee)))
   or
   ee])

(define-metafunction CoreChkC+
  ⊢sizeof : ω -> ee or #f
  [(⊢sizeof τ) 1]
  [(⊢sizeof (struct T)) ,(length (term (⊢struct-lookup ,(*D*) T)))]
  [(⊢sizeof (array 0 he _)) he]
  [(⊢sizeof (ntarray 0 (x + i) _)) (x + ,(+ 1 (term i)))]
  [(⊢sizeof (ntarray 0 i _)) ,(+ 1 (term i))]
  [(⊢sizeof _) ,(raise 'impossible)])



(define-metafunction CoreChkC+
  ⊢dyn-bound-cast-ok? : τ τ -> #t or #f
  [(⊢dyn-bound-cast-ok? (ptr c (ntarray _ _ τ)) (ptr c (ntarray _ _ τ))) #t]
  [(⊢dyn-bound-cast-ok? (ptr c (array _ _ τ)) (ptr c (array _ _ τ))) #t]
  [(⊢dyn-bound-cast-ok? _ _) #f])

(define-metafunction CoreChkC+
  ⊢nt-ptr-deref? : Γ e -> #t or #f
  [(⊢nt-ptr-deref? Γ (* x))
   #t
   (where (_ (ptr c (ntarray _ _ _))) (⊢ty-env-lookup Γ x))]
  [(⊢nt-ptr-deref? _ _) #f])


(define-metafunction CoreChkC+
  ⊢ty-env-lookup : Γ x -> (maybe-e τ) or #f
  [(⊢ty-env-lookup () _) #f]
  [(⊢ty-env-lookup ((x = maybe-e : τ) _ ...) x) (maybe-e τ)]
  [(⊢ty-env-lookup (_ (x_′ = maybe-e_′ : τ_′) ...) x)
   (⊢ty-env-lookup ((x_′ = maybe-e_′ : τ_′) ...) x)])

(define-metafunction CoreChkC+
  ⊢base? : n τ -> #t or #f
  [(⊢base? n int) #t]
  [(⊢base? n (ptr u ω)) #t]
  [(⊢base? 0 τ) #t]
  [(⊢base? n (ptr c (array 0 0 τ_′))) #t]
  [(⊢base? n (ptr c (ntarray 0 0 τ_′))) #t]
  [(⊢base? _ _) #f])

(define-metafunction CoreChkC+
  ⊢cast-ok? : m τ τ -> #t or #f
  [(⊢cast-ok? u _ τ) #t]
  [(⊢cast-ok? c _ int) #t]
  [(⊢cast-ok? c _ (ptr u ω)) #t]
  [(⊢cast-ok? c τ_′ τ) #t
   (judgment-holds (⊢subtype τ_′ τ))]
  [(⊢cast-ok? _ _ _) #f])


;; deref-type under the context of operational semantics
(define-metafunction CoreChkC+
  ⊢deref-type-dyn : D τ -> τ
  [(⊢deref-type-dyn _ int) int]
  [(⊢deref-type-dyn _ (ptr m τ)) τ]
  [(⊢deref-type-dyn _ (ptr m (ntarray _ _ τ))) τ]
  [(⊢deref-type-dyn _ (ptr m (array _ _ τ))) τ]
  [(⊢deref-type-dyn D (ptr m (struct T)))
   τ_1
   (where ((τ_1 _) _ ...) (⊢struct-lookup D T))])

(define-metafunction CoreChkC+
  ⊢deref-type : ω -> τ
  [(⊢deref-type τ) τ]
  [(⊢deref-type (array le he τ)) τ]
  [(⊢deref-type (ntarray le he τ)) τ])


(define-metafunction CoreChkC+
  ⊢mode-ok? : m m -> #t or #f
  [(⊢mode-ok? u u) #t]
  [(⊢mode-ok? c _) #t]
  [(⊢mode-ok? _ _) #f])

(module+ test
  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 0 int)))) () c p (ptr c (ntarray -3 0 int))))

  (test-equal (term (⊢deref-type (ntarray -3 1 int))) (term int))

  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 1 int)))) () c (* p) int))

  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 1 int)))) () c ((* p) + (1 : int)) int))

  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 0 int)))) () c (if (* p) ((* p) + (1 : int)) (5 : int)) int))

  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 0 int)))) () c (if (* p) (55 : int) (5 : int)) int))

  ;;test let
  (test-judgment-holds
   (⊢ty () () c (let x = (5 : int) in (6 : int)) int))

  (test-judgment-holds
   (⊢ty () () c (let x = (5 : int) in x) int))

  (test-judgment-holds
   (⊢ty () () c (let x = (5 : int) in (let y = (6 : int) in (x + y))) int))

  ;;tests if rule, type only changes if h is 0
  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray 0 6 int)))) () c (if (* p) p p) (ptr c (ntarray 0 6 int))))

  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -1 0 int))) (x = none : (ptr c (ntarray -1 1 int)))) () c (if (* p) p x) (ptr c (ntarray -1 1 int))))
  ;; tests multi-variable let rule

  (test-judgment-holds
   (⊢ty () () c (let x = (5 : int) in (let y = (6 : int) in (x + y))) int))

  (test-judgment-holds
   (⊢ty () () c (let x = (5 : int) in (let y = (6 : int) in (let z = (malloc (ptr c (array 0 1 int))) in (x + y)))) int))

  (test-judgment-holds
   (⊢ty () () c (let x = (malloc (array 0 1 int)) in
                     (let y = (malloc (array 0 1 int)) in
                          (let z = (malloc (array 0 1 int)) in
                               (* (x + (* y))))))
        int))

  (test-judgment-holds
   (⊢ty () () c (let x = (malloc (array 0 1 int)) in (* x)) int)))


(define-metafunction CoreChkC+
  ⊢lookup-bounds : x ρ -> (x x)
  [(⊢lookup-bounds x ((x_!_0 (_ _)) ... (x (x_0 x_1)) (x_!_0 (_ _)) ...))
   (x_0 x_1)])


(define-metafunction CoreChkC+
  ⊢instantiate-fun-args : τ (x τ e) ... -> (τ ...) or #f
  [(⊢instantiate-fun-args τ)
   (τ)]
  [(⊢instantiate-fun-args τ_res (x_0 int e_0) (x_1 τ_1 e_1) ...)
   (int τ_′ ...)
   (where (τ_1′ ...) ((⊢instantiate-type x_0 e_0 τ_1) ...))
   (where τ_res′ (⊢instantiate-type x_0 e_0 τ_res))
   (where (τ_′ ...) (⊢instantiate-fun-args τ_res′ (x_1 τ_1′ e_1) ...))
   or
   #f]
  [(⊢instantiate-fun-args τ_res (x_0 τ_0 e_0) (x_1 τ_1 e_1) ...)
   (τ_0 τ_′ ...)
   (where (τ_′ ...) (⊢instantiate-fun-args τ_res (x_1 τ_1 e_1) ...))])

;;; need to figure out a different way to do this in coq.
;;; can't prove termination the way it is
(define-metafunction CoreChkC+
  ⊢instantiate-type : x e τ -> τ or #f
  [(⊢instantiate-type x (n : int) (in-hole Eτ (x + l)))
   (⊢instantiate-type x (n : int) (in-hole Eτ ,(+ (term n) (term l))))]
  [(⊢instantiate-type x x_0 (in-hole Eτ (x + l)))
   (⊢instantiate-type x x_0 (in-hole Eτ (x_0 + l)))]
  [(⊢instantiate-type x e (in-hole Eτ (x + l)))
   #f]
  [(⊢instantiate-type x _ τ)
   τ])


(define-metafunction CoreChkC+
  ⊢bind-expr : ee -> (cE x)
  [(⊢bind-expr ee)
   ([let x = ee in hole] x)
   (where x ,(gensym 'x_e))])

(define-metafunction CoreChkC+
  ⊢check : ρ x τ -> cE
  [(⊢check ρ x (ptr c τ))
   (⊢check-null x)]
  [(⊢check ρ x (ptr c (struct T)))
   (⊢check-null x)]
  [(⊢check ρ x (ptr c (ntarray le he τ)))
   (in-hole (⊢check-bounds-nt ρ x) (⊢check-null x))]
  [(⊢check ρ x (ptr c (array le he τ)))
   (in-hole (⊢check-bounds ρ x) (⊢check-null x))]
  [(⊢check ρ x _)
   hole])

(define-metafunction CoreChkC+
  ⊢check-null : x -> cE
  [(⊢check-null x) (if x hole (enull))])

;; is it really a good idea to make this partial?
(define-metafunction CoreChkC+
  ⊢check-bounds : ρ x -> cE or #f
  [(⊢check-bounds (_ ... (x (x_lo x_hi)) _ ...) x)
   (if (x_hi <=? 0)
       (ebounds)
       (if (1 <=? x_lo)
           (ebounds)
           hole))]
  [(⊢check-bounds _ _)
   #f])

;; is it really a good idea to make this partial?
(define-metafunction CoreChkC+
  ⊢check-bounds-nt : ρ x -> cE or #f
  [(⊢check-bounds-nt (_ ... (x (x_lo x_hi)) _ ...) x)
   (if (x_hi <=? -1)
       (ebounds)
       (if (1 <=? x_lo)
           (ebounds)
           hole))]
  [(⊢check-bounds-nt _ _)
   #f])

(define-metafunction CoreChkC+
  ⊢widen-bounds-deref-new : ρ x -> cE or #f
  [(⊢widen-bounds-deref-new (_ ... (x (_ x_hi)) _ ...) x)
   (if x_hi
       hole
       (let x_tmp = (x_hi = 1) in
            hole))
   (where x_tmp ,(gensym 'eff_))]
  [(⊢widen-bounds-deref-new _ _)
   #f])

(define-metafunction CoreChkC+
  ⊢widen-bounds-strlen-new : ρ x x -> cE or #f
  [(⊢widen-bounds-strlen-new (_ ... (x (_ x_hi)) _ ...) x x_strlen)
   (if (x_strlen <=? x_hi)
       hole
       (let x_tmp = (x_hi = x_strlen) in
            hole))
   (where x_tmp ,(gensym 'eff_))]
  [(⊢widen-bounds-strlen-new _ _)
   #f])

(module+ test
  (parameterize ((*D* (term ((foo ((int x) (int y)))))) ; a struct defn
                 (*H* (term ((5 : int))))) ; a heap for the type system tests

    (test-judgment-holds (⊢wf () int))
    (test-judgment-holds (⊢wf () (ptr c (array 0 5 int))))
    (test-judgment-holds (⊢wf ((x = none : int)) (ptr c (array (x + 0) (x + 5) int))))
    (test-judgment-holds (⊢ty ((x = none : int)) () c x int))
    (test-judgment-holds (⊢ty () ((5 : int)) c (5 : int) int))
    (test-judgment-holds (⊢ty () ((5 : int)) c (let x = (5 : int) in x) int))
    (test-judgment-holds (⊢ty () () c (0 : int) int))
    (test-judgment-holds (⊢ty () () c (4 : int) int))
    (test-judgment-holds (⊢ty () () c (0 : (ptr c int)) (ptr c int)))
    (test-judgment-holds (⊢ty () () c (1 : (ptr c (array 0 0 int)))
                              (ptr c (array 0 0 int))))
    (test-judgment-holds (⊢ty () () c (0 : (ptr c (array 0 0 int)))
                              (ptr c (array 0 0 int))))
    (test-judgment-holds (⊢ty () () c (1 : (ptr u (array 0 5 int)))
                              (ptr u (array 0 5 int))))
    (test-equal (judgment-holds (⊢ty () () c (1 : (ptr c (array 0 5 int))) τ) τ)
                '())
    (test-judgment-holds (⊢ty () () c (1 : (ptr c int)) (ptr c int))) ; T-PtrC
    (parameterize ((*D* '((T ((int y) (int x))))))
      (test-judgment-holds (⊢ty () () c (& (* (malloc (ptr c (struct T))) = (malloc (struct T))) → x) τ)))
    (test-judgment-holds (⊢ty () () c (& (malloc (struct foo)) → x)
                              (ptr c int)))
    (test-judgment-holds (⊢ty () () c ((1 : int) + (2 : int)) int))
    (test-judgment-holds (⊢ty () () c (malloc int) (ptr c int)))
    ;; need to allow this for now on
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
     (⊢ty () () c (* ((malloc (array 0 3 int)) + ((1 : int) + (1 : int)))) int))
    (test-judgment-holds
     (⊢ty () () c (* (malloc (array 0 3 int)) = (5 : int)) int))
    (test-judgment-holds
     (⊢ty () () c (* ((malloc (array 0 3 int)) + (1 : int)) = (5 : int)) int))

    ;; same tests but for ntarray
    (test-judgment-holds
     (⊢ty () () c (* (malloc (ntarray 0 3 int))) int))
    (test-judgment-holds
     (⊢ty () () c (* ((malloc (ntarray 0 3 int)) + ((1 : int) + (1 : int)))) int))
    (test-judgment-holds
     (⊢ty () () c (* (malloc (ntarray 0 3 int)) = (5 : int)) int))
    (test-judgment-holds
     (⊢ty () () c (* ((malloc (ntarray 0 3 int)) + (1 : int)) = (5 : int)) int))

    ;; T-LetStr
    (test-judgment-holds
     (⊢ty () () c (let x = (malloc (ntarray 0 4 int)) in
                       (let x_0 = (strlen x) in
                            x_0
                            )) int))

(test-judgment-holds
     (⊢ty () () c (let x = (malloc (ntarray 0 4 int)) in
                       (let x_0 = (strlen x) in
                            (let x_1 =
                              (if (1 : int)
                                  x
                                  (malloc (ntarray 0 (x_0 + 0) int))) in (1 : int)))) int))


    ;; T-Str
    (test-judgment-holds
     (⊢ty () () c (strlen (malloc (ntarray 0 4 int)))  int))

    ;; T-BinopInd
    (test-judgment-holds
     (⊢ty () () c
          (let x = (malloc (ntarray 0 4 int)) in
               (x + (3 : int))) (ptr c (ntarray -3 1 int))))

    (test-judgment-holds
     (⊢ty () () c
          (let x = (malloc (array 0 4 int)) in
               (x + (3 : int))) (ptr c (array -3 1 int))))

    (test-judgment-holds
     (⊢ty () () c
          (let x = (malloc (array 0 4 int)) in
               (let y = (x + (3 : int)) in (* y))) int))

    ;; T-VCall
    (parameterize ([*F* (term ((defun ((x : int) (x + (1 : int))) : int)
                               ;; 2: dependent function
                               (defun ((x : int) (y : (ptr c (array 0 (x + 1) int)))
                                       (* (y + x))) : int)
                               ;; 3: yet another dependent function
                               (defun ((x : int)
                                       (malloc (array 0 (x + 1) int))) :
                                       (ptr c (array 0 (x + 1) int)))


                               ;; 4: a non-dependent function for testing subtyping
                               (defun ((y : (ptr c (array 0 5 int))) y) : (ptr c (array 0 5 int)))))])
      (test-judgment-holds
       (⊢ty () () c
            (call 1 (2 : int))
            int))

      (test-judgment-holds
       (⊢subtype (ptr c (array -1 9 int)) (ptr c (array 0 5 int))))
      (test-judgment-holds
       (⊢ty () () c
            (call 4 (0 : (ptr c (array -1 9 int))))
            (ptr c (array 0 5 int))))

      (test-judgment-holds
       (⊢ty () () c
            (call 2 (0 : int) (malloc (array 0 1 int)))
            int))

      (test-judgment-holds
       (⊢ty ((y = none : int) (x = none : int)) () c
            (call 2 y (malloc (array 0 (y + 1) int)))
            int))

      (test-equal (judgment-holds
                   (⊢ty ((y = none : int) (x = none : int)) () c
                        (call 2 y (malloc (array 0 (x + 1) int)))
                        τ) τ)
        '())

      (test-equal (judgment-holds
                   (⊢ty ((y = none : int) (x = none : int)) () c
                        (call 3 (y + (1 : int)))
                        τ) τ)
        '())

      (test-judgment-holds
       (⊢ty () () c
            (call 3 (1 : int))
            (ptr c (array 0 2 int))))

      (test-judgment-holds
       (⊢ty ((y = none : int)) () c
            (call 3 y)
            (ptr c (array 0 (y + 1) int))))


      (test-judgment-holds
       (⊢ty () () c
            (call 2 (0 : int) (malloc (array 0 2 int)))
            int))

      ;; fails because the function expects an array of size x + 1, and in this case x = 1
      (test-equal (judgment-holds
                 (⊢ty () () c
                      (call 2 (1 : int) (malloc (array 0 1 int)))
                      τ) τ)
                '()))))

(define-syntax-rule (type-check e)
  (judgment-holds (⊢ty () () c e τ) τ))

(define-syntax-rule (test-type-check e τ)
  (test-equal (type-check e) '(τ)))

(define-syntax-rule (test-type-check-fails e)
  (test-equal (type-check e) '()))


(define-syntax-rule (compile-e e)
  (compile-e* (term e)))

(define (compile-e* e #:H [H '()])
  (parameterize ([*H* H])
    (match (judgment-holds (⊢ty>>> () () () c ,e ee _) ee)
      [(list ee) ee]
      ['() (error (call-with-output-string (λ (p) (fprintf p "does not typecheck:~a" (list H e)))))]
      [(list _ _ ...) (raise "typing judgment is non-deterministic")])))

(define (compile-F* F)
  (match (judgment-holds (⊢Fwf>>> () () () c ,F eF) eF)
    [(list eF) eF]
    ['() (raise "one of the functions is not well-formed")]
    [(list _ _ ...) (raise "typing judgment is non-deterministic (Fwf)")]))


(define (iterate---> conf cache)
  (match (apply-reduction-relation (---> 'c) conf)
    [(list) (cons conf cache)]
    [(list new-conf) (iterate---> new-conf (cons conf cache))]
    [_ (raise "reduction relation for e is non-deterministic")]))

(define (⇓e-c e #:H [H '()])
  (iterate---> (list H e) '()))

(define (⇓e e #:H [H '()])
  (match (apply-reduction-relation*
          --->cu
          (term (,H ,e)))
    [(list e) e]
    ['() (error "not possible?")]
    [_ (error "reduction relation for ee is non-deterministic")]))

(define (iterate-CEK conf)
  (match (apply-reduction-relation --->^CEK conf)
    [(list) conf]
    [(list new-conf) (iterate-CEK new-conf)]
    [_ (error "reduction relation for ee is non-deterministic")]))

(define (⇓ee ee #:eH [eH '()])
  (iterate-CEK
   (term (,eH () ,ee ()))))


(module+ test
  (test-->> (---> 'c)
            (term (((8 : int) (0 : int))
                   (let x = (1 : int) in
                        (let y = (4 : (ptr c (array (x + -1) 6 int))) in
                             y))))
            (term (((8 : int) (0 : int)) (4 : (ptr c (array 0 6 int))))))
  (parameterize ((*D* (term ((foo ((int x) (int y)))))) ; a struct defn
                 (*H* (term ((5 : int) (5 : int) (7 : int))))) ; a heap for the type system tests
    (test-judgment-holds
     (⊢ty () () c (unchecked (cast (ptr c int) (5 : int))) (ptr c int))))
  (test-equal
    (judgment-holds
      (⊢ty ((x = none : (ptr c (ntarray 0 1 int))) (x = none : (ptr c (ntarray 0 0 int))))
        () c x τ)
      τ)
    '((ptr c (ntarray 0 1 int))))

  ;; for function preservation
  (test-equal
    (judgment-holds
      (⊢ty () () c (let x = (4 : int) in (malloc (ntarray 0 (x + 0) int))) τ) τ)
    '((ptr c (ntarray 0 4 int))))

  ;; T-LetNonStr
  (test-type-check (let g55676 = (strlen (malloc (ntarray 0 12 int))) in (1 : int)) int)

  (test-equal (term (⊢dyn-bound-cast-ok? (ptr c (ntarray 0 4 int)) (ptr c (ntarray -2 6 int)))) #t)
  (test-equal (term (⊢dyn-bound-cast-ok? (ptr c (ntarray -2 6 int)) (ptr c (ntarray 0 4 int)))) #t)

  (test-type-check (0 : (ptr c (ntarray -2 6 int))) (ptr c (ntarray -2 6 int)))

  ;; T-DynCast
  (test-type-check (dyn-bound-cast (ptr c (ntarray 0 4 int)) (0 : (ptr c (ntarray -2 6 int)))) (ptr c (ntarray 0 4 int)))
  (test-type-check (dyn-bound-cast (ptr c (ntarray -2 6 int)) (0 : (ptr c (ntarray 0 4 int)))) (ptr c (ntarray -2 6 int)))
  (test-type-check-fails
   (dyn-bound-cast (ptr c (ntarray 0 4 (ptr c (array 0 1 int)))) (0 : (ptr c (ntarray -2 6 int)))))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (ntarray 0 4 int))
                           (0 : (ptr c (ntarray -2 6 int))))))
           (term (() (0 : (ptr c (ntarray -2 6 int))))))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (ntarray 0 4 int))
                               (0 : (ptr c (ntarray 2 4 int))))))
           (term (() Bounds)))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (ntarray 0 4 int))
                               (0 : (ptr c (ntarray 2 5 int))))))
           (term (() Bounds)))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (ntarray 0 4 int))
                               (0 : (ptr c (ntarray -1 3 int))))))
           (term (() Bounds)))
  (test-equal (term (⊢dyn-bound-cast-ok? (ptr c (ntarray 0 4 int)) (ptr c (ntarray -2 6 int)))) #t)
  (test-equal (term (⊢dyn-bound-cast-ok? (ptr c (ntarray -2 6 int)) (ptr c (ntarray 0 4 int)))) #t)

  (test-type-check (0 : (ptr c (ntarray -2 6 int))) (ptr c (ntarray -2 6 int)))

  ;; T-DynCast
  (test-type-check (dyn-bound-cast (ptr c (array 0 4 int)) (0 : (ptr c (array -2 6 int)))) (ptr c (array 0 4 int)))
  (test-type-check (dyn-bound-cast (ptr c (array -2 6 int)) (0 : (ptr c (array 0 4 int)))) (ptr c (array -2 6 int)))
  (test-type-check-fails
   (dyn-bound-cast (ptr c (array 0 4 (ptr c (array 0 1 int)))) (0 : (ptr c (array -2 6 int)))))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (array 0 4 int))
                           (0 : (ptr c (array -2 6 int))))))
           (term (() (0 : (ptr c (array -2 6 int))))))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (array 0 4 int))
                               (0 : (ptr c (array 2 4 int))))))
           (term (() Bounds)))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (array 0 4 int))
                               (0 : (ptr c (array 2 5 int))))))
           (term (() Bounds)))

  (test--> (---> 'c)
           (term (() (dyn-bound-cast (ptr c (array 0 4 int))
                               (0 : (ptr c (array -1 3 int))))))
           (term (() Bounds))))


;; ee
(module+ test
  (test--> --->^ (term (() (let y = 4 in (let x = 5 in x))))
           (term (() (let y = 4 in (let x = 5 in 5)))))
  (test-->> --->^ (term (() (let y = 4 in  (let x = 5  in x))))
            (term (() 5)))
  (test-->> --->^ (term (() (let x = 5 in (let x = 7 in x))) ) (term (() 7)))
  (test-->> --->^ (term (() (let x = 5 in (let eff = (x = 3) in x))) ) (term (() 3)))
  (test-->> --->^ (term (() (if (1 + 2) 5 6))) (term (() 5)))
  (test-->> --->^ (term (() (if (1 - 1) 5 6))) (term (() 6)))
  (test-->> --->^ (term ((1 1 1 1 1 0 1 1) (strlen 1))) (term ((1 1 1 1 1 0 1 1) 5)))
  (test-->> --->^ (term ((1 1 1 1 1 0 1 1) (strlen 0))) (term ((1 1 1 1 1 0 1 1) (strlen 0))))
  (test-->> --->^ (term ((1 1 1 1 1 1 1 1) (strlen 1))) (term ((1 1 1 1 1 1 1 1) (strlen 1))))
  (test-->> --->^ (term ((1 1 1 1 1 0 1 1) (strlen 10))) (term ((1 1 1 1 1 0 1 1) (strlen 10))))
  (test-->> --->^ (term ((1) (malloc 2))) (term ((1 0 0) 2)))
  (test-->> --->^ (term (() (enull))) (term (() Null)))
  (test-->> --->^ (term (() (ebounds))) (term (() Bounds)))
  (test-->> --->^ (term (() (malloc 4))) (term ((0 0 0 0) 1)))
  (test--> --->^ (term (() (malloc 0))) (term (() 0)))
  (test--> --->^ (term (() (malloc -1))) (term (() 0)))
  (parameterize ([*eF* '((defun x (let x_lo =
                                    0
                                    in
                                    (let x_hi =
                                      0
                                      in
                                      (if (let x_derefed =
                                            (* (if x x (enull)))
                                            in
                                            (if x_derefed (if x_hi x_derefed (let eff_ifnt = (x_hi = 1) in x_derefed)) x_derefed))
                                          (1 + (call 1 ((let x_e = x in (if x_e x_e (enull))) + 1)))
                                          0)))))])
    (test-->> --->^ (term ((1 1 1 1 1 0 1 1) (call 1 1))) (term ((1 1 1 1 1 0 1 1) 5))))
  (parameterize ([*eF* (term ((defun x (x + 1))))])
    (test-->> --->^ (term (() (call 1 1))) (term (() 2)))
    (test--> --->^ (term (() (call 1 1))) (term (() (let x = 1 in (x + 1))))))
  (test--> --->^ (term (() (let y = 4 in y)))
           (term (() (let y = 4 in 4))))


  (parameterize ([*eF* (term ((defun x y (x + y))))])
    (test-->>
     --->^CEK
     '(() () (let x = 4 in  ((x + (let x = 3 in (call 1 x (x + 1)))) - (let x = (malloc 1) in (16 - (* x = 4)) ) )) ())
     '((4) () -1 ())))



  (let ([ee
         (compile-e* '(let x = (malloc (ntarray 0 2 int)) in
                           ;; assign the first two elements to be 1
                           (let _ = (* x = (4 : int)) in
                                (let _ = (* (x + (1 : int)) = (1 : int)) in
                                     ;; cast the bounds of the ntarray to 0
                                     (let y = (cast (ptr c (ntarray 0 0 int)) x) in
                                          ;; access the first element
                                          ;; the upper bound of y will be extended
                                          (* y))))))])
    (test-->>
     --->^CEK
     `(() () ,ee ())
     '((4 1 0) () 4 ()))))

;; Big Step Simulation
;; If both evaluate to a value or throw an error, then perform an exact comparison (after erasing e)
;; If e or ee is stuck in some configuration (H e') where e' is not a value of error,
;;   we massage e' or ee' into 'stuck before performing the exact comparison
(define (bigstep-simulation e)
  (let ([eHeΣeeeK_′ (⇓ee (compile-e* e))]
        [He_′ (⇓e e)])
    (equal? (massage-He He_′)
            (massage-eHee eHeΣeeeK_′))))

(define (extract-single msg-thunk e)
  (match e
    [(list e) e]
    ['() (error (string-append "failed:" (force msg-thunk)))]
    [_ (error (string-append "non-deterministic behavior:" (force msg-thunk)))]))

(define (has-unchecked-redex? t)
  (ormap
   (λ (m)
     (match (term (⊢mode ,(bind-exp (first (match-bindings m)))))
       ['u #t]
       [_ #f]))
   (redex-match CoreChkC+ (in-hole E e) t)))

(define (progress-preservation e)
  (let ([es (⇓e-c e)])
    (when (*debug*)
      (for ([e es])
        (println e)))
    (let ([τs (for/list ([e (filter (redex-match? CoreChkC+ (_ e))es)])
                (parameterize ([*H* (first e)])
                  (extract-single (delay (call-with-output-string (λ (p) (print e p)))) (judgment-holds (⊢ty () ()  c ,(second e) τ) τ))))])
      (when (cons? es)
        (and
         (let ([e (second (first es))])
           ;; (println e)
           (or (redex-match CoreChkC+ ε e)
               (redex-match CoreChkC+ (n : vτ) e)
               (has-unchecked-redex? e)
               (error (call-with-output-string
                       (λ (p)
                         (fprintf p "progress does not hold. reduces to ~a" e))))))))
      (for ([τ τs]
                [τ_next (if (cons? τs) (cdr τs) '())])
        (or (judgment-holds (⊢subtype ,τ_next ,τ))
            (error (call-with-output-string
                       (λ (p)
                         (fprintf p "preservation does not hold. ~a is not a subtype of ~a" τ_next τ)))))))))

(define/match (massage-He _)
  [((list H e))
   (let ([eH (erase-heap H)]
         [ee (massage-e e)])
     (list eH ee))])

(define/match (massage-eHee _)
  [((list eH eΣ ee eK))
   (list eH (massage-ee eΣ ee eK))])

(define/match (massage-e e)
  [((list n ': _)) n]
  [('Bounds) e]
  [('Null) e]
  [(_) 'stuck])

(define (erase-heap H)
  (map (curry car) H))

(define/match (massage-ee eΣ ee eK)
  [('() n '()) ee]
  [('() 'Bounds '()) ee]
  [('() 'Null '()) ee]
  [(_ _ _) 'stuck])

;; Theorem 4: Simulation (small step version)
(define (simulation-small-step e-conf)
  (match-let ([(list H e) e-conf])
    (let ([ee-conf (list (erase-heap H) (compile-e* e #:H H))])
      (letrec ([go (λ (e-conf ee-conf)
                     (call-with-values
                      (λ () (simulation-small-step-helper e-conf ee-conf))
                      (λ xs (match xs
                              [(list (? void?)) (void)] ; no more steps can be taken
                              [(list e-conf ee-conf) (go e-conf ee-conf)]
                              [_ (error "simulation-small-step: impossible")]) ; check for one more step
                        )))])
        (go e-conf ee-conf)))))

(define/match (econfluence conf_0 conf_1)
  [((list eH_0 ee_0) (list eH_1 ee_1))
   (unless (equal? (massage-eHee (⇓ee ee_0 #:eH eH_0)) (massage-eHee (⇓ee ee_1 #:eH eH_1)))
     (error "e-confluence does not hold")
     ;; (error (format "small step simulation does not hold:\ne-conf-next: ~a\nee-conf-next: ~a\nee-conf-next*: ~a" e-conf-next conf ee-conf-next*))
     )])

(define (simulation-small-step-helper e-conf ee-conf)
  (match (apply-reduction-relation --->cu e-conf)
    [(list) (void)]  ; TODO: make sure ee-conf also evaluates to a stuck state
    [(list e-conf-next)
     (match (list e-conf e-conf-next)
       [(list (list H e) (list H-next e-next))
        (let ([eH-next (erase-heap H-next)]
              [ee-next (compile-e* e-next #:H H-next)])
          (let ([ee-conf-next* (list eH-next ee-next)])
            (econfluence ee-conf ee-conf-next*)
            ))])]
    [_ (error "simulation-small-step: non-deterministic semantics for e")]))


;; type-based compilation
(module+ test
  (check-pred bigstep-simulation
              '(* ((malloc (array 0 2 int)) + ((2 : int) + (4 : int)))))
  (check-pred bigstep-simulation
              '(* ((malloc (array 0 2 int)) + ((2 : int) + (4 : int)))))
  (check-pred bigstep-simulation
              '(* ((malloc (array 0 2 int)) + (2 : int))))
  (check-pred bigstep-simulation
              '(* ((malloc (ntarray 0 2 int)) + (2 : int))))
  (check-pred bigstep-simulation
              '(* ((malloc (ntarray 0 2 int)) + (2 : int)) = (4 : int)))
  (check-pred bigstep-simulation
              '(* ((malloc (ntarray 0 2 int)) + (1 : int)) = (4 : int)))
  (check-pred bigstep-simulation
              '(* ((malloc (array 0 2 int)) + (1 : int)) = (4 : int)))
  (check-pred bigstep-simulation
              '(* (0 : (ptr c (ntarray 0 2 int)))))
  (check-pred bigstep-simulation
              '(* (0 : (ptr c (array 0 2 int)))))
  (check-pred bigstep-simulation
              '(* (0 : (ptr c (ntarray 0 2 int))) = (5 : int)))
  (check-pred bigstep-simulation
              '(* (0 : (ptr c (array 0 2 int))) = (5 : int)))
  (check-pred bigstep-simulation
              '(* (malloc (ptr c int)) = (malloc int)))
  (check-pred bigstep-simulation
              '(cast (ptr c int) (* (malloc (ptr c int)))))
  (check-pred bigstep-simulation
              '(let x =
                 (0 : (ptr c (ntarray 0 0 int)))
                 in
                 (if (* x)
                     (1 : int)
                     (1 : int))))
  (check-pred bigstep-simulation
              '(if (* (0 : (ptr c (ntarray 0 0 int))))
                  (1 : int)
                  (1 : int)))
  (check-pred bigstep-simulation
              '(let g135606 =
                 (0 : (ptr c (ntarray -1 9 int)))
                 in
                 (strlen g135606)))
  (check-pred bigstep-simulation
              '(let x =
                 (malloc (ntarray 0 9 int))
                 in
                 (unchecked
                  (if (* x)
                      ((malloc (ntarray 0 4 int)) + (0 : int))
                      ((malloc (ntarray 0 4 int)) + (0 : int))))))

  ;; strlen
  (check-pred
   (λ (x) (= (length x) 1))
   (parameterize ([*F* '((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
                                 (if (* x)
                                     ((1 : int) + (call 1 (x + (1 : int))))
                                     (0 : int))) : int))])
     (judgment-holds (⊢fwf>>> () () () c ((x : (ptr c (ntarray 0 0 int))) ) int
                              (if (* x)
                                  ((1 : int) + (call 1 (x + (1 : int))))
                                  (0 : int))
                              ee) ee)))

  ;; not well-formed because only ntarray can be widened
  (check-pred
   (λ (x) (= (length x) 0))
   (parameterize ([*F* '((defun ((x : (ptr c (array 0 0 int)))    ;strlen
                                 (if (* x)
                                     ((1 : int) + (call 1 (x + (1 : int))))
                                     (0 : int))) : int))])
     (judgment-holds (⊢fwf>>> () () () c ((x : (ptr c (array 0 0 int))) ) int
                              (if (* x)
                                  ((1 : int) + (call 1 (x + (1 : int))))
                                  (0 : int))
                              ee) ee)))

  (check-pred
   (λ (x) (= (length x) 1))
   (judgment-holds (⊢fwf>>> () () () c ((x : int) (y : (ptr c (ntarray 0 (x + 1) int))))
                            int (* (y + x)) ee) ee))

  (check-pred
   (λ (x) (and (= (length x) 1) (= (length (car x)) 4)))
   (judgment-holds (⊢Fwf>>> () () () c
                         ((defun ((x : int) (x + (1 : int))) : int)
                          (defun ((x : int) (y : (ptr c (array 0 (x + 1) int)))
                                            (* (y + x))) : int)
                          (defun ((x : int)
                                  (malloc (array 0 (x + 1) int))) :
                            (ptr c (array 0 (x + 1) int)))
                          (defun ((y : (ptr c (array 0 5 int))) y) : (ptr c (array 0 5 int)))) eF) eF))

  (parameterize ([*D* '((g333568 (((ptr c (array -6 9 int)) g333569)
                                  (int g333570) (int g333571)
                                  (int g333572) (int g333573))))])
    (check-pred bigstep-simulation
                '(& (* (malloc (ptr c (struct g333568)))) → g333572)))

  (parameterize ([*F* '((defun ((x : int) (y : int) (z : int) (let h = (2 : int) in h)) : int))])
    (parameterize ([*eF* (compile-F* (*F*))])
      (check-pred bigstep-simulation
                  '(call
                    1
                    (*
                     (if (10 : int) (malloc int) (malloc int))
                     =
                     (let g18772519 = (5 : int) in g18772519))
                    (* (let g18772520 = (10 : int) in (malloc int)) = (cast int (10 : int)))
                    (cast int (call 1 (0 : int) (8 : int) (10 : int)))))))

  (check-pred bigstep-simulation
              ;; initialize an ntarray
              '(let x = (malloc (ntarray 0 4 int)) in
                    ;; assign the first two elements to be 1
                    (let _ = (* x = (1 : int)) in
                         (let _ = (* (x + (1 : int)) = (1 : int)) in
                              ;; cast the bounds of the ntarray to 0
                              (let y = (cast (ptr c (ntarray 0 0 int)) x) in
                                   ;; access the first element
                                   ;; the upper bound of y will be extended
                                   (* y))))))

  (check-pred progress-preservation
              ;; initialize an ntarray
              '(let x = (malloc (ntarray 0 4 int)) in
                    ;; assign the first two elements to be 1
                    (let _ = (* x = (1 : int)) in
                         (let _ = (* (x + (1 : int)) = (1 : int)) in
                              ;; cast the bounds of the ntarray to 0
                              (let y = (cast (ptr c (ntarray 0 0 int)) x) in
                                   ;; access the first element
                                   ;; the upper bound of y will be extended
                                   (* y))))))

  ;; T-PtrC when bounds are negative
  (check-pred progress-preservation
              '(((if (0 : int) (let g432561 = (malloc (array 0 7 int)) in (g432561 + (2 : int)))
                     (let g432562 = (malloc (array 0 7 int)) in
                          (g432562 + (2 : int)))) + (0 : int)) +
                (8 : int)))

  (check-pred progress-preservation
              '(let g443498 = (let g443499 = (malloc int) in g443499) in
                    (let g443500 = (malloc (ntarray 0 7 int)) in (g443500 + (10 : int)))))

  (check-pred progress-preservation
              '(cast int (let g447042 = (malloc (ntarray 0 2 int)) in (g447042 + (5 : int)))))


  (parameterize ([*D* (term ((g460584 ((int g460585) (int g460586) (int g460587) (int g460588) (int g460589)))))])
    (check-pred progress-preservation
                (term (if (let g460604 = (strlen (let g460605 = (2 : int) in (let g460606 = (malloc (ntarray 0 18 int)) in (g460606 + (8 : int))))) in g460604) (let g460607 = (cast (ptr c (struct g460584)) (let g460608 = (malloc (struct g460584)) in g460608)) in (let g460609 = (8 : int) in (let g460610 = (malloc (array 0 5 int)) in (g460610 + (8 : int))))) (let g460611 = (malloc (array 0 5 int)) in (g460611 + (8 : int)))))))

  (check-not-exn (λ ()
               (simulation-small-step
              ;; initialize an ntarray
                '(() (let x = (malloc (ntarray 0 4 int)) in
                      ;; assign the first two elements to be 1
                      (let _ = (* x = (1 : int)) in
                           (let _ = (* (x + (1 : int)) = (1 : int)) in
                                ;; cast the bounds of the ntarray to 0
                                (let y = (cast (ptr c (ntarray 0 0 int)) x) in
                                     ;; access the first element
                                     ;; the upper bound of y will be extended
                                     (* y)))))))))

  (check-equal? (apply-reduction-relation*
                 (---> 'c)
                 '(() (let x = (1 : int) in (* ((malloc (ntarray 0 2 int)) + (2 : int)) =
                                               (4 : int)))))
                '((((0 : int) (0 : int) (0 : int)) Bounds)))
  (test-judgment-holds
   (⊢ty () () c
        (let g36711 =
          (cast (ptr c (ntarray -4 0 int)) (let g36713 = (malloc (ntarray 0 9 int)) in (g36713 + (4 : int))))
          in
          (let g36712 =
            (cast (ptr c (ntarray 0 0 int)) g36711)
            in
            (if (* g36712) g36712 (let g36734 = (malloc (ntarray 0 0 int)) in (g36734 + (0 : int))))
            ))
        _))


  ;; missing malloc rule for CEK semantics
  (parameterize* ([*F*
                (term
                 ((defun
                    ((g91826 : int) (g91827 : int) (g91828 : int) (g91829 : int)
                                    (cast int ((let g91830 = (malloc (ntarray 0 (g91829 + 14) int)) in (g91830 + (4 : int))) + (4 : int)))) : int)))]
                [*eF* (compile-F* (*F*))]
               )
    (check-pred bigstep-simulation '(call 1 (5 : int) (6 : int) (1 : int) (3 : int))'(if 
      (*
       (let g91831 = (malloc (array 0 8 int)) in (g91831 + (7 : int)))
       =
       (3 : int))
      (* (let g91832 = (malloc int) in g91832) = (10 : int)))))

  (check-pred bigstep-simulation
            '(let g84826 =
               (let g84827 =
                 (cast
                  int
                  (*
                   (let g84828 = (malloc (array 0 10 int)) in (g84828 + (2 : int)))
                   =
                   (8 : int)))
                 in
                 (let g84830 = (malloc (ntarray 0 10 int)) in (g84830 + (2 : int))))
               in
               (let g84831 =
                 (strlen
                  (let g84832 =
                    (strlen g84826)
                    in
                    (let g84833 =
                      (6 : int)
                      in
                      (let g84834 =
                        (malloc (ntarray 0 14 int))
                        in
                        (g84834 + (10 : int))))))
                 in
                 g84831)))

  (check-not-exn(λ ()(parameterize 
                    ((*D* '((g2556429 ((int g2556430) ((ptr c (array -7 5 int)) g2556431) ((ptr c int) g2556432) (int g2556433) (int g2556434))) (g2556435 ((int g2556436) ((ptr c int) g2556437) (int g2556438) ((ptr c int) g2556439) (int g2556440)))))
                     (*F* 
                      '((defun ((g2556441 : int) (g2556442 : int) (g2556443 : int) (g2556444 : int) (* (let g2556445 = (malloc int) in g2556445))) : int) (defun ((g2556446 : int) (g2556447 : int) (g2556448 : int) (1 : int)) : int))))
                  (progress-preservation '(* (let g2556449 = (let g2556450 = (if (7 : int) (let g2556451 = (malloc (struct g2556435)) in g2556451) (let g2556452 = (malloc (struct g2556435)) in g2556452)) in (* (& g2556450 → g2556438))) in (let g2556453 = (dyn-bound-cast (ptr c (ntarray -9 (g2556449 + 1) int)) (let g2556454 = (malloc (ntarray 0 (g2556449 + 18) int)) in (g2556454 + (14 : int)))) in (cast (ptr c (array -9 7 int)) (let g2556455 = (let g2556457 = (malloc (ntarray 0 2 int)) in (g2556457 + (2 : int))) in (if (* g2556455 = (2 : int)) (let g2556456 = (cast (ptr c (ntarray 0 0 int)) g2556455) in (let g2556458 = (malloc (array 0 21 int)) in (g2556458 + (10 : int)))) (let g2556456 = (cast (ptr c (ntarray 0 0 int)) g2556455) in (let g2556459 = (malloc (array 0 21 int)) in (g2556459 + (10 : int))))))))) = (let g2556460 = (let g2556461 = (malloc (struct g2556435)) in g2556461) in (* (& g2556460 → g2556436)))))))))
