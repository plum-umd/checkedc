#lang racket
(provide (all-defined-out))
(require "nt-array.rkt")
(require redex/reduction-semantics)
;; (require redex/gui)
(require rackunit)

(define INT-SIZE 11)

(define *rand-gen* (make-parameter (current-pseudo-random-generator)))

;; Γ ::= Listof (x τ)

;; e ::= (n : τ) | (e + e) | x | (malloc ω) | (if e e e) (currently generates (if (* e1) e e) if e1 has the correct type, switch to only x?)
;;       | (cast τ e) | let x = e in e
;;       | (* e) | ( (* e) = e) | (unchecked e) | (strlen e) (e must have type (ptr c (ntarray l h)))
;;       | (& e -> f) | (call (n : τ) e ...))

;; τ ::= int | (ptr c ω)

;; ω ::= (struct T) | (array l h int)
;; | (ntarray l h int) | int

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;struct generators


;;generates a struct table
(define (gen:structs n)
  (build-list (random n (*rand-gen*)) (λ (x) (list (gensym) (map (λ (x) (list (second x) (first x))) (gen:env '() n))))))

;; Given a struct table returns a struct name
(define (gen:struct sd)
  (match sd
    ['() #f]
    [_ (let ((s (list-ref sd (random (length sd) (*rand-gen*)))))
         (match s
           [`(,l ,r) l]))]))

;;given a type and a list of fields returns a field with that type
(define (find-field d τ)
  (let ((f (filter (λ (x)
                     (match x
                       [`(,t ,l) (equal? t τ)]
                       [_ #f])) d)))
    (if (zero? (length f)) #f (match (list-ref f (random (length f) (*rand-gen*)))
                                [`(,t ,l) l]))))

;;given a type and struct-table find a
;;struct with a field of that type
(define (get-field sd τ)
  (let ((s (filter (λ (x) (match x
                   [`(,l ,d) (find-field d τ)]
                   [_ #f])) sd)))
    (if (zero? (length s)) #f (match (list-ref s (random (length s) (*rand-gen*)))
                               [`(,l ,d) (list l (find-field d τ))]))))

;;given a struct-table and a type finds
;; a struct where the first field is of that type
(define (get-first-field sd ω)
  (let ((s (filter (λ (x) (match x
                   [`(,t ,l) (equal? (first (first l)) ω)]
                   [_ #f])) sd)))
    (if (zero? (length s)) #f (car (list-ref s (random (length s) (*rand-gen*)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;type generators

;;generates a random τ
;;struct-table Nat -> τ
(define (gen:τ Γ sd i)
  (if (<= i 0)
      'int
      (if (zero? (random 2 (*rand-gen*))) 'int
      `(ptr c ,(gen:ω Γ sd (sub1 i))))))

;;generates a random well-formed ω
;; struct-table Nat -> ω
(define (gen:ω Γ sd i) 
      (choose i
              (λ (i) (if (empty? sd) 'int `(struct ,(gen:struct sd))))
              (λ (i) (let ((x (gen:bounds Γ)) (y (gen:bounds Γ)))   
                       `(array ,(- (random INT-SIZE (*rand-gen*))) ,(if x x (random 1 INT-SIZE (*rand-gen*))) int)))
              (λ (i) (let ((x (gen:bounds Γ)) (y (gen:bounds Γ)))   
                       `(ntarray ,(- (random INT-SIZE (*rand-gen*))) ,(if x x (random INT-SIZE (*rand-gen*))) int)))
              (λ (i) `(array ,(- (random INT-SIZE (*rand-gen*))) ,(random 1 INT-SIZE (*rand-gen*)) int))
              (λ (i) `(ntarray ,(- (random INT-SIZE (*rand-gen*))) ,(random INT-SIZE (*rand-gen*)) int))))

;;Given an enviornment generates either literal or variable bounds
(define (gen:bounds Γ)
  (match (pick-variable-or-value Γ 'int)
    [`(,n : int) #f]
    [x `(,x + ,(random INT-SIZE (*rand-gen*)))]))

;;Given a type generates a subtype of it
;; Since we are generating something that is a subtype the bounds must be larger
(define (gen:sub sd τ i)
  (match τ
    [`(ptr c (ntarray ,(? number? l) ,(? number? h) ,τ)) `(ptr c (ntarray ,(- l (random (add1 (abs l)) (*rand-gen*))) ,(+ h (random INT-SIZE (*rand-gen*))) ,τ))]
    [`(ptr c (array ,(? number? l) ,(? number? h) ,τ)) `(ptr c (array ,(- l (random (add1 (abs l)) (*rand-gen*))) ,(+ h (random INT-SIZE (*rand-gen*))) ,τ))]
    [`(ptr c (ntarray ,(? number? l) (,x + ,(? number? h)) ,τ)) `(ptr c (ntarray ,(- l (random (add1 (abs l)) (*rand-gen*))) (, x + ,(+ h (random INT-SIZE (*rand-gen*)))) ,τ))]
    [`(ptr c (array ,(? number? l) (,x + ,(? number? h))  ,τ)) `(ptr c (array ,(- l (random (add1 (abs l)) (*rand-gen*))) (,x + ,(+ h (random INT-SIZE (*rand-gen*)))) ,τ))]
    [`(ptr c ,ω) (let ((s (get-first-field sd ω))) (if s `(ptr c (struct ,s)) τ))]
    [_ τ]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;expression generators 


;;Generates an expression of type τ
;; Env τ Nat -> expr
(define (gen:expr f sd Γ τ i)
  (match τ
    ['int (gen:int-expr f sd Γ i)]
    [`(ptr c ,ω) 
     (if (<= i 0) (if (zero? (random 2 (*rand-gen*))) (pick-variable-or-value Γ τ) (gen:lit τ))
     (choose i
             (λ (i) (pick-variable-or-value Γ τ))
             (λ (i) (if (malloc-ok? ω) (let ((x (gensym))) `(let ,x = (malloc ,ω) in ,x))
                        (let ((n (get-sub ω)))
                          `(,(gen:expr f sd Γ `(ptr c ,(sub-bound ω n)) (sub1 i)) + (,n : int)))))
             (gen:cast f sd Γ (sub1 i) τ)
             (λ (i) `(if ,(gen:int-expr f sd Γ (sub1 i)) ,(gen:expr f sd Γ τ (sub1 i)) ,(gen:expr f sd Γ τ (sub1 i))))
             (λ (i) (let ((x (gensym)) (τ_1 (gen:τ Γ sd (sub1 i))))
                      `(let ,x = ,(gen:expr f sd Γ τ_1 (sub1 i)) in ,(gen:expr f sd (cons (list x τ_1) Γ) τ (sub1 i)))))
             (λ (i) (let ((x (get-ntvar Γ)))
                      (if x `(if (* ,(car x)) ,(gen:expr f sd (cons (list (car x) (nt-incr (cdr x))) Γ) τ (sub1 i)) ,(gen:expr f sd Γ τ (sub1 i))) (gen:expr f sd Γ τ (sub1 i)))))    
             ;;NEW
             (λ (i) (let ((x (gensym)) (h (random INT-SIZE (*rand-gen*))))
                      `(let ,x = (malloc (ntarray 0 ,h int)) in
                         ,(initialize-arr h x f sd (cons (list x `(ptr c (ntarray 0 ,h int))) Γ) τ (sub1 i)))))
             (λ (i) (let ((x (get-ntvar Γ)) (y (gensym)) (z (gensym))) (if x `(let ,z = (let ,y = (strlen ,(car x)) in ,(gen:expr f sd (cons (list (car x) (str-incr (cdr x) y)) (cons (list y 'int) Γ)) 'int (sub1 i))) in ,(gen:lit τ))
                                                              (gen:expr f sd Γ τ (sub1 i)))))
             ;;NEW HERE 
             (λ (i) (let ((x (gensym)) (y (gensym)) (t `(ptr c (ntarray ,(- (random INT-SIZE (*rand-gen*))) 0 int)))) `(let ,x = ,(gen:expr
                                                               f
                                                               sd
                                                               Γ
                                                               t
                                                               (sub1 i)) in
                                                                   (if (* ,x)
                                                                       (let ,y = (cast (ptr c (ntarray 0 0 int)) ,x) in ,(gen:expr f sd (cons (list x t) (cons (list y `(ptr c (ntarray 0 0 int))) Γ)) τ (sub1 i)))
                                                                       (let ,y = (cast (ptr c (ntarray 0 0 int)) ,x) in ,(gen:expr f sd (cons (list x t) (cons (list y `(ptr c (ntarray 0 0 int))) Γ)) τ (sub1 i)))))))
       
             (λ (i) (let ((x (if (equal? ω 'int) (get-field sd ω) (get-field sd τ))))
                   (match x
                     [`(,s ,t) (if (equal? ω 'int) (let ((l (gensym))) `(let ,l =  ,(gen:expr f sd Γ `(ptr c (struct ,s)) (sub1 i)) in (& ,l → ,t)))
                                   (let ((l (gensym))) `(let ,l =  ,(gen:expr f sd Γ `(ptr c (struct ,s)) (sub1 i)) in (* (& ,l → ,t)))))]
                     [_ (gen:lit τ)]))) ;;here
             (λ (i) (let ((fd (get-fun f τ))) (if fd (gen:call f sd Γ (car fd) (cdr fd) (sub1 i)) (gen:expr f sd Γ τ (sub1 i)))))))]))


;;takes a type and a variable, if it's a ntarray with integer bounds it adds the variable
;; τ x -> τ
(define (str-incr τ y)
  (match τ
    [`(ptr c (ntarray ,l ,h int)) `(ptr c (ntarray ,l (,y + 0) int))]
    [_ τ]))

;;Generates a random integer expression
;;Env Nat -> expr
(define (gen:int-expr f sd Γ i)
  (if (<= i 0) (if (zero? (random 2 (*rand-gen*))) (pick-variable-or-value Γ 'int) (gen:lit 'int))
      (choose i
              (gen:cast f sd Γ (sub1 i) 'int)
          (λ (i) (pick-variable-or-value Γ 'int)) ;; x | (n: τ)
          (λ (i) `(,(gen:int-expr f sd Γ (sub1 i)) + ,(gen:int-expr f sd Γ (sub1 i)))) ;`;(e + e)
          (λ (i) `(if ,(gen:int-expr f sd Γ (sub1 i)) ,(gen:int-expr f sd Γ (sub1 i)) ,(gen:int-expr f sd Γ (sub1 i)))) ;;(if e e e)
          (λ (i) (let ((x (gensym)) (τ_1 (gen:τ Γ sd (sub1 i))))
                      `(let ,x = ,(gen:expr f sd Γ τ_1 (sub1 i)) in ,(gen:int-expr f sd (cons (list x τ_1) Γ) (sub1 i)))))
          (λ (i) (let ((x (get-ntvar Γ)))
                      (if x `(if (* ,(car x)) ,(gen:int-expr f sd (cons (list (car x) (nt-incr (cdr x))) Γ) (sub1 i)) ,(gen:int-expr f sd Γ (sub1 i))) (gen:int-expr f sd Γ (sub1 i)))))
          (λ (i) `(* ,(gen:expr f sd Γ '(ptr c int) (sub1 i)))) ;; (* e)
          (λ (i) `(* ,(gen:expr f sd Γ `(ptr c  (array ,(- (random INT-SIZE (*rand-gen*))) ,(random 1 INT-SIZE (*rand-gen*)) int)) (sub1 i))))
          (λ (i) `(* ,(gen:expr f sd Γ `(ptr c  (ntarray ,(- (random INT-SIZE (*rand-gen*))) ,(random INT-SIZE (*rand-gen*)) int)) (sub1 i))))
          (λ (i) `(* ,(gen:expr f sd Γ '(ptr c int) (sub1 i)) = ,(gen:int-expr f sd Γ (sub1 i))))
          (λ (i) `(* ,(gen:expr f sd Γ
                                `(ptr c  (array ,(- (random INT-SIZE (*rand-gen*))) ,(random 1 INT-SIZE (*rand-gen*)) int)) (sub1 i)) = ,(gen:int-expr f sd Γ (sub1 i))))
          (λ (i) `(* ,(gen:expr f sd Γ
                                `(ptr c  (ntarray ,(- (random INT-SIZE (*rand-gen*))) ,(random 1 INT-SIZE (*rand-gen*)) int)) (sub1 i)) = ,(gen:int-expr f sd Γ (sub1 i))))
          (λ (i) (let ((x (get-field sd 'int)))
                   (match x
                     [`(,s ,t) (let ((l (gensym))) `(let ,l =  ,(gen:expr f sd Γ `(ptr c (struct ,s)) (sub1 i)) in (* (& ,l → ,t))))]
                     [_ (gen:lit 'int)])))
          (λ (i) (let ((fd (get-fun f 'int))) (if fd (gen:call f sd Γ (car fd) (cdr fd) (sub1 i)) (gen:expr f sd Γ 'int (sub1 i)))))
          (λ (i) (let ((x (get-ntvar Γ)) (y (gensym)) (z (gensym))) (if x `(let ,z = (let ,y = (strlen ,(car x)) in ,(gen:expr f sd (cons (list (car x) (str-incr (cdr x) y)) (cons (list y 'int) Γ)) 'int (sub1 i))) in (0 : int))
                                                              (gen:expr f sd Γ 'int (sub1 i))))))))
         

;;generator of a cast expression of type τ
;; Env Nat τ -> (Nat -> expr)
(define (gen:cast f sd Γ i τ)
  (match τ
    ['int (λ (i) `(cast ,τ ,(gen:expr f sd Γ (gen:τ Γ sd (sub1 i)) (sub1 i))))]
    [`(ptr c (ntarray ,(? number? l) (,x + ,(? number? h)) ,τ2)) (λ (i) `(dyn-bound-cast ,τ
                                                                                  ,(gen:expr f sd Γ `(ptr c (ntarray ,(- l (random (add1 (abs l)) (*rand-gen*))) (, x + ,(+ h (random INT-SIZE (*rand-gen*)))) ,τ2)) (sub1 i))))]
    [`(ptr c (array ,(? number? l) (,x + ,(? number? h))  ,τ2))  (λ (i) `(dyn-bound-cast , τ
                                                                                  ,(gen:expr f sd Γ `(ptr c (array ,(- l (random (add1 (abs l)) (*rand-gen*))) (,x + ,(+ h (random INT-SIZE (*rand-gen*)))) ,τ2)) (sub1 i))))]
    [`(ptr c ,ω) (λ (i) `(cast ,τ ,(gen:expr f sd Γ (gen:sub sd τ (sub1 i)) (sub1 i))))]
    [_ (λ (i) `(cast ,τ ,(gen:expr f sd Γ τ (sub1 i))))]))

;;assigns a value to all of the elements of a null-terminated array
;;NEW
(define (initialize-arr n v f sd Γ τ i)
    (if (<= n 0)
        (gen:expr f sd Γ τ (sub1 i))
        (let ((x (gensym))) `(let ,x = (* (,v + (,n : int)) = ,(gen:expr f sd Γ 'int (sub1 i))) in
                               ,(initialize-arr (sub1 n) v f sd (cons (list x 'int) Γ) τ i))))) 

;;generates a call expression
(define (gen:call f sd Γ fd p i)
  (match fd
    [`(defun ((,x : ,τ) ... ,e) : ,τ_res) (cons 'call (cons p (gen:args f sd Γ i τ)))]))

;;a generator for random literals of type τ
;; τ -> expr
(define (gen:lit τ)
  (match τ
    ['int `(,(random INT-SIZE (*rand-gen*)) : ,τ)]
    [`(ptr c ,ω) (let ((x (gensym)))
                       (if (malloc-ok? ω) `(let ,x = (malloc ,ω) in ,x)
                     ;; need better way than enumerating all possibilites
                      ;; need to figure out what to do if lower bound is dependent FIX  
                     (match ω
                        [`(array ,(? number? l) ,(? number? h) ,τ) `(let ,x = (malloc (array 0 ,(+ h (abs l)) ,τ)) in (,x + (,(abs l) : int)))]
                        [`(ntarray ,(? number? l) ,(? number? h) ,τ) `(let ,x = (malloc (ntarray 0 ,(+ h (abs l)) ,τ)) in (,x + (,(abs l) : int)))]
                        [`(array ,(? number? l) (,h + ,(? number? n)) ,τ) `(let ,x = (malloc (array 0 (,h + ,(+ n (abs l))) ,τ)) in (,x + (,(abs l) : int)))]
                        [`(ntarray ,(? number? l) (,h + ,(? number? n)) ,τ) `(let ,x = (malloc (ntarray 0 (,h + ,(+ n (abs l))) ,τ)) in (,x + (,(abs l) : int)))]
                        [`(array (,l + ,(? number? n)) ,(? number? h) ,τ) `(let ,x = (malloc (array 0 ,(+ h (abs l)) ,τ)) in (,x + (,(abs l) : int)))]
                        [`(ntarray (,l + ,(? number? n)) ,h ,τ) `(let ,x = (malloc (ntarray 0 ,(+ h (abs l)) ,τ)) in (,x + (,(abs l) : int)))]
                        [_ `(malloc ,ω)])))]))


;; Finds a variable with type pointer to a null-terminated array (only case besides int allowed in if)
(define (get-ntvar Γ)
  (let ((l (filter (λ (x) (match x
                   [`(,x (ptr c (ntarray ,l ,h ,t))) #t]
                   [_ #f])) Γ)))
    (if (zero? (length l)) #f (let ((x (list-ref l (random (length l) (*rand-gen*)))))
                                (if (not (equal? (cdr (assoc (car x) Γ)) (cdr x))) #f x)))))

;;Makes sure the bounds are ok for malloc
(define (malloc-ok? ω)
  (match ω
    [`(struct ,T) #t]
    ['int #t]
    [`(array ,(? number? l) ,(? number? h) τ) (and (= 0 l) (< 0 h))]
    [`(ntarray ,(? number? l) ,(? number? h) τ) (and (= 0 l) (<= 0 h))]
    [`(array ,l ,h τ) (= 0 l)]
    [`(ntarray ,l ,h τ) (= 0 l)]
    [`(ptr c ,ω1) (malloc-ok? ω1)]
    [_ #f]))

;;gets a number appropriate for adding FIX?
;; add sub for variable bounds
(define (get-sub ω)
  (match ω
    [`(array ,(? number? l) ,(? number? h) ,τ) (random (add1 (abs l)) (*rand-gen*))]
    [`(ntarray ,(? number? l) ,(? number? h) ,τ) (random (add1 (abs l)) (*rand-gen*))]
    [`(array ,(? number? l) (,h + ,(? number? n)) ,τ) (random (add1 (abs l)) (*rand-gen*))]
    [`(ntarray ,(? number? l) (,h + ,(? number? n)) ,τ) (random (add1 (abs l)) (*rand-gen*))]
    [_ #f]))

;;returns the type after adding n
;;need to add dependent examples FIX
(define (sub-bound ω n)
  (match ω
    [`(array ,(? number? l) ,(? number? h) ,τ) `(array ,(+ l n) ,(+ h n) ,τ)]
    [`(ntarray ,(? number? l) ,(? number? h) ,τ) `(ntarray ,(+ l n) ,(+ h n) ,τ)]
    [_ ω]))

;;increases the bounds of an ntarray pointer pointing at 0
(define (nt-incr t)
  (match t
    [`(ptr c (ntarray ,l 0 ,τ)) `(ptr c (ntarray ,l 1 ,τ))]
    [_ t]))

;;generates a list of arguments 
(define (gen:args f sd Γ i args)
  (match args
    ['() '()]
    [(cons τ r) (cons (gen:expr f sd Γ τ i) (gen:args f sd Γ i r))]))

;;((defun ((x : τ) ... e) : τ) ...) τ -> (defun ((x : τ) ... e) : τ) or #f
(define (get-fun f τ)
  (let ((fs (filter (λ (b) (match b
                   [(cons `(defun ((,x : ,τ_1) ... ,e) : ,τ_res) n) (if (equal? τ τ_res) #t #f)]
                   [_ #f])) (car (foldl (λ (x a) (cons (cons (cons x (cdr a)) (car a)) (add1 (cdr a)))) (cons '() 1) f)))))
    (if (empty? fs) #f (list-ref fs (random (length fs) (*rand-gen*))))))


;;Listof X -> X
;;picks a random element of a list
(define (choose i . cs)
  ((if (<= i 0)
      (first cs)
      (list-ref cs (random (length cs) (*rand-gen*))))
   (sub1 i)))

;;Γ τ -> expr
(define (pick-variable-or-value Γ τ)
  (let ((g:t (filter (λ (b) (equal? (second b) τ))
                     Γ)))    (if (empty? g:t)
        (gen:lit τ)
        (first (list-ref g:t (random (length g:t) (*rand-gen*)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;function generators

;;creates an argument list
(define (gen:env sd n)
  (match n
    [0 '()]
    [_ (cons (list (gensym) (gen:τ '() sd (random n (*rand-gen*)))) (gen:env sd (sub1 n)))]))

;; converts an argument list into correct arguments
(define (to-defun l sd n)
  (let ((t (gen:τ '() sd n)))
  `(defun ,(append (map (λ (x) `(,(first x) : ,(second x))) l) (list (gen:expr '() sd l t n))) : ,t)))

;;generates a function enviornment
(define (gen:funs sd n)
  (build-list (random n (*rand-gen*)) (λ (x) (to-defun (gen:env '() (random n (*rand-gen*))) '() (random n (*rand-gen*))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test helpers

;; takes a string and append to it the current state of the random generator
(define (make-test-name test-name)
  (call-with-output-string
   (λ (p)
     (fprintf p "~a (seed: ~a)"
              test-name
              (pseudo-random-generator->vector (*rand-gen*))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;tests




(module+ test
  ;;sanity
  (let ((τ (gen:τ '() '() 10)))
  (test-judgment-holds
   (⊢ty ((p = none : (ptr c (ntarray -3 0 int)))) () c ,(gen:expr '() '() '() τ 10) τ))))

(define (loop n)
  (let* ((sd (gen:structs 10))
        (fs (gen:funs sd 10)))
  (parameterize ((*D* sd)
                 (*F* fs))
  (if (zero? n) (begin (display fs) (display sd))
      (let ((t (gen:τ '() sd 10)))
        (let ((x (gen:expr fs sd '() t 2)))
          (display n)
          (display ":\n")
          (display x)
          (display "\n")
          (display t)
          (display "\n")
          (test-judgment-holds
          (⊢ty () () c ,x τ))
          ;(display "\n")
          (loop (sub1 n))))))))

(define (loop2 n)
 (let* ((sd (gen:structs 10))
        (fs (gen:funs sd 10)))
  (parameterize ((*D* sd)
                 (*F* fs))
    (let ((t (gen:τ '() sd 10)))
        (let ((x (gen:expr fs sd '() t 10)))
          (match (judgment-holds
          (⊢ty () () c ,x τ) τ)
            ['() (display x) (display "\n") (display fs) (display "\n") (display t)(display "\n") (display sd) (display "\n") n]
            [_ (display n)
               (display "\n")
               (loop2 (add1 n))]))))))


(define (test-bisimulation ch)
  (let ([num-tests (place-channel-get ch)])
    (parameterize ([*rand-gen* (make-pseudo-random-generator)])
      (test-case
          (make-test-name "Bigstep Simulation with Functions ans Structs")
        (for ([i num-tests])
          (let* ((sd (gen:structs 5))
                 (fs (gen:funs sd 5)))
            (parameterize ([*D* sd]
                           [*F* fs])
              (let* ([τ (gen:τ '() '() 2)]
                     [e (gen:expr fs sd '() τ 9)]
                     [efs (compile-F* fs)])
                (parameterize ([*eF* efs])
                  (with-check-info
                    (('structs sd)
                     ('functions fs)
                     ('nth (+ 1 i)))
                    (check-pred bigstep-simulation e)))))))))))

(define (test-progress-preservation ch)
  (let ([num-tests (place-channel-get ch)])
    (parameterize ([*rand-gen* (make-pseudo-random-generator)])
      (test-case
          (make-test-name "Progress & Preservation for closed programs")
        (for ([i num-tests])
          (let* ((sd (gen:structs 5))
                 (fs (gen:funs sd 5)))
            (parameterize ([*D* sd]
                           [*F* fs])
              (let* ([τ (gen:τ '() '() 2)]
                     [e (gen:expr fs sd '() τ 9)]
                     [efs (compile-F* fs)])
                (parameterize ([*eF* efs])
                  (with-check-info
                    (('structs sd)
                     ('functions fs)
                     ('nth (+ 1 i))
                     ('e e))
                    (check-not-exn (lambda () (progress-preservation e)))))))))))))

(define (test-simulation-small-step ch)
  (let ([num-tests (place-channel-get ch)])
    (parameterize ([*rand-gen* (make-pseudo-random-generator)])
      (test-case
          (make-test-name "Simulation in small step")
        (for ([i num-tests])
          (let* ((sd (gen:structs 5))
                 (fs (gen:funs sd 5)))
            (parameterize ([*D* sd]
                           [*F* fs])
              (let* ([τ (gen:τ '() '() 2)]
                     [e (gen:expr fs sd '() τ 9)]
                     [efs (compile-F* fs)])
                (parameterize ([*eF* efs])
                  (with-check-info
                    (('structs sd)
                     ('functions fs)
                     ('nth (+ 1 i))
                     ('e e))
                    (check-not-exn (lambda () (simulation-small-step (list '() e))))))))))))))
