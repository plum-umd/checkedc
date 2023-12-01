#lang racket
(require "compiled-checkNT.rkt")
(require "nt-array.rkt")
(require redex/reduction-semantics)
(provide main)
(provide gen:funs)
(provide gen:structs)
(provide gen:expr)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Translate entire programs.

;;adds the top stuff
(define (main D F e)
  (let* ((Fnames (get-names F))
         (tr (translate '() D Fnames e))
         (funs (translate-funs F Fnames 1)))
  (string-append "#include <stdio_checked.h> \n"
                 "#include <stdlib.h> \n"
                 "#include <stdchecked.h> \n"
                 "#include <string_checked.h> \n"
                 "nt_array_ptr<char> nt_calloc( char x, char y) : count(x) {\n"
                 "return _Assume_bounds_cast<nt_array_ptr<char>>(calloc<char>(x, y), count(x)); \n}\n"
                 (foldl string-append "" (map car funs))
                 (foldl string-append "" (map cdr funs))
                 (translate-structs D)
                 (foldl string-append "" (map car (third tr)))
                 (foldl string-append "" (map cdr (third tr)))
                 "int main(void) _Checked {\n"
                 "char c = " (first tr) ";\n"
                 "unchecked{\n"
                 "printf(\"%i\", (int)c);\n}\n"
                 "return 0;\n}")))
;;current language
;; e = (n : τ) | x | e + e | (let x = e in e) | (if e e e)
;; (strlen e) | (* e) | (* e = e)

;;translates an expression
;; returns a list with the translated expression, the type of the expression, and a string with the functions
(define (translate  Γ D F e)
  (match e
     [`(,n : ,τ) (list (number->string n) τ '(("" . "")))]
     [`(,e1 + (,n : int)) (let ((t1 (translate Γ D F e1)))
                    (match (second t1)
                      ['int (list (string-append (first t1) "+" (number->string n)) 'int (third t1))]
                      [`(ptr c ,ω) (list (string-append (first t1) "+" (number->string n)) `(ptr c ,(bounds-sub ω n)) (third t1))]))]
     [`(,e1 + ,e2) (let ((t1 (translate Γ D F e1)) (t2 (translate Γ D F e2))) (list (string-append (first t1) " + " (first t2)) 'int (append (third t1) (third t2))))]
     [`(let ,x = ,e1 in ,e2) (let ((letf (gensym "let")) (v (translate Γ D F e1)))
                              (let ((e (translate (cons (cons x (second v)) Γ) D F e2)))
                                (let ((args (remove-duplicates
                                             (append (filter (λ (m) (not (equal? x (cdr m)))) (append (get-free-vars Γ D F e1) (free-type-vars (second v)) (get-free-vars (cons (cons x (second v)) Γ) D F e2)))))))
                                (list (string-append (symbol->string letf) "( " (call-args (map cdr args)) ")")
                                      (second e)
                                      (cons (let->fun letf x v e args)
                                            (append (third v) (third e)))))))]
     [`(if ,g ,e1 ,e2) (let ((name (gensym "if")) (v (translate Γ D F g)) (t1 (translate Γ D F e1)) (t2 (translate Γ D F e2)))
                         (let ((args (remove-duplicates (append (get-free-vars Γ D F g) (get-free-vars Γ D F e1) (get-free-vars Γ D F e2)))))
                         (list (string-append (symbol->string name) "( " (call-args (map cdr args)) ")")
                               (second t1)
                               (cons (if->fun name v t1 t2 args)(append (third v) (third t1) (third t2))))))]
     [`(call ,n ,e1 ...) (match-let ([(cons `(defun ((,x : ,τ_1) ... ,e2) : ,τ) name)(fun-lookup F n)])
                          (let ((tr (get-args Γ D F e1)))
                                 (list (string-append (symbol->string name) "(" (first tr) ")") τ (second tr))))]
     [`(strlen ,e1) (let ((tr (translate Γ D F e1))) (list (string-append "strlen((const char *)" (first tr) ")") 'int (third tr)))]
     [`(* ,e1 = ,e2) (let ((t1 (translate Γ D F e1)) (t2 (translate Γ D F e2)))
                       (list
                        (string-append "( *(" (first t1) ") = " (first t2) ")")
                        (second t2)
                        (append (third t1) (third t2))))]
     [`(* ,e1) (let ((t1 (translate Γ D F e1)))
                       (list
                        (string-append "*(" (first t1) ")")
                        'int ;;safe assumption??
                        (third t1)))]
     [`(cast ,τ ,e) (let ((letf (gensym "cast")) (v (translate Γ D F e)) (args (remove-duplicates (append (free-type-vars τ) (get-free-vars Γ D F e)))))
                      (list (string-append (symbol->string letf) "( " (call-args (map cdr args)) ")")
                                      τ
                                      (cons (cast->fun letf (gensym) τ v args)
                                            (third v))))

      #;(let ((tr (translate Γ D F e))) (list (string-append "(" (translate-type τ) ")" (first tr)) τ (third tr)))]
     [`(malloc ,ω) (allocate ω)]
     [`(& ,e → ,f) (let ((tr (translate Γ D F e)))
                     (match-let ([`(ptr c (struct ,T)) (second tr)])
                       (list
                        (string-append "&("(first tr) "->" (symbol->string f)")")
                        `(ptr c ,(field-lookup D T f))
                        (third tr))))]
     [(? symbol?) (list (symbol->string e)(cdr (assoc e Γ equal?)) '(("" . "")))]
     [_ (list "" 'int '(("" . "")))]))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Let expressions
;; let expressions are translated into functions

;;translates a let into a function
(define (let->fun name x t1 t2 args)
  (cons
   (string-append
    (translate-type (second t2)) " " (symbol->string name) 
   "( " (fun-args args) ")" (count (second t2)) ";\n")
   (string-append
   (translate-type (second t2)) " " (symbol->string name)
   "(" (fun-args args) ")" (count (second t2)) " {\n"
   (dec-type (second t1) x) " = "
   (first t1) ";\n"
   "return " (first t2) ";\n}\n")))

;;takes a list of free variables and their types and translates them into function arguments
(define (fun-args args)
  (match args
    ['() "void "]
    [`(,s) (string-append (dec-type (car s)  (cdr s)) " ")]
    [(cons h t) (string-append (dec-type (car h) (cdr h))", " (fun-args t))]))

;;takes a list of free variables and translates them into the format to be passed into a let function call
(define (call-args args)
  (match args
    ['() ""]
    [`(,s) (symbol->string s)]
    [(cons h t) (string-append (symbol->string h) ", " (call-args t))]))

;;takes an expression and returns a list of the free variables
(define (get-free-vars Γ D F e)
  (match e
    [`(,n : ,τ) (free-type-vars τ)]
    [`(,e1 + ,e2) (append (get-free-vars Γ D F e1) (get-free-vars Γ D F e2) )]
    [`(let ,x = ,e1 in ,e2) (append (get-free-vars Γ D F e1)
                                    (filter (λ (v) (not (equal? x (cdr v)))) (get-free-vars (cons (cons x (second (translate Γ D F e1))) Γ) D F e2)))]
    [`(if ,g ,e1 ,e2) (append (get-free-vars Γ D F g) (get-free-vars Γ D F e1) (get-free-vars Γ D F e2))]
    [`(call ,n ,e1 ...) (foldr (λ (x a) (append (get-free-vars Γ D F x) a)) '() e1)]
    [`(strlen ,e1) (get-free-vars Γ D F e1)]
    [`(unchecked ,e1) (get-free-vars Γ D F e1)]
    [`(malloc ,ω) (free-type-vars ω)]
    [`(cast ,τ ,e) (append (free-type-vars τ) (get-free-vars Γ D F e))]
    [`(& ,e → ,f) (get-free-vars Γ D F e)]
    [`(* ,e) (get-free-vars Γ D F e)]
    [`(* ,e1 = ,e2) (append (get-free-vars Γ D F e1) (get-free-vars Γ D F e2))]
    [x (list (cons (cdr (assoc x Γ equal?)) x))]))

;;takes an expression and returns a list of the free type variables (necessary because for example something could
;; be in a malloc)
(define (get-type-vars Γ D F e)
  (match e
    [`(,n : ,τ) (free-type-vars τ)]
    [`(,e1 + ,e2) (append (get-type-vars Γ D F e1) (get-type-vars Γ D F e2))]
    [`(let ,x = ,e1 in ,e2) (append (get-type-vars Γ D F e1) (get-type-vars (cons (cons x (second (translate Γ D F e1))) Γ) D F e1))]
    [`(if ,g ,e1 ,e2) (append (get-type-vars Γ D F g) (get-type-vars Γ D F e1) (get-type-vars Γ D F e2))]
    [`(call ,n ,e1 ...) (foldr (λ (x a) (append (get-type-vars Γ D F x) a)) '() e1)]
    [`(strlen ,e1) (get-type-vars Γ D F e1)]
    [`(unchecked ,e1) (get-type-vars Γ D F e1)]
    [`(malloc ,ω) (free-type-vars ω)]
    [`(cast ,τ ,e) (get-type-vars Γ D F e)]
    [`(& ,e → ,f) (get-type-vars Γ D F e)]
    [`(* ,e) (get-type-vars Γ D F e)]
    [`(* ,e1 = ,e2) (append (get-type-vars Γ D F e1) (get-type-vars Γ D F e2))]
    [x (display x) (list (cons (cdr (assoc x Γ equal?)) x))]))

;;takes a type and returns a list of free variables
(define (free-type-vars τ)
  (match τ
    ['int '()]
    ['(ptr c int) '()]
    [`(ptr c (array ,l (,h + ,(? number? n)) ,t)) (list (cons 'int h))]
    [`(ptr c (ntarray ,l (,h + ,(? number? n)) ,t)) (list (cons 'int h))]
    [`(ptr c (array ,l ,h int)) '()]
    [`(ptr c (ntarray ,l ,h int)) '()]
    [`(array ,l (,h + ,(? number? n)) ,t) (list (cons 'int h))]
    [`(ntarray ,l (,h + ,(? number? n)) ,t) (list (cons 'int h))]
    [`(array ,l ,h int) '()]
    [`(ntarray ,l ,h int) '()]
    [`(ptr c (struct ,T)) '()]
    [_ '()]))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cast functions
;;translates a let into a function
(define (cast->fun name x t1 e2 args)
  (cons
   (string-append
    (translate-type t1) " " (symbol->string name) 
   "(" (fun-args args) " )" (count t1) ";\n")
   (string-append
   (translate-type t1) " " (symbol->string name)
   "(" (fun-args args) " )" (count t1) " {\n"
   (dec-type (second e2) x) " = "
   (first e2) ";\n"
   "return (" (translate-type t1) ") " (symbol->string x)  ";\n}\n")))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Conditional expressions

;;translates a conditional into a function
(define (if->fun name t1 t2 t3 args)
  (cons
   (string-append
    (translate-type (second t2)) " " (symbol->string name) 
   "( " (fun-args args) ")" (count (second t2)) ";\n")
   (string-append
   (translate-type (second t2)) " " (symbol->string name)
   "(" (fun-args args) ")" (count (second t2)) " {\n"
    "if (" (first t1) "){\n return " (first t2) ";\n} \n else{\n"
   "return " (first t3) ";\n}\n}\n")))
   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Types

;;current types
;; τ = int | (ptr c ω)
;; ω = int | (array l h int) | (ntarray l h int) | (struct T)

;;translate types
(define (translate-type τ)
  (match τ
    ['int "char"]
    ['(ptr c int) "ptr<char>"]
    [`(ptr c (array ,l ,h int)) "array_ptr<char>"]
    [`(ptr c (ntarray ,l ,h int)) "nt_array_ptr<char>"]
    [`(ptr c (struct ,T)) (string-append  "ptr<" (symbol->string T) ">" )]
    [_ ""]))

;;translates types for declarations (the bounds can only be declared if there is a variable)
(define (dec-type τ name)
(match τ
    ['int (string-append "char " (symbol->string name))]
    ['(ptr c int) (string-append "ptr<char> " (symbol->string name))]
    [`(ptr c (array ,l (,h + ,(? number? n)) ,t)) (string-append "array_ptr<char> " (symbol->string name) " : count(" (symbol->string h) " + " (number->string (- n l)) ")")]
    [`(ptr c (ntarray ,l (,h + ,(? number? n)) ,t)) (string-append "nt_array_ptr<char> " (symbol->string name) " : count(" (symbol->string h) " + " (number->string (- n l)) ")")]
    [`(ptr c (array ,l ,h int)) (string-append "array_ptr<char> " (symbol->string name) " : count(" (number->string (- h l)) ")")]
    [`(ptr c (ntarray ,l ,h int)) (string-append "nt_array_ptr<char> " (symbol->string name) " : count(" (number->string (- h l)) ")")]
    [`(ptr c (struct ,T)) (string-append "ptr<" (symbol->string T) "> " (symbol->string name))]
    [_ ""]))

;;returns the count for function prototypes and declarations
;;translates types for declarations (the bounds can only be declared if there is a variable)
(define (count τ)
(match τ
    ['int ""]
    ['(ptr c int) ""]
    [`(ptr c (array ,l (,h + ,(? number? n)) ,t)) (string-append " : count(" (symbol->string h) " + " (number->string (- n l)) ")")]
    [`(ptr c (ntarray ,l (,h + ,(? number? n)) ,t)) (string-append " : count(" (symbol->string h) " + " (number->string (- n l)) ")")]
    [`(ptr c (array ,l ,h int)) (string-append  " : count(" (number->string (- h l)) ")")]
    [`(ptr c (ntarray ,l ,h int)) (string-append  " : count(" (number->string (- h l)) ")")]
    [`(ptr c (struct ,T)) ""]
    [_ ""]))

;;takes an ω and returns the correct argument to be passed to malloc to allocate a pointer to that type
(define (size τ)
  (match τ
  ['int "1, sizeof(char) "]
  [`(array 0 (,h + ,(? number? n)) ,t) (string-append (symbol->string h) " + " (number->string n) ", sizeof(char) ")]
  [`(ntarray 0 (,h + ,(? number? n)) ,t) (string-append (symbol->string h) " + " (number->string n) ", sizeof(char) ")]
  [`(array 0 ,(? number? h) ,t) (string-append (number->string h) ", sizeof(char) ")]
  [`(ntarray 0 ,(? number? h) ,t) (string-append (number->string h) ", sizeof(char) " )]
  [`(struct ,T) (string-append "1 , " "sizeof( " (symbol->string T) " ) ")]))

;;computes bounds in addition
(define (bound-sub le n)
  (match le
    [(? number? ?) (- le n)]
    [`(,x + ,l) `(,x + ,(- l n))]))

;; computes type of addition
(define (bounds-sub ω n)
  (match ω
    [`(ntarray ,le ,he ,τ) `(ntarray ,(bound-sub le n) ,(bound-sub he n) ,τ)]
    [`(array ,le ,he ,τ) `(array ,(bound-sub le n) ,(bound-sub he n) ,τ)]))

;;returns the correct allocation
;; since calloc can't be used for nt-arrays
(define (allocate ω)
  (match ω
    #;[`(ntarray 0 ,(? number? h)  ,τ) (list
                                      (string-append "(int nt_checked[]) {"
                                                     (string-join (build-list (add1 h) (λ (x) "\'0\'")) ", ") " }")
                                      `(ptr c ,ω)
                                      '(("" . "")))]
    #;[`(struct ,T) (list (string-append "(" (symbol->string T) ")calloc<char>(" (size ω) ")")
                        `(ptr c ,ω)
                        '(("" . "")))]
    [`(ntarray 0 ,h ,τ) (list (string-append "nt_calloc(" (size ω) ")")
                                                         `(ptr c ,ω)
                                                         '(("" . "")))]
    [_(list (string-append "calloc<char>(" (size ω) ")")
                                                         `(ptr c ,ω)
                                                         '(("" . "")))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Structs

;;translates a struct table
(define (translate-structs sd)
  (match sd
    ['() ""]
    [`((,name ,fs) . ,r) (string-append (translate-struct name fs) (translate-structs r))]))


;;translates an invidual struct definition
(define (translate-struct name fs)
  (string-append "typedef struct _" (symbol->string name) " {\n" (translate-fields fs) "} " (symbol->string name) ";\n"))

;;translates struct fields
(define (translate-fields fs)
  (match fs
    ['() ""]
    [`((,t ,x) . ,r) (string-append (translate-type t) " " (symbol->string x) ";\n" (translate-fields r))]))

;;returns the type of a field
(define (field-lookup D T f)
  (match D
    [`((,s ,fs) . ,r) (if (equal? s T)
                          (foldr (λ (x a) (if (equal? (second x) f) (first x) (if a a #f))) #f fs)
                          (field-lookup r T f))]
    ['() #f]))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Functions


;;takes a list of expressions and translates them into the format to be passed into a function call
(define (get-args Γ D F args)
  (match args
    ['() (list "" '())]
    [`(,s) (let ((tr (translate Γ D F s))) (list (first tr) (third tr)))]
    [(cons h t) (let ((tr (translate Γ D F h)) (trs (get-args Γ D F t)))
                  (list (string-append (first tr) ", " (first trs))
                        (append (third tr) (second trs))))]))

;;compiles a list of arguments
(define (translate-args vs ts)
  (match vs
    ['() "void"]
    [`(,x . ,r) (string-append (dec-type (first ts) x)
                             (if (cons? r) (string-append ", " (translate-args r (rest ts))) ""))]))


;;compiles a function
(define (translate-fun f name)
  (match f
    ['() (list "" '())]
    [`(defun ((,x : ,τ_1) ... ,e) : ,τ) (let ((body (translate (map cons x τ_1) '() '() e)))
                                           (cons (cons
                                                 (string-append (translate-type τ) " " (symbol->string name) " (" (translate-args x τ_1) ") " (count τ) "  ;\n")
                                                 (string-append (translate-type τ) " " (symbol->string name) " (" (translate-args x τ_1) ") " (count τ)  " {\n"
                                                       "return " (first body) ";\n}"))
                                                (third body)))]))

;;compiles a list of functions returns the functions as well as any let functions in their bodies
(define (translate-funs F Fnames n)
  (match F
    ['() '()]
    [`(,f . ,r) (let* ((name (fun-lookup Fnames n)) (fun (translate-fun f (cdr name))) (funs (translate-funs r Fnames (add1 n))))
                  (append fun funs))]))

;;names the functions
(define (get-names Fnames)
  (map (λ (f) (cons f (gensym "fun"))) Fnames))

;;returns the name and the function at position n
(define (fun-lookup Fnames n)
  (if (or (empty? Fnames) (<= n 0) (< (length Fnames) n)) #f
  (match n
    [1 (first Fnames)]
    [_ (fun-lookup (rest Fnames) (sub1 n))])))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Tests
#|
(define fs (gen:funs '() 4))
(define sd (gen:structs 4))
(define e (gen:expr fs sd '() 'int 4))
(display (main sd fs e))
|#
