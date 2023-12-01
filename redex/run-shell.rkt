#lang racket
(require "to-checkc.rkt")
(require "nt-array.rkt")
(require redex/reduction-semantics)

;;needs to be changed for local paths
(define PATH-TO-RACKET "")
(define PATH-TO-CHECKEDC "" )
(define EXPR-SIZE 11)

;;Slightly hacky way to do this, using ports to
;; write to the file since I couldn't figure out
;; doing > as a subprocess

;;runs to-checkc and writes to test2.c
;;then tries to compile test2.c
(define (compile sd fs e s)
;;does the equivalent of the command
;; racket to-checkc.rkt > test2.c
(define test (open-output-file "test2.c" #:mode 'binary #:exists 'replace))
(display s test)
(close-output-port test)
  
;;compiles the new test2.c file with the clang compiler
(define-values (sp out in err)
  (subprocess #f #f #f PATH-TO-CHECKEDC "test2.c"))
(printf "stdout:\n~a" (port->string out))
(printf "stderr:\n~a" (port->string err))
(close-input-port out)
(close-output-port in)
(close-input-port err)
(subprocess-wait sp)
 ;; returns if the subprocess succeeded
  (subprocess-status sp))


;;runs the compiled file a.out
(define (exec)
(define-values (sp out in err)
  (subprocess #f #f #f "./a.out"))
(define text (port->string out))
(printf "stdout:\n~a" text)
(printf "stderr:\n~a" (port->string err))
(let ((x text))
(close-input-port out)
(close-output-port in)
(close-input-port err)
(subprocess-wait sp)
(cons (subprocess-status sp)
  x)))


;; returns the value
(define (find lst)
  (match lst
    ['() #f]
    [_ (match (first lst)
       [`(,n : int) n]
       [_ (let ((x (find (first lst)))) (if x x (find (rest lst))))])]))

;;applies apply-reduction-relation*
(define (reduce e fs sd)
  (parameterize ((*F* fs)
     (*D* sd))
(match (second (first (apply-reduction-relation*
          --->cu (term (() ,e)))))
  [`(,n : int) n]
  ['Bounds ""]
  [_ "err"])))

;;runs main n times
(define (n-run n)
  (if (zero? n) 0 (begin (run) (n-run (sub1 n)))))

(define (batch n)
  (let* ((fs (gen:funs '() EXPR-SIZE)) (sd (gen:structs EXPR-SIZE)) (es (build-list n (λ (x) (gen:expr fs sd '() 'int EXPR-SIZE)))))
                               (foldr
                                (λ (r rs)
                                  (match r
                                    [(cons e 'fail) (list (first rs) (second rs) (cons (add1 (car (third rs))) (cons e (car (third rs)))))]
                                    [(cons e (list v r)) (if (equal? (string->number v) r)
                                                       (list (add1 (first rs)) (second rs) (third rs))
                                                       (list (first rs) (cons (add1 (car (second rs))) (cons e (car (second rs)))) (third rs)))]))
                                (list 0 (cons 0 '()) (cons 0 '()))
                                (map
                                (λ(e) (if
                                       (zero? (compile fs sd e (main sd fs e)))
                                       (cons e (list (cdr (exec)) (reduce e fs sd)))
                                       (cons e 'fail)))
                                es))))

;;calls batch and displays results.
(define (test-res n)
  (display "running tests ...\n")
  (match (batch n)
    [(list n1 (cons n2 es2) (cons n3 es3)) (display "ran ") (display n) (display " tests\n")
                                           (display "failed to compile: ") (display n3)
                                           (display "\ncompiled but disagreed with redex: ") (display n2)
                                           (display "\nsucceeded: ") (display n1)]))


;;runs main until the compiler fails
(define (run)
  (let* ((fs (gen:funs '() EXPR-SIZE)) (sd (gen:structs EXPR-SIZE)) (e (gen:expr fs sd '() 'int EXPR-SIZE))
                               (m (compile fs sd e (main sd fs e))))
    (if (zero? m)
        (let ((x (exec))
              (r (reduce e fs sd))) (display "\n") (display (cdr x)) (display "=?") (display r) (display "\n")
          (display (equal? (string->number (cdr x)) r)) (display "\n")
      (if (equal? (string->number (cdr x)) r) (run) (begin (display sd) (display fs) (display e)'failed)))
        (begin (display sd) (display fs) (display e)'failed))))

#;(test-res 1000)
