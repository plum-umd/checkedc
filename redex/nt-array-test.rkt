#lang racket
(define (partition-tests n k)
  (let ([i (quotient n k)])
    (cons (- n (* i (- k 1))) (build-list (- k 1) (const i)))))


(module+ test
  ;; (map place-wait
  ;;      (for/list ([num-tests (partition-tests 10000 (quotient (processor-count) 2))])
  ;;        (let ([p (dynamic-place "compiled-checkNT.rkt" 'test-bisimulation)])
  ;;          (place-channel-put p num-tests)
  ;;          p)))

  ;; (map place-wait
  ;;      (for/list ([num-tests (partition-tests 1000 (quotient (processor-count) 2))])
  ;;        (let ([p (dynamic-place "compiled-checkNT.rkt" 'test-progress-preservation)])
  ;;          (place-channel-put p num-tests)
  ;;          p)))

  (map place-wait
       (for/list ([num-tests (partition-tests 10000 (quotient (processor-count) 2))])
         (let ([p (dynamic-place "compiled-checkNT.rkt" 'test-simulation-small-step)])
           (place-channel-put p num-tests)
           p))))
