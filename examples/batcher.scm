(define-module (language clambda batcher)
  #:use-module (language clambda clambda)
  #:use-module (language clambda scm)
  #:use-module (ice-9 pretty-print)
  #:export (make-batcher))

#|
A sort utility that combines batcher sorting network and
merge sort

LGPL, Copyright Stefan Israelsson Tampe
|#

(define (pp x)
  (pretty-print (syntax->datum x))
  x)

(define (log2 x) (/ (log x) (log 2)))
(define (batcher n)
  (let* ((network '())
         (tee     (inexact->exact (ceiling (log2 n))))
         (p       (ash 1 (- tee 1))))
    (let loop ((p p))
      (if (> p 0)
          (begin
            (let loop2 ((q (ash 1 (- tee 1)))
                        (r 0)
                        (d p))
              (if (> d 0)
                  (begin
                    (let loop3 ((i 0))
                      (if (<= i (- n d 1))
                          (begin
                            (if (= (logand i p) r)
                                (set! network
                                      (cons (list i (+ i d)) network)))
                            (loop3 (+ i 1)))))
                    (loop2 (ash q -1) p (- q p)))))
            (loop (ash p -1)))))
    (reverse network)))
                       
(define (compswap x q> p temp)
  (lambda (pair)
    (with-syntax ((n1 (datum->syntax x (car  pair)))
                  (n2 (datum->syntax x (cadr pair))))
      #`(<if> (#,q> (<ref> #,p (<c> n1)) (<ref> #,p (<c> n2)))
              (<begin>
               (<=> #,temp (<ref> #,p (<c> n1)))
               (<=> (<ref> #,p (<c> n1)) (<ref> #,p (<c> n2)))
               (<=> (<ref> #,p (<c> n2)) #,temp))))))

(define-syntax make-batcher
  (lambda (x)
    (syntax-case x ()
      ((_ fname n q< type)
       (with-syntax ((p     (datum->syntax x 'p))
                     (t     (datum->syntax x 't)))                
         #'(mk-batcher0 n p t fname q< type))))))

(define-syntax mk-batcher0
  (lambda (x)
    (syntax-case x ()
      ((_ n p t fname q< type)
       #`(<define> void fname (((type *) p))
                   (<let*> ((type t *))
                     #,@(map (compswap x #'q< #'p #'t) 
                             (batcher (syntax->datum #'n)))))))))
