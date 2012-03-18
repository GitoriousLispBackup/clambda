(define-module (language clambda parse match-parse)
  #:use-module (ice-9 match-phd)
  #:export     (match-parse *pair? *car *cdr *null? *equal?))

(define (syntax? x)
  (and (vector? x) (eq? (vector-ref x 0) 'syntax-object)))

(define (syntax-e x)
  (if (syntax? x)
      (vector-ref x 1)
      x))

#|
A matcher that can be used on syntax structures

see the racket documentation!
|#

(define-syntax aif
  (syntax-rules ()
    ((_ (a) p x y)
     (let ((a p))
       (if a x y)))))

(define (tr-line-no x y)
  (if (> (aif (it) (syntax-source y) (cdar it) 0) 0)
      y
      (datum->syntax x (syntax-e y))))

(define (*car x)
  (if (syntax? x)
      (let ((y (syntax-e x)))
	(if (pair? y)
	    (let ((z (car y)))
	      (if (syntax? z)
		  (tr-line-no x z)
		  (datum->syntax x z)))
	    (error "taking car of non pair syntax object")))
      (car x)))	  

(define (*cdr x)
  (if (syntax? x)
      (let ((y (syntax-e x)))
	(if (pair? y)
	    (let ((z (cdr y)))
	      (if (syntax? z)
                  (tr-line-no x z)
		  (datum->syntax x z)))
	    (error "taking cdr of non pair syntax object")))
      (cdr x)))	  

(define (*pair? x)
  (if (syntax? x)
      (let ((y (syntax-e x)))
	(pair? y))
      (pair? x)))

(define (*null? x)
  (if (syntax? x)
      (let ((y (syntax-e x)))
	(null? y))
      (null? x)))

(define (*equal? x1 x2)
  (if (syntax? x1) (set! x1 (syntax-e x1)))
  (if (syntax? x2) (set! x2 (syntax-e x2)))
  (equal? x1 x2))


(make-phd-matcher match-parse
     ( (*car *cdr *pair? *null? *equal?)
       (  (+ (*car *cdr *pair? *null? *equal?))
          (- ( car  cdr  pair?  null?  equal?)))))
