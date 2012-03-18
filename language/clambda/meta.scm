(define-module (language clambda meta)
  #:export     (!m! :m: <m>))


#|
this define logic to modify the meaning of syntax transformer

usage:

(!m! directive
     (syntax-define r ...) 
     ...)

directives:  (:mark key)    will mark the syntax-defined macro with key
                            key will be true for appropriate symbols
|#

(define :m: 'marker)
(define <m> 'marker)

(define-syntax !m!
  (syntax-rules (*m* <m>)
    ((_ (*m* key) item ...)
     (begin
       (mark-transformer key item)
       ...))
    ((_ (<m> key) item ...)
     (begin
       (<>-transformer key item)
       ...))))


(define-syntax mark-transformer
  (syntax-rules (define define-syntax)
    ((_ key (define-syntax name . l))
     (begin
       (define (key x) (symbol-property x 'key))
       (define-syntax name . l)
       (set-symbol-property! 'name 'key #t)))

    ((_ key (define (name . a) . l))
     (begin
       (define (key x) (symbol-property x 'key))
       (define (name . a) . l)
       (set-symbol-property! 'name 'key #t)))

    ((_ key (define name . l))
     (begin
       (define (key x) (symbol-property x 'key))
       (define name . l)
       (set-symbol-property! 'name 'key #t)))))

(define-syntax <>-transformer
  (lambda (x)
    (syntax-case x (define define-syntax ->)
      ((q key (define-syntax name . l))
       #'(begin
           (define-syntax name . l)
           (set-symbol-property! 'name 'tr #t)))
    
      ((q key (define (name -> <name> . a) . l))
       #'(begin
           (define (<name> . a) . l)
           (define  name `(4321 ,<name>))))

      ((q key (define name -> <name> . l))
       #'(begin
           (define <name> . l)
           (define name `(4321 ,<name>)))))))

