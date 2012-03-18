(define-module (language clambda line)
  #:use-module (language clambda fmt)
  #:use-module (language clambda parse syntax-parse)
  #:use-module (ice-9    match      )
  #:export (line my-line my-block get-line-nr auto zoute *c-line-numbers*))

(define-syntax auto
  (lambda (x)
    (syntax-case x ()
      ((_ (a ...)) #'(a ...))
      ((_ a      ) 
       (with-syntax ((w (datum->syntax x (get-line-nr x))))
         #'(zoute w a))))))

;; This is used on symbols that represent variables
(define lit? (lambda (x) (or (string? x) (number? x) (char? x))))
(define (zoute w x) 
  (if (lit? x) 
      (error 
       (format 
        #f
        "(ln ~a) wrapping of constant is missing use (<c> ~a) or (<scm> ~a)"
        w x x)))
  
  (lambda (v)
    (let ((g (if (procedure? x) 
                 x
                 (lambda (v)  
                   (match v
                     ('type  (error (format #f "~a is not a value" x)))
                     (_ (c= v x)))))))
      ;(pk `(zoute ,v ,x ,(g v)))
      (match v
        (#f       fmt-null)
        (#t       (g #t))
        ('type    (g 'type))
        ('expr    #t)
        (v        (g v))))))

(define (my-block . a)
  (if (> (length a) 1)
      (apply c-block `(,fmt-null ,@a))
      (car a)))

(define (get-line-nr x)
  (let ((q (syntax-source x)))
    (if q (cdar q) q)))

(define *c-line-numbers* #f)
(define (line x)
  (if *c-line-numbers*
      (if x (begin
              (set! *lnr* x)
              (cpp-line x))
          (cpp-line *lnr*))
      fmt-null))

(define (my-line x)
  (lambda (v) (line x)))
