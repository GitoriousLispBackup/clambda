(define-module (language clambda syntax-ops)
  #:use-module (language clambda validators )
  #:use-module (language clambda fmt        )
  #:use-module (language clambda parse syntax-parse)
  #:use-module (ice-9    match              )
  #:use-module (language clambda line       )
  #:export (mk-op-2 mk-op-1 mk-exp-op-1))

(define (type-it x t)
  (let ((T (x 'type)))
    (pk `(type-it ,T))
    (match T
      (('%array t n) `(,t *))
      ((? procedure?) t)
      (T T))))
      

(define (2op-it cop lnx lny ax ay t)
  (lambda (v)
    (match v
      ('expr 
       (and (ax 'expr) (ay 'expr)))
        
      (#f 
         (if (and (ax 'expr) (ay 'expr))
             (cop (ax #t) (ay #t))
             (my-block 
              (line lnx)
              (ax #f)
              (line lny)
              (ay #f))))

      (#t (cop (ax #t) (ay #t)))

      (_
       (let ((xx (gensym "x"))
             (yy (gensym "y")))
         
         (if (and (ax 'expr) (ay 'expr))
             (c= v (cop (ax #t) (ay #t)))
             (my-block
              (line lnx)
              (c-var (type-it ax t) xx)
              (line lny)
              (c-var (type-it ay t) yy)
              (line lnx)
              (ax xx)
              (line lny)
              (ay yy)
              (c= v (cop xx yy)))))))))

(define-syntax mk-op-2
  (syntax-rules ()
    ((_ op cop)
     (define-syntax op
       (lambda (z)
         (define <arg3> (mk-arg-vd #f 'op 3))
         (define <arg2> (mk-arg-vd #t 'op 2))
         (reg-form z)
         (syntax-parse z ()
           ((w t x y : <arg3>)
            (with-syntax ((lnx (datum->syntax #'x (get-line-nr #'x)))
                          (lny (datum->syntax #'y (get-line-nr #'y))))
              #'(2op-it cop lnx lny (auto x) (auto y) (auto t))))
             
           ((w x y : <arg2>)
            (with-syntax ((lnx (datum->syntax #'x (get-line-nr #'x)))
                          (lny (datum->syntax #'y (get-line-nr #'y))))
              #'(2op-it cop lnx lny (auto x) (auto y) 'int)))))))))

(define (1op-it cop lnx x t)
  (lambda (v)
    (let ((ax (lambda (v) (x v))))
      (let ((xx (gensym "x")))
        (match v
          ('expr 
           (ax 'expr))

          (#f    
           (if (ax 'expr)
               (cop (ax #t))
               (my-block 
                (line lnx)
                (ax #f))))

          (#t 
           (cop (ax #t)))

          (_
           (if (ax 'expr)
               (c= v (cop (ax #t)))
               (my-block
                (line lnx)
                (c-var t xx)
                (line lnx)
                (ax xx)
                (c= v (cop xx))))))))))

(define-syntax mk-op-1
  (syntax-rules ()
    ((_ op cop)
     (define-syntax op
       (lambda (z)
         (define <arg2> (mk-arg-vd #f 'op 2))
         (define <arg1> (mk-arg-vd #t 'op 1))
         (reg-form z)
         (syntax-parse z ()
           ((w t x : <arg2>)
            (with-syntax ((lnx (datum->syntax #'x (get-line-nr #'x))))
              #'(1op-it cop lnx (auto t) (auto x))))
         
           ((w x : <arg1>)
            (with-syntax ((lnx (datum->syntax #'x (get-line-nr #'x))))
              #'(1op-it cop lnx (auto x) 'int)))))))))

(define (exp-it cop x)
  (lambda (v)
    (match v
      ('expr (x 'expr))
      (#t    (cop (x #t)))              
      (_     (c= v (cop (x #t)))))))

(define-syntax mk-exp-op-1
  (syntax-rules ()
    ((_ op cop)
     (define-syntax op
       (lambda (x)
         (define <arg1> (mk-arg-vd #t 'op 1))
         (reg-form x)
         (syntax-parse x ()
           ((_ x : <arg1>)
            #'(exp-it cop (auto x)))))))))
