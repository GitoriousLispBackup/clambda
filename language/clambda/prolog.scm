(define-module (language clambda prolog)
  #:use-module (language clambda clambda)
  #:use-module (language clambda scm)
  #:export (:fail: :cc: :cut: :and: :or: :call: :var: :not: :when:
                   ::when:: :=: :match: :define: :pp:))

(define-syntax Y
  (syntax-rules ()
    ((_ w (f . l)) (f w . l))))

(define-syntax :fail:
  (syntax-rules ()
    ((_ (cc cut fail)) (! <tcall> fail))))

(define-syntax :cc:
  (syntax-rules ()
    ((_ (cc cut fail)) (! <tcall> cc fail))))

(define-syntax :cut:
  (syntax-rules ()
    ((_ (cc cut fail)) (! <tcall> cc cut))))

(define-syntax :and:
  (syntax-rules ()
    ((_ w x)   (Y w x))
    ((_ (cc cut fail) (:cut:) . l)
     (:and: (cc cut cut) . l))     
    ((_ (cc cut fail) x . l)
     (<let> ((ccc (<lambda> (fail) (:and: (cc cut fail) . l))))
       (Y (ccc cut fail) x)))))

(define-syntax :or:
  (syntax-rules ()
    ((_ w x)      (Y w x))
    ((_ (cc cut fail) x . l)
     (<let*> ((P (<scm-call> c_newframe))
              (f (<lambda> () 
                   (<scm-call> c_unwind P)
                   (or-work P (cc cut fail) . l))))
       (Y (cc cut f) x)))))

(define-syntax or-work
  (syntax-rules ()
    ((_ P w x)      (Y w x))
    ((_ P (cc cut fail) x . l)
     (<let*> ((f (<lambda> () 
                   (<scm-call> c_unwind P)
                   (or-work P (cc cut fail) . l))))
       (Y (cc cut f) x)))))


(define-syntax :call:
  (syntax-rules ()
    ((_ (cc cut fail) f . l) (<tcall> f cc fail . l))))

(define-syntax :var:
  (syntax-rules ()
    ((_ w (v ...) code ...)
     (<let> ((v (<scm-call> c_var)) ...)
       (:and: w code ...)))))


(define-syntax :not:
  (syntax-rules ()
    ((_ (cc cut fail) x)
     (<let*> ((P   (<scm-call> c_newframe))
              (ccc (<lambda> (ffail) 
                     (! <tcall> fail)))
              (f   (<lambda> ()
                     (<scm-call> c_unwind P)
                     (! <tcall> cc fail))))
       (Y (ccc cut f) x)))))

(define-syntax :when:
  (syntax-rules ()
    ((_ w c-expr code ...)
     (<if> c-expr
           (:and: w code ...)
           (:fail: w)))))

(define-syntax ::when::
  (syntax-rules ()
    ((_ w scm-expr code ...)
     (<<if>> scm-expr
             (:and: w code ...)
             (:fail: w)))))

(define-syntax :=:
  (syntax-rules ()
    ((_ w x y)
     (<<if>> (<scm-call> c_unify x y)
             (:cc:   w)
             (:fail: w)))))

(define (generate-temp x)
  (let loop ((x x) (r '()))
    (syntax-case x ()
      ((x . l)
       (loop #'l (cons (datum->syntax #'x (gensym "g")) r)))
      (() (reverse r)))))

(define-syntax :pp:
  (syntax-rules ()
    ((_ w s v ...)
     (:when: w (<begin> (<format> #t s (<scm-call> c_scm v) ...)
                        (<format> #t "~%")
                        (<c> 1))
             (:cc:)))))
  

(define-syntax :match:
  (lambda (x)
    (syntax-case x ()
      ((_ (cc cut fail) (x ...) . l)
       (with-syntax (((p ...) (generate-temp #'(x ...))))
         #'(<let> ((p x) ... (P (<scm-call> c_newframe)))
             (match0 P (cc fail fail) (p ...) . l)))))))

(define-syntax match0
  (syntax-rules ()
    ((_ P (cc cut fail) ps (p ... code) . l)
     (<let> ((ffail (<lambda> () 
                      (<scm-call> c_unwind P)
                      (match0 P (cc cut fail) ps . l))))
       (match1 (cc cut ffail) ps (p ...) code)))
    ((_ P (cc cut fail) ps)
     (! <tcall> fail))))

(define-syntax match1
  (syntax-rules ()
    ((_ w (p ps ...) (q qs ...) code)
     (match2 w p q (match1 w (ps ...) (qs ...) code)))
    ((_ w () () code)
     (Y w code))))

(define-syntax match2
  (syntax-rules (and unquote _)
    ((_ w x (and p) code)
     (match2 w x p code))

    ((_ w x (and p . q) code)
     (match2 w x p (match2 w x (and . q) code)))

    ((_ w x (unquote p) code)
     (<let> ((p x)) code))

    ((_ w x (p . q) code)
     (<let*> ((r (<scm-call> c_lookup x)))
       (<<if>> (<scm-call> c_pair r)
               (<let*> ((r (<scm-call> c_lookup x)))
                 (<let> ((car (<scm-call> c_car r))
                         (cdr (<scm-call> c_cdr r)))
                   (match2 w car p (match2 w cdr q code))))
               (:fail: w))))

    ((_ w x _  code) 
     code)

    ((_ w x () code)
     (<let*> ((r (<scm-call> c_lookup x)))
       (<<if>> (<scm-call> c_unify x (<scm> '()))
             code
             (:fail: w))))
    
    ((_ w x a code)
     (<let*> ((r (<scm-call> c_lookup x)))
       (<<if>> (<scm-call> c_unify x (<scm> a))
               code
               (:fail: w))))))
    

(define-syntax :define:
  (syntax-rules ()
    ((_ (f . l) code ...)
     (<<define>> (f cc fail . l) (Y (cc fail fail) (:and: code ...))))))

        
