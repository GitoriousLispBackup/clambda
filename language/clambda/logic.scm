(define-module (language clambda logic)
  #:use-module (language clambda clambda)
  #:use-module (language clambda scm)
  #:export (:fail: :cc: :cut: :and: :or: :call: :var: :not: :when:
                   ::when:: :=: :match: :define: :pp: :code: _ S))

(define-syntax S
  (lambda (x) (error "S feature only in code environment")))


(define-syntax _
  (lambda (x)
    (syntax-case x ()
      ((_ . l) #'(error "__ is a symbol macro"))
      (_       #'(<scm-call> gp_mkvar S)))))


(define-syntax Y
  (syntax-rules ()
    ((_ w (f . l)) (f w . l))))

(define-syntax :fail:
  (syntax-rules ()
    ((_ (s cut fail cc)) (<tcall-log> fail))))

(define-syntax :cc:
  (syntax-rules ()
    ((_ (s cut fail cc)) (<tcall-log> cc s fail))))

(define-syntax :and:
  (syntax-rules (:cut:)
    ((_ (s cut p cc)) 
     (<tcall-log> cc s p))
    ((_ w x)   (Y w x))
    ((_ (s cut fail cc) :cut: . l)
     (:and: (s cut cut cc) . l))     
    ((_ (s cut fail cc) x . l)
     (<let> ((ccc (<lambda-log> s (s fail2) 
                     (:and: (s cut fail2 cc) . l))))
       (Y (s cut fail ccc) x)))))

(define-syntax :or:
  (syntax-rules ()
    ((_ w x)      (Y w x))
    ((_ (s cut fail cc) x . l)
     (<let*> ((P (<scm-call> gp_newframe s))
              (f (<lambda-log-p> s () 
                    (<scm-call> gp_gp_unwind P)
                    (or-work (P cut fail cc) . l))))
       (Y (P cut f cc) x)))))

(define-syntax with-S
  (syntax-rules ()
    ((_ s code ...)
     (fluid-let-syntax ((S (lambda (x)
                             (syntax-case x ()
                               ((_ . l) #'(error "S is a symbol macro"))
                               (_ #'s)))))
         code ...))))

(define-syntax :code:
  (syntax-rules ()
    ((_ (s cut p cc) x ...)
     (with-S s
        (<begin>
         x ...
         (<tcall-log> cc s p))))))

(define-syntax or-work
  (syntax-rules ()
    ((_ w x)      (Y w x))
    ((_ (s cut fail cc) x . l)
     (<let*> ((f (<lambda-log-p> s () 
                   (<scm-call> gp_gp_unwind s)
                   (or-work (s cut fail cc) . l))))
       (Y (s cut f cc) x)))))


(define-syntax :call:
  (syntax-rules ()
    ((_ (s cut fail cc) f . l) (<tcall-log> f s fail cc . l))))

(define-syntax :var:
  (syntax-rules ()
    ((_ (s cut p cc) (v ...) code ...)
     (<let> ((v (<scm-call> gp_mkvar s)) ...)
       (:and: (s cut p cc) code ...)))))


(define-syntax :not:
  (syntax-rules ()
    ((_ (s cut fail cc) x)
     (<let*> ((P   (<scm-call> gp_newframe s))
              (ccc (<lambda-log> P (ss ffail) 
                     (<tcall-log> fail)))
              (f   (<lambda-log-p> P ()
                     (<scm-call> gp_gp_unwind P)
                     (<tcall-log> cc s fail))))
       (Y (s cut f ccc) x)))))

(define-syntax :when:
  (lambda (x)
    (syntax-case x ()
      ((_ w c-expr code ...)
       (with-syntax (((s . _) #'w))
         #'(<if> (with-S s c-expr)
                 (:and: w code ...)
                 (:fail: w)))))))

(define-syntax ::when::
  (lambda (x)
    (syntax-case x ()
      ((_ w scm-expr code ...)
       (with-syntax (((s . _) #'w))
         #'(<<if>> (with-S s scm-expr)
                   (:and: w code ...)
                   (:fail: w)))))))

(define-syntax :=:
  (syntax-rules ()
    ((_ (s cut p cc) x y)
     (<let> ((SCM s (<scm-call> gp_gp_unify (with-S s x) (with-S s y) s)))
       (<<if>> s 
          (<tcall-log> cc s p)
          (<tcall-log> p))))))

(define (generate-temp x)
  (let loop ((x x) (r '()))
    (syntax-case x ()
      ((x . l)
       (loop #'l (cons (datum->syntax #'x (gensym "g")) r)))
      (() (reverse r)))))

;;Todo fix this
(define-syntax :pp:
  (syntax-rules ()
    ((_ (s . l) v)
     (:code: (s . l)
       (<format> #t "~a~%" (<scm-call> smob2scm (<scm> v) s))))))


(define-syntax :match:
  (lambda (x)
    (syntax-case x ()
      ((_ (s cut fail cc) (x ...) . l)
       (with-syntax (((p ...) (generate-temp #'(x ...))))
         #'(<let> ((p x) ... (P (<scm-call> gp_newframe s)))
             (match0 P (P fail fail cc) (p ...) . l)))))))

(define-syntax match0
  (syntax-rules ()
    ((_ P (s cut fail cc) ps (p ... code))
     (match1 (s cut fail cc) ps (p ...) code))

    ((_ P (s cut fail cc) ps (p ... code) . l)
     (<let> ((ffail (<lambda-log-p> s () 
                      (<scm-call> gp_gp_unwind P)
                      (match0 P (s cut fail cc) ps . l))))
       (match1 (s cut ffail cc) ps (p ...) code)))
    ((_ P (s cut fail cc) ps)
     (<tcall-log> fail))))

(define-syntax match1
  (syntax-rules ()
    ((_ w (p ps ...) (q qs ...) code)
     (match2 w p q (match1 (ps ...) (qs ...) (:and: code))))
    ((_ w () () code)
     (Y w code))))

(define-syntax match2
  (syntax-rules (and unquote _)
    ((_ w x (and p) code)
     (match2 w x p code))

    ((_ w x (and p . q) code)
     (match2 w x p (match2 x (and . q) code)))

    ((_ w x (unquote p) code)
     (<let> ((p x)) (add-s w code)))

    ((_ (s . l) x (p . q) code)
     (<let*> ((s (<scm-call> gp_pair_bang x s)))
       (<<if>> s
         (<let> ((car (<scm-call> gp_car    x s))
                 (cdr (<scm-call> gp_gp_cdr x s)))
           (match2 (s . l) car p (match2 cdr q code)))
         (:fail: (s . l)))))

    ((_ w x _  code) 
     (add-s w code))

    ((_ (s . l) x () code)
     (<let*> ((s (<scm-call> gp_null_bang x s)))
       (<<if>> s
         (add-s (s . l) code)
         (:fail: (s . l)))))
    
    ((_ (s . l) x a code)
     (<let*> ((s (<scm-call> gp_gp_unify x (<scm> a) s)))
       (<<if>> s
         (add-s (s . l) code)
         (:fail: (s . l)))))))
    
(define-syntax add-s
  (syntax-rules ()
    ((_ w (f b ...)) (f w b ...))))

(define-syntax :define:
  (syntax-rules ()
    ((_ (f . l) code ...)
     (define-log (f s fail cc . l) (Y (s fail fail cc) (:and: code ...))))))

        
