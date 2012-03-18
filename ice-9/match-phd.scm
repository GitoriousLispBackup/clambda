;;;; match.scm -- portable hygienic pattern matcher
;;
;; This code is written by Alex Shinn and placed in the
;; Public Domain.  All warranties are disclaimed.

;; This is a full superset of the popular MATCH package by Andrew
;; Wright, written in fully portable SYNTAX-RULES (R5RS only, breaks
;; in R6RS SYNTAX-RULES), and thus preserving hygiene.

;; This is a simple generative pattern matcher - each pattern is
;; expanded into the required tests, calling a failure continuation if
;; the tests fail.  This makes the logic easy to follow and extend,
;; but produces sub-optimal code in cases where you have many similar
;; clauses due to repeating the same tests.  Nonetheless a smart
;; compiler should be able to remove the redundant tests.  For
;; MATCH-LET and DESTRUCTURING-BIND type uses there is no performance
;; hit.

;; The original version was written on 2006/11/29 and described in the
;; following Usenet post:
;;   http://groups.google.com/group/comp.lang.scheme/msg/0941234de7112ffd
;; and is still available at
;;   http://synthcode.com/scheme/match-simple.scm
;; It's just 80 lines for the core MATCH, and an extra 40 lines for
;; MATCH-LET, MATCH-LAMBDA and other syntactic sugar.
;;
;; A variant of this file which uses COND-EXPAND in a few places for
;; performance can be found at
;;   http://synthcode.com/scheme/match-cond-expand.scm
;;
;; 2009/11/25 - adding `***' tree search patterns
;; 2008/03/20 - fixing bug where (a ...) matched non-lists
;; 2008/03/15 - removing redundant check in vector patterns
;; 2008/03/06 - you can use `...' portably now (thanks to Taylor Campbell)
;; 2007/09/04 - fixing quasiquote patterns
;; 2007/07/21 - allowing ellipse patterns in non-final list positions
;; 2007/04/10 - fixing potential hygiene issue in match-check-ellipse
;;              (thanks to Taylor Campbell)
;; 2007/04/08 - clean up, commenting
;; 2006/12/24 - bugfixes
;; 2006/12/01 - non-linear patterns, shared variables in OR, get!/set!


;; 2010/11/10
;; Various improvements Implemented by Stefan Israelsson Tampe among others
;; Translated the code using the lispy defmacro macrology. My changes is as 
;; well put into public domain.

;; phd e.g. customable API for list processing
;; <z>  matcher system
;; $    matcher added with some more features on the = construct
;; cond , like or but the first successful match is only used
;; ,    inside non quasiquote mode will insert outer defined variable e.g.  (let ((A 1)) (match 2 (,A #t))) will produce #t

(define-module (ice-9 match-phd)
  #:use-module (srfi srfi-9)
  #:export     (match-define match-let* match-let match-letrec match-lambda*
			     match-lambda match make-phd-matcher))

(define-syntax match
  (syntax-rules (-abs -phd)
    ((match)
     (match-syntax-error "missing match expression"))
    ((match atom)
     (match-syntax-error "no match clauses"))

    ((match -abs abs -phd p . l)
     (match* (abs p) . l))
    ((match phd p -abs abs . l)
     (match* (abs p) . l))

    ((match -abs abs . l)
     (match* (abs ((car cdr pair? null? equal?) ())) . l))

    ((match -phd p . l)
     (match* (() p) . l))

    ((match x . l)
     (match* (() ((car cdr pair? null? equal?) ())) x . l))))

(define-syntax match*
  (syntax-rules ()
    ((match* abs (app ...) (pat . body) ...)
     (let ((v (app ...)))
       (match-next abs v ((app ...) (set! (app ...))) (pat . body) ...)))
    ((match* abs #(vec ...) (pat . body) ...)
     (let ((v #(vec ...)))
       (match-next abs v (v (set! v)) (pat . body) ...)))
    ((match* abs atom (pat . body) ...)
     (let ((v atom))
       (match-next abs v (atom (set! atom)) (pat . body) ...)))
    ))

(define-syntax match-next
  (syntax-rules (=>)
    ;; no more clauses, the match failed
    ((match-next abs v g+s)
     (error 'match (format #f "no matching pattern for: ~% ~a" v)))
    ;; named failure continuation
    ((match-next abs v g+s (pat (=> failure) . body) . rest)
     (let ((failure (lambda () (match-next abs v g+s . rest))))
       ;; match-one analyzes the pattern for us
       (match-one abs v pat g+s (match-drop-ids (begin . body)) (match-drop-ids (failure)) ())))
    ;; anonymous failure continuation, give it a dummy name
    ((match-next abs v g+s (pat . body) . rest)
     (match-next abs v g+s (pat (=> failure) . body) . rest))))

(define-syntax match-one
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(match-one ,(syntax->datum (syntax l))))
       (syntax (match-one* . l))))))


(define-syntax abs-drop
  (syntax-rules ()
    ((_ a k        ) k)
    ((_ a (k ...) v) (k ... v))))

(define-syntax match-one*
  (syntax-rules ()
    ;; If it's a list of two or more values, check to see if the
    ;; second one is an ellipse and handle accordingly, otherwise go
    ;; to MATCH-TWO.
    ((match-one* abs v (p q . r) g+s sk fk i)
     (match-check-ellipse
      q
      (match-extract-vars abs p (abs-drop (match-gen-ellipses abs v p r  g+s sk fk i)) i ())
      (match-two abs v (p q . r) g+s sk fk i)))
    ;; Go directly to MATCH-TWO.
    ((match-one* . x)
     (match-two . x))))

(define-syntax insert-abs
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(insert-abs ,(syntax->datum (syntax l))))
       (syntax (insert-abs* . l))))))


(define-syntax insert-abs*
  (syntax-rules (begin)
    ((insert-abs abs (begin . l)) (begin . l))
    ((insert-abs abs (x))         (x))
    ((insert-abs abs (n nn ...))  (n abs nn ...))))
    
(define-syntax match-two
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(match-two ,(syntax->datum (syntax l))))
       (syntax (match-two* . l))))))
  
(define-syntax match-two*
  (syntax-rules (_ ___ *** <> cond unquote unquote-splicing quote quasiquote 
                   ? $ = and or not set! get!)
    ((match-two (abs ((car cdr pair? null? equal?) pp)) 
                v () g+s (sk ...) fk i)
     (if (null? v) 
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) (sk ... i))
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) fk)))

    ((match-two (abs ((car cdr pair? null? equal?) pp)) 
                v (quote p) g+s (sk ...) fk i)
     (if (equal? v 'p)
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) (sk ... i))
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) fk)))
    
    ;;Stis uquote logic
    ((match-two (abs ((car cdr pair? null? equal?) pp)) 
                v (unquote p)  g+s (sk ...) fk i)
     (if (equal? v p)
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) (sk ... i))
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) fk)))
    ((match-two (abs ((ccar ccdr ppair? null? equal?) rr)) 
                v ((unquote-splicing p) . ps)  g+s sk fk i)
     (let loop ((vv v)
                (pp p))
       (if (pair? pp)
           (if (and (ppair? vv) (equal? (ccar vv) (car pp)))
               (loop (ccdr vv) (cdr pp))
               (insert-abs (abs ((ccar ccdr ppair? null? equal?) rr)) fk))
           (match-one (abs ((ccar ccdr ppair? null? equal?) rr)) 
                      vv ps g+s sk fk i))))
    
    ((match-two abs v (quasiquote p) . x)
     (match-quasiquote abs v p . x))    
    ((match-two abs v (and) g+s (sk ...) fk i) (insert-abs abs (sk ... i)))
    ((match-two abs v (and p q ...) g+s sk fk i)
     (match-one abs v p g+s (match-one v (and q ...) g+s sk fk) fk i))
    ((match-two abs v (or) g+s sk fk i) (insert-abs abs fk))
    ((match-two abs v (or p) . x)
     (match-one abs v p . x))
    ((match-two abs v (or p ...) g+s sk fk i)
     (match-extract-vars abs (or p ...) 
                         (abs-drop (match-gen-or abs v (p ...) 
                                                 g+s sk fk i)) i ()))
    ((match-two abs v (cond) g+s sk fk i) (insert-abs abs fk))
    ((match-two abs v (cond p) . x)
     (match-one abs v p . x))
    ((match-two abs v (cond p ps ...) g+s sk fk i)
     (match-one abs v p g+s sk 
                (abs-drop (match-one abs v 
                                     (cond ps ...) g+s sk fk i)) i))
    ((match-two abs v (not p) g+s (sk ...) (fk fkk ...) i)
     (match-one abs v p g+s (match-drop-ids (fk abs fkk ...)) (sk ... i) i))
    ((match-two abs v (get! getter) (g s) (sk ...) fk i)
     (let ((getter (lambda () g))) (insert-abs abs (sk ... i))))
    ((match-two abs v (set! setter) (g (s ...)) (sk ...) fk i)
     (let ((setter (lambda (x) (s ... x)))) (insert-abs abs (sk ... i))))
    ((match-two abs v (? pred . p) g+s sk fk i)
     (if (pred v) 
         (match-one abs v (and . p) g+s sk fk i) 
         (insert-abs abs fk)))
    
    ;; stis, added $ support!
    ((match-two abs v ($ n) g-s sk fk i)
     (if (n v) 
         (insert-abs abs sk)
         (insert-abs abs fk)))
    
    ((match-two abs v ($ nn p ...) g+s sk fk i)
     (if (nn v)
	 (match-$ abs (and) 0 (p ...) v sk fk i)
	 (insert-abs abs fk)))
     
    ;; stis, added the possibility to use set! and get to records    
    ((match-two abs v (= 0 m p) g+s sk fk i)
     (let ((w  (struct-ref v m)))
       (match-one abs w p ((struct-ref v m) (struct-set! v m)) sk fk i)))

    ((match-two abs v (= g s p) g+s sk fk i)
     (let ((w (g v))) (match-one abs w p ((g v) (s v)) sk fk i)))

    ((match-two abs v (= proc p) g+s . x)
     (let ((w (proc v))) (match-one abs w p () . x)))

    ((match-two (abs ((ccar ccdr ppair? null? equal?) rr)) 
                v ((<> f p) . l) g+s sk fk i)
     (let ((res (f v)))
       (if res
           (match-one abs (car res) p g+s 
                      (match-one (cdr res) l g+s sk fk)
                      fk i)
           (insert-abs abs fk))))

    ((match-two abs v (p ___ . r) g+s sk fk i)
     (match-extract-vars abs p 
                         (abs-drop 
                          (match-gen-ellipses abs v p r g+s sk fk i) i ())))
    ((match-two (abs phd) v p       g+s sk fk i)
     (match-abstract () abs phd v p g+s sk fk i))))

(define-syntax match-gen-or
  (syntax-rules ()
    ((_ abs v p g+s (sk ...) fk (i ...) ((id id-ls) ...))
     (let ((sk2 (lambda (id ...) (insert-abs abs (sk ... (i ... id ...))))))
       (match-gen-or-step abs v p g+s (match-drop-ids (sk2 id ...)) fk (i ...))))))

(define-syntax match-gen-or-step
  (syntax-rules ()
    ((_ abs v () g+s sk fk . x)
     ;; no OR clauses, call the failure continuation
     (insert-abs abs fk))
    ((_ abs v (p) . x)
     ;; last (or only) OR clause, just expand normally
     (match-one abs v p . x))
    ((_ abs v (p . q) g+s sk fk i)
     ;; match one and try the remaining on failure
     (match-one abs v p g+s sk (match-gen-or-step v q g+s sk fk i) i))
    ))

(define-syntax match-three
  (lambda (x)
    (syntax-case x ()
      ((q abs w p g+s sk fk i)
       (check-sym (syntax->datum (syntax p))) 
       (syntax (match-three* abs w p g+s sk fk i))))))

(define-syntax match-three*
  (syntax-rules (_ ___ *** quote quasiquote ? $ = and or not set! get!)
    ((match-two (abs ((car cdr pair? null?) rr)) v (p) g+s sk fk i)
     (if (and (pair? v) (null? (cdr v)))
         (let ((w (car v)))
           (match-one (abs ((car cdr pair? null?) rr)) w p ((car v) (set-car! v)) sk fk i))
         fk))
    ((match-two abs v (p *** q) g+s sk fk i)
     (match-extract-vars abs p (match-gen-search v p q g+s sk fk i) i ()))
    ((match-two abs v (p *** . q) g+s sk fk i)
     (match-syntax-error "invalid use of ***" (p *** . q)))
    ((match-two (abs ((car cdr pair? null? equal?) pp)) v (p . q) g+s sk fk i)
     (if (pair? v)
         (let ((w (car v)) (x (cdr v)))
           (match-one (abs ((car cdr pair? null? equal?) pp)) 
                      w p ((car v) (set-car! v))
                      (match-one x q ((cdr v) (set-cdr! v)) sk fk)
                      fk
                      i))
         (insert-abs (abs ((car cdr pair? null? equal?) pp)) fk)))
    ((match-two abs v #(p ...) g+s . x)
     (match-vector abs v 0 () (p ...) . x))
    ((match-two abs v _ g+s (sk ...) fk i) (insert-abs abs (sk ... i)))
    ;; Not a pair or vector or special literal, test to see if it's a
    ;; new symbol, in which case we just bind it, or if it's an
    ;; already bound symbol or some other literal, in which case we
    ;; compare it with EQUAL?.
    ((match-two (abs ((car cdr pair? null? equal?) pp)) 
                v x g+s (sk ...) fk (id ...))
     (let-syntax
         ((new-sym?
           (syntax-rules (id ...)
             ((new-sym? x sk2 fk2) sk2)
             ((new-sym? y sk2 fk2) fk2))))
       (new-sym? random-sym-to-match
                 (let ((x v)) 
                   (insert-abs (abs ((car cdr pair? null? equal?) pp)) 
                               (sk ... (id ... x))))
                 (if (equal? v x) 
                     (insert-abs (abs ((car cdr pair? null? equal?) pp)) 
                                 (sk ... (id ...)))
                     (insert-abs (abs ((car cdr pair? null? equal?) pp)) 
                                 fk)))))
    ))

;;warn agains miss spelled abstractions
(define (check-sym x)
  (let ((f (lambda (x)
             (let ((l (string->list (symbol->string x))))
               (if (eq? (car l) #\<)
                   (if (not (and (pair? (cdr l)) 
                                 (eq? #\> (cadr l)) (null? (cddr l))))
                       (let loop ((l l))
                         (if (pair? l)
                             (if (null? (cdr l))
                                 (if (eq? (car l) #\>)
                                     (warn (format #f
             "<> like variable that is not an abstraction e.g. ~a"
                                                   x)))
                                 (loop (cdr l)))))))))))
    (if (symbol? x)
        (f x)
        (if (and (pair? x) (symbol? (car x)))
            (f (car x))))))
            

         

        
    
(define-syntax match-abstract
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(match-abstract ,(syntax->datum (syntax l))))
       (syntax (match-abstract* . l))))))

(define-syntax match-abstract*
  (lambda (x)
    (syntax-case x ()
      ((q x () phd          y p               . l)
       (syntax (match-phd () phd x y p . l)))

      #;((q (x ...) ((a) us ...) phd y ((b bs ...) . ps) g+s sk fk i)
      (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
      (syntax (let ((ret ((a bs ...) y)))
      (if ret
                         (match-one  (((a) us ... x ...) phd) 
                                     (cdr ret) ps g+s sk fk i)
                         (insert-abs (((a) us ... x ...) phd) fk))))
           (syntax (match-abstract ((a) x ...) 
                                   (us ...) phd 
                                   y ((b bs ...) . ps) g+s sk fk i))))

      #;((q (x ...) ((a aa as ...) us ...) phd y ((b  bs ...) . ps) g+s sk fk i)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (let ((ret ((a bs ...) y)))
                     (if ret
                         (let ((aa (car ret)))
                           (match-one  (((a as ...) us ... x ...) phd) 
                                       (cdr ret) ps g+s sk fk (aa . i)))
                         (insert-abs (((a as ...) us ... x ...) phd) fk))))
           (syntax (match-abstract ((a aa as ...) x ...) (us ...) phd y 
                                   ((b bs ...) . ps) g+s sk fk i))))



      ((q (x ...) ((a) us ...) phd y (b . ps) g+s sk fk i)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (let ((ret (a y)))
                     (if ret
                         (match-one  (((a) us ... x ...) phd) (cdr ret) 
                                     ps g+s sk fk i)
                         (insert-abs (((a) us ... x ...) phd) fk))))
           (syntax (match-abstract ((a) x ...) (us ...) phd y (b . ps) 
                                   g+s sk fk i))))

      ((q (x ...) ((a aa as ...) us ...) phd y (b . ps) g+s sk fk i)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (let ((ret (a y)))
                     (if ret
                         (let ((aa  (car ret)))
                           (match-one  (((a as ...) us ... x ...) phd) 
                                       (cdr ret) ps g+s sk fk (aa . i)))
                         (insert-abs (((a as ...) us ... x ...) phd) fk))))
           (syntax (match-abstract ((a aa as ...) x ...) (us ...) phd y 
                                   (b . ps) g+s sk fk i))))
      ((q () abs phd y p g+s sk fk i)
       (syntax (match-phd () phd abs y p g+s sk fk i))))))

(define-syntax match-phd
  (lambda (x)
    (syntax-case x ()
      ((_ phd (c (            )) abs . l) 
       (syntax (match-three (abs (c phd)) . l)))
      ((_ (phd ...) (c ((h a) hh ...)) abs v (h2 . l) g+s sk fk i)
       (if (eq? (syntax->datum (syntax h)) 
                (syntax->datum (syntax h2)))
           (syntax (match-one (abs (a ((h a) hh ... phd ...))) 
                              v l g+s (set-phd-sk c sk) (set-phd-fk c fk) i))
           (syntax (match-phd ((h a) phd ...) (c (hh ...)) abs v (h2 . l) 
                              g+s sk fk i))))
      ((_ () phd abs . l)
       (syntax (match-three (abs phd) . l))))))

(define-syntax set-phd-fk
  (syntax-rules (begin)
    ((_ abs          cc (begin . l))  (begin . l))
    ((_ abs          cc (fk))         (fk))
    ((_ (abs (c pp)) cc (fk fkk ...)) (fk (abs (cc pp)) fkk ...))))

(define-syntax set-phd-sk
  (syntax-rules (begin)
    ((_ abs          cc (begin . l)  i ...)  (begin . l))
    ((_ abs          cc (fk)         i ...)  (fk))
    ((_ (abs (c pp)) cc (fk fkk ...) i ...)  (fk (abs (cc pp)) fkk ... i ...))))

(define-syntax match-$
  (lambda (x)
    (syntax-case x ()
      ((q abs (a ...) m (p1 p2 ...) . v)
       (with-syntax ((m+1 (datum->syntax (syntax q) 
					 (+ (syntax->datum (syntax m)) 1))))
          (syntax (match-$ abs (a ... (= 0 m p1)) m+1 (p2 ...) . v))))
      ((_ abs newpat  m ()            v kt ke i)
       (syntax (match-one abs v newpat () kt ke i))))))


(define-syntax match-gen-ellipses
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(match-gen-ellipses ,@(syntax->datum (syntax l))))
       (syntax (match-gen-ellipses* . l))))))


(define-syntax match-gen-ellipses*
  (syntax-rules ()
    ((_ (abs ((qcar qcdr qpair? qnull? qequal?) ppqq))
        v p () g+s (sk ...) fk i ((id id-ls) ...))
     
     ;; simple case, match all elements of the list
     (let loop ((ls v) (id-ls '()) ...)
       (cond
        ((qnull? ls)
         (let ((id (reverse id-ls)) ...) 
           (insert-abs (abs ((qcar qcdr qpair? qnull? qequal?) ppqq))
                       (sk ... i))))
        ((qpair? ls)
         (let ((w (qcar ls)))
           (match-one (abs ((qcar qcdr qpair? qnull? qequal?) ppqq))
                      w p ((qcar ls) (set-car! ls))
                      (match-drop-ids (loop (qcdr ls) (cons id id-ls) ...))
                      fk i)))
        (else
         (insert-abs (abs ((qcar qcdr qpair? qnull? qequal?) ppqq))
                     fk)))))

    ((_ (abs ((qcar qcdr qpair? qnull? qequal?) qqpp))
        v p r g+s (sk ...) fk i ((id id-ls) ...))
     ;; general case, trailing patterns to match, keep track of the
     ;; remaining list length so we don't need any backtracking
     (match-verify-no-ellipses
      r
      (letrec ((f (lambda (x) 
                    (if (qpair? x) 
                        (cons (qcar x) 
                              (f (qcdr x))) 
                        '()))))

      (let* ((tail-len (length 'r))
             (ls (f v))
             (len (length ls)))
        (if (< len tail-len)
            fk
            (let loop ((ls ls) (n len) (id-ls '()) ...)
              (cond
                ((= n tail-len)
                 (let ((id (reverse id-ls)) ...)
                   (match-one (abs ((qcar qcdr qpair? qnull? qequal?) qqpp))
                              ls r (#f #f) (sk ...) fk i)))
                ((pair? ls)
                 (let ((w (car ls)))
                   (match-one (abs ((qcar qcdr qpair? qnull? qequal?) qqpp))
                              w p ((car ls) (set-car! ls))
                              (match-drop-ids
                               (loop (cdr ls) (- n 1) (cons id id-ls) ...))
                              fk
                              i)))
                (else
                 fk))))))))))


(define-syntax match-drop-ids
  (syntax-rules ()
    ((_ expr            ) expr)
    ((_ abs expr ids ...) expr)))

(define-syntax match-gen-search
  (syntax-rules ()
    ((match-gen-search abs v p q g+s sk fk i ((id id-ls) ...))
     (letrec ((try (lambda (w fail id-ls ...)
                     (match-one abs w q g+s
                                (match-drop-ids
                                 (let ((id (reverse id-ls)) ...)
                                   sk))
                                (match-drop-ids (next w fail id-ls ...)) i)))
              (next (lambda (w fail id-ls ...)
                      (if (not (pair? w))
                          (fail)
                          (let ((u (car w)))
                            (match-one
                             abs u p ((car w) (set-car! w))
                             (match-drop-ids
                              ;; accumulate the head variables from
                              ;; the p pattern, and loop over the tail
                              (let ((id-ls (cons id id-ls)) ...)
                                (let lp ((ls (cdr w)))
                                  (if (pair? ls)
                                      (try (car ls)
                                           (lambda () (lp (cdr ls)))
                                           id-ls ...)
                                      (fail)))))
                             (fail) i))))))
       ;; the initial id-ls binding here is a dummy to get the right
       ;; number of '()s
       (let ((id-ls '()) ...)
         (try v (lambda () (insert-abs abs fk)) id-ls ...))))))

(define-syntax match-quasiquote
  (syntax-rules (unquote unquote-splicing quasiquote)
    ((_ abs v (unquote p) g+s sk fk i)
     (match-one abs v p g+s sk fk i))
    ((_ abs v ((unquote-splicing p) . rest) g+s sk fk i)
     (if (pair? v)
       (match-one abs v
                  (p . tmp)
                  (match-quasiquote tmp rest g+s sk fk)
                  fk
                  i)
       (insert-abs abs fk)))
    ((_ abs v (quasiquote p) g+s sk fk i . depth)
     (match-quasiquote abs v p g+s sk fk i #f . depth))
    ((_ abs v (unquote p) g+s sk fk i x . depth)
     (match-quasiquote abs v p g+s sk fk i . depth))
    ((_ abs v (unquote-splicing p) g+s sk fk i x . depth)
     (match-quasiquote abs v p g+s sk fk i . depth))
    ((_ abs v (p . q) g+s sk fk i . depth)
     (if (pair? v)
       (let ((w (car v)) (x (cdr v)))
         (match-quasiquote
          abs w p g+s
          (match-quasiquote-step x q g+s sk fk depth)
          fk i . depth))
       (insert-abs abs fk)))
    ((_ abs v #(elt ...) g+s sk fk i . depth)
     (if (vector? v)
       (let ((ls (vector->list v)))
         (match-quasiquote abs ls (elt ...) g+s sk fk i . depth))
       (insert-abs abs fk)))
    ((_ abs v x g+s sk fk i . depth)
     (match-one abs v 'x g+s sk fk i))))

(define-syntax match-quasiquote-step
  (syntax-rules ()
    ((match-quasiquote-step abs x q g+s sk fk depth i)
     (match-quasiquote abs x q g+s sk fk i . depth))))

(define-syntax match-extract-vars
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(match-extract-vars ,(syntax->datum (syntax l))))
       (syntax (match-extract-vars* . l))))))


;;We must be able to extract vars in the new constructs!!
(define-syntax match-extract-vars*
  (syntax-rules (_ ___ *** ? $ <> = quote quasiquote unquote 
                   unquote-splicing and or not get! set!)
    ((match-extract-vars abs (? pred . p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs ($ rec . p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs (= proc p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs (= u m p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs (quote x) (k kk ...) i v)
     (k abs kk ... v))
    ((match-extract-vars abs (unquote x) (k kk ...) i v)
     (k abs kk ... v))
    ((match-extract-vars abs (unquote-splicing x) (k kk ...) i v)
     (k abs kk ... v))
    ((match-extract-vars abs (quasiquote x) k i v)
     (match-extract-quasiquote-vars abs x k i v (#t)))
    ((match-extract-vars abs (and . p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs (or . p) . x)
     (match-extract-vars abs p . x))
    ((match-extract-vars abs (not . p) . x)
     (match-extract-vars abs p . x))
    ;; A non-keyword pair, expand the CAR with a continuation to
    ;; expand the CDR.
    ((match-extract-vars abs (<> f p) k i v)
     (match-extract-vars abs p k i v))
    ((match-extract-vars (abs phd) p k i v)
     (abs-extract-vars () abs phd p k i v))))

(define-syntax match-extract-vars2
  (syntax-rules (_ ___ *** ? $ = quote quasiquote and or not get! set!)
    ((match-extract-vars abs (p q . r) k i v)
     (match-check-ellipse
      q
      (match-extract-vars abs (p . r) k i v)
      (match-extract-vars abs p (match-extract-vars-step (q . r) k i v) i ())))
    ((match-extract-vars abs (p . q) k i v)
     (match-extract-vars abs p (match-extract-vars-step q k i v) i ()))
    ((match-extract-vars abs #(p ...) . x)
     (match-extract-vars abs (p ...) . x))
    ((match-extract-vars abs _ (k kk ...) i v)    (k abs kk ... v))
    ((match-extract-vars abs ___ (k kk ...) i v)  (k abs kk ... v))
    ((match-extract-vars abs *** (k kk ...) i v)  (k abs kk ... v))
    ;; This is the main part, the only place where we might add a new
    ;; var if it's an unbound symbol.
    ((match-extract-vars abs p (k kk ...) (i ...) v)
     (let-syntax
         ((new-sym?
           (syntax-rules (i ...)
             ((new-sym? p sk fk) sk)
             ((new-sym? x sk fk) fk))))
       (new-sym? random-sym-to-match
                 (k abs kk ... ((p p-ls) . v))
                 (k abs kk ... v))))
    ))

(define-syntax abs-extract-vars
  (lambda (x)
    (syntax-case x ()
      ((q . l) 
       ;(pk `(abs-extract-vars ,@(syntax->datum (syntax l))))
       (syntax (abs-extract-vars* . l))))))

(define-syntax abs-extract-vars*
  (lambda (x)
    (syntax-case x ()
      ((q abs () phd p . l) (syntax (match-extract-phd () phd abs p . l)))
      ((q (abs ...) ((a x . xs) us ...) phd ((b bs ...) w ...) k i v)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (match-extract-vars 
                    (((a . xs) us ... abs ...) phd) (w ...) k i ((x x-ls) . v)))
           (syntax (abs-extract-vars   
                    ((a x . xs) abs ...) (us ...) phd ((b bs ...) w ...) 
                    k i v))))

      ((q (abs ...) ((a) us ...) phd ((b bs ...) w ...) k i v)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (match-extract-vars 
                    (((a) us ... abs ...) phd) (w ...) k i v)))
           (syntax (abs-extract-vars   
                    ((a) abs ...) (us ...) phd ((b bs ...) w ...) k i v)))

      ((q (abs ...) ((a x . xs) us ...) phd (b w ...) k i v)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (match-extract-vars 
                    (((a . xs) us ... abs ...) phd) (w ...) k i ((x x-ls) . v)))
           (syntax (abs-extract-vars   
                    ((a x . xs) abs ...) (us ...) phd (b w ...) k i v))))

      ((q (abs ...) ((a) us ...) phd (b w ...) k i v)
       (if (eq? (syntax->datum (syntax a)) (syntax->datum (syntax b)))
           (syntax (match-extract-vars 
                    (((a) us ... abs ...) phd) (w ...) k i v))
           (syntax (abs-extract-vars   
                    ((a) abs ...) (us ...) phd (b w ...) k i v))))
      ((q () a phd p k i v)
       (syntax (match-extract-phd () phd a p k i v))))))

(define-syntax match-extract-phd
  (syntax-rules ()
    ((_ _ phd abs . l) (match-extract-vars2 (abs phd) . l))))

(define-syntax match-extract-vars-step
  (syntax-rules ()
    ((_ abs p k i v ((v2 v2-ls) ...))
     (match-extract-vars abs p k (v2 ... . i) ((v2 v2-ls) ... . v)))
    ))

(define-syntax match-extract-quasiquote-vars
  (syntax-rules (quasiquote unquote unquote-splicing)
    ((match-extract-quasiquote-vars abs (quasiquote x) k i v d)
     (match-extract-quasiquote-vars abs x k i v (#t . d)))
    ((match-extract-quasiquote-vars abs (unquote-splicing x) k i v d)
     (match-extract-quasiquote-vars abs (unquote x) k i v d))
    ((match-extract-quasiquote-vars abs (unquote x) k i v (#t))
     (match-extract-vars abs x k i v))
    ((match-extract-quasiquote-vars abs (unquote x) k i v (#t . d))
     (match-extract-quasiquote-vars abs x k i v d))
    ((match-extract-quasiquote-vars abs (x . y) k i v (#t . d))
     (match-extract-quasiquote-vars abs
      x
      (match-extract-quasiquote-vars-step y k i v d) i ()))
    ((match-extract-quasiquote-vars abs #(x ...) k i v (#t . d))
     (match-extract-quasiquote-vars abs (x ...) k i v d))
    ((match-extract-quasiquote-vars abs x (k kk ...) i v (#t . d))
     (k abs kk ... v))
    ))

(define-syntax match-extract-quasiquote-vars-step
  (syntax-rules ()
    ((_ abs x k i v d ((v2 v2-ls) ...))
     (match-extract-quasiquote-vars abs x k (v2 ... . i) 
                                    ((v2 v2-ls) ... . v) d))
    ))


(define-syntax match-define
  (syntax-rules (abstractions)
    ((q abstractions abs arg code)
     (match-extract-vars abs arg (sieve (match-define-helper0 arg code) ()) 
                         () ()))
    ((q arg code)
     (match-extract-vars ()  arg (sieve (match-define-helper0 arg code) ()) 
                         () ()))))

(define-syntax sieve
  (syntax-rules ()
    ((_ cc (w ...) ((v q) v2 ...))
     (sieve cc (v w ...) (v2 ...)))
    ((_ cc (w ...) (v v2 ...))
     (sieve cc (v w ...) (v2 ...)))
    ((_ (cc ...) w ())
     (cc ... w))))
  
(define-syntax match-define-helper0
  (lambda (x)
    (syntax-case x ()
      ((q arg code v)
       (with-syntax ((vtemp (map (lambda (x)
				   (datum->syntax
				    (syntax q) (gensym "temp")))
				 (syntax->datum (syntax v)))))
	  (syntax (match-define-helper v vtemp arg code)))))))

(define-syntax match-define-helper
  (syntax-rules ()
    ((_ (v ...) (vt ...) arg code) 
     (begin 
       (begin (define v 0) 
	      ...)
       (let ((vt 0) ...)
	 (match  code 
		 (arg (begin (set! vt v) 
			     ...)))
	 (begin (set! v vt) 
		...))))))


;;;Reading the rest from upstream

;;Utility
(define-syntax include-from-path/filtered
  (lambda (x)
    (define (hit? sexp reject-list)
      (if (null? reject-list)
	  #f
	  (let ((h (car reject-list))
		(l (cdr reject-list)))
	    (if (and (pair? sexp)
		     (eq? 'define-syntax (car sexp))
		     (pair? (cdr sexp))
		     (eq? h (cadr sexp)))
		#t
		(hit? sexp l)))))

    (define (read-filtered reject-list file)
      (with-input-from-file (%search-load-path file)
        (lambda ()
          (let loop ((sexp (read)) (out '()))
            (cond
             ((eof-object? sexp) (reverse out))
             ((hit? sexp reject-list)
              (loop (read) out))
             (else
              (loop (read) (cons sexp out))))))))

    (syntax-case x ()
      ((_ reject-list file)
       (with-syntax (((exp ...) (datum->syntax
                                 x 
                                 (read-filtered
                                  (syntax->datum #'reject-list)
                                  (syntax->datum #'file)))))
		    #'(begin exp ...))))))

(include-from-path/filtered
 (match-extract-vars  match-one       match-gen-or      match-gen-or-step 
                      match-two       match match-next  match-gen-ellipses
                      match-drop-ids  match-gen-search  match-quasiquote
                      match-quasiquote-step  match-extract-vars-step
                      match-extract-quasiquote-vars  
                      match-extract-quasiquote-vars-step)
 "ice-9/match.upstream.scm")



(define-syntax make-phd-matcher
  (syntax-rules ()
    ((_ name pd)
     (begin
       (define-syntax name 
         (lambda (x)
           (syntax-case x ()
             ((_ . l)
              (syntax (match -phd pd . l))))))))))
  

