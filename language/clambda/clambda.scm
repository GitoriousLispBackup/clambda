(define-module (language clambda clambda)
  #:use-module (ice-9    match-phd          )
  #:use-module (language clambda meta       )
  #:use-module (language clambda validators )
  #:use-module (language clambda fmt        )
  #:use-module (language clambda parse syntax-parse)
  #:use-module (language clambda parse match-parse )
  #:use-module (language clambda line       )
  #:use-module (language clambda syntax-ops )
  #:use-module (srfi srfi-1)
  #:re-export  (auto my-block)
  #:export     (clambda->c *debug-clambda* f-define f-sub f-let* f-if <lit>
                           z f-begin f-call f-recur f-next <=> <==> <recur> 
                           <next> <call> <icall> <+> <-> <*> </> <icall>
                           q< q> q<= q>= <and> <or> <!=> <bit-and> <bit-or>
                           <bit-xor> <define> <if> <let*> <begin> <const> 
                           <global> <struct> %array <ref> <++> <--> <syntax>
                           <cast> -> <.> <not> <addr> <declare> <let>
                           <declare-rename> <c> <scm-call> <acall>
                           <case> <cond> <size-of> <malloc> <free>
                           <clambda-stub> <error> -.> => auto-t
                           <goto> <label> <break> <while-1> init-clambda
                           *clambda* clambda-add *c-line-numbers* mk-var
                           *cage* mk-lambda-cage
                           ))

(define-syntax aif
  (syntax-rules ()
    ((_ (a) p . l)
     (let ((a p)) (if a . l)))))

(define *clambda* '())
(define *lnr* 0)
(define (init-clambda)
  (fluid-set! *cage* (mk-top-cage))
  (set! *lnr* 0)
  (set! *clambda* '()))

(define (clambda-add x)
  (set! *clambda* (cons x *clambda*)))

(define (c-it x)
  (lambda (v)
    (match v
      (#t x)
      (v  (if (symbol? v)
              (c= v x)
              (v x))))))

(define (<c> x)
  (if (procedure? x)
      x
      (c-it x)))

(define-syntax parental
  (syntax-rules ()
    ((_ parent p)
      (match parent
        ('()  (set! p (lambda v (error (format #f "~a is not defined" v)))))
        ((q)  (set! p q))))))


(define mk-cage
  (let ((syms '())
        (p     #f))
    (lambda parent
      (parental parent p)
      (lambda x
        (match x
          (('top s) (if (assq s syms)
                        #f
                        (p 'top s)))
          (('new s) (set! syms (cons (cons s s) syms)))
          (('ref s) (aif (it) (assq s syms)
                        (cdr it)
                        (p 'ref s))))))))

(define mk-top-cage
  (let ((syms '())
        (p     #f))
    (lambda parent
      (parental parent p)
      (lambda x
        (match x
          (('top s) (assq s syms))
          (('new s) (set! syms (cons (cons s s) syms)))
          (('ref s) (aif (it) (assq s syms)
                        (cdr it)
                        (p 'ref s))))))))

#|
TODO, make closure variables work with set!
|#

(define mk-lambda-cage
    (lambda (clr . parent)
      (let ((syms '())
            (cp   '())
            (p     'no-parent)
            (n      2))
        (parental parent p)
        (lambda x
          ;(pk `(cage ,x))
          (match x
            (('top s) (if (assq s syms)
                          #f
                          (p 'top s)))
            (('new s) 
             (set! syms (cons (cons s s) syms)))
            (('ref '__closure)
             '__closure)
            (('ref s) (aif (it) (assq s syms)
                           (cdr it)
                           (aif (it) (assq s cp)
                                ((cdr it) clr)
                                (if (p 'top s)
                                    (p 'ref s)
                                    (let* ((m n)
                                           (v (lambda (clr) 
                                                `(AREF ,(clr #t) ,m))))
                                      (set! cp (cons (cons s v) cp))
                                      (set! n (+ n 1))
                                      (p 'ref s)
                                      (v clr))))))
            (('len)     (length cp))
            (('clr obj)   (map (lambda (cp)
                                 (lambda v
                                   (c= ((cdr cp) obj)
                                       (p 'ref (car cp)))))
                             (reverse cp))))))))
                               
(define *cage* (make-fluid))
(define *top*  (make-fluid))

(fluid-set! *cage* (mk-top-cage))
(fluid-set! *top* #t)

(define (mk-var type sym val . l)
  (let* ((g   (if (null? l)
                  (gensym (symbol->string sym))
                  sym))
         (use (lambda () ((fluid-ref *cage*) 'ref g))))
    ((fluid-ref *cage*) 'new g)
    (lambda v
      ;(pk `(var ,v))
      (match v
        (('def )   (lambda x (c-var type g)))
        (('init)   (lambda x
                     (if (eq? val '*)
                         fmt-null
                         (begin
                           (val g)))))
        (('type)   type)
        (('val)    val)
        (('use)    (use))
        (('set x)  (x (use g)))
        (('expr)   #t)
        ((#f)      fmt-null)
        ((#t)      (use))
        ((v)       (c= v (use)))))))


(define-syntax <lit>
  (syntax-rules ()
    ((_ x) 
     (lambda (v)
       (match v
         (#f    fmt-null)
         (#t    x)
         ('expr #t)
         ('type 'literal)
         (_  (c= v x)))))))

(define (reg-form x)
  (if (syntax-source x)
      (set! *src-tag* x)))


;; symbol translator
(define (sym->csym s)
  (define (f x)
    (match x
      ((#\: . l) `(#\_ #\c ,@(f l)))
      ((#\> . l) `(#\_ #\g ,@(f l)))
      ((#\< . l) `(#\_ #\l ,@(f l)))
      ((#\! . l) `(#\_ #\e ,@(f l)))
      ((#\* . l) `(#\_ #\s ,@(f l)))
      ((#\- . l) `(#\_ #\_ ,@(f l)))
      ((#\? . l) `(#\_ #\p ,@(f l)))
      ((#\_ . l) `(#\_     ,@(f l)))
      ((x   . l)  (cons x (f l)))
      (()        '())))
  (string->symbol
   (list->string (f (string->list 
                     (symbol->string s))))))

(define (csym->sym s)
  (define (f x)
    (match x
      ((#\_ #\c . l) `(#\: ,@(f l)))
      ((#\_ #\s . l) `(#\* ,@(f l)))
      ((#\_ #\l . l) `(#\< ,@(f l)))
      ((#\_ #\g . l) `(#\> ,@(f l)))
      ((#\_ #\e . l) `(#\! ,@(f l)))
      ((#\_ #\p . l) `(#\? ,@(f l)))
      ((#\_ #\_ . l) `(#\- ,@(f l)))
      ((#\_     . l) `(#\_ ,@(f l)))
      ((x       . l)  (cons x (f l)))
      (()            '())))
  (string->symbol
   (list->string (f (string->list 
                     (symbol->string s))))))



(define <fail> (lambda (x) (list #t)))



;; ********************* TOOLBOX ********************
(define-syntax auto-quote
  (lambda (x)
    (syntax-case x ()
      ((_ a)
       (let ((v (syntax->datum #'a)))
         (if (symbol? v)
             (with-syntax ((qa (datum->syntax #'a 
                                              (sym->csym
                                               (syntax->datum #'a)))))
               #'(quote qa))
             #'a))))))


(define-syntax mako
  (lambda (x) 
    (syntax-case x ()
      ((_ (r ...) (c . code))
       (with-syntax ((ln (datum->syntax #'c (get-line-nr #'c))))
         #'(mako (r ... (my-line ln) (auto c)) code)))
      ((_ (code ...) ())
       #'(list code ...)))))

(define-syntax mamma
  (syntax-rules ()
    ((_ x) 
     (f-begin (mako () (x))))))


(define-syntax auto2
  (syntax-rules ()
    ((_ (a ...)) (a ...))
    ((_ a      ) (zou (auto-quote a)))))

(define (zou x)
  (lambda (v)
    (match v
      ('expr #t)
      (#f    fmt-null)
      (#t    x)
      (v    (c= v x)))))

(define-syntax auto-tt
  (syntax-rules (<array>)
    ((_ (<array> a b)) (list '%array (auto-tt a) (auto-tt b)))
    ((_ (<array> a  )) (list '%array (auto-tt a)            ))
    ((_ (a b ...))     (list (auto-tt a) 'b ...))
    ((_ a      )       (auto-quote a))))

(define-syntax auto-t
  (lambda (x)
    (syntax-case x ()
      ((_ x) #'((auto2 x) #t)))))

(define-syntax auto-type
  (syntax-rules ()
    ((_ x) (auto-tt x))))

(define old-pk pk)
(define *debug-clambda* #t)
(define pk (lambda (x)
             (if *debug-clambda* (old-pk x) x)))

(define void-it (lambda (c) (c #f)))

(define (z-2 x)
  (match x
    ((_ _) x)
    (x     `(SCM ,x))))

(define (z-3 x)
  (match x
    ((_ _ _) x)
    ((s   v) `(SCM ,s ,v))))

(define (clambda->c fn) 
  (define (g l)
    (map (lambda (x)
           (if (and (pair? x) (eq? (car x) '+dive+))
               x
               (fmt #f           
                    (fmt-let 'braceless-bodies? #f
                             x))))
         l))

  (define (f x)
    (match x
      ((('+dive+ . x) . l) (string-append (f (g x)) 
                                          (string-append "\n" (f l)))) 
      ((x             . l) (string-append x 
                                          (string-append "\n" (f l))))
      (()                  "")))
  (pp 'clambda->c)
  (let* ((S   (open fn (logior O_WRONLY O_CREAT O_TRUNC)))
         (ret (f (g (reverse *clambda*)))))
    (format S "~a" ret)
    (close S)
    #t))

(define-syntax +fkn+
  (syntax-rules ()
    ((_ F)
     (lambda (v)
       (let ((G (lambda () F)))
         (match v
           ('expr #t)
           (#f  (G))
           (#t  (G))
           ('type non-decidable)
           (v   (c= v (G)))))))))


(define <er1-list1> (<parse-list..> 
                 #t
                 "Buggy"
                 "(x ...) in (<syntax> (x ...) c ...) is missing"
                 2
                 ))


(define-syntax <syntax>
  (syntax-parse-rules ()
    ((_ (b ...) a ... : <er1-list1>) ((lambda () b ... `(+dive+ ,a ...))))))


(define-syntax <clambda-stub>
  (syntax-rules ()
    ((_ . l) (list '+dive+ . l))))

(define-syntax <error>
  (syntax-rules ()
    ((_ m) (+fkn+ `(ERROR ,(auto-t m))))))
;; ***************** const

(define-syntax <const>
  (lambda (x)

    (define <tp>   (mk-type-vd         #t '<const>))
    (define <id>   (mk-identifier-vd   #t '<const>))
    (define <arg3> (mk-arg-vd          #t '<const> 3))

    (reg-form x)

    (syntax-parse x ()
      ((_ (t : <tp>) (s : <id>)  v : <arg3>)
       #'(begin
           (define s (mk-var (auto-type t)
                             (auto-t s)
                             (auto v)
                             'no-gensym))
           
           (set! *clambda*
                 (cons (c-const (c-var (auto-type t) (s #t) (v #t)))
                       *clambda*)))))))
 
;; ***************** global

(define-syntax <global>
  (lambda (x)
    (define <tp>   (mk-type-vd         #t '<global>))
    (define <id>   (mk-identifier-vd   #t '<global>))
    (define <arg2> (mk-arg-vd          #f '<global> 2))
    (define <arg3> (mk-arg-vd          #t '<global> 3))

    (reg-form x)
    (syntax-parse x ()
      ((_ (t : <tp>) (s : <id>) : <arg2>)
       (pp `(global ,#'s))
       #'(begin
           (define s (mk-var (auto-type t)
                             (auto-t s)
                             #f
                             'no-gensym))
           (set! *clambda* (cons ((s 'def) #t) *clambda*))))
                 
      ((_ (t : <tp>) (s : <id>) v : <arg3>)
       (pp `(global ,#'s))
       #'(begin
           (define s (mk-var (auto-type t)
                             (auto-t s)
                             (auto v)
                             'no-gensym))
           (set! *clambda*
                 `(,(c-var (auto-type t) (s #t) (v #t))
                   ,@*clambda*)))))))

;; ****************** goto/label

;; this is a low level routine and should normally not be used in programs
;; this is needed because restrictions in placing labels in c language specification
(define-syntax <while-1>
  (lambda (x)
    (define <arg..> (mk-arg*-vd #t '<while-1> 1))
    (syntax-parse x ()
      ((_ a ... : <arg..>)
       #'(lambda (v)
           (c-while 1 ((<begin> a ...) v)))))))

(define (goto-it s y)
  (let ((F (if (eq? '* s)
                c-break
               (c-goto y))))
    (lambda v
      (match v
        ((#f)    F)
        ((#t)    (error "<goto> cannot be in a expression context"))
        (('expr) #f)
        ((v)     (error "<goto> does not return a value"))))))

(define-syntax <goto>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<goto> 1))
    (syntax-parse x ()
      ((_ y : <arg>)
       #'(goto-it 'y (auto-t y))))))



(define (label-it s y)
  (let ((F (if (eq? s '*)
               fmt-null
               (c-label y))))
           (lambda v
             (match v
               ((#f)    F)
               ((#t)    (error "<label> cannot be in a expression context"))
               (('expr) #f)
               ((v)     (error "<label> does not return a value"))))))

(define-syntax <label>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<label> 1))
    (syntax-parse x ()
      ((_ y : <arg>)
       #'(label-it 'y (auto-t y))))))

(define break-it
  (let ((F c-break))
    (lambda v
      (match v
        ((#f)    F)
        ((#t)    (error "<break> cannot be in a expression context"))
        (('expr) #f)
        ((v)     (error "<break> does not return a value"))))))

(define-syntax <break>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<break> 0))
    (syntax-parse x ()
      ((_ : <arg>)
       #'break-it))))

;; ***************** struct

(define-syntax <struct>
  (lambda (x)

    (define <struct-list2> (<parse-list> 
                            #t
                            "Buggy"
                            "2 items needed in (<struct> name decl)"
                            3
                            ))

    (define <struct-list1> (<parse-list..> 
                            #t
                            "second argument is a list in <struct>"
                            "number of struct declarations are zero"
                            1
                            ))

    (define <struct-sym>  (<symbol> "<struct> name has to be a symbol"))

    (define <decl> (mk-decl-vd #t '<struct>))
    (reg-form x)
    (syntax-parse x ()      
      ((_ (n : <struct-sym>) 
          ((a : <decl>) ... : <struct-list1>)  :  <struct-list2>) 
       (with-syntax ((ln (datum->syntax #'x (get-line-nr #'(a ...)))))         
         (pp `(struct ,#'n))
         #'(set! *clambda*
                 (cons
                  (list
                   '+dive+
                   (line ln)
                   (c-typedef 
                    (c-struct (auto-t n) (list (farg a) ...))
                    (auto-t n)))
                  *clambda*)))))))

;; ***************** cast
(define-syntax <cast>
  (lambda (x)
    (define <tp>     (mk-type-vd #t '<cast>))
    (define <2-args> (mk-arg-vd  #t '<cast> 2))
    (reg-form x)
    (syntax-parse x ()
      ((_ (t : <tp>) r : <2-args>)
       #'(lambda (v)
           (let* ((tt (auto-type t))
                  (g (lambda () (c-paren (c-cast tt ((auto r) #t))))))
             (match v
               (#f  fmt-null)
               (#t        (g))
               ('expr     #t)
               ('type     tt)
               (v   (c= v (g))))))))))


(define-syntax <malloc>
  (lambda (x)
    (define <tp>     (mk-type-vd #t '<malloc>))
    (define <3-args> (mk-arg-vd  #t '<malloc> 3))
    (reg-form x)
    (syntax-parse x ()
      ((_ (t : <tp>)  n s : <3-args>)
       #'(lambda (v)
           (let ((g (lambda () (c-cast (auto-type t) 
                                       `(malloc ,(auto-t n) ,(auto-t s))))))
             (match v
               (#f  (error "malloc returns to nothing"))
               (#t  (g))
               ('type '(void *))
               ('expr #t)
               (v   (c= v (g))))))))))


(define-syntax <free>
  (lambda (x)
    (define <1-args> (mk-arg-vd #t '<free> 1))
    (reg-form x)
    (syntax-parse x ()
      ((_ x : <1-args>)
       #'(lambda (v)
           (let ((g (lambda () `(free (auto-t v)))))
             (match v
               (#f  (error "free does not return a value"))
               (#t  (g))
               ('type 'undefined)
               ('expr #f)
               (v   (error "free does not return a value")))))))))


(define-syntax <size-of>
  (lambda (x)
    (define <1-args> (mk-arg-vd #t '<size-of> 1))
    (reg-form x)

    (syntax-parse x ()
      ((_ t : <1-args>)
       #'(lambda (v)
           (let ((g (lambda () (c-sizeof (auto-type t)))))
             (match v
               (#f  fmt-null)
               (#t       (g)) 
               ('expr     #t)
               ('type     'int)
               (v   (c= v (g))))))))))

;; ***************** ref

(define (ref-it vv i)
  (lambda (v)
    (let* ((g (lambda () (c-apply (list 'AREF (vv #t) (i #t))))))
      (match v
        (#f    fmt-null)
        (#t    (g))
        
        ('type (match (vv 'type)
                 (('%array t . l) t)
                 ((t '* '* . l)  `(,t * ,@l))
                 ((t '*)          t)
                 (_               (error "type-error in <ref>"))))
        
        ('expr #t)
        (_  (c= v (g)))))))

(define-syntax <ref>
  (lambda (x)
    (define <2-args> (mk-arg-vd #t '<ref> 2))
    (reg-form x)
    (syntax-parse x ()    
      ((_ w i : <2-args>)
       #'(ref-it (auto w) (auto i))))))

;; ************************************** declare ****************

(define (qa x)
  (syntax-case x ()
    ((t a) #'a)
    (a     #'a)))

(define (qt x)
  (syntax-case x ()
    ((t a) #'(auto-type t))
    (a     #'(auto-type SCM))))

(define (pp x)
  (format #t "~10a~%" (syntax->datum x))
  x)

(define-syntax <declare>
  (lambda (x)
    (define <decl-list3> 
      (<parse-list> 
       #f
       "Buggy"
       "not three items in (<declare> res-type fkn-name var-decl)"
       4
       ))

    (define <decl-list2> 
      (<parse-list> 
       #t
       "Buggy"
       "not three items in (<declare> res-type fkn-name var-decl)"
       3
       ))

    (define <decl-list>
      (<parse-list..> 
       #t
       "variable declaration part is not a list"
       "Buggy"  
       ))

    (define <fsym>  (<symbol> #t "function name is not an id"))
    (define <decl> (mk-decl-vd #t 'function))
    (define <tp>   (mk-type-vd #t 'function))
    (reg-form x)
    (syntax-parse x ()
      ((_ (t : <tp>) (f : <fsym>)    ((a : <decl>) ... : <decl-list>) 
          : <decl-list3>)
       (pp `(declare ,#'f))
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))
         #'(begin
             (define f (mk-var `(lambda (,argt ...) ,(auto-type t))
                               (auto-t f)
                               #f
                               'no-gensym))
             (set! *clambda*
                   (cons
                    (c-prototype (auto-type t) 
                                 (f #t) 
                                 (list (list argt 'arg) ...))
                    *clambda*)))))
      
      ((_ (f : <fsym>)    ((a : <decl>) ... : <decl-list>)
          : <decl-list2>)
       (pp `(declare ,#'f))
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))
         #'(begin
             (define f (mk-var `(lambda (,argt ...) ,(auto-type SCM))
                               (auto-t f)
                               #f
                               'no-gensym))
             (set! *clambda*
                   (cons
                    (c-prototype (auto-type SCM) 
                                 (f #t) 
                                 (list (list argt 'arg) ...))
                    *clambda*))))))))

(define-syntax <declare-rename>
  (lambda (x)
    (define <decl-list3> 
      (<parse-list> 
       #f
       "Buggy"
       "not three items in (<declare> res-type fkn-name var-decl)"
       4
       ))

    (define <decl-list2> 
      (<parse-list> 
       #t
       "Buggy"
       "not three items in (<declare> res-type fkn-name var-decl)"
       3
       ))

    (define <decl-list>
      (<parse-list..> 
       #t
       "variable declaration part is not a list"
       "Buggy"  
       ))

    (define <fsym>  (<symbol> #t "function name is not an id"))
    (define <decl> (mk-decl-vd #t 'function))
    (define <tp>   (mk-type-vd #t 'function))
    (reg-form x)
    (syntax-parse x (->)
      ((_ (t : <tp>) (f : <fsym>) -> (ff : <fsym>)
          ((a : <decl>) ... : <decl-list>) 
          : <decl-list3>)
       (pp `(declare-rename ,#'f))
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))
         #'(begin
             (define f (mk-var `(lambda (,argt ...) ,(auto-type t))
                               (auto-t ff)
                               #f
                               'no-gensym))
             (set! *clambda*
                   (cons
                    (c-prototype (auto-type t) 
                                 (f #t) 
                                 (list (list argt 'arg) ...))
                    *clambda*)))))
      
      ((_ (f : <fsym>)   -> (ff : <fsym>)
          ((a : <decl>) ... : <decl-list>)
          : <decl-list2>)
       (pp `(declare ,#'f))
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))
         #'(begin
             (define f (mk-var `(lambda (,argt ...) ,(auto-type SCM))
                               (auto-t ff)
                               #f
                               'mo-gensym))
             (set! *clambda*
                   (cons
                    (c-prototype (auto-type SCM) 
                                 (f #t) 
                                 (list (list argt 'arg) ...))
                    *clambda*))))))))


;; ********************************** DEFINE/SUB *************************
(define (f-define f args code)
  (let ((r (gensym "ret")))
    (let* ((fs    (f 'use))
           (ft    (caddr (f 'type))) ;(lambda (at ...) ft)
           (as    (map (lambda (a) (a 'use )) args))
           (ts    (map (lambda (a) (a 'type)) args)))
      (c-fun ft
             fs
             (map (lambda (t s) (list t s)) ts as)
             (my-block
              (c-var ft r)
              ((f-begin code) r)
              r)))))

(define (f-sub f args code)  
  (let ((r (gensym "ret")))
    (let* ((f     (f 'use))
           (as    (map (lambda (a) (a 'use )) args))
           (ts    (map (lambda (a) (a 'type)) args)))
      (c-fun 'void
             f
             (map (lambda (t s) (list t s)) ts as)
             ((f-begin code) #f)))))

;;cage logic to handle closures correctly
(define-syntax with-cage
  (syntax-rules ()
    ((_ code ...)
     (with-fluids ((*cage* (if (fluid-ref *top*)
                               (mk-cage (fluid-ref *cage*))
                               (fluid-ref *cage*))))
       (with-fluids ((*top* #f))
         code ...)))))

(define-syntax <define>
  (lambda (x)
    (define <tp>    (mk-type-vd         #t  'define))
    (define <id>    (mk-identifier-vd   #t  'define))
    (define <decl>  (mk-decl-vd         #t  'define))
    (define <void>  (mk-tag-vd          #f  'define 'void))
    (define <li2>   (<parse-list>
                     #t
                     (format #f "error in define")
                     (format #f "error in define")
                     2))
    (define <li*>   (<parse-list..>
                     #t
                     (format #f "error in define")
                     (format #f "error in define")
                     0))

    (define <li4..> (<parse-list..>
                     #t
                     (format #f 
                             "error in define not of the form ~%  ~a"
                             "(define tp nm args c1 c2 ...")
                     (format #f 
                             "error in define not of the form ~%  ~a"
                             "(define tp nm args c1 c2 ...")
                     5))   
    
    (reg-form x)
    (syntax-parse x ()
      ((_ f (a ...) . l)
       #'(<define> SCM f (a ...) . l))

      ((_ (v : <void>) (f : <id>)  ((a : <decl>) ... : <li*>)  
          code ... : <li4..>)
       
       (format #t "(define void ~a ...)~%" (syntax->datum #'f))   
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))
         #'(begin
             (define f (mk-var `(lambda (,argt ...) 'void)
                               (auto-t f)
                               #f 'no-gensym))
             (with-cage
              (let* ((arg (mk-var argt (auto-t arg) #f 'no-gensym)) 
                     ...)
                (set! *clambda*
                      (cons (c-prototype 'void
                                         (f #t) 
                                         (list (list (arg 'type) (arg 'use))
                                               ...))
                            *clambda*))
                (set! *clambda* 
                     (cons                       
                      (f-sub f (list arg ...) (mako () (code ...)))
                      *clambda*)))))))


      
      ((_ (t : <tp>) (f : <id>)  ((a : <decl>) ... : <li*>) 
          code ... : <li4..>)
       (format #t "(define <tp> ~a ...)~%" (syntax->datum #'f))
       (with-syntax (((arg  ...) (map qa #'(a ...)))
                     ((argt ...) (map qt #'(a ...))))

         #'(begin
             (define f (mk-var `(lambda (,argt ...) ,(auto-type t))
                               (auto-t f)
                               #f 'no-gensym))             
             (with-cage
              (let* ((arg (mk-var argt (auto-t arg) #f 'no-gensym)) 
                     ...)                      
                (set! *clambda*
                      (cons (c-prototype (caddr (f 'type))
                                         (f #t) 
                                         (list (list (arg 'type) 
                                                     (arg 'use))
                                               ...))
                            *clambda*))
                (set! *clambda*
                      (cons
                       (f-define f (list arg ...) (mako () (code ...)))
                       *clambda*)))))))
      
      ((a ...) (register-error #t "malformed define" #'x)))))

;; ************************************ BEGIN *************************

(define (f-begin a)
  (lambda (v)
    (match v
      (#f 
       (match a
         (() fmt-null)
         (_  (apply my-block (map void-it a)))))

      (#t 
       (error "begin is not an expression"))

      ('expr 
       #f)

      ('type 
       (match a  
         (() 'null)
         ((a ... b) (b 'type))))
                   
      (_
       (match a  
         (()        (error "empty begin cannot be at functional position"))
         ((a ... b)  
          (apply my-block `(,@(map void-it a) ,(b v)))))))))

(define-syntax <begin> 
  (syntax-rules ()
    ((_ a ...) (f-begin (mako () (a ...))))))


;; ************************************** if *************************

(define (f-if p . l)
  (define (cmp x y)
    #|
    x       <next> -> x
    <next>  y      -> y
    x       x      -> x
    _       _      -> #f
    |#
    (if (eq? x '<next>)
        y
        (it (eq? y '<next>)
            x
            (if (eq? x y)
                x
                #f))))
  
  (match l
    ((x y)
     (lambda (v)
       (match v
         ('expr (and (p 'expr) (x 'expr) (y 'expr)))
         ('type
             (let ((t1 (x 'type))
                   (t2 (y 'type)))
               (aif (it) (cmp t1 t2)
                    it
                    (error (format #f "type-error in if,~% ~a neq ~a" t1 t2)))))
         (_
          (if (p 'expr)
              (c-if (p #t) (x v) (y v))
              (let ((pred (gensym "pred")))
                (my-block
                 (c-var 'int pred)
                 (p pred)
                 (c-if pred (x v) (y v)))))))))
          

    ((x)
     (lambda (v)
       (match v
         ('expr (and (p 'expr) (x 'expr)))
         ('type (x 'type))
         (_
          (if (p 'expr)
              (c-if (p #t) (x v))
              (let ((pred (gensym "pred")))
                (my-block
                 (c-var 'int pred)
                 (p pred)
                 (c-if pred (x v)))))))))))


(define-syntax <if>
  (lambda (x)
    (define <arg2> (mk-arg-vd #f '<if> 2))
    (define <arg3> (mk-arg-vd #t "<if> and not 2 args either" 3))
    (reg-form x)
    (syntax-parse x ()
       ((_ p x  ) #'(f-if (auto p) (auto x)))
       ((_ p x y) #'(f-if (auto p) (auto x) (auto y))))))


;; ************************************** let* ***********************
(define-syntax <let*>
  (lambda (x)
    (define <decl> (mk-let-vd #t '<let*>))
    (define <li*>   (<parse-list..>
                     #t
                     (format #f "error in <let*> varlist (varg ...)")
                     (format #f "error in <let*> varlist (varg ...)")
                     0))

    (define <li3..> (<parse-list..>
                     #t
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<let*> args c1 c2 ...")
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<let*> args c1 c2 ...")
                     3))   
    (reg-form x)    
    (syntax-parse x ()
      ((_ ((v : <decl>) ... : <li*>) code ... : <li3..>)
       #`(leta () (v ...) ff-let* f-let* (mako () (list code ...)))))))

(define-syntax <let>
  (lambda (x)
    (define <decl> (mk-let-vd #t '<let>))
    (define <li*>   (<parse-list..>
                     #t
                     (format #f "error in <let*> varlist (varg ...)")
                     (format #f "error in <let*> varlist (varg ...)")
                     0))

    (define <li3..> (<parse-list..>
                     #t
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<let> args c1 c2 ...")
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<let> args c1 c2 ...")
                     3))   
    (reg-form x)    
    (syntax-parse x ()
      ((_ ((v : <decl>) ... : <li*>) code ... : <li3..>)
       #`(leta () (v ...) ff-let f-let (mako () (list code ...)))))))

(define-syntax leta
  (lambda (x)
    (syntax-case x (*)
      ((_ (b ...) ((a) . l) g f code)
       #'(leta (b ... ('SCM          a (auto-type a) '*)) l g f code))
      ((_ (b ...) ((a v) . l) g f code)
       #'(leta (b ... ('SCM          a (auto-type a) (auto v))) l g f code))
      ((_ (b ...) ((t a *) . l) g f code)
       #'(leta (b ... ((auto-type t) a (auto-type a) '*)) l g f code))
      ((_ (b ...) ((t a v) . l) g f code)
       #'(leta (b ... ((auto-type t) a (auto-type a) (auto v))) l g f code))
      ((_ b () g f code)
       #'(g b () f code)))))


(define-syntax ff-let*
  (lambda (x)
    (syntax-case x ()
      ((_ ((t s sp v) . l) (ss ...) f code)
       #'(let ((s (mk-var t sp v)))
           (ff-let* l (ss ... s) f code)))
      ((_ () (ss ...) f code)
       #'(lambda (v)
           ((f (list ss ...) code) v))))))

(define-syntax ff-let
  (lambda (x)
    (syntax-case x ()
      ((_ ((t s sp v) ...) () f code)
       #'(let ((s (mk-var t sp v)) ...)
           (lambda (w)
             ((f (list s ...) code) w)))))))

(define (f-let vars code)
  (f-begin 
   (append
    (map (lambda (s) (s 'def))  vars)
    (map (lambda (s) (s 'init)) vars)
    code)))

(define (f-let* vars code)
  (match vars
    ((x . l)
     (f-begin (list (x 'def)
                    (x 'init)
                    (f-let* l code))))

    (() (f-begin code))))


;; ************************************** call  *******************
(define (reduce f i arg)
  (match arg
    ((x . l) (f x (reduce f i l)))
    (()      i)))

(define (f-call0 f ts tf arg)
  (if (not ts) (error (format #f "function ~a is not declared" f)))
  (lambda (v)
    (match v
      ('expr (reduce (lambda (x y) (and x y))
                     #t 
                     (map (lambda (f) (f 'expr)) 
                          arg)))
      ('type tf)
      (#t `(,f  ,@(map (lambda (f) (f #t)) arg)))
      (#f 
       (if (reduce (lambda (x y) (and x y))
                   #t
                   (map (lambda (f) (f 'expr)) 
                        arg))
           `(,f ,@(map (lambda (f) (f #t)) arg))
           (let* ((vl   (map (lambda (x)   (gensym "a")) ts))
                  (defs (map (lambda (s t) (c-var t s))  vl ts))
                  (sets (map (lambda (s a) (a s))        vl arg)))
             (if v
                 (apply my-block `(,@defs ,@sets ,`(,f ,@vl)))
                 (apply my-block `(,@defs ,@sets ,`(,f ,@vl)))))))
      (_
       (if (reduce (lambda (x y) (and x y))
                   #t
                   (map (lambda (f) (f 'expr)) 
                        arg))
           (c= v `(,f ,@(map (lambda (f) (f #t)) arg)))
           (let* ((vl   (map (lambda (x)   (gensym "a")) ts))
                  (defs (map (lambda (s t) (c-var t s))  vl ts))
                  (sets (map (lambda (s a) (a s))        vl arg)))
             (if v
                 (apply my-block `(,@defs ,@sets ,(c= v `(,f ,@vl))))
                 (apply my-block `(,@defs ,@sets ,`(,f ,@vl))))))))))

(define (f-call f a)  (f-call0 (f #t)
                               (cadr  (f 'type))
                               (caddr (f 'type))
                               a))

(define (s-call f a)  (f-call0 f 
                               (map (lambda x 'SCM) a)
                               'SCM
                               a))

(define (type-it x t)
  (let ((T (x 'type)))
    ;(pk `(type-it ,T))
    (match T
      (('%array t n) `(,t *))
      ((? procedure?) t)
      (T T))))

(define (f-icall f arg)
  (lambda (v)
    (let* ((exp #f)
           (g (lambda () 
                (if exp
                    (if (eq? exp 'true) #t #f)
                    (if (fold (lambda (x y) (and x y))
                              #t (map (lambda (x) (x 'expr)) arg))
                        (begin (set! exp 'true)  #t)
                        (begin (set! exp 'false) #f)))))
           (h (lambda (v)
                (let ((s (map (lambda v (gensym "a")) arg)))
                  ((f-begin
                    (append
                     (map (lambda (x s)
                            (lambda v 
                              (c-var (type-it x 'error) s)))
                          arg s)
                     (map (lambda (x s)
                            (lambda v (x s)))
                          arg s)
                     (list (lambda (v)
                             (if v 
                                 (c= v `(,(f #t) ,@s))
                                 `(,(f #t) ,@s))))))
                   v)))))
    (match v
      ('expr (g))                 
      (#f (if (g)
              `(,(f #t) ,@(map (lambda (f) (f #t)) arg))
              (h #f)))
                                        
      (#t `(,(f #t) ,@(map (lambda (f) (f #t)) arg)))

      (v  (if (g)
              (c= v `(,(f #t) ,@(map (lambda (f) (f #t)) arg)))
              (h v)))))))


(define-syntax <call>
  (lambda (x)
    (define <li2..> (<parse-list..> #t 
                                  "malformed (<call> f a1 ...)"
                                  "malformed (<call> f a1 ...)"
                                  2))
    (reg-form x)
    (syntax-parse x ()
      ((_ f a ... : <li2..>)
       #'(f-call (auto f) (list (auto a) ...))))))

(define-syntax <scm-call>
  (lambda (x)
    (define <li2..> (<parse-list..> #t 
                                  "malformed (<scm-call> f a1 ...)"
                                  "malformed (<scm-call> f a1 ...)"
                                  2))
    (reg-form x)
    (syntax-parse x ()
      ((_ f a ... : <li2..>)
       #'(s-call 'f (list (auto a) ...))))))


(define-syntax <icall>
  (lambda (x)
    (define <li2..> (<parse-list..> #t 
                                  "malformed (<icall> f a1 ...)"
                                  "malformed (<icall> f a1 ...)"
                                  2))
    (syntax-parse x ()
      ((_ f a ... : <li2..>)
       #'(f-icall (<lit> f) (list (auto a) ...))))))

(define-syntax <acall>
  (lambda (x)
    (define <li2..> (<parse-list..> #t 
                                  "malformed (<icall> f a1 ...)"
                                  "malformed (<icall> f a1 ...)"
                                  2))
    (syntax-parse x ()
      ((_ f a ... : <li2..>)
       #'(f-icall (auto f) (list (auto a) ...))))))

;; ************************************** recur *******************
;  TAIL CALL VERSION ONLY


(define-syntax <recur>
  (lambda (x)
    (define <decl> (mk-let-vd #t '<recur>))
    (define <id>   (mk-identifier-vd #t '<recur>))
    (define <li*>   (<parse-list..>
                     #t
                     (format #f "error in <recur> varlist (varg ...)")
                     (format #f "error in <recur> varlist (varg ...)")
                     0))

    (define <li4..> (<parse-list..>
                     #t
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<recur> label args c1 c2 ...")
                     (format #f 
                             "error in <let*> not of the form ~%  ~a"
                             "(<recur> label args c1 c2 ...")
                     4))   
    (reg-form x)
    (syntax-parse x ()
      ((_ (sym : <id>) ((a : <decl>) ... : <li*>) code ... : <li4..>)
       #'(leta () (a ...) ff-let* f-recur* 
               (sym (list (mamma code) ...)))))))


(define-syntax f-recur*
  (lambda (x)
    (syntax-case x ()
      ((_ ss (sym code))
       #'(let ((sym (mk-var 'void (auto-t sym) ss)))
           (f-recur ss (list sym code)))))))

(define (f-recur vars sym+code)
  (define (f-rec vars sym code)
    (match vars
      ((x . l)
       (f-begin (list (x 'def) 
                      (x 'init) 
                      (f-rec l sym code))))
      (() 
       (f-begin `(,(lambda x (c-label (sym #t))) ,@code)))))

  (match sym+code
    ((sym code)
     (f-rec vars sym code))))

;; ********************************** <next> *********************
(define-syntax <next>
  (lambda (x)
    (define <id> (mk-identifier-vd #t '<next>))
    (define <li2..> (<parse-list..> #t 
                                  "malformed (<next> f a1 ...)"
                                  "malformed (<next> f a1 ...)"
                                  2))
    (reg-form x)

    (syntax-parse x ()
      ((_ (sym : <id>) a ... : <li2..>)
       #'(f-next sym (auto a) ...)))))
                     
(define (f-next sym . as)
  (lambda (v)
    (match v
      ('expr #f)
      ('type '<next>)
      (_
       (let* ((ss (sym 'val))
              (ws (map (lambda x (gensym "next")) ss)))
         ((f-begin (append
                    (map (lambda (w s) (lambda x (c-var (s 'type) w))) ws ss)
                    (map (lambda (w a) (lambda x (a w)              )) ws as)
                    (map (lambda (w s) (lambda x (c= (s #t) w)))       ws ss)
                    (list (lambda x (c-goto (sym #t)))))) #f))))))

    
;; ************************************** = *******************

(define (=-it v s)
  (lambda (w)
    (match w
      (#f  (v (s #t)))
      (#t  (v (s #t)))
      ('expr #f)
      (_   (error "<=> does not return a value")))))

(define-syntax <=>  
  (lambda (x)
    (define <arg2> (mk-arg-vd        #t '<=> 2))
    (reg-form x)
    (syntax-parse x ()
      ((_ s v : <arg2>)
       #'(=-it (auto v) (auto s))))))

;; ************************************** binop *******************


(mk-op-2 <!=>       c!=  )
(mk-op-2 <==>       c==  )
(mk-op-2 <+>        c+   )
(mk-op-2 f2-        c-   )
(mk-op-2 f2*        c*   )
(mk-op-2 </>        c/   )
(mk-op-2 <and>      c&&  )
(mk-op-2 <or>       c-or )
(mk-op-2 <bit-and>  c&   )
(mk-op-2 <bit-or>   c-bit-or)
(mk-op-2 <bit-xor>  c^   )
(mk-op-2 q<         c<   )
(mk-op-2 q>         c>   )
(mk-op-2 q<=        c<=  )
(mk-op-2 q>=        c>=  )


(mk-op-1 f1-        c-   )
(mk-op-1 <not>      c!   )

#|
 Some operators have a more complex type deduction need, 
 let's just not support any functional version of
 these and just treet them as expressions.
|#

(mk-exp-op-1 <addr> c&)
(mk-exp-op-1 f1*    c*)



(define-syntax <->
  (lambda (x)
    (define <arg2>  (mk-arg-vd  #f '<-> 2))
    (define <arg3>  (mk-arg-vd  #f '<-> 3))
    (define <type>  (mk-tag-vd  #f '<-> 'type))
    (define <tp>    (mk-type-vd #t '<->))
    (reg-form x)
    (syntax-parse x ()
      ((_ ((type : <type>) (t : <tp>)) x )           
       #'(f1- t x))

      ((_ ((type : <type>) (t : <tp>)) x y : <arg3>) 
       #'(f2- t x y))

      ((_ x) 
       #'(f1-   x))
      ((_ x y : <arg2>) 
       #'(f2-   x y)))))

(define-syntax <*>
  (lambda (x)    
    (define <arg2>  (mk-arg-vd  #f '<*> 2))
    (define <arg3>  (mk-arg-vd  #f '<*> 3))
    (define <type>  (mk-tag-vd  #f '<*> 'type))
    (define <tp>    (mk-type-vd #t '<*>))
    (reg-form x)
    (syntax-parse x ()
      ((_ ((type : <type>) (t : <tp>)) x )           
       #'(f1* t x))
      ((_ ((type : <type>) (t : <tp>)) x y : <arg3>) 
       #'(f2* t x y))
      ((_ x)   
       #'(f1*   x))
      ((_ x y : <arg2>) 
       #'(f2*   x y)))))


(define (xx-it op x)
  (lambda (v)
    (match v
      ('expr #f)
      (#f (op (x #t)))
      (#t (op (x #t)))
      (_  (error " <++> <--> cannot be used as values")))))

(define-syntax <-->
  (lambda (x)
    (define <arg1>  (mk-arg-vd  #f '<--> 1))
    (reg-form x)
    (syntax-parse x ()
      ((_ x : <arg1>)
       #'(xx-it c-- (auto x))))))

(define-syntax <++>
  (lambda (x)
    (define <arg1>  (mk-arg-vd  #f '<++> 1))
    (reg-form x)
    (syntax-parse x ()
      ((_ x : <arg1>)
       #'(xx-it c++ (auto x))))))

(define-syntax ->
  (lambda (x)
    (define <arg2*> (mk-arg*-vd #t '-> 2))
    (reg-form x)
    (syntax-parse x ()
      ((_ x y ... : <arg2*>)
       #'(f-> (auto x) (auto-t y) ...)))))

(define-syntax -.>
  (lambda (x)
    (define <arg3*> (mk-arg*-vd #t '-> 3))
    (reg-form x)
    (syntax-parse x ()
      ((_ x y z ... : <arg3*>)
       #'(<.> (-> x (auto-t y)) (auto-t z) ...)))))


(define-syntax =>
  (lambda (x)
    (define (<check=> y)
      (define f
        (lambda (y)
          (syntax-case y (- ->)
            ((- x . l)
             (f #'l))
            ((-> x . l)
             (f #'l))
            (() (list #t))
            ((a . l)
             (register-error #t "error in the form ~a" x x)))))
      (define <arg3*> (mk-arg*-vd #t '=> 3))
      (syntax-parse y ()
        ((_ a : <arg3*> . l)
         (f #'l))))

    (reg-form x)

    (syntax-parse x ()
      ((_ a v ... : <check=>) #'(=>0 (auto a) ((auto-t v) ...))))))

(define-syntax =>0
  (syntax-rules (- ->)
    ((_ ret (- y . l))
     (=>0 (<.> ret y) l))
    ((_ ret (-> y . l))
     (=>0 (-> ret y) l))
    ((_ ret ()) ret)))

(define (f-> a . l)
  (lambda (v)
    (match v
      ('expr #t)
      (#f   fmt-null)
      (#t   (apply c-> (cons (a #t) l)))
      (_    (c= v (apply c-> (cons (a #t) l)))))))


(define-syntax <.>
  (lambda (x)
    (define <arg2*> (mk-arg*-vd #t '<.> 2))
    (reg-form x)
    (syntax-parse x ()
      ((_ a x ... : <arg2*>)
       #'(f. (auto a) (auto-t x) ...)))))

(define (f. a . l)
  (lambda (v)
    (match v
      ('expr #t)
      (#f   fmt-null)
      (#t   (apply c. (cons (a #t) l)))
      (_    (c= v (apply c. (cons (a #t) l)))))))


(define-syntax <cond>
  (lambda (x)
    (define <li1..> (mk-arg*-vd #t '<case> 1))
    (define <stm> (<parse-list..>
                   #t
                   (format 
                    #f
                    "the matcher in <case> need to be of the form ~%  ~a"
                    "(match code1 code2 ...)")
                   (format 
                    #f
                    "the matcher in <case> need to be of the form ~%  ~a"
                    "(match code1 code2 ...)")
                   2))
    (reg-form x)

    (syntax-parse x ()
      ((_ x (a ... : <stm>) ... : <li1..>)
       #'(<ccond> (a ...) ...)))))
      
(define-syntax <ccond>
  (syntax-rules (:t)
    ((_ (:t a ...) . l)
     (<begin> a ...))
    ((_ (p code ...))
     (<if> p (<begin> code ...)))
    ((_ (p code ...) . l)
     (<if> p (<begin> code ...) 
           (<ccond> . l)))))

(define-syntax <case0>
  (syntax-rules (:t)
    ((_ x (:t a ...) . l) 
     (<begin> a ...))
    ((_ x (p code ...))
     (<if> (<==> x p) 
           (<begin> code ...) ))
    ((_ x (p code ...) . l)
     (<if> (<==> x p)
           (<begin> code ...) 
           (<case0> x . l)))))

;; TODO make this macro not leak, e.g. allow an expression in the
;; equality context. also consider modelling it using switch statement 
;; or even implement such an element.
(define-syntax <case>
  (lambda (x)
    (define <li2..> (mk-arg*-vd #t '<case> 2))
    (define <stm> (<parse-list..>
                   #t
                   (format 
                    #f
                    "the matcher in <case> need to be of the form ~%  ~a"
                    "(match code1 code2 ...)")
                   (format 
                    #f
                    "the matcher in <case> need to be of the form ~%  ~a"
                    "(match code1 code2 ...)")
                   2))
    (reg-form x)
    (syntax-parse x ()
      ((_ x (a ... : <stm>) ... : <li2..>)
       #'(let ((s (gensym "case")))
           (lambda (v)
             (match v
               ('expr #f)
               (#t (error "case statement cannot be in a expression"))
               (#f
                (my-block
                 (c-var 'int s)
                 ((auto x) s)
                 ((<case0> s (a ...) ...) #f)))
               (_
                (my-block
                 (c-var 'int s)
                 ((auto x) s)
                 ((<case0> s (a ...) ...) v))))))))))

