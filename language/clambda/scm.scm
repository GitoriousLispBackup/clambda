(define-module (language clambda scm)
  #:use-module (language clambda      clambda    )
  #:use-module (language clambda      validators )
  #:use-module (language clambda      fmt        )
  #:use-module (ice-9    match-phd               )
  #:use-module (language clambda parse syntax-parse)
  #:export 
  (auto-inits auto-defs init-clambda-scm <scm> <cons> <car> <cdr> <pair?> 
              <append> <set-car> <set-cdr> <match> <scm-ext> <reverse>
              <<+>> <<->> <<*>> <</>> <<if>> s< s> s<= s>= scmbd
              <number?> <integer?> <fixnum->int> <number->double>
              <double->number> ! <lambda> <scm-alloc> <format>
              <tcall> <tr-call> <<define>> <int->fixnum> <s-lambda>
              <f-lambda>))

(define (pp x)
  (format #t "~10a~%" (syntax->datum x))
  x)


#|

Basic support to ease SCM variable manipulation
|#


#|
****************************** literal list constructions ******************
Now this works  
(<scm> '(a b c))

And this works straight out of the box.
(<let*> ((w (<scm> '(b a))))
  (<scm> `(a ,b ,@w)))
****************************************************************************
This desperately need a way to construc literal symbols at startup e.g.
we do not want to execute the symbol generating code for every function 
invocation e.g. we need to register symbol generating and at compilation
issue code that generates symbols and float constants otherwize the code will
be very slow.
|#

(define (mk-generator GENSYM)
  (let ((*symbols* '()))
    (lambda x
      (match x
        (('get s)
         (let loop ((x *symbols*))
           (match x
             (((,s . z) . _) z)
             (( _       . l) (loop l))
             (() 
              (let ((G (GENSYM s)))
                (set! *symbols* (cons (cons s G) *symbols*))
                G)))))

        (('reset)
         (set! *symbols* '()))
        
        (('map F)
         (map (lambda (x) (F (car x) (cdr x))) *symbols*))
        
        (('get-defs)
         (map (lambda (x) (c-var 'SCM (cdr x))) *symbols*))
        
        (('get-map)
         *symbols*)))))

(define mk-symbol (mk-generator (lambda (s) (gensym (symbol->string s)))))
(define mk-num    (mk-generator (lambda (f) (gensym "scm_num"))))
(define mk-char   (mk-generator (lambda (f) (gensym "scm_char"))))
(define mk-string (mk-generator (lambda (f) (gensym "scm_string"))))
(define mk-scm-fkn
  (let ((data '()))
    (lambda x
      (match x
        (('new c-name scm-name narg str)
         (set! data (cons (list c-name scm-name narg str)
                          data)))
        (('reset) (set! data '()))
        (('init)
         (map (lambda (x)
                (match x
                  ((c-name scm-name narg str)
                   (lambda x
                     `(scm_c_define_gsubr ,(symbol->string scm-name)
                                          ,narg
                                          0
                                          0
                                          ,c-name)))))
              data))))))

(define-syntax <scm-ext>
  (lambda (x)
    (syntax-case x (<define>)
      ((_ (<define> fnm (arg ...) code ...))
       (with-syntax ((n (datum->syntax 
                         #'fnm
                         (length
                          (syntax->datum #'(arg ...))))))
         #'(begin
             (<define> fnm (arg ...) code ...)
             (mk-scm-fkn 'new (auto-t fnm) 'fnm n "")))))))
                       

(define-syntax init-clambda-scm
  (lambda (x)
    (syntax-case x ()
      ((_)
       (begin
         (mk-symbol  'reset)
         (mk-num     'reset)
         (mk-char    'reset)
         (mk-string  'reset)
         (mk-scm-fkn 'reset)
         #'(init-clambda))))))

;; Generates initiation code for symbol literal to be used in c-functions
;; e.g. it will be pre-coded and calculated in an initi function

(define (symbol-stub Data Sym)
  (lambda x
    (c= Sym `(scm_from_locale_symbol                    
              ,(symbol->string Data)))))

(define (num-stub Data Sym)
  (let* ((Str (number->string Data))
         (N   (string-length Str)))
    (lambda x
      (c= Sym
          `(scm_c_locale_stringn_to_number 
            ,Str        ; String
            ,N          ; String Length
            10)))))     ; Radix

(define (char-stub Data Sym)
  (lambda x
    (c= Sym `(scm_integer_to_char
               (SCM_I_MAKINUM
                ,(char->integer Data))))))

(define (string-stub Data Sym)
  (lambda x
    (c= Sym `(scm_from_locale_string ,Data))))

(define (auto-defs)
  (set! *clambda*
        (cons
         (append '(+dive+)
                 (mk-symbol 'get-defs)
                 (mk-num    'get-defs)
                 (mk-char   'get-defs)
                 (mk-string 'get-defs))

         *clambda*)))

(define (auto-inits)
  (let ((R (append (mk-symbol  'map symbol-stub)
                   (mk-num     'map num-stub)
                   (mk-char    'map char-stub)
                   (mk-string  'map string-stub)
                   (mk-scm-fkn 'init)
                   (list (<lit> 'SCM_BOOL_T)))))
    (f-begin R)))
      

;; ************************ arithmetic operations ****************
(define-syntax <<+>>
  (lambda (x)
    (define <arg2> (mk-arg-vd #t '<<+>> 2))
    (syntax-parse x ()
      ((_ x y : <arg2>) 
       #'(<scm-call> ASM_ADD x y)))))

(define-syntax <<*>>
  (lambda (x)
    (define <arg2> (mk-arg-vd #t '<<*>> 2))
    (syntax-parse x ()
      ((_ x y : <arg2>) 
       #'(<scm-call> scm_product x y)))))

(define-syntax <</>>
  (lambda (x)
    (define <arg2> (mk-arg-vd #t '<</>> 2))
    (syntax-parse x ()
      ((_ x y : <arg2>) 
       #'(<scm-call> scm_divide x y)))))

(define-syntax <<->>
  (lambda (x)
    (define <arg1> (mk-arg-vd #f '<<->> 1))
    (define <arg2> (mk-arg-vd #t '<<->> 2))
    (syntax-parse x ()
      ((_ x   : <arg1>)
       #'(<scm-call> ASM_SUB (<scm> 0) x))
      ((_ x y : <arg2>) 
       #'(<scm-call> ASM_SUB x y)))))


(define-syntax if-wrap
  (syntax-rules (<<and>> <<or>> <<not>>)
    ((_ (<<and>> p ...)) (<and> (if-wrap p) ...))
    ((_ (<<or>>  p ...)) (<or>  (if-wrap p) ...))
    ((_ (<<not>> p))     (<not> (if-wrap p)))
    ((_ p) (<not> (<==> (<scm> #f) p)))))

(define-syntax <<if>>
  (syntax-rules ()
    ((_ p x y) (<if> (if-wrap p) x y))
    ((_ p x  ) (<if> (if-wrap p) x  ))))


(define-syntax s<
  (lambda (x)
    (define <arg> (mk-arg-vd #t 's< 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> scm_less_p x y)))))
(define-syntax s>
  (lambda (x)
    (define <arg> (mk-arg-vd #t 's> 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> scm_gr_p x y)))))
(define-syntax s<=
  (lambda (x)
    (define <arg> (mk-arg-vd #t 's<= 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> scm_leq_p x y)))))
(define-syntax s>=
  (lambda (x)
    (define <arg> (mk-arg-vd #t 's>= 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> scm_geq_p x y)))))
;; ******************************** List operations **********************
(define-syntax <cons>
  (lambda (x)
    (define <arg2> (mk-arg-vd #t '<cons> 2))
    (syntax-parse x ()
      ((_ x y : <arg2>) 
       #'(<scm-call> scm_cons x y)))))

(define-syntax <car>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<car> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> SCM_CAR x)))))

(define-syntax <cdr>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<cdr> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> SCM_CDR x)))))

(define-syntax <pair?>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<pair?> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> scm_pair_p x)))))

(define-syntax <CONSP>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<CONSP> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<icall> 'SCM_CONSP x)))))

(define-syntax <set-car>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<set-car> 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> SCM_SETCAR x y)))))

(define-syntax <set-cdr>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<set-cdr> 2))
    (syntax-parse x ()
      ((_ x y : <arg>) 
       #'(<scm-call> SCM_SETCDR x y)))))

(define-syntax <format>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<format> 2))
    (syntax-parse x ()
      ((_ p x l ...) 
       #'(<scm-call> scm_simple_format (<scm> p) (<scm> x) 
                     (<scm> `(,l ...)))))))


(define-syntax <integer?>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<integer?> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> scm_integer_p x)))))

(define-syntax <number?>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<number?> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> scm_number_p x)))))

(define-syntax <fixnum->int>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<fixnum->int> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<icall> 'scm_to_int x)))))

(define-syntax <int->fixnum>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<int->fixnum> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<icall> 'scm_from_int x)))))

(define-syntax <number->double>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<number->double> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<icall> 'scm_to_double 
                  x)))))

(define-syntax <double->number>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<double->number> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<icall> 'scm_from_double x)))))

(define-syntax <scm-alloc>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<scm-alloc> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<cast> (SCM *)
                 (<icall>
                  'SCM2PTR
                  (<icall> 'scm_words 
                           (<lit> 'scm_tc7_program) (<+> x (<c> 1)))))))))


(define-syntax <set-cell>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<set-cell> 3))
    (syntax-parse x ()
      ((_ o n v : <arg>) 
       #'(<icall> 'SCM_SET_CELL_OBJECT 
                  o n v)))))

(define-syntax <get-cell>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<get-cell> 2))
    (syntax-parse x ()
      ((_ o n v : <arg>) 
       #'(<icall> 'SCM_CELL_OBJECT 
                  o n)))))

(define-syntax <append>
  (lambda (x)
    (syntax-case x ()
      ((_) 
       #'(<lit> 'SCM_EOL))

      ((_ a) 
       #'a)

      ((_ a b)
       #'(<scm-call> scm_append (<scm-call> scm_list_2 a b)))

      ((_ a b c)
       #'(<scm-call> scm_append (<scm-call> scm_list_3 a b c)))

      ((_ a b c d)
       #'(<scm-call> scm_append (<scm-call> scm_list_4 a b c d)))
      
      ((_ a b c d e)
       #'(<scm-call> scm_append (<scm-call> scm_list_5 a b c d e)))

      ((_ . l)
       (with-syntax ((n (datum->syntax #'x (length (syntax->datum #'l)))))
         #'(<scm-call> scm_append (<scm-call> scm_list_n (<scm> n) . l)))))))

(define-syntax <reverse>
  (lambda (x)
    (define <arg> (mk-arg-vd #t '<reverse> 1))
    (syntax-parse x ()
      ((_ x : <arg>) 
       #'(<scm-call> scm_reverse x)))))

(define-syntax <scm>
  (lambda (x)
    (define (a x)
      (match (syntax->datum x)
        ((? symbol? s) 
         (with-syntax ((s (datum->syntax x (mk-symbol 'get s))))
           #'(<lit> 's)))

        ((? number? n)
         (with-syntax ((s (datum->syntax x (mk-num 'get n))))
           #'(<lit> 's)))

        ((? char?   ch)
         (with-syntax ((s (datum->syntax x (mk-char 'get ch))))
           #'(<lit> 's)))

        ((? string? str)
         (with-syntax ((s (datum->syntax x (mk-string 'get str))))
           #'(<lit> 's)))
              
        (#f       #'(<lit> 'SCM_BOOL_F))       
        (#t       #'(<lit> 'SCM_BOOL_T))
        (()       #'(<lit> 'SCM_EOL))))

    (define (aa x)
      (match (syntax->datum x)
        ((? number? n)
         (with-syntax ((s (datum->syntax x (mk-num 'get n))))
           #'(<lit> 's)))

        ((? char?   ch)
         (with-syntax ((s (datum->syntax x (mk-char 'get ch))))
           #'(<lit> 's)))

        ((? string? str)
         (with-syntax ((s (datum->syntax x (mk-string 'get str))))
           #'(<lit> 's)))
              
        (#f       #'(<lit> 'SCM_BOOL_F))       
        (#t       #'(<lit> 'SCM_BOOL_T))
        (()       #'(<lit> 'SCM_EOL))
        (_ x)))
       

    (define (q x)
      (syntax-case x ()
        ((x . l)
         (with-syntax ((xx (q #'x))
                       (ll (q #'l)))
           #'(<cons> xx ll)))
        
        (x  (a #'x))))

    (define (qq x)
      (syntax-case x (unquote unquote-splicing)
        ((unquote x)
         #'(<scm> x))

        ((((unquote-splicing x) . l))
         (with-syntax ((ll (qq #'l)))
           #'(<append> (<scm> p) ll)))
        
        ((x . l)
         (with-syntax ((xx (qq #'x))
                       (ll (qq #'l)))
           #'(<cons> xx ll)))
        
        (x  (a #'x))))
    

    (syntax-case x (quote quasiquote)
      ((_ (quote      x)) (q  #'x))
      ((_ (quasiquote x)) (qq #'x))
      ((_ x)              (aa #'x)))))


; ------------------------------------------------------------------------
; ------------------------------- C - MATCH ------------------------------
; ------------------------------------------------------------------------

(define-syntax <match>
  (lambda (x)
    (define <ali0..> (mk-list*-vd #t "args must be a list" 0))
    (define <pat1..> (mk-list*-vd #t "pattern part cannot be empty" 1))
    (define <qli2..> 
      (mk-list*-vd #t "not of the form (<match> (x ...) row row2 ...)" 2))
    
    (syntax-parse x ()
      ((_ (v ... : <ali0..>) (pat ... cc : <pat1..>) ... : <qli2..>)
       (let* ((n (length (syntax->datum #'(v ...)))))
         (map (lambda (x) (if (not (eq? (length x) n))
                              (error "wrong number of patterns")
                              #t))
              (syntax->datum #'((pat ...) ...)))
         #'(velo () (v ...) (pat ... cc) ...))))))
  

(define-syntax velo
  (lambda (x)
    (syntax-case x ()
      ((_ (b ...) (a1 a ...) . l)
       (with-syntax ((w (datum->syntax x (gensym "w"))))
         #'(velo (b ... (a1 w)) (a ...) . l)))
      ((_ (b ...) () . l)
       (with-syntax ((out (datum->syntax x (gensym "out"))))
         #'(velo2 * () l (b ...) out ))))))


(define-syntax velo2
  (lambda (x)
    (syntax-case x ()
      ((_ onext (b ...) ((p ...) a ...) . l)
       (with-syntax ((next (datum->syntax x (gensym "next"))))
         #'(velo2 next (b ... (onext next p ...)) (a ...) . l)))
      ((_ _ (b ...) () q out)
       #'(match0 q out b ...)))))

(define-syntax match0
  (lambda (x)
    (define (calc-pat-length x n)
      (syntax-case x (and unquote)
        ((and p)
         (calc-pat-length #'p n))

        ((and p . ps)
         (max (calc-pat-length #'p (+ n 1))
              (calc-pat-length #'(and . ps) n)))

        ((unquote x)
         n)

        ((x . l)
         (max (calc-pat-length #'x (+ n 1))
              (calc-pat-length #'x n)))

        (_ n)))

    (define (pat-length0 x)
      (syntax-case x ()
        ((pat . l)
         (max (calc-pat-length #'pat 1)
              (pat-length0 #'l)))
        (() 
         0)))

    (define (pat-length x)
      (syntax-case x ()
        ((pat . l)
         (max (pat-length0 #'pat)
              (pat-length #'l)))
        (() 
         0)))

    (syntax-case x ()
      ((_ ((z w) ...) out (onext next pat ... code) ... 
          (e-onext e-next e-pat ... e-code))
       (with-syntax ((n (datum->syntax #'out (pat-length 
                                               #'((pat ...) ... (e-pat ...))))))
         #'(lambda v
             (match v
               ((#t) (error "<match> does not work in expression context"))
               (('expr) #f)
               (_ 
                ((<let*> (((<array> SCM n) work *)
                          (SCM w (<scm> z))
                          ...)                        
                         (<while-1>
                          (<begin>
                           (<label> onext)
                           (match-work (w ...) (pat ...) 
                                       work (<duo> v code (<break>)) next))
                          ...
                          (<begin>
                           (<label> e-onext)
                           (match-work (w ...) (e-pat ...)
                                       work (<duo> v e-code (<break>)) *))))
                 #f)))))))))

(define-syntax <duo>
  (syntax-rules ()
    ((_ v x y)
     (duo v (auto x) (auto y)))))

(define (duo v x y)
  (lambda q
    (match v
      ((#t)     (error "duo cannot be in ane expression"))
      ((#f)     (my-block (x #f) (y #f)))
      (('expr)  #f)
      ((v)      (my-block (x v)  (y #f))))))


(define-syntax match-work
  (lambda (x)
    (syntax-case x ()
      ((_ (w1 w ...) (pat1 pat ...) work cc next)
       #'(<begin>
          (<=> (<ref> work (<c> 0)) w1)
          (match-work0 0 pat1 work 
                       (match-work (w ...) (pat ...) work cc next)
                       next)))

      ((_ () () work cc next)
       #'cc))))

(define-syntax scmbd
  (lambda (x)
    (syntax-case x () 
      ((_ x)
       (if (symbol? (syntax->datum #'x))
           #'(begin
               (catch #t    
                 (lambda q (if (symbol? x) #t))
                 (lambda q 
                   (error 
                    (format 
                     #f
                     "unbound variable found in <match> pattern did you mean ,~a or '~a?"
                     'x 'x))))
               (<scm> x))
           #'(<scm> x))))))

      
(define-syntax match-work0
  (lambda (x)   
    (syntax-case x (and unquote)

      ((_ i (and p) work cc next)
       #'(match-work0 i p work cc next))

      ((_ i (and p . ps) work cc next)
       (with-syntax ((ii (datum->syntax #'i (+ 1 (syntax->datum #'i)))))
         #'(<begin>
            (<=> (<ref> work (<c> ii)) (<ref> work (<c> i)))
            (match-work0 ii p work 
                         (match-work0 i (and . ps) work cc next)
                         next))))

      ((_ i (unquote z) work cc next)
       #'(<let*> ((z (<ref> work (<c> i))))
                 cc))

      ((_ i (x . y) work cc next)
       (with-syntax ((ii (datum->syntax #'i (+ 1 (syntax->datum #'i)))))
         #'(<if> (<CONSP> (<ref> work (<c> i)))
                 (<begin>
                  (<=> (<ref> work (<c> ii)) (<car> (<ref> work (<c> i))))
                  (<=> (<ref> work (<c> i))  (<cdr> (<ref> work (<c> i))))
                  (match-work0 ii x work 
                               (match-work0 i y work cc next) 
                               next))
                 (<goto> next))))
      
      ((_ i x work cc next)
       (if (eq? (syntax->datum #'x) '_)
           #'cc
           #'(<if> (<==> (scmbd x) (<ref> work (<c> i)))
                   cc
                   (<goto> next)))))))


;; ---------------------------- support for tail calls ---------------------
;; 

(define-syntax <tcall>
  (lambda (x)
    (syntax-case x ()
      ((_ f a ...)
       #'(tcall-pre 1 () () ((auto a) ...) (auto f) tcall)))))


(define-syntax tcall-pre
  (lambda (x)
    (syntax-case x ()
      ((_ i (n ...) (b ...) (a a2 ...) f mac)
       (with-syntax ((ii (datum->syntax #'i (+ 1 (syntax->datum #'i)))))
         #'(tcall-pre ii (n ... i) (b ... a) (a2 ...) f mac)))

      ((_ n (i ...) (a ...) () f mac)
       #'(mac f n (i ...) (a ...))))))

(define-syntax <nop>
  (syntax-rules ()
    ((_)
     (lambda v fmt-null))))

(define-syntax <return>
  (syntax-rules ()
    ((_ x)
     (lambda v
       (c-return (x #t))))))

;;...................................................
;;.................... TAIL CALLS ...................
;;...................................................
(define (tcall-it code)
  (lambda (v)
    (match v
      (#f    (error "<tcall> can only be at tail position"))
      (#t    (error "<tcall> can only be at tail position"))
      ('expr #f)
      (v     (code v)))))

(define -frame (mk-var '(SCM *) '__frame #f 'no-gensym)) 
(define -stack (mk-var '(SCM *) '__stack #f 'no-gensym)) 

(define-syntax tcall
  (lambda (x)
    (syntax-case x ()
      ((_ f n (i ...) (a ...))
       (with-syntax ((assert-stack 
                      (if (> (syntax->datum #'n) 10)
                          #'(<icall> 'assert-stack -stack (<c> n))
                          #'(<nop>))))

       #'(tcall-it 
          (<begin>
           assert-stack
           (<=> (<ref> -frame (<c> 0)) (<scm> n))
           (<=> (<ref> -frame (<c> i)) a) ... 
           (<return> (<cast> (void *) f)))))))))
                   


(define-syntax trampoline
  (lambda (x)
    (syntax-case x ()
      ((_ f -frame -stack)
       (with-syntax ((loop (datum->syntax #'f (gensym "loop"))))
         #'(<begin>
            (<recur> loop ((tail-fkn w (<cast> tail-fkn
                                               (<acall> f -frame -stack))))
              (<if> w
                    (<begin>
                     (<=> -stack (<+> -frame 
                                      (<fixnum->int>
                                       (<ref> -frame (<c> 0)))))
                     (<next> loop (<cast> tail-fkn
                                          (<acall> w -frame -stack))))
                    (<begin>
                     (<icall> 'free__frame -frame)
                     (<ref> -frame (<c> 0)))))))))))



(define-syntax <tr-call>
  (lambda (x)
    ;(pk (syntax->datum x))
    (syntax-case x ()
      ((_ (st) f a ...)
       #'(tcall-pre 1 () () ((auto a) ...) ((auto f) st)  tr-call2))
                   
      ((_ f a ...)
       #'(tcall-pre 1 () () ((auto a) ...) (auto f) tr-call)))))



(define-syntax tr-call
  (lambda (x)
    (syntax-case x ()
      ((_ f n (i ...) (a ...))
       (with-syntax ((assert-stack 
                      (if (> (syntax->datum #'n) 10)
                          #'(<=> -stack
                                 (<icall> 'assert__stack 
                                          -stack (<c> n)))
                          #'(<=> -stack
                                 (<icall> 'assert__stack 
                                          -stack (<c> 10))))))

       #'(<begin>
          assert-stack
          (<=> (<ref> -stack (<c> 0)) (<scm> n))
          (<=> (<ref> -stack (<c> i)) a)
          ...
          (<let*> (((SCM *) ss (<+> -stack (<c> n))))
            (trampoline f -stack ss))))))))

(define-syntax tr-call2
  (lambda (x)
    (syntax-case x ()
      ((_ (f st) n (i ...) (a ...))
       (with-syntax ((assert-stack 
                      (if (> (syntax->datum #'n) 10)
                          #'(<=> st
                                 (<icall> 'assert__stack 
                                          st (<c> n)))
                          #'(<=> st
                                 (<icall> 'assert__stack 
                                          st (<c> 10))))))

       #'(<begin>
          assert-stack
          (<=> (<ref> st (<c> 0)) (<int->fixnum> (<c> n)))
          (<=> (<ref> st (<c> i)) a)
          ...
          (<let*> (((SCM *) ss (<+> st (<c> n))))
            (trampoline f st ss))))))))


          
(define-syntax <<define>>
  (lambda (x)
    (syntax-case x ()      
      ((_ (f a ...) code ...)
       #'(tcall-pre 1 () () (a ...) (f code ...) def)))))


(define (putback v beg)
  (lambda q 
    (beg (pp (v #t)))))

(define-syntax def
  (lambda (x)
    (syntax-case x ()
      ((_ (f code ...) n (i ...) (a ...))
       #'(<define> tail-fkn f (((SCM *) -frame)  ((SCM *) -stack))
           (<let*> ((a (<ref> -frame (<c> i))) ... (ret (<scm> 0)))
             (putback ret (<begin> code ...))
             (<=> (<ref> -frame (<c> 0)) ret)
             (<cast> (void *) (<c> 0))))))))

#|
------------------------------------------------------------------------
closures
------------------------------------------------------------------------
|#

(define-syntax scm->scm*
  (syntax-rules ()
    ((_ x) (<cast> (SCM *) (<icall> 'SCM_UNPACK x)))))

(define-syntax scm*->scm
  (syntax-rules ()
    ((_ x) (<icall> 'SCM_PACK x))))

(define-syntax *->scm
  (syntax-rules ()
    ((_ x) (scm*->scm (<cast> (SCM *) x)))))

(define-syntax !
  (lambda (x)
    (syntax-case x ()
      ((_ (s) call c a ...)
       #'(call (s) (<icall> 'TAILFKN (<ref> (scm->scm* c)
                                       (<c> 1)))
               c a ...))

      ((_ call c a ...)
       #'(call (<icall> 'TAILFKN (<ref> (scm->scm* c)
                                       (<c> 1)))
               c a ...)))))
        

(define-syntax <lambda>
  (lambda (x)
    (syntax-case x ()      
      ((_ (a ...) code ...)
       #'(tcall-pre 2 () () (a ...) (code ...) c-lambda)))))


(define-syntax c-lambda
  (lambda (x)
    (syntax-case x ()
      ((_ (code ...) n (i ...) (a ...))
       (with-syntax ((lam (datum->syntax x (gensym "lam"))))
         #'(let ((cl (mk-var '(SCM *) '__closure #f 'no-gensym)))
             (with-fluids ((*cage* (mk-lambda-cage cl (fluid-ref *cage*))))
               (let ((cg (fluid-ref *cage*)))
                 (<define> tail-fkn lam (((SCM *) -frame)  ((SCM *) -stack))
                   (lambda v (c-var (cl 'type) (cl #t)))
                   (lambda v (c= (cl #t) 
                                 ((scm->scm* (<ref> -frame (<c> 1))) #t)))
                   (<let*> ((a (<ref> -frame (<c> i)))
                            ... 
                            (ret (<scm> 0)))
                     (putback ret (<begin> code ...))
                     (<=> (<ref> -frame (<c> 0)) ret)
                     (<cast> (void *) (<c> 0))))
                 (lambda (v)
                   ;(pk `(lambda lam ,v))
                   (match v
                     ('expr #f)
                     ('type 'SCM)
                     (_
                      (lambda (fm)
                        (with-fluids ((*cage* cg))
                          (((<let> (((SCM *) obj 
                                     (<scm-alloc> (<+> (<c> 1) 
                                                       (<c> (cg 'len))))))
                              (<=> (<ref> obj (<c> 1)) (*->scm lam))
                              (f-begin 
                               (cg 'clr obj))
                              (scm*->scm obj))
                            v) fm))))))))))))))


(define-syntax <s-lambda>
  (lambda (x)
    (syntax-case x ()      
      ((_ lam-stack (a ...) code ...)
       #'(tcall-pre 2 () () (a ...) (lam-stack code ...) s-lambda)))))

(define-syntax s-lambda
  (lambda (x)
    (syntax-case x ()
      ((_ (lam-stack code ...) n (i ...) (a ...))
       (with-syntax ((lam (datum->syntax x (gensym "lam"))))
         #'(let ((cl (mk-var '(SCM *) '__closure #f 'no-gensym)))
             (with-fluids ((*cage* (mk-lambda-cage cl (fluid-ref *cage*))))
               (let ((cg (fluid-ref *cage*)))
                 (<define> tail-fkn lam (((SCM *) -frame)  ((SCM *) -stack))
                   (lambda v (c-var (cl 'type) (cl #t)))
                   (lambda v (c= (cl #t) 
                                 ((scm->scm* (<ref> -frame (<c> 1))) #t)))
                   (<let*> ((a (<ref> -frame (<c> i)))
                            ... 
                            (ret (<scm> 0)))
                     (putback ret (<begin> code ...))
                     (<=> (<ref> -frame (<c> 0)) ret)
                     (<cast> (void *) (<c> 0))))
                 (lambda (v)
                   ;(pk `(lambda lam ,v))
                   (match v
                     ('expr #f)
                     ('type 'SCM)
                     (_
                      (lambda (fm)
                        (with-fluids ((*cage* cg))
                          (((<let> (((SCM *) obj lam-stack))
                              (<=> lam-stack (<+> lam-stack 
                                                  (<c> (+ 2
                                                          (cg 'len)))))
                              (<=> (<ref> obj (<c> 1)) (*->scm lam))
                              (f-begin 
                               (cg 'clr obj))
                              (scm*->scm obj))
                            v) fm))))))))))))))

(define-syntax <f-lambda>
  (lambda (x)
    (syntax-case x ()      
      ((_ lam-stack (a ...) code ...)
       #'(tcall-pre 2 () () (a ...) (lam-stack code ...) f-lambda)))))

(define-syntax f-lambda
  (lambda (x)
    (syntax-case x ()
      ((_ (lam-stack code ...) n (i ...) (a ...))
       (with-syntax ((lam (datum->syntax x (gensym "lam"))))
         #'(let ((cl (mk-var '(SCM *) '__closure #f 'no-gensym)))
             (with-fluids ((*cage* (mk-lambda-cage cl (fluid-ref *cage*))))
               (let ((cg (fluid-ref *cage*)))
                 (<define> tail-fkn lam (((SCM *) -frame)  ((SCM *) -stack))
                   (lambda v (c-var (cl 'type) (cl #t)))
                   (lambda v (c= (cl #t) 
                                 ((scm->scm* (<ref> -frame (<c> 1))) #t)))
                   (<let*> ((a (<ref> -frame (<c> i)))
                            ... 
                            (ret (<scm> 0)))
                     (<=> lam-stack
                          (<+> cl
                               (<cast> int (<ref> cl (<c> 0)))))
                     (putback ret (<begin> code ...))
                     (<=> (<ref> -frame (<c> 0)) ret)
                     (<cast> (void *) (<c> 0))))
                 (lambda (v)
                   ;(pk `(lambda lam ,v))
                   (match v
                     ('expr #f)
                     ('type 'SCM)
                     (_
                      (lambda (fm)
                        (with-fluids ((*cage* cg))
                          (((<let> (((SCM *) obj lam-stack))
                              (<=> lam-stack (<+> lam-stack 
                                                  (<c> (+ 2 (cg 'len)))))
                              (<=> (<ref> obj (<c> 0)) 
                                   (<cast> SCM (<c> (+ (cg 'len) 
                                                       2))))
                              (<=> (<ref> obj (<c> 1)) (*->scm lam))
                              (f-begin 
                               (cg 'clr obj))
                              (scm*->scm obj))
                            v) fm))))))))))))))
