(define-module (language clambda parse syntax-parse)
  #:use-module (language clambda parse match-parse)
  #:use-module (ice-9 pretty-print)
  #:use-module (ice-9 match-phd)
  #:use-module (language tree-il)
  #:use-module (language tree-il)
  #:export (syntax-parse syntax-parse-rules
            <symbol> <number> <string> <char> <car>
            <parse-list> <parse-list..> ver register-error
            *errors* : *src-tag* get-line-nr get-file-name))


(define (syntax? x)
  (and (vector? x) (eq? (vector-ref x 0) 'syntax-object)))

(define (syntax-e x)
  (if (syntax? x)
      (vector-ref x 1)
      x))

(define (<---> a b)
  (define (f x)
    (let ((res (b x)))
      (if res 
	  (list #t)
	  (match-parse -abs ((a a.x)) x
                       ((a . l) (f l))    
		       (_       #f)))))
  f)

(define (<cons> a b)
  (lambda (x)
    (match-parse -abs ((a a.x) (b b.x)) x
       ((a b) (list #t))
       (_       #f))))

(define <e>
  (lambda (x)
    (list #t)))

(define <id>
  (lambda (x)
    (match-parse x
       ((_ . l) (cons #t l))
       (_        #f))))

(define (<and> s l)
  (lambda (x)
    (if (s x)
        (l x)
        #f)))

(define (<last> s r)
  (lambda (x)
    (match-parse -abs ((s s.x)) x
                 ((s . l) 
                  (if (r (cons l '()))
                      (list #t)
                      #f))
                 (_ #f))))
                        
                               
(define *id* (make-fluid))
(define (<car> s)
  (lambda (x)
    (with-fluids ((*id* x))
      (match-parse x
                   ((x . l) (let ((r (s x)))
                              (if r
                                  (cons #t l)
                                  #f)))
                   (_       #f)))))
                              
(define (<eoln> x)
  (match-parse x
               (()   (list #t))
               (_    #f)))

(define (eq?... x) (eq? '... x))

(define-syntax ver
  (syntax-rules ()
    ((_ x)     (endit 0 x ()))))

(define-syntax ver0
  (lambda (x)
    (syntax-case x (:)
      ((_ a b   . l)   (if (eq? (syntax->datum #'b) '...)
                           #'(<--->  (ver00 a) (ver0 . l))
                           #'(<cons> (ver00 a) (ver0 b . l))))
      ((_ a)           #'(<cons> (ver00 a) <eoln>))
      ((_ a . l)       #'(<cons> (ver00 a) <e>))
      ((_)             #'<eoln>))))

(define-syntax endit
  (lambda (x)
    (syntax-case x (:)
      ((_ 1 (: s) (head ...))   #'(<car> (<and> s (ver0 head ...))))
      ((_ 0 (: s) (head ...))   #'(<and> s (ver0 head ...)))
      ((_ _ (: x y . l) _ )   
       (error ": placed wrongly, should be (a1 a2 ... : <v>)"))
      ((_ 1 (: s . l) (head ...))   #'(<car> (<and> s (ver0 head ... . l))))
      ((_ 0 (: s . l) (head ...))   #'(<and> s (ver0 head ... . l)))
      ((_ n ()        (head ...))   #'(ver0 head ...))
      ((_ n (x y . l) (head ...))   #'(endit n (y . l) (head ... x)))
      ((_ n (x   . l) (head ...))   #'(ver0 head ... x . l)))))

(define-syntax ver00
  (lambda (x)
    (syntax-case x (: ::)
      ((_ (v :  s))  #'(<and> s (ver00 v)))
      ((_ (v :: s))  #'(endit 1 (a : s) ()))
      ((_ (a .  l))  #'(endit 1 (a . l) ()))
      ((_ ()      )  #'<eoln>)
      ((_ a)         #'<id>))))

(define (ma x)
  (syntax-case x (:)
    ((v     : x y   . l)  (error "missplaced :"))
    ((:             . l)  (error "missplaced :"))
    
    ((v     : class    ) 
     (with-syntax ((vv (ma0 #'v)))
       #'(vv)))
    
    ((v     : class . l)  
     (with-syntax ((vv (ma0 #'v))
                   (ll (ma #'l)))
       #'(vv . ll)))
    
    ((v              . l)  
     (with-syntax ((vv (ma0 #'v))
                   (ll (ma #'l)))
       #'(vv . ll)))
    
    ( a                    
      #'a)))

(define (ma0 x)
  (syntax-case x (: ::)
    ((v     : x y   . l)  (error "missplaced :"))

    ((v     :: class    )  
     (ma #'(v : class)))

    ((v     : class    )  
     (ma0 #'v))

    ((v     : class . l)  
     (with-syntax ((vv (ma0 #'v))
                   (ll (ma0 #'l)))
       #'(vv . ll)))

    (_                     
     (ma x))))


(define-syntax syntax-parse
  (lambda (x)
    (syntax-case x ()
      ((_ . l)
       (set! *errors* '())
       #'(syntax-parse0 . l)))))

(define (pp x)
  (pk (syntax->datum x))
  x)

(define (z p x) 
  x)

(define-syntax syntax-parse0
  (lambda (x)
    (syntax-case x ()
      ((_ q r (p code ...))               
       (with-syntax ((p2    (z x (ma #'p)))
                     (ver2  #'(ver p)))
         #'(begin
             ;;(pretty-print (tree-il->scheme (macroexpand 'ver2)))
             (if (ver2 q)
                 (syntax-case q r
                   (p2  code ...))
                 (error "macro did not pass the validator!")))))
    
      ((_ q r (p code ...) . l)               
       (with-syntax ((p2    (z x (ma #'p)))
                     (ver2  #'(ver p)))
         #'(begin
             ;;(pretty-print (tree-il->scheme (macroexpand 'ver2)))
             (let ((cc (lambda (w) (syntax-parse0 w r . l))))
               (if (ver2 q)
                   (syntax-case q r
                     (p2  code ...)
                     (_   (cc q)))
                   (cc q)))))))))

(define-syntax syntax-parse-rules
  (syntax-rules ()
    ((_ w (p c) ...) 
     (lambda (x)
       (syntax-parse x w 
         (p #'c) ...)))))

(define *errors* '())

(define *src-tag* #f)
(define (get-data f x)
  (let loop ((x x) (pr #t))
    (let ((r (syntax-source x)))
      (if r
          (f r)
          (if (*pair? x)
              (loop (*car x) pr)
              (let loop2 ((x (fluid-ref *id*)))
                (let ((r (syntax-source x)))
                  (if r
                      (f r)
                      (if (*pair? x)
                          (loop2 (*car x))
                          (if pr
                              (loop *src-tag* #f)
                              -1))))))))))
            
(define (get-line-nr x)
  (get-data cdar x))
(define (get-file-nm x)
  (get-data (lambda (x) (cdr (caddr x))) x))

(define (mk-error-str s . l)
  (apply format `(#f ,s ,@(map syntax->datum l))))

(define (register-error pr s x . l)
  (let ((Str (format #f "error at ~a (~a),~% ~a" 
                     (get-line-nr x)
                     (get-file-nm x)
                     (apply mk-error-str `(,s ,@l)))))
    (if pr
        (error Str)
        (begin
          (set! *errors* (cons Str *errors*))
          #f))))
                           


(define (print-error)
  (format #t "ERROR: syntax-parse ~a~%" (car *errors*)))


(define (<parse-list> pr str-list str-len . n)
  (lambda (x)
    ;(pp `(parse-list ,x))
    (match-parse x
                 ((a ...) (if (> (length n) 0)
                              (if (eq? (car n) (length a))
                                  (list #t)
                                  (register-error pr str-len x))
                              (list #t)))
                 (_       (register-error pr str-list x)))))

(define (<parse-list..> pr str-list str-len . n)
  (lambda (x)
    ;(pp `(parse-list.. ,x))
    (match-parse x
                 ((a ...) (if (> (length n) 0)
                              (if (<= (car n) (length a))
                                  (cons #t 
                                        (let loop ((a a) (i (car n)))
                                          (if (= i 0)
                                              a
                                              (loop (cdr a) (- i 1)))))
                                  (register-error pr str-len x))
                              (list #t)))
                 (_       (register-error pr str-list x)))))

(define-syntax mk-predicate
  (lambda (x)
    (syntax-case x ()
      ((_ n)
       (let ((base (symbol->string (syntax->datum #'n))))
	 (with-syntax ((ns (datum->syntax #'n 
					  (string->symbol
					   (string-append
					    "<" base ">"))))
		       (pr (datum->syntax #'n 
					  (string->symbol
					   (string-append
					    base "?")))))
           #'(define (ns . str)
               (let ((data (match str
                             ((str)    (cons #f str))
                             ((pr str) (cons pr str)))))
                 (lambda (z)
                   (match-parse z 
                     ((x . l)
                      (if (pr (syntax-e x))
                          (cons #t l)
                          (register-error (car data)
                                          (format #f "[~a] ~a" 
                                                  (syntax->datum x)
                                                  (cdr data))
                                          z)))
                     (x (register-error (car data)
                                        (format #f "[~a] ~a" 
                                                (syntax->datum x)
                                                (cdr data))
                                        z))))))))))))


(mk-predicate symbol)
(mk-predicate number)
(mk-predicate string)
(mk-predicate char)


