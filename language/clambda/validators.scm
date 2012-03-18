(define-module (language clambda validators)
  #:use-module (language clambda parse syntax-parse )
  #:use-module (language clambda parse match-parse  )
  #:use-module (ice-9 match        )
  #:export (mk-tag-vd mk-identifier-vd mk-type-vd mk-decl-vd mk-let-vd
                      mk-decl-vd mk-arg-vd mk-arg*-vd mk-list-vd mk-list*-vd))

(define-syntax aif
  (syntax-rules ()
    ((_ (a) p . l)
     (let ((a p)) (if a . l)))))
                      
(define (mk-tag-vd pr s z)
  (lambda (x)
    (match-parse -abs () x
      ((,z . l)
       (cons #t l))
      (_  (register-error pr "did not match ~a in ~a" x z s)))))


(define symset 
  (list->char-set
   (append
    (char-set->list
     (char-set-intersection char-set:ascii char-set:letter+digit))
    '( #\: #\* #\< #\> #\! #\? #\- #\_))))

(define (mk-list-vd pr str n)
  (<parse-list> pr str str n))
(define (mk-list*-vd pr str n)
  (<parse-list..> pr str str n))

(define (mk-identifier-vd pr locnm)
  (define <sym> (<symbol> pr (format #f "id is not a symbol in ~a" locnm)))
  (lambda (x)
    (if (<sym> x)
        (syntax-case x ()
          ((xx . u)
           (let ((l (string->list
                     (symbol->string 
                      (syntax->datum #'xx)))))
             (match l
               ((#\* ...) 
                (register-error #t "*... not an id in ~a" 
                                #'x locnm))

               (l 
                (let loop ((l l))
                  (match l
                    ((yy . l) 
                     (if (char-set-contains? symset yy)
                         (loop l)
                         (register-error #t "in ~a not allowed character id = ~a" 
                                          #'x locnm #'xx)))
                      
                    (()  (cons #t #'u))
                    (yy  (register-error #t "in ~a not allowed character in id = ~a" 
                                         #'x locnm #'xx)))))))))
        #f)))

(define (star? x)
  (let ((x (syntax->datum x)))
    (member x '(* ** *** **** *****))))

(define (mk-type-vd pr n)
  (define <sym>    (mk-identifier-vd #f n))
  (define (<f> x)
    (match-parse -abs ((<sym> s.x) (<f> f.x))
           x
      ( (<sym> . l) 
        (cons #t l))
      ( (('<array> <f> x) . l)
        (cons #t l))
      ( ((<f> (? star?) (? star?) ...) . l)
        (cons #t l))
      ( _  #f)))
  (lambda (x)
    (aif (it) (<f> x) 
        (cons #t (cdr it))
        (register-error pr "~%-----------~%type clause: ~%type> ~a~%is malformed in ~a~%-------------~%"
                        x x n))))


(define (mk-decl-vd pr s)
  (lambda (x)
    (define <tp>   (mk-type-vd       pr s))
    (define <sym2> (mk-identifier-vd #f s))
    (define <sym3> (mk-identifier-vd pr s)) 
                                     

    (define <list2> 
      (<parse-list> 
       pr
       (format #f
         "variable declaration in ~a is not a var name or a (type varname)"
         s)
       (format #f
        "not (type var-name) or var-name in ~a var name declaration"
        s)
       2))
    
    (syntax-parse x ()
      (((s : <sym2>) . l)
       (cons #t #'l))
      
      ((((t : <tp>) (s : <sym3>) : <list2>) . l)
       (cons #t #'l)))))      

(define (mk-let-vd pr s)
  (lambda (x)
    (define <tp>   (mk-type-vd       pr s))
    (define <id>   (mk-identifier-vd pr s))

    (define <list1> 
      (<parse-list> 
       #f
       (format #f
        "variable declaration in ~a is not a ([type] varname [val])"
         s)
       (format #f
        "not ([type] var-name val) in ~a var name declaration"
        s)
       1))

    (define <list2> 
      (<parse-list> 
       #f
       (format #f
        "variable declaration in ~a is not a ([type] varname [val])"
         s)
       (format #f
        "not ([type] var-name val) in ~a var name declaration"
        s)
       2))

    (define <list3> 
      (<parse-list> 
       pr
       (format #f
        "variable declaration in ~a is not a ([type] varname [val])"
         s)
       (format #f
        "not ([type] var-name val) in ~a var name declaration"
        s)
       3))

    (syntax-parse x ()
      (((           (id : <id>)   :: <list1>) . l)
       (cons #t #'l))
      (((           (id : <id>) v : <list2>) . l)
       (cons #t #'l))
      ((((t : <tp>) (id : <id>) v : <list3>) . l)
       (cons #t #'l)))))


(define (mk-arg-vd pr s n)
  (<parse-list> 
   pr
   (format 
    #f
    "not ~a args in arglist (in ~a)"
    n s)   
   (format 
    #f
    "not ~a args in arglist (in ~a)"
    n s)
   (+ n 1)))

(define (mk-arg*-vd pr s n)
  (<parse-list..> 
   pr
   (format 
    #f
    "less then ~a args in arglist (in ~a)"
    n s)   
   (format 
    #f
    "less then  ~a args in arglist (in ~a)"
    n s)
   (+ n 1)))
