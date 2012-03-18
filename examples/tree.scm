(use-modules (language clambda clambda))
(use-modules (language clambda scm))

#|
  Example code, splay tree using conses and guiles SCM system. 
  Nodes are of the form (key val left right) and the head of the 
  tree is in a cons cell. We assume that key are fixnums in order
  to get a speedy lookup code but this probably works on adresses 
  as well.

  call (ins    tree key val), to insert a key val pair
  call (del    tree key) , to delete the key item
  call (get    tree key) , to lookup the val of a key item, #f is returned at failure

  A splay tree is self organizing in that it will arrange the number of tree walks to be
  short for the working set. So if the usage pattern are similar and local then the tree
  will organize itself so that the hot set migrates quickly to the top of the tree.

  License: LGPL, Copyright: Stefan Israelsson Tampe
|#

(init-clambda-scm)

(auto-defs)

;(clambda-add (cpp-include "header.h"))

;; Accessors
(define-syntax get-tree
  (syntax-rules ()
    ((_ tree) (<car> tree))))

(define-syntax mk-tree
  (syntax-rules ()
    ((_ l) (<cons> l (<scm> '())))))

(define-syntax set-tree
  (syntax-rules ()
    ((_ tree val) (<set-car> tree val))))

(define-syntax set-val
  (syntax-rules ()
    ((_ x v) (<set-car> (<cdr> x) v))))

(define-syntax left
  (syntax-rules (get set)
    ((_ get x)     (<car> (<cdr> (<cdr> x))))
    ((_ set x val) (<set-car> (<cdr> (<cdr> x)) val))))

(define-syntax right
  (syntax-rules (get set)
    ((_ get x)     (<car> (<cdr> (<cdr> (<cdr> x)))))
    ((_ set x val) (<set-car> (<cdr> (<cdr> (<cdr> x))) val))))

(define-syntax set-top
  (syntax-rules ()
    ((_ me tree ippp ppp)
     (<if> ippp
	   (<if> (<==> ippp (<c> -1))
		 (left  set ppp me)
		 (right set ppp me))
	   (set-tree tree me)))))

;; rotation patterns
(define-syntax zig
  (syntax-rules ()
    ((_ tree left right me p)
     (<begin>
      (left  set p  (right get me))
      (right set me p)
      (set-tree tree me)))))

(define-syntax zig-zig
  (syntax-rules ()
    ((_ tree left right me p pp ippp ppp)
     (<begin>
      (<let*> ((save-pr (right get p))
               (save-mr (right get me)))
              (right set me p)
	      (left set p save-mr)
	      (right set p pp)
	      (left set pp save-pr)              
	      (set-top me tree ippp ppp))))))

(define-syntax zig-zag
  (syntax-rules ()
    ((_ tree left right me p pp ippp ppp)
     (<begin>
      (left set pp (right get me))
      (right set me pp)
      (right set p (left get me))
      (left set me p)
      (set-top me tree ippp ppp)))))


;; the splay code
(define-syntax splay
  (syntax-rules ()
    ((_ ip ipp ippp me p pp ppp tree)
     (<if> ip
	   (<if> ipp
		 (<if> (<==> ipp (<c> -1))
		       (<if> (<==> ip (<c> -1))
			     (zig-zig tree left right me p pp ippp ppp)
			     (zig-zag tree left right me p pp ippp ppp))
		       (<if> (<==> ip (<c> -1))
			     (zig-zag tree right left me p pp ippp ppp)
		             (zig-zig tree right left me p pp ippp ppp)))
		 (<if> (<==> ip (<c> -1))
		       (zig tree left  right me p)
		       (zig tree right left  me p)))))))


(<define> splay-lookup (tree key)
   (<recur> loop ((SCM ppp (<scm> #f))
		  (SCM pp  (<scm> #f)) 
		  (SCM p   (<scm> #f))
		  (SCM me  (get-tree tree))
		  (int ippp (<c> 0))
		  (int ipp  (<c> 0))
		  (int ip   (<c> 0)))
     (<scm> 1)
     (<match> (me)
       ((,k ,v . ,r)
	(<if> (<==> k key)
	      (<begin> (splay ip ipp ippp me p pp ppp tree)
		       v)
	      (<match> (r)
		((,l ,r)
		 (<if> (q< key k)
		       (<<if>> l
			       (<next> loop pp p me l ipp ip (<c> -1))
			       (<scm> #f))
		       (<<if>> r
			       (<next> loop pp p me r ipp ip (<c> 1))
			       (<scm> #f))))
		(_ (<error> (<scm> "wrong tree format"))))))
       (_  (<error> (<scm> "wrong tree format"))))))


(<define> lookup (tree key)
   (<recur> loop ((SCM me  (get-tree tree)))
     (<match> (me)
       ((,k ,v . ,r)
	(<if> (<==> k key)
	      v
	      (<match> (r)
		((,l ,r)
		 (<if> (q< key k)
		       (<<if>> l
			       (<next> loop l)
			       (<scm> #f))
		       (<<if>> r
			       (<next> loop r)
			       (<scm> #f))))
		(_ (<error> (<scm> "wrong tree format"))))))
       (_  (<error> (<scm> "wrong tree format"))))))



(<define> insert (tree key val)
  (<recur> loop ((SCM me (get-tree tree)))
    (<match> (me)
      ((,k ,v . ,r)
       (<if> (<==> k key)
	     (set-val me val)
	     (<match> (r)
	       ((,l ,r)
		(<if> (q< key k)
		      (<<if>> l
			      (<next> loop l)
			      (left set me (<scm> `(,key ,val #f #f))))
		      (<<if>> r
			      (<next> loop r)
			      (right set me (<scm> `(,key ,val #f #f))))))
	       (_ (<error> (<scm> "wrong tree format"))))))
      
      (_ 
       (set-tree tree (<scm> `(,key ,val #f #f)))))))

(<scm-ext>
 (<define> new-tree () (mk-tree (<scm> #f))))

(<define> splay-top (tree key)
  (<recur> loop ()
    (<if> (<==> key (<car> (get-tree tree)))
          (<scm> #t)
          (<begin>
           (<call> splay-lookup tree key)
           (<next> loop)))))


(<global> int n (<c> 0))
(<global> int m (<c> 5))

(<scm-ext> 
  (<define> get (tree key)
    (<++> n)
    (<if> (q<= m n)
          (<call> splay-lookup tree key)
          (<call> lookup       tree key))))

(<scm-ext>
 (<define> ins (tree key val)
   (<call> insert tree key val)
   (<call> splay-top  tree key)))

(<define> get-leftmost-key (node)
  (<recur> loop ((me node))
    (<match> (me)
      ((,k _ ,l . _)
       (<<if>> l
               (<next> loop l)
               k)))))

(<define> get-rightmost-key (node)
  (<recur> loop ((me node))
    (<match> (me)
      ((,k _ _ ,r)
       (<<if>> r
               (<next> loop r)
               k)))))

(<scm-ext>
 (<define> del (tree key)
   (<<if>> (<call> lookup tree key)
           (<begin>
            (<call> splay-top tree key)
            (<match> ((get-tree tree))
              ((_ _ ,l ,r)
               (<<if>> l                       
                       (<let*>  ((kl (<call> get-rightmost-key l))
                                 (ll (mk-tree l)))
                                (<call> splay-top ll kl)
                                (right set (get-tree ll) r)
                                (set-tree tree (get-tree ll)))
                       (set-tree tree r))))
            (<scm> #t))
           (<scm> #f))))

(<scm-ext>
 (<define> mille (t n state)
   (<recur> loop ((int i (<c> 0)))
     (<if> (<==> i (<c> 10000000))
           (<scm> #t)
           (<begin>
            (<call> get t (<icall> 'scm_random n state))
            (<next> loop (<+> i (<c> 1))))))))

(<scm-ext>
 (<define> mille-hash (t n state)
   (<recur> loop ((int i (<c> 0)))
     (<if> (<==> i (<c> 10000000))
           (<scm> #t)
           (<begin>
            (<icall> 'scm_hash_ref t (<icall> 'scm_random n state) (<scm> #f))
            (<next> loop (<+> i (<c> 1))))))))
   
                              
(<define> void init()
  (auto-inits))

(clambda->c "tree.c")
