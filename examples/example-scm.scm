(use-modules (language clambda clambda))
(use-modules (language clambda scm))

(init-clambda)

(auto-defs)

(<const>  int q (<c> 12.4))
(<global> int a (<c> 10))
(<declare> SCM f (x))

(<define> sum ((int n))
  (<recur> loop ((int s (<c> 0)) (int i (<c> 0)))
    (<if> (<==> i n)
          s
          (<next> loop (<+> s i) (<+> i (<c> 1))))))


(<define> list-length (li)
  (<recur> loop ((l li) (i (<scm> 0)))
    (<match> (l)
      ((,x . ,l)  
       (<next> loop l (<<+>> i (<scm> 1))))
      
      (() i))))
       


(<define> tree-mul (a b) 
          (<match> (a b)
            ((,xa . ,la)  (,xb . ,lb)
             (<cons> (<call> tree-mul xa xb) (<call> tree-mul la lb)))

            (() _
             (<scm> '()))

            (_  ()
             (<scm> '()))

            (_ _
             (<<*>> a b))))
    
(<define> void init-raw ()
  (auto-inits))

(clambda->c "example-1.c")
