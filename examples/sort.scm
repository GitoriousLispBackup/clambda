(use-modules (language clambda clambda))
(use-modules (language clambda scm    ))
(use-modules (language clambda fmt))

(init-clambda-scm)
(auto-defs)
       
;;***************************************************************
(<global> (<array> int (<c> 1000)) map)
(<define> void init-map ()
  (<recur> loop ((int i (<c> 1)))
    (<if> (q< i (<c> 1000))
          (<recur> loop2 ((int j0   (<c> 20)) 
                          (int j    (<c> 20)) 
                          (int best (<c> 20)))
            (<if> (q< j (<c> 30))
                  (<let*> ((int k (<%> i j)))
                    (<if> (q< k best)
                          (<next> loop2 j  (<+> j 1)  k)
                          (<next> loop2 j0 (<+> j 1)  best)))
                  (<=> (<ref> map i) j0))))))

#|
(<define> void lastpart 
           (((int *) p)
            ((int *) 1 )
            (int     stp))

  (<recur> loop ()
    (<if> (<not> (<==> q stp))
          (<begin>
           (<=> (<*> p) (<*> q))
           (<++> p)
           (<++> q)
           (<next> loop)))))

           
(<define> void merge (((int *) v1)
                      ((int *) v2)
                      ((int *) p )
                      (int n1)
                      (int n2))
          (<let*> (((int *) stp1 (<+> v1 n1))
                   ((int *) stp2 (<+> v2 n2)))

            (<recur> loop ()
              (<cond> 
               ((<==> p1 stp1) (lastpart p p2 stp2))
               ((<==> p2 stp2) (lastpart p p1 stp1))
               (:t
                (<if> (q<= (<*> p1) (<*> p2))
                      (<begin> (<=> (<*> p) (<*> p1)) (<++> p1))
                      (<begin> (<=> (<*> p) (<*> p2)) (<++> p2)))
                (<++> p)
                (<next> loop))))))


(<define> void sort (((int *) p)
                     ((int *) r)
                     (int n))
    
   (<let*>  ((int m (<if> (q< n 1000)
                          (<ref> map n)
                          30))             
             (int N (<div> n m))
             ((sort-f m-sort  (<ref> fmap m))))
     

     (<recur> loop ((int i 0))
         (<if> (q<= n (<+> m i))
               (m0-sort (<+> p i) (<+> r i))
               (<begin>
                (m-sort (<+> p i) (<+> r i))
                (<next> loop (<+> i m)))))

     (<recur> loop ((int i m))
       (<if> (q< i n)
             (<begin>
              (<recur> loop2 ((int j 0))
                (<if> (q< j n)
                      (<begin>
                       (<call> merge (<+> p j) (<+> p (<+> j i)) (<+> r j) 
                               i (<if> (q< (<+> j i i) n)
                                       j
                                       (<-> n (<+> j i))))
                       (<next> loop2 (<+> j i i)))))
              (<next> loop (<*> i 2)))))))
     
            

|#

(<define> void init()
   (auto-inits)
   (reg-b b2 2)
   (reg-b b3 3)
   (reg-b b4 4)
   (reg-b b5 5)
   (reg-b b6 6)
   (reg-b b7 7)
   (reg-b b8 8)
   (reg-b b9 9)
   (reg-b b10 10)
   (reg-b b11 11)
   (reg-b b12 12)
   (reg-b b13 13)
   (reg-b b14 14)
   (reg-b b15 15)
   (reg-b b16 16)
   (reg-b b17 17)
   (reg-b b18 18)
   (reg-b b19 19)
   (reg-b b20 20)
   (reg-b b21 21)
   (reg-b b22 22)
   (reg-b b23 23)
   (reg-b b24 24)
   (reg-b b25 25)
   (reg-b b26 26)
   (reg-b b27 27)
   (reg-b b28 28)
   (reg-b b29 29)
   (reg-b b30 30))

(<define> void init ()
  (auto-inits)
  (<call> init-batcher)

(clambda->c "sort.c")


