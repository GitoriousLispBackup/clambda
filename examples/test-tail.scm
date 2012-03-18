(use-modules (language clambda clambda))
(use-modules (language clambda scm))
(use-modules (language clambda prolog))
(use-modules (language clambda fmt))

(init-clambda-scm)

(clambda-add (cpp-include "tail-header.h"))

(auto-defs)


(<global> (<array> SCM 10) stack-ar)

(<<define>> (f x s)
   (<<if>> (s< x (<scm> 10000000))
           (<tcall> f 
                    (<<+>> x (<scm> 1))
                    (<<+>> s (<scm> 3)))
           s))

(<scm-ext>
 (<define> fw ()
   (<let> (( (SCM *) stack stack-ar))
     (<tr-call> (stack) f (<scm> 0) (<scm> 0)))))
               

(<scm-ext>
 (<define> fy ()
   (<recur> loop ((x (<scm> 0)) (s (<scm> 0)))
     (<<if>> (s< x (<scm> 10000000))
             (<next> loop 
                     (<<+>> x (<scm> 1))
                     (<<+>> s (<scm> 3)))
             s))))


(<scm-ext>
 (<define> fx (y)
    (<let*> (((SCM *) stack stack-ar)
             (g (<lambda> (x) (<<+>> x y)))
             (h (<lambda> (x) (<<+>> x (! <tr-call> g (<scm> 2))))))
      (<scm> 1)
      (! (stack) <tr-call> h (<scm> 3)))))

      

;;Queens test
(:define: (selectq X U Xs)
  (:match: (U Xs)
           ((X . Xs)   _             
            (:cc:))
           (( ,Y .  ,Ys)   ( Y . ,Zs)   
            (:call: selectq X Ys Zs))))


(:define: (range-list M N U)
 (:match: (U)
   ((M)       (::when:: (s>= M N) (:cut:) (:cc:)))
   ((M . ,L)  (:call: range-list (<<+>> M (<scm> 1)) N L))))

(:define: (attack3 X N V)
  (:match: (V)
    ((,Y . _)  (:or: (:when: (<==> (<scm-call> c_scm X) 
                                   (<<+>> (<scm-call> c_scm Y) N))
                             (:cc:))
                     
                     (:when: (<==> (<scm-call> c_scm X) 
                                   (<<->> (<scm-call> c_scm Y) N))
                             (:cc:))))
    ((_ . ,Y)  (:call: attack3 X (<<+>> N (<scm> 1)) Y))))


(:define: (attack X Xs) (:call: attack3 X (<scm> 1) Xs))

(:define: (queens3 UnplacedQs SafeQs Qs)
  ;(:pp: "queens3 Unplaced ~a -> ~a" UnplacedQs SafeQs)
  (:match: (UnplacedQs)
    ( _  (:var: (Q UnplacedQs1)
	   (:and: (:call: selectq Q UnplacedQs UnplacedQs1)
		  (:not: (:call: attack Q SafeQs))
		  (:call: queens3 UnplacedQs1 
                          (<scm-call> c_cons Q SafeQs) Qs))))
    (()  (:=: SafeQs Qs))))



(:define: (queens N Qs) 
  (:var: (Ns)
     (:pp: "queens (~a)" N)
     (:call: range-list (<scm> 1)   N  Ns)
     (:pp: "range res:  (~a)" Ns)
     (:call: queens3   Ns (<scm> '()) Qs)))



(<scm-ext>
 (<define> fqueens (n)
    (<let*> (((SCM *) stack stack-ar)
             (Qs      (<scm-call> c_var))
             (cc (<lambda> (fail)
                   ;(<format> #t "res> ~a~%" (<scm-call> c_scm Qs))
                   (! <tcall> fail)))
             (f  (<lambda> () (<scm> #f))))
      (<format> #t "starting~%")
      (<tr-call> (stack) queens cc f n Qs))))

(<define> void init()
  (<icall> 'gp_init)
  (auto-inits))


(clambda->c "test-tail.c")

