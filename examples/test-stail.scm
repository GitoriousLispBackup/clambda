(use-modules (language clambda clambda))
(use-modules (language clambda scm))
(use-modules (language clambda sprolog))
(use-modules (language clambda fmt))

;;Queens test
(init-clambda-scm)

(clambda-add (cpp-include "tail-header.h"))

(auto-defs)

(<global> (<array> SCM 10    ) stack-ar )
(<global> (<array> SCM 100000) lam-array)
(<global> (SCM *) lam-stack lam-array)

(:define: lam-stack (selectq X U Xs)
  (:match: (U Xs)
           ((X . Xs)   _             
            (:cc:))
           (( ,Y .  ,Ys)   ( Y . ,Zs)   
            (:call: selectq X Ys Zs))))


(:define: lam-stack (range-list M N U)
 (:match: (U)
   ((M)       (::when:: (s>= M N) (:cut:) (:cc:)))
   ((M . ,L)  (:call: range-list (<<+>> M (<scm> 1)) N L))))

#;
(:define: lam-stack (attack3 X N V)
  (:match: (V)
    ((,Y . _)  (:or: (:when: (<==> (<scm-call> c_scm X) 
                                   (<<+>> (<scm-call> c_scm Y) N))
                                   
                             (:cc:))
                     
                     (:when: (<==> (<scm-call> c_scm X) 
                                   (<<->> (<scm-call> c_scm Y) N))
                             (:cc:))))
    ((_ . ,Y)  (:call: attack3 X (<<+>> N (<scm> 1)) Y))))

#;
(:define: lam-stack (attack3 X N V)
  (:match: (V)
    ((,Y . ,YY)  (:or: (:when: (<or> (<==> (<scm-call> c_scm X) 
                                           (<-> (<+> (<cast> scm_t_bits 
                                                             (<scm-call> c_scm Y))
                                                     (<cast> scm_t_bits N))
                                                (<c> 2)))
                                     (<==> (<scm-call> c_scm X) 
                                           (<+> (<-> (<cast> scm_t_bits 
                                                             (<scm-call> c_scm Y))
                                                     (<cast> scm_t_bits N))
                                                (<c> 2))))

                               (:cc:))
                       (:call: attack3 X (<<+>> N (<scm> 1)) YY)))))

(<<define>> (attack CC Fail X Xs) 
  (<let> ((X (<scm-call> c_scm X)))
    (<recur> loop ((int N (<c> 6)) (Xs Xs))
      (<let> ((Xs (<scm-call> c_lookup Xs)))
        (<<if>> (<scm-call> c_pair Xs)
                (<let*> ((int A  (<cast> int
                                         (<scm-call> c_scm 
                                                     (<scm-call> c_car    
                                                                 Xs))))
                         (B  (<scm-call> c_cdr    Xs)))
                  (<if> (<or> (<==> X (<-> (<+> A N) (<c> 2)))
                              (<==> X (<+> (<-> A N) (<c> 2))))
                        (! <tcall> Fail)
                        (<next> loop (<+> N (<c> 4)) B)))
                (! <tcall> CC Fail))))))

              

#;
(:define: lam-stack (attack X Xs) (:call: attack3 X (<scm> 1) Xs))

#;
(:define: lam-stack (queens3 UnplacedQs SafeQs Qs)
  ;(:pp: "queens3 Unplaced ~a -> ~a" UnplacedQs SafeQs)
  (:match: (UnplacedQs)
    ( _  (:var: (Q UnplacedQs1)
	   (:and: (:call: selectq Q UnplacedQs UnplacedQs1)
		  (:call: attack Q SafeQs)
		  (:call: queens3 UnplacedQs1 
                          (<scm-call> c_cons Q SafeQs) Qs))))
    (()  (:=: SafeQs Qs))))

(:define: lam-stack (queens3 UnplacedQs SafeQs Qs)
  ;(:pp: "queens3 Unplaced ~a -> ~a" UnplacedQs SafeQs)
  (:match: (UnplacedQs)
    ( _  (:var: (Q UnplacedQs1)
	   (:and: (:call: selectq Q UnplacedQs UnplacedQs1)
		  (attack-mac Q SafeQs 
                              (queens3 UnplacedQs1 
                                       (<scm-call> c_cons Q SafeQs) Qs)))))
    (()  (:=: SafeQs Qs))))



(:define: lam-stack (queens N Qs) 
  (:var: (Ns)
     (:pp: "queens (~a)" N)
     (:call: range-list (<scm> 1)   N  Ns)
     (:pp: "range res:  (~a)" Ns)
     (:call: queens3   Ns (<scm> '()) Qs)))



(<scm-ext>
 (<define> squeens (n)
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

(clambda->c "test-stail.c")

