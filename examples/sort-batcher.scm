(use-modules (language clambda batcher))
(use-modules (language clambda clambda))
(use-modules (language clambda scm    ))
(use-modules (language clambda fmt))

(define-syntax mk-batcher
  (syntax-rules ()
    ((_ n b) (make-batcher b n q> int))))

(define-syntax reg-b
  (syntax-rules ()
    ((_ b n)
     (<=> (<ref> fmap (<c> n)) b))))


(init-clambda-scm)

(clambda-add (c-typedef '(%fun void ((* int))) (auto-t search-f)))

(<global> (<array> search-f 31) fmap)
(mk-batcher 2 b2)
(mk-batcher 3 b3)
(mk-batcher 4 b4)
(mk-batcher 5 b5)
(mk-batcher 6 b6)
(mk-batcher 7 b7)
(mk-batcher 8 b8)
(mk-batcher 9 b9)
(mk-batcher 10 b10)
(mk-batcher 11 b11)
(mk-batcher 12 b12)
(mk-batcher 13 b13)
(mk-batcher 14 b14)
(mk-batcher 15 b15)
(mk-batcher 16 b16)
(mk-batcher 17 b17)
(mk-batcher 18 b18)
(mk-batcher 19 b19)
(mk-batcher 20 b20)
(mk-batcher 21 b21)
(mk-batcher 22 b22)
(mk-batcher 23 b23)
(mk-batcher 24 b24)
(mk-batcher 25 b25)
(mk-batcher 26 b26)
(mk-batcher 27 b27)
(mk-batcher 28 b28)
(mk-batcher 29 b29)
(mk-batcher 30 b30)

(<define> void init-batcher()
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

(clambda->c "sort-batcher.c")
