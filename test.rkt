#lang s-exp "base.rkt"



((λ ([x : Num]) ((+ 2) x)) 3)

;(λ ([x : Num]) (sqr x))

(let-pair ([(pair x y)
            (((λ ([x : Num]) (λ ([y : Num]) (pair x y))) 2) 3)])
          ((+ y) x))