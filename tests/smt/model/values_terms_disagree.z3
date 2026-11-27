;; edited: Z3 printed `((= x 1) true)` and `((+ x 1) 2)`; they are changed to `false` and 77
sat
((x 1)
 ((= x 1) false)
 ((+ x 1) 77))
