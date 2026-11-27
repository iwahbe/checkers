;; edited: Z3 printed `1`; the value is `(ite true 1 2)`
sat
(
  (define-fun x () Int
    (ite true 1 2))
)
