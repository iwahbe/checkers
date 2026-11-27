;; edited: Z3 printed `1`; the value is an `ite` whose other branch isn't a term
sat
(
  (define-fun x () Int
    (ite true 1 (this is (not smt))))
)
