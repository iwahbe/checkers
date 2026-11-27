;; edited: Z3 printed `(> x 0)` for `a1`; it is changed to `false`
sat
(
  (define-fun a1 () Bool
    false)
  (define-fun x () Int
    5)
)
