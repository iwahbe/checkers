;; edited: Z3 printed `(define-fun g ((x!0 Int) (x!1 Int)) Int 1)`; both parameters are named `x`
sat
(
  (define-fun g ((x Int) (x Int)) Int
    x)
)
