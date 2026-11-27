;; edited: Z3 printed `(define-fun f ((x!0 C)) B (mk Q))`; the parameter is renamed `R` and the body is `(mk (as R C))`
sat
(
  (define-fun f ((R C)) B
    (mk (as R C)))
)
