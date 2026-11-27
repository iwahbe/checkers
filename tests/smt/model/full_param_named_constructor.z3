;; edited: Z3 printed `(define-fun f ((x!0 C)) B (mk Q))`; the parameter is renamed `R`, a constructor's name, and the body is `(|mk| R)`
sat
(
  (define-fun f ((R C)) B
    (|mk| R))
)
