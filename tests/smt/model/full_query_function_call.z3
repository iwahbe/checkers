;; edited: Z3 printed `(define-fun g ((x!0 Int)) Int 6)`; the body calls the query's `dbl`
sat
(
  (define-fun g ((x!0 Int)) Int
    (dbl x!0))
)
