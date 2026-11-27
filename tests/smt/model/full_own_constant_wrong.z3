;; edited: Z3 printed `(define-fun k () Int (+ 1 2))`; the value is changed to 4
sat
(
  (define-fun x () Int
    k)
  (define-fun k () Int
    4)
)
