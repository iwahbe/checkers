;; edited by hand: a lambda whose bound variable is also a constant of the model, unused
sat
(
  (define-fun x () Int
    5)
  (define-fun a () (Array Int Int)
    (lambda ((x Int)) 3))
)
