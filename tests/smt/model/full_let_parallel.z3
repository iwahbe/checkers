;; edited by hand: a parallel let in a definition of the model
sat
(
  (define-fun x () Int
    (let ((a 1)) (let ((a 2) (b a)) b)))
)
