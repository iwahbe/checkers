;; edited: the array is `(_ as-array k!0)`, where `k!0` has a `Bool` result
sat
(
  (define-fun a () (Array Int Int)
    (_ as-array k!0))
  (define-fun k!0 ((x!0 Int)) Bool
    true)
  (define-fun f ((x!0 Int)) Int
    0)
)
