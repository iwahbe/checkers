sat
(
  (define-fun g () Bool
    (forall ((y Int)) (! (>= (f y) 0) :pattern ((f y)))))
  (define-fun x () Int
    1)
  (define-fun f ((x!0 Int)) Int
    0)
)
