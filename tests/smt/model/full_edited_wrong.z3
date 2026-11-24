;; edited by hand: Z3 printed f with 4 as its default; 9 makes fact 1, (= (f 3) 4), false
sat
(
  (define-fun f ((x!0 Int)) Int
    (ite (= x!0 5) 11
      9))
)
