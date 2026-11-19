(set-logic ALL)
(declare-const g (Array Int Int))
(assert (not (= g (lambda ((x Int) (y Int)) x))))
(check-sat)
