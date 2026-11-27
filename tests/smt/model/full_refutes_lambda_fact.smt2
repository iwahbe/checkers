; A `lambda` in a fact that evaluation never reaches. Z3 5.3.3: sat, and
; every assertion holds in its model, but `refutes` refuses a query with a
; `lambda` in it.
(set-logic ALL)
(declare-const y Int)
(assert (ite (= y 1) true (= (select (lambda ((x Int)) x) y) y)))
(assert (= y 1))
(assert (not false))
(check-sat)
