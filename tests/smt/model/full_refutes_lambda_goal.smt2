; A `lambda` in the goal that evaluation never reaches. Z3 5.3.3: sat, and
; every assertion holds in its model, but `refutes` refuses a query with a
; `lambda` in it.
(set-logic ALL)
(declare-const y Int)
(assert (= y 1))
(assert (not (ite (= y 1) false (= (select (lambda ((x Int)) x) y) y))))
(check-sat)
