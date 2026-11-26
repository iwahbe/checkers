; A `lambda` in a definition never called. Z3 5.3.3: sat, and every
; assertion holds in its model, but `refutes` refuses a query with a
; `lambda` in it.
(set-logic ALL)
(define-fun-rec g ((n Int)) Int (select (lambda ((x Int)) x) n))
(declare-const y Int)
(assert (= y 1))
(assert (not false))
(check-sat)
