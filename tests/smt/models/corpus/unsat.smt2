(set-logic ALL)
; Z3 answers `unsat`: counted, with no model to check.
(declare-const x Int)
(assert (= x 1))
(assert (not (= x 1)))
(check-sat)
(get-value (x))
