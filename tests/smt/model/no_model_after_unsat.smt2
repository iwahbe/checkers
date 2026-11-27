(set-logic ALL)
; Z3 answers `unsat`: there is no model to check.
(declare-const x Int)
(assert (= x 1))
(assert (not (= x 1)))
(check-sat)
