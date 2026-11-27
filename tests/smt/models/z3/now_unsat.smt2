(set-logic ALL)
; Recorded `sat`; asked again, the stand-in for Z3 answers `unsat`, which
; fails the run.
; z3 says: unsat
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
