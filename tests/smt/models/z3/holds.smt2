(set-logic ALL)
; Asked again, the stand-in for Z3 answers with this model.
; z3 says: sat
; z3 says: ((define-fun x () Int 1))
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
