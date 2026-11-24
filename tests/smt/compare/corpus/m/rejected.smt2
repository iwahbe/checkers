(set-option :produce-models true)
(set-option :rlimit 1000)
(set-logic ALL)
(declare-const x Int)
(assert (not (= x x)))
(check-sat)
(get-value (x))
; z3 says: (error "line 5 column 1: rejected")
; z3 says: unsat
