(set-option :produce-models true)
(set-option :reproducible-resource-limit 1000)
(set-logic ALL)
(declare-const x Int)
(assert (not (= x x)))
(check-sat)
(get-value (x))
; z3 says: unsat
; z3 says: (error "line 7 column 14: model is not available")
; z3 says: (:rlimit-count 40
; z3 says:  :time 0.01)
