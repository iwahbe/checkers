(set-option :produce-models true)
(set-option :reproducible-resource-limit 1000)
(set-logic ALL)
(declare-const x Int)
(assert (not (= x 1)))
(check-sat)
(get-value (x))
; z3 says: sat
; z3 says: ((x 2))
; z3 says: (:rlimit-count 12
; z3 says:  :time 0.02)
