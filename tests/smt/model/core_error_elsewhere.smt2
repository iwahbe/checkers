; Z3's line for `(get-unsat-core)` is removed only as its own line right
; after `sat`; anywhere else it stays and the answer doesn't read.
; (The answer is edited.)
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const x Int)
(assert (! (= x 3) :named a1))
(assert (not false))
(check-sat)
(get-unsat-core)
(get-value (x))
