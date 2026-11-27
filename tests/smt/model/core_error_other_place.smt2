; Z3's line for `(get-unsat-core)` is removed only when it names where
; that command ends (line 10, column 15 here): one naming another place
; stays, and the answer doesn't read. (The answer is edited.)
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const x Int)
(assert (! (= x 3) :named a1))
(assert (not false))
(check-sat)
(get-unsat-core)
(get-value (x))
