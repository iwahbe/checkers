; A query asking for an unsat core. Z3 5.3.3 answers `sat`, then an error
; for `(get-unsat-core)` ("unsat core is not available"), then the values;
; the model is read past that one line.
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const x Int)
(assert (! (= x 3) :named a1))
(assert (not false))
(check-sat)
(get-unsat-core)
(get-value (x))
