(set-option :rlimit 1)
(set-logic ALL)
(declare-const x Int)
(assert (! (> (* x (* x x)) 7) :named a))
(assert (not (> x 1)))
(check-sat)
  (get-unsat-core)  ; no `:produce-unsat-cores true` above
