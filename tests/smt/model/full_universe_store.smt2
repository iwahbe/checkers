(set-logic ALL)
; With two elements Z3 prints the universe of `S`, so an array indexed by
; `S` has a normal form and the fact is evaluated.
(declare-sort S 0)
(declare-const s S)
(declare-const t S)
(declare-const i Int)
(assert (not (= s t)))
(assert (= (store (store ((as const (Array S Int)) 0) s i) t 4) ((as const (Array S Int)) 4)))
(assert (not false))
(check-sat)
