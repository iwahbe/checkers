(set-logic ALL)
; The same query with the whole model: Z3 prints the universe of `S`, one
; element, so the array has a normal form and the fact holds.
(declare-sort S 0)
(declare-const s S)
(declare-const i Int)
(assert (= (store ((as const (Array S Int)) 0) s i) ((as const (Array S Int)) 4)))
(assert (not false))
(check-sat)
