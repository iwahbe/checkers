(set-logic ALL)
; Z3 prints no universe for `S` beside `(get-value …)`: how many elements
; `S` has is not known, so an array indexed by `S` has no normal form and
; the fact is not determined.
(declare-sort S 0)
(declare-const s S)
(declare-const i Int)
(assert (= (store ((as const (Array S Int)) 0) s i) ((as const (Array S Int)) 4)))
(assert (not false))
(check-sat)
(get-value (s i))
