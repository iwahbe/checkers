(set-logic ALL)
; A cardinality constraint whose variable is spelled like an element says
; `(= x x)`, which fixes nothing: the model is not read. (The answer is
; edited.)
(declare-sort S 0)
(declare-const s S)
(assert (= (store ((as const (Array S Int)) 0) s 4) ((as const (Array S Int)) 4)))
(assert (not false))
(check-sat)
