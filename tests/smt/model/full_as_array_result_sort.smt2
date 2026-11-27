(set-logic ALL)
; `(_ as-array f)` needs `f` of one parameter, the index sort, and a
; result of the element sort: a `Bool` result is not read. (Edited.)
(declare-fun f (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 0) (f 0)))
(assert (not false))
(check-sat)
