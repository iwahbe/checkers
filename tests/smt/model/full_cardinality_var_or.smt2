(set-logic ALL)
; As above, with an `or`: the variable is spelled like the element
; `S!val!1`. (The answer is edited.)
(declare-sort S 0)
(declare-const s S)
(assert (= (store ((as const (Array S Int)) 0) s 4) ((as const (Array S Int)) 4)))
(assert (not false))
(check-sat)
