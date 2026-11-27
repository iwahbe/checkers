(set-logic ALL)
; The query declares `S!val!1`, the name Z3 gives an element of `S` in its
; model, which here holds the query's constant too. No model is read.
(declare-sort S 0)
(declare-const |S!val!1| S)
(declare-const b S)
(declare-const c S)
(assert (not (= b c)))
(assert (not (= c |S!val!1|)))
(assert (not (= |S!val!1| b)))
(assert (not false))
(check-sat)
