(set-logic ALL)
(declare-const s String)
(assert (not (= s "a")))
(check-sat)
