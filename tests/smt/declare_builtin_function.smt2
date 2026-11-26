(set-logic ALL)
(declare-fun sin (Int) Int)
(assert (not (= (sin 7) 12345)))
(check-sat)
