(set-logic ALL)
(declare-fun is-x (Int) Bool)
(assert (not (is-x 1)))
(check-sat)
