(set-logic ALL)
(assert (not (and (= (- 3) (- 0 3)) (= (- (- 4)) 4) (= (- 0) 0))))
(check-sat)
