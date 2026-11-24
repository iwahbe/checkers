(set-logic ALL)
(assert (not (= (select (lambda ((x Int)) (+ x 1)) 4) 5)))
(check-sat)
