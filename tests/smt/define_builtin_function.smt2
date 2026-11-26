(set-logic ALL)
(define-fun const ((x Int)) (Array Int Int) (lambda ((i Int)) i))
(assert (not (= (select ((as const (Array Int Int)) 1) 5) 1)))
(check-sat)
