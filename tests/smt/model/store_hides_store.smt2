(set-logic ALL)
; The outer store at an index hides an inner one at the same index.
(assert (not (and (= (select (store (store ((as const (Array Int Int)) 0) 1 5) 1 7) 1) 7) (= (store (store ((as const (Array Int Int)) 0) 1 5) 1 7) (store ((as const (Array Int Int)) 0) 1 7)))))
(check-sat)
