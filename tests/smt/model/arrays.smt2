(set-logic ALL)
; select on constant arrays and stores; map +; equality of constant arrays
; with stores, over Int and over Bool indices.
(assert (not (and (= (select (store ((as const (Array Int Int)) 3) 7 4) 7) 4) (= (select (store ((as const (Array Int Int)) 3) 7 4) 8) 3) (= (select ((_ map (+ (Int Int) Int)) (store ((as const (Array Int Int)) 3) 7 4) ((as const (Array Int Int)) 1)) 7) 5) (not (= ((as const (Array Int Int)) 3) ((as const (Array Int Int)) 4))) (not (= (store ((as const (Array Int Int)) 3) 0 1) ((as const (Array Int Int)) 1))) (= (store (store ((as const (Array Bool Int)) 3) true 1) false 1) ((as const (Array Bool Int)) 1)) (= (store ((as const (Array Int Int)) 3) 0 3) ((as const (Array Int Int)) 3)))))
(check-sat)
