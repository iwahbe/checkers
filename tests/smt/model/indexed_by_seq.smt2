(set-logic ALL)
; Arrays indexed by sequences and by arrays.
(assert (not (and (= (select (store ((as const (Array (Seq Int) Int)) 0) (seq.unit 1) 9) (seq.++ (seq.unit 1) (as seq.empty (Seq Int)))) 9) (= (select (store ((as const (Array (Array Int Int) Int)) 0) ((as const (Array Int Int)) 1) 9) ((as const (Array Int Int)) 1)) 9) (= (select (store ((as const (Array (Array Int Int) Int)) 0) ((as const (Array Int Int)) 1) 9) ((as const (Array Int Int)) 2)) 0))))
(check-sat)
