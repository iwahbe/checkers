(set-logic ALL)
; Arrays of arrays, and arrays inside sequences and data, compared.
(declare-datatypes ((Box 0)) (((box (unbox (Array Int Int))))))
(assert (not (and
  (= (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)) 1 ((as const (Array Int Int)) 1)) (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)) 1 ((as const (Array Int Int)) 1)))
  (not (= (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)) 1 ((as const (Array Int Int)) 1)) ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0))))
  (= (seq.unit ((as const (Array Int Int)) 0)) (seq.unit (store ((as const (Array Int Int)) 0) 3 0)))
  (not (= (seq.unit ((as const (Array Int Int)) 0)) (seq.unit ((as const (Array Int Int)) 1))))
  (= (box (store ((as const (Array Int Int)) 0) 2 5)) (box (store (store ((as const (Array Int Int)) 0) 2 7) 2 5)))
  (not (= (box ((as const (Array Int Int)) 0)) (box (store ((as const (Array Int Int)) 0) 2 5)))))))
(check-sat)
