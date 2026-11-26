; Fields Z3 takes as co-variant: an array whose value sort is the datatype
; itself or another datatype that mentions it, a sequence of it, a declared
; sort applied to it.
(set-logic ALL)
(declare-sort S 1)
(declare-datatypes ((L 1)) ((par (T) ((nil) (cons (h T) (t (L T)))))))
(declare-datatypes ((D 0)) (((b) (c (s1 (Array Int D)) (s2 (Seq D)) (s3 (Array Int (L D))) (s4 (S D))))))
(declare-const d D)
(assert (not (= d b)))
(check-sat)
