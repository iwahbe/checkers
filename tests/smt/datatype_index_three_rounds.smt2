(set-logic ALL)
; Through three datatypes, each putting its parameter where the last does: `T` in an index. Rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((W1 1)) ((par (A) ((w1 (f (Array A Int)))))))
(declare-datatypes ((W2 1)) ((par (B) ((w2 (x2 (W1 B)))))))
(declare-datatypes ((W3 1)) ((par (C) ((w3 (x3 (W2 C)))))))
(declare-datatypes ((T 0)) (((leaf) (mk (x (W3 T))))))
(assert (not false))
(check-sat)
