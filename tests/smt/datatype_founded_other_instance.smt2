(set-logic ALL)
; A sequence of the datatype at another argument (`(D Int)`) doesn't
; count against it in Z3 5.3.3, which accepts it. `(D A)` has a value
; (`(K [])`) at every `A`, so the reader accepts it too.
(declare-datatypes ((D 1)) ((par (A) ((K (f (Seq (D Int))))))))
(declare-const x (D Bool))
(assert (= x ((as K (D Bool)) (as seq.empty (Seq (D Int))))))
(assert (not false))
(check-sat)
