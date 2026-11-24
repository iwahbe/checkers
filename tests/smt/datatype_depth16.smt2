(set-logic ALL)
; `Box` sixteen deep has a value. Accepted.
(declare-datatypes ((Box 1)) ((par (A) ((box (unbox A))))))
(declare-datatypes ((W 0)) (((w (x (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))))))))))))
(assert (not false))
(check-sat)
