(set-logic ALL)
; `(box (box (box 0)))` is a value of `(Box (Box (Box Int)))`, nested deeper
; than there are datatypes.
(declare-datatypes ((Box 1)) ((par (T) ((box (unbox T))))))
(declare-datatypes ((W 0)) (((w (x (Box (Box (Box Int))))))))
(declare-const c W)
(assert (not false))
(check-sat)
