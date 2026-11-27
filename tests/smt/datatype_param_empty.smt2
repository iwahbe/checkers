(set-logic ALL)
; `(U T)` needs a `(Box (U T))`, which needs a `(U T)`: no value, though
; `Box` and `U` each look fine alone. (Z3 5.3.3 accepts this.)
(declare-datatypes ((Box 1) (U 1)) ((par (T) ((box (unbox T)))) (par (T) ((u (x (Box (U T))))))))
(declare-const c (U Int))
(assert (not false))
(check-sat)
