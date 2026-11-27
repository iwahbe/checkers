; A quoted symbol with a byte that is not UTF-8 (0xff): read and written
; back, as Z3 reads it.
(set-logic ALL)
(declare-const |aÿb| Int)
(assert (not (= |aÿb| 1)))
(check-sat)
