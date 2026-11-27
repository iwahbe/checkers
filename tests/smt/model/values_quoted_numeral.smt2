(set-logic ALL)
; `|1|` is a symbol, not the numeral `1`: not read. (The answer is
; edited.)
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
