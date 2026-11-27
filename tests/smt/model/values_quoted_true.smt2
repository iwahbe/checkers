(set-logic ALL)
; `|true|` is a symbol, not the constant `true`: not read. (The answer is
; edited.)
(declare-const p Bool)
(assert p)
(assert (not false))
(check-sat)
(get-value (p))
