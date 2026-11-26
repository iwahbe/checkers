(set-option :reproducible-resource-limit 1)
(set-logic ALL)
(declare-const x Int)
(declare-const |a
b| Int)
(assert (not (> (* |a
b| (* x x)) 7)))
(check-sat)
(get-value (|a
b| x
 ))
