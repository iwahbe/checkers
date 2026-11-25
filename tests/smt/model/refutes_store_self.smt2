; Storing an array's own value changes nothing. Z3 5.3.3: unsat. `refutes`
; must not accept a model whose `a` is a number that reads back as a normal
; form but isn't its number (smt/model_checks.ck builds two such models).
(set-logic ALL)
(declare-const a (Array Int Int))
(assert (not (= (store a 0 (select a 0)) a)))
(assert (not false))
(check-sat)
