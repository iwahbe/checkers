(set-logic ALL)
; An array is a `lambda` of one variable, of the array's index sort; one
; of no variables is not read. (The answer is edited.)
(declare-fun f (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 0) (f 0)))
(assert (not false))
(check-sat)
