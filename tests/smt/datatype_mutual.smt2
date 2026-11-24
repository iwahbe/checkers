(set-logic ALL)
; Mutually recursive datatypes: `Tree` gets a value from `Forest`'s `nil`,
; with a parameter.
(declare-datatypes ((Tree 1) (Forest 1)) ((par (A) ((node (label A) (kids (Forest A))))) (par (A) ((nil) (cons (head (Tree A)) (tail (Forest A)))))))
(declare-const t (Tree Int))
(assert (not false))
(check-sat)
