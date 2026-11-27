(set-logic ALL)
; Two closures whose captured `let` variables are both undetermined, for the
; same reason, are not the same array: one is constantly true, the other
; constantly false.
(assert (= (let ((x (= (lambda ((i Int)) (+ i 1)) (lambda ((i Int)) (+ 1 i))))) (lambda ((j Int)) x))
           (let ((x (= (lambda ((i Int)) i) (lambda ((i Int)) (+ 1 i))))) (lambda ((j Int)) x))))
(assert (not false))
(check-sat)
