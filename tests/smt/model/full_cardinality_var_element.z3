;; edited: Z3 names the variable `x`; it is renamed `S!val!0`, an element
sat
(
  (declare-fun S!val!0 () S)
  (forall ((S!val!0 S)) (= S!val!0 S!val!0))
  (define-fun s () S
    S!val!0)
)
