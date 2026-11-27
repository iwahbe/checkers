;; edited: Z3 names the variable `x`; it is renamed `S!val!1`, an element
sat
(
  (declare-fun S!val!0 () S)
  (declare-fun S!val!1 () S)
  (forall ((S!val!1 S)) (or (= S!val!1 S!val!0) (= S!val!1 S!val!1)))
  (define-fun s () S
    S!val!0)
)
