;; edited: `S!val!0` is spelled `S!val!00` throughout
sat
(
  (declare-fun S!val!1 () S)
  (declare-fun S!val!00 () S)
  (forall ((x S)) (or (= x S!val!1) (= x S!val!00)))
  (define-fun b () S
    S!val!1)
  (define-fun a () S
    S!val!00)
)
