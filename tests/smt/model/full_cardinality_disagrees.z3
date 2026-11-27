;; edited: the cardinality constraint names `S!val!2` in place of `S!val!1`
sat
(
  (declare-fun S!val!1 () S)
  (declare-fun S!val!0 () S)
  (forall ((x S)) (or (= x S!val!2) (= x S!val!0)))
  (define-fun b () S
    S!val!1)
  (define-fun a () S
    S!val!0)
)
