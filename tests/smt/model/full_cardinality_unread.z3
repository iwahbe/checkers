;; edited: the cardinality constraint is replaced by `(forall whatever …)`
sat
(
  (declare-fun S!val!1 () S)
  (declare-fun S!val!0 () S)
  (forall whatever (this is not read))
  (define-fun b () S
    S!val!1)
  (define-fun a () S
    S!val!0)
)
