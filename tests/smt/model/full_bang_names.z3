sat
(
  ;; universe for S:
  ;;   S!val!1 S!val!2 S!val!0 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun S!val!1 () S)
  (declare-fun S!val!2 () S)
  (declare-fun S!val!0 () S)
  ;; cardinality constraint:
  (forall ((x S)) (or (= x S!val!1) (= x S!val!2) (= x S!val!0)))
  ;; -----------
  (define-fun b () S
    S!val!0)
  (define-fun c () S
    S!val!1)
  (define-fun S!val!1 () S
    S!val!2)
)
