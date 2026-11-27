sat
(
  ;; universe for S:
  ;;   S!val!1 S!val!0 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun S!val!1 () S)
  (declare-fun S!val!0 () S)
  ;; cardinality constraint:
  (forall ((x S)) (or (= x S!val!1) (= x S!val!0)))
  ;; -----------
  (define-fun s () S
    S!val!0)
  (define-fun i () Int
    4)
  (define-fun t () S
    S!val!1)
)
