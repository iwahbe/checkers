sat
(
  ;; universe for S:
  ;;   S!val!0 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun S!val!0 () S)
  ;; cardinality constraint:
  (forall ((x S)) (= x S!val!0))
  ;; -----------
  (define-fun s () S
    S!val!0)
  (define-fun i () Int
    4)
)
