sat
(
  ;; universe for (P Int):
  ;;   P!val!1 P!val!0 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun P!val!1 () (P Int))
  (declare-fun P!val!0 () (P Int))
  ;; cardinality constraint:
  (forall ((x (P Int))) (or (= x P!val!1) (= x P!val!0)))
  ;; -----------
  (define-fun q () (P Int)
    P!val!1)
  (define-fun p () (P Int)
    P!val!0)
)
