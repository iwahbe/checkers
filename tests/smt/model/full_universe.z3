sat
(
  ;; universe for U:
  ;;   U!val!1 U!val!0 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun U!val!1 () U)
  (declare-fun U!val!0 () U)
  ;; cardinality constraint:
  (forall ((x U)) (or (= x U!val!1) (= x U!val!0)))
  ;; -----------
  (define-fun a () U
    U!val!0)
  (define-fun b () U
    U!val!1)
  (define-fun g ((x!0 U)) U
    (ite (= x!0 U!val!1) U!val!0
      U!val!1))
)
