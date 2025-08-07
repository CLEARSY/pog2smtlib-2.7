(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(define-sort |Z| () Int)
(declare-const c2 |REAL|)
(declare-const c1 |Z|)

(define-fun |int.real| ((x |Z|)) |REAL| (to_real x))
(assert (!
  (not (= (|int.real| c1) c2))
  :named |Goal|)
)
(check-sat)
(exit)
