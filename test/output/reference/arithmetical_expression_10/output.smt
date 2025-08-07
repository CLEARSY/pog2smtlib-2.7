(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(define-sort |Z| () Int)
(declare-const c2 |REAL|)
(declare-const c1 |Z|)

(define-fun |real.floor| ((x |REAL|)) |Z| (to_int x))
(assert (!
  (not (= c1 (|real.floor| c2)))
  :named |Goal|)
)
(check-sat)
(exit)
