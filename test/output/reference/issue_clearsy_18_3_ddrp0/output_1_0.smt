(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p2 |Z|)
(declare-const v0 |Z|)
(declare-const v1 |Z|)
(declare-const c0 |Z|)
(assert (!
  (not
    (= (- (- v0 v1) p2) c0))
  :named |Goal|))
(check-sat)
(exit)
