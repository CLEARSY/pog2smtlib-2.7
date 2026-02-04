(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p2 |Z|)
(declare-const v0 |Z|)
(declare-const v1 |Z|)
(declare-const p0 |Z|)
(declare-const c0 |Z|)
(assert (!
  (< p0 p1)
  :named |Hypothesis:3|))
(assert (!
  (< p1 p2)
  :named |Hypothesis:4|))
(assert (!
  (< p0 v0)
  :named |Local_Hyp:0|))
(assert (!
  (not
    (= (- (- v0 v1) p2) c0))
  :named |Goal|))
(check-sat)
(exit)
