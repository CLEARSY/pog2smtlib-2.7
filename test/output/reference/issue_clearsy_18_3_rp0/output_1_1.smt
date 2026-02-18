(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p1 |Z|)
(declare-const v0 |Z|)
(declare-const v1 |Z|)
(declare-const p0 |Z|)
(declare-const c1 |Z|)
(declare-const c0 |Z|)
(assert (!
  (not
  (< p0 v0))
  :named |Local_Hyp:1|))
(assert (!
  (not
  (< p1 v1))
  :named |Local_Hyp:3|))
(assert (!
  (not
    (= (+ v0 p1) (+ c0 c1)))
  :named |Goal|))
(check-sat)
(exit)
