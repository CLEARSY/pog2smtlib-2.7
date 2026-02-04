(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p0 |Z|)
(declare-const p2 |Z|)
(declare-const v0 |Z|)
(declare-const p1 |Z|)
(declare-const v2 |Z|)
(declare-const c2 |Z|)
(declare-const c0 |Z|)
(declare-const c1 |Z|)
(assert (!
  (< p0 p1)
  :named |Hypothesis:3|))
(assert (!
  (< p1 p2)
  :named |Hypothesis:4|))
(assert (!
  (= c0 c1)
  :named |Define:lprp:4|))
(assert (!
  (= c1 c2)
  :named |Define:lprp:5|))
(assert (!
  (= v0 c0)
  :named |Define:inv:3|))
(assert (!
  (= v2 (+ c0 c1))
  :named |Define:inv:4|))
(assert (!
  (not
    (= (+ v0 p1) (+ c0 c1)))
  :named |Goal|))
(check-sat)
(exit)
