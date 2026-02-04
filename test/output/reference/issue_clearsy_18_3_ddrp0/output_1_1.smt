(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p1 |Z|)
(declare-const v0 |Z|)
(declare-const c1 |Z|)
(declare-const c0 |Z|)
(assert (!
  (not
    (= (+ v0 p1) (+ c0 c1)))
  :named |Goal|))
(check-sat)
(exit)
