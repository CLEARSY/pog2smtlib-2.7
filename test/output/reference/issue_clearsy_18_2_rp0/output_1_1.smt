(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const p2 |Z|)
(declare-const c2 |Z|)
(declare-const c1 |Z|)
(declare-const c0 |Z|)
(assert (!
  (not
    (= (+ c2 p2) (+ c0 c1)))
  :named |Goal|))
(check-sat)
(exit)
