(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c3 |Z|)
(declare-const c1 |Z|)
(declare-const c0 |Z|)
(assert (!
  (not
    (= c3 (+ c0 c1)))
  :named |Goal|))
(check-sat)
(exit)
