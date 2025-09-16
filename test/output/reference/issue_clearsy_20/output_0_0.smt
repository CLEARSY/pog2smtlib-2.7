(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c0 |Z|)
(declare-const c1 |Z|)
(assert (!
  (not
    (= c0 c1))
  :named |Goal|))
(check-sat)
(exit)
