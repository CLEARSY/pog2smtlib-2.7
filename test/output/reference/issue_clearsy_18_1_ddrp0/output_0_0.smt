(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c1 |Z|)
(declare-const c2 |Z|)
(assert (!
  (not
    (< c1 c2))
  :named |Goal|))
(check-sat)
(exit)
