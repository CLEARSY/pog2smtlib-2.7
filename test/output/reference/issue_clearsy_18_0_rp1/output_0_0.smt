(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c3 |Z|)
(assert (!
  (not
    (<= 0 c3))
  :named |Goal|))
(check-sat)
(exit)
