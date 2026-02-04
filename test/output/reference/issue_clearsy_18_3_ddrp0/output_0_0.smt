(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c0 |Z|)
(assert (!
  (not
    (= 0 c0))
  :named |Goal|))
(check-sat)
(exit)
