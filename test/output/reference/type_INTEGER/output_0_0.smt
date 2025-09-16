(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const co |Z|)
(assert (!
  (not
    (= co 0))
  :named |Goal|))
(check-sat)
(exit)
