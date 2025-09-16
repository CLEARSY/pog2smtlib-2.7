(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort |AS| 0)
(declare-const co2 |Z|)
(declare-const co1 |AS|)
(assert (!
  (not
    (= co2 0))
  :named |Goal|))
(check-sat)
(exit)
