(set-option :print-success false)
(set-logic HO_ALL)
(declare-datatype |ES| ((e0)(e1)(e2)))
(declare-sort P 1)
(define-sort |POW ES| () (P |ES|))
(declare-const co |ES|)
(declare-const ES |POW ES|)
(assert (!
  (not
    (= co e0))
  :named |Goal|))
(check-sat)
(exit)
