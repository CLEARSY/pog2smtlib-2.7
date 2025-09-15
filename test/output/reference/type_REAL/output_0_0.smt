(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(declare-const co |REAL|)
(assert (!
  (not (= co 1.0))
  :named |Goal|))
(check-sat)
(exit)
