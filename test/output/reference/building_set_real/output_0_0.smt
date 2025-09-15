(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(declare-const co |REAL|)
(assert (!
  (not (not true))
  :named |Goal|))
(check-sat)
(exit)
