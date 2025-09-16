(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(declare-const co |BOOL|)
(assert (!
  (not
    (not
      true))
  :named |Goal|))
(check-sat)
(exit)
