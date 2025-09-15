(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(declare-const c1 |BOOL|)
(assert (!
  (not (= true c1))
  :named |Goal|))
(check-sat)
(exit)
