(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(define-const MAXINT |Z| 2147483647)
(assert (!
  (not
    (= MAXINT 0))
  :named |Goal|))
(check-sat)
(exit)
