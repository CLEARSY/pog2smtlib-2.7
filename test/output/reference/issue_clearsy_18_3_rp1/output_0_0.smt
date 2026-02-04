(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c0 |Z|)
(declare-const c1 |Z|)
(assert (!
  (= c0 c1)
  :named |Define:lprp:4|))
(assert (!
  (not
    (= 0 c0))
  :named |Goal|))
(check-sat)
(exit)
