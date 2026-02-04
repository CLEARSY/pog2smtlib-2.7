(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c1 |Z|)
(declare-const c2 |Z|)
(declare-const c0 |Z|)
(assert (!
  (= c0 c1)
  :named |Define:lprp:4|))
(assert (!
  (= c1 c2)
  :named |Define:lprp:5|))
(assert (!
  (not
    (< c1 c2))
  :named |Goal|))
(check-sat)
(exit)
