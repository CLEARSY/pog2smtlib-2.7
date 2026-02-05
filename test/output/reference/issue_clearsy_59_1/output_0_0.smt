(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-const c3 |Z|)
(declare-const c2 |Z|)
(assert (!
  (= c2 c3)
  :named |Define:lprp:5|))
(assert (!
  (not
    (<= 0 c3))
  :named |Goal|))
(check-sat)
(exit)
