(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-const c2 |Z|)
(declare-const c3 |Z|)
(declare-const c6 |Z|)
(declare-const c4 |Z|)
(declare-const c5 |Z|)
(assert (!
  (= c2 c3)
  :named |Define:lprp:8|))
(assert (!
  (= c3 (+ c4 1))
  :named |Define:lprp:9|))
(assert (!
  (= c4 (+ c5 1))
  :named |Define:lprp:10|))
(assert (!
  (= c5 (+ c6 1))
  :named |Define:lprp:11|))
(assert (!
  (not
    (<= 0 c2))
  :named |Goal|))
(check-sat)
(exit)
