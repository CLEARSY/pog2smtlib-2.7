(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c4 |Z|)
(declare-const c2 |Z|)
(declare-const c3 |Z|)
(declare-const c1 |Z|)
(assert (!
  (not
    (= c1 (- (- c2 c3) c4)))
  :named |Goal|))
(check-sat)
(exit)
