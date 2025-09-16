(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c5 |Z|)
(declare-const c2 |Z|)
(declare-const c3 |Z|)
(declare-const c1 |Z|)
(declare-const c0 |Z|)
(declare-const c4 |Z|)
(assert (!
  (not
    (or
      (and
        (= c0 c1)
        (not
          (= c0 c2)))
      (=
        (=>
          (= c0 c3)
          (= c0 c4))
        (= c0 c5))))
  :named |Goal|))
(check-sat)
(exit)
