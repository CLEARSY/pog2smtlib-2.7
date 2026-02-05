(set-option :print-success false)
(set-option :produce-unsat-cores true)
(set-logic ALL)
(assert (!
  (not
    (not
      (= (+ 1 1) 1)))
  :named |Goal|))
(check-sat)
(get-unsat-core)
(exit)
