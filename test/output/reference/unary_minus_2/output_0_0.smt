(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (+ 1.5 (- 2.5)) (- 1.0)))
  :named |Goal|))
(check-sat)
(exit)
