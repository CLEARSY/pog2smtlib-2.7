(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (+ 0 1) (+ 2 1)))
  :named |Goal|))
(check-sat)
(exit)
