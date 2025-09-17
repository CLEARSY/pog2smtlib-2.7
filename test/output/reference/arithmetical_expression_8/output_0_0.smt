(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (+ 2 1) 3))
  :named |Goal|))
(check-sat)
(exit)
