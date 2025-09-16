(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (+ 2 2) 5))
  :named |Goal|))
(check-sat)
(exit)
