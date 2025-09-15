(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not (<= (+ 1.5 1.5) 2.5))
  :named |Goal|))
(check-sat)
(exit)
