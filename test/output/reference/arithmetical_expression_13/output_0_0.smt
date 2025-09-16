(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (mod 5 2) 1))
  :named |Goal|))
(check-sat)
(exit)
