(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (= (- 3 1) 2))
  :named |Goal|))
(check-sat)
(exit)
