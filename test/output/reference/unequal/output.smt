(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not (not (= (+ 2 2) 4)))
  :named |Goal|)
)
(check-sat)
(exit)
