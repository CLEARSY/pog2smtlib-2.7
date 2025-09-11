(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not (> 1 (+ 1 1)))
  :named |Goal|)
)
(check-sat)
(exit)
