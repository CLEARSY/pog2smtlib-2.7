(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not (not true))
  :named |Goal|))
(check-sat)
(exit)
