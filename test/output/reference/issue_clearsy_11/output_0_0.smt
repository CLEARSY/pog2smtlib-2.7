(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not false)
  :named |Goal|))
(check-sat)
(exit)
