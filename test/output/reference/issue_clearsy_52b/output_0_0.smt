(set-option :print-success false)
(set-logic HO_ALL)
(declare-datatype |JOURS| ((lundi)(mardi)(mercredi)(jeudi)(vendredi)(samedi)(dimanche)))
(assert (!
  (not
    (= dimanche lundi))
  :named |Goal|))
(check-sat)
(exit)
