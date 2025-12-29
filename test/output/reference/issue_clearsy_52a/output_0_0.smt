(set-option :print-success false)
(set-logic HO_ALL)
(declare-sort |ANNEES| 0)
(declare-const deces |ANNEES|)
(declare-const naissance |ANNEES|)
(assert (!
  (not
    (not
      (= naissance deces)))
  :named |Goal|))
(check-sat)
(exit)
