(set-option :print-success false)
(set-logic HO_ALL)
(assert (!
  (not
    (or
      (forall
        ((xx |BOOL|)(yy |BOOL|))
        (=>
          (and
            true
            true)
          (= xx yy)))
      (= (+ 1 1) 2)))
  :named |Goal|))
(check-sat)
(exit)
