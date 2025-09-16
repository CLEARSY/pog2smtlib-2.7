(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const c2 |Z|)
(declare-const c1 |Z|)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(assert (!
  (not
    (= (maplet c1 c2) (maplet c2 1)))
  :named |Goal|))
(check-sat)
(exit)
