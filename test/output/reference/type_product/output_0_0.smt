(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-const co |(Z x Z)|)
(assert (!
  (not
    (= co (maplet 0 0)))
  :named |Goal|))
(check-sat)
(exit)
