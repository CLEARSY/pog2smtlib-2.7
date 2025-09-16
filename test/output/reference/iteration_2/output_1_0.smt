(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const NATURAL |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NATURAL) (<= 0 e)))
  :named |ax.set.in.NATURAL|))
(assert (!
  (not
    (|set.in Z| 2 NATURAL))
  :named |Goal|))
(check-sat)
(exit)
