(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const v1 |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const NATURAL1 |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NATURAL1) (<= 1 e)))
  :named |ax.set.in.NATURAL1|))
(assert (!
  (<= v1 0)
  :named |Define:lprp:2|))
(assert (!
  (not
    (|set.in Z| v1 NATURAL1))
  :named |Goal|))
(check-sat)
(exit)
