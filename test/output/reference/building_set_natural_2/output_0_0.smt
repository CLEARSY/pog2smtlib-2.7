(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const v1 |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const NATURAL |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NATURAL) (<= 0 e)))
  :named |ax.set.in.NATURAL|))
(assert (!
  (< 2 v1)
  :named |Define:lprp:2|))
(assert (!
  (< v1 5)
  :named |Define:lprp:3|))
(assert (!
  (not
    (|set.in Z| v1 NATURAL))
  :named |Goal|))
(check-sat)
(exit)
