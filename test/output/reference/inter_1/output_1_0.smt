(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const elt |Z|)
(declare-const vset1 |POW POW Z|)
(declare-const vset2 |POW Z|)
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(declare-const |set.empty POW Z| |POW POW Z|)
(assert (!
  (forall ((e |POW Z|)) (not (|set.in POW Z| e |set.empty POW Z|)))
  :named |ax.set.in.empty POW Z|))
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (= s t)
      (forall ((e |POW Z|)) (= (|set.in POW Z| e s) (|set.in POW Z| e t)))))
  :named |ax.set.eq POW Z|))
(assert (!
  (|set.in POW Z| vset2 vset1)
  :named |Define:lprp:3|))
(assert (!
  (|set.in Z| elt vset2)
  :named |Define:lprp:4|))
(assert (!
  (not
    (not
      (= vset1 |set.empty POW Z|)))
  :named |Goal|))
(check-sat)
(exit)
