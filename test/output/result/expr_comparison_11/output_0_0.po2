(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-const wset |POW Z|)
(declare-const vset |POW Z|)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))
(assert (!
  (not (|set.subseteq Z| vset wset))
  :named |Goal|)
)
(check-sat)
(exit)
