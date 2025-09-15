(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-const wset |POW Z|)
(declare-const vset |POW Z|)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))
(assert (!
  (not (= vset wset))
  :named |Goal|))
(check-sat)
(exit)
