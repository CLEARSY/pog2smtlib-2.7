(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-const s1 |POW Z|)
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.diff Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.diff Z| s t))
       (and (|set.in Z| e s) (not (|set.in Z| e t)))))
  :named |ax.set.in.diff Z|))
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= (|set.diff Z| s1 s1) |set.empty Z|))
  :named |Goal|))
(check-sat)
(exit)
