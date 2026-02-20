(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-const co3 |POW Z|)
(declare-const co2 |POW Z|)
(declare-const co1 |POW Z|)
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.union Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.union Z| s t))
       (or (|set.in Z| e s) (|set.in Z| e t))))
  :named |ax.set.in.union Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= (|set.union Z| (|set.union Z| co1 co2) co3) (|set.union Z| co1 (|set.union Z| co2 co3))))
  :named |Goal|))
(check-sat)
(exit)
