(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const s3 |POW Z|)
(declare-const s2 |POW Z|)
(declare-const s1 |POW Z|)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|) (e |Z|))
    (=>
      (and (|set.subseteq Z| s t) (|set.in Z| e s))
      (|set.in Z| e t)))
  :named |ax.set.subseteq.elim Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=>
      (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      (|set.subseteq Z| s t)))
  :named |ax.set.subseteq.intro Z|))
(assert (!
  (|set.subseteq Z| s1 s2)
  :named |Define:lprp:4|))
(assert (!
  (|set.subseteq Z| s2 s3)
  :named |Define:lprp:5|))
(assert (!
  (not
    (|set.subseteq Z| s1 s3))
  :named |Goal|))
(check-sat)
(exit)
