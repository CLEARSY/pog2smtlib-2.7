(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))

(define-const MININT |Z| (- 2147483648))

(define-const MAXINT |Z| 2147483647)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))

(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))
(assert (!
  (not (|set.in POW Z| INTEGER (|sub-sets Z| INT)))
  :named |Goal|))
(check-sat)
(exit)
