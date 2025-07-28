(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))
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

(define-const MININT |Z| (- 2147483648))

(define-const MAXINT |Z| 2147483647)

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))

(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))

(declare-fun |non empty sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (= (|set.in POW Z| s (|non empty sub-sets Z| t))
       (and (|set.in POW Z| s (|sub-sets Z| t))
            (not (= s |set.empty Z|)))))
  :named |ax.non empty sub-sets Z|))

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(assert (!
  (not (|set.in POW Z| INTEGER (|non empty sub-sets Z| INT)))
  :named |Goal|)
)
(check-sat)
(exit)
