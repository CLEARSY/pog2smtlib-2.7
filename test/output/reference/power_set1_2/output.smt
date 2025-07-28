(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const p1 |POW Z|)

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
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

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))

(declare-fun |non empty sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (= (|set.in POW Z| s (|non empty sub-sets Z| t))
       (and (|set.in POW Z| s (|sub-sets Z| t))
            (not (= s |set.empty Z|)))))
  :named |ax.non empty sub-sets Z|))
(assert (!
  (not (= p1 |set.empty Z|))
  :named |Define:lprp:2|)
)
(assert (!
  (not (|set.in POW Z| p1 (|non empty sub-sets Z| p1)))
  :named |Goal|)
)
(check-sat)
(exit)
