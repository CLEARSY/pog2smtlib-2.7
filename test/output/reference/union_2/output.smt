(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW POW Z| () (P |POW Z|))

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(define-sort |POW POW POW Z| () (P |POW POW Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.subseteq POW Z| (|POW POW Z| |POW POW Z|) Bool)
(assert (!
    (forall ((s |POW POW Z|) (t |POW POW Z|))
      (=
        (|set.subseteq POW Z| s t)
        (forall ((e |POW Z|)) (=> (|set.in POW Z| e s) (|set.in POW Z| e t)))
      )
    )
    :named |ax.set.subseteq POW Z|))

(declare-fun |set.in POW POW Z| (|POW POW Z| |POW POW POW Z|) Bool)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))

(declare-fun |sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
 (assert (!
    (forall ((s |POW POW Z|) (t |POW POW Z|))
        (=
            (|set.in POW POW Z| s (|sub-sets POW Z| t))
            (|set.subseteq POW Z| s t)
        )
     )
 :named |ax.sub-sets POW Z|))

(declare-const |set.empty POW Z| |POW POW Z|)
(assert (!
  (forall ((e |POW Z|)) (not (|set.in POW Z| e |set.empty POW Z|)))
  :named |ax.set.in.empty POW Z|))

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
 (assert (!
    (forall ((s |POW Z|) (t |POW Z|))
        (=
            (|set.in POW Z| s (|sub-sets Z| t))
            (|set.subseteq Z| s t)
        )
     )
 :named |ax.sub-sets Z|))

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(declare-const vset |POW POW Z|)

 (declare-fun |non empty sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
 (assert (!
    (forall ((s |POW POW Z|) (t |POW POW Z|))
        (= (|set.in POW POW Z| s (|non empty sub-sets POW Z| t))
            (and (|set.in POW POW Z| s (|sub-sets POW Z| t))
                (not (= s |set.empty POW Z|)))))
        :named |ax.non empty sub-sets POW Z|))

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
  (|set.in POW POW Z| vset (|non empty sub-sets POW Z| (|non empty sub-sets Z| INTEGER)))
  :named |Define:lprp:1|)
)
(assert (!
  (not (not (= vset |set.empty POW Z|)))
  :named |Goal|)
)
(check-sat)
(exit)
