(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-const vset2 |POW Z|)
(declare-const vset1 |POW Z|)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.inter Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.inter Z| s t))
       (and (|set.in Z| e s) (|set.in Z| e t))))
  :named |ax.set.in.inter Z|))
(assert (!
  (not (|set.in Z| 0 (|set.inter Z| vset1 vset2)))
  :named |Goal|)
)
(check-sat)
(exit)
