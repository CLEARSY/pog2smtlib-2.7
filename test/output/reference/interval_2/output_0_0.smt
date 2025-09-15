(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const vconst |Z|)
(declare-const vset2 |POW Z|)
(declare-const vset1 |POW Z|)

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))
(assert (!
  (= vset1 (|interval| 1 12))
  :named |Define:lprp:1|))
(assert (!
  (= vset2 (|interval| 4 9))
  :named |Define:lprp:2|))
(assert (!
  (|set.in Z| vconst vset2)
  :named |Define:lprp:3|))
(assert (!
  (not (|set.in Z| vconst vset1))
  :named |Goal|))
(check-sat)
(exit)
