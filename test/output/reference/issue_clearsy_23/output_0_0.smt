(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const s5 |POW Z|)
(declare-const s13 |Z|)
(declare-const s14 |Z|)
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
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(declare-const s13$1 |Z|)
(assert (!
  (= s5 (|interval| 0 255))
  :named |Define:ctx:1|))
(assert (!
  (|set.in Z| s13 s5)
  :named |Define:inv:1|))
(assert (!
  (|set.in Z| s14 s5)
  :named |Define:inv:2|))
(assert (!
  (not
    (|set.in Z| s13$1 s5))
  :named |Goal|))
(check-sat)
(exit)
