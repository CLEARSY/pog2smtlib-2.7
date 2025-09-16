(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(declare-fun |max| (|POW Z|) |Z|)
(assert (!
  (forall ((s |POW Z|))
    (=> (not (= s |set.empty Z|)) (|set.in Z| (|max| s) s)))
  :named |ax.max.is.member|))
(assert (!
  (forall ((s |POW Z|))
    (forall ((e |Z|))
      (=> (|set.in Z| e s) (<= e (|max| s)))))
    :named |ax.max.is.ge|))
(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
(assert (!
  (not
    (= (|max| (|interval| 2 10)) 3))
  :named |Goal|))
(check-sat)
(exit)
