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

(declare-fun |min| (|POW Z|) |Z|)
(assert (!
  (forall ((s |POW Z|))
    (=> (not (= s |set.empty Z|)) (|set.in Z| (|min| s) s)))
  :named |ax.min.is.member|))
 (assert (!
   (forall ((s |POW Z|))
     (forall ((e |Z|))
        (=> (|set.in Z| e s) (<= (|min| s) e))))
  :named |ax.min.is.ge|))

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
(assert (!
  (not (= (|min| (|interval| 2 10)) 3))
  :named |Goal|))
(check-sat)
(exit)
