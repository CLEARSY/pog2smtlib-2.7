(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const ub |Z|)
(declare-const lb |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |interval| (|Z| |Z|) |POW Z|)
(assert (!
  (forall ((l |Z|)(u |Z|)(e |Z|))
    (= (|set.in Z| e (|interval| l u))
      (and (<= l e) (<= e u))))
  :named |ax.set.in.interval|))
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (< ub lb)
  :named |Define:lprp:3|))
(assert (!
  (not
    (= (|interval| lb ub) |set.empty Z|))
  :named |Goal|))
(check-sat)
(exit)
