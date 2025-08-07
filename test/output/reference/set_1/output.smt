(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const vconst |Z|)
(declare-const vset |POW Z|)

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (= vset (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 3)(= x 4)(= x 10)))))
  :named |Define:lprp:1|)
)
(assert (!
  (|set.in Z| vconst (|interval| 9 12))
  :named |Define:lprp:2|)
)
(assert (!
  (not (|set.in Z| vconst vset))
  :named |Goal|)
)
(check-sat)
(exit)
