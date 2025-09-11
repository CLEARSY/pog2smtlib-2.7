(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(declare-fun |set.subset Z| (|POW Z| |POW Z|) Bool)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.subset Z| s t)
      (and
        (|set.subseteq Z| s t)
        (not (= s t)))))
  :named |ax.set.subset Z|))
(assert (!
  (not (|set.subset Z| (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)))) (|set.intent Z| (lambda ((x |Z|)) (or (= x (+ 0 1))(= x (+ 1 1)))))))
  :named |Goal|)
)
(check-sat)
(exit)
