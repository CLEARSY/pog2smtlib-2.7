(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (not (or
(forall ((xx |BOOL|)(yy |BOOL|))   (=>
    (and
true
true
)
(= xx yy)))
(forall ((xx |Z|)(yy |Z|))   (=>
    (and
(|set.in Z| xx (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 3)(= x 4)))))
(|set.in Z| yy (|set.intent Z| (lambda ((x |Z|)) (or (= x 4)(= x 5)))))
)
(< xx yy)))
))
  :named |Goal|)
)
(check-sat)
(exit)
