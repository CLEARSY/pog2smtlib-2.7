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
(declare-fun |INTER Z Z| (|? Z| (-> |Z| |POW Z|)) |POW Z|)
(assert (!
  (forall ((P |? Z|)(E (-> |Z| |POW Z|))(x |Z|))
    (= (|set.in Z| x (|INTER Z Z| P E))
       (forall ((e |Z|)) (=> (P e) (|set.in Z| x (E e))))))
  :named |ax.set.in.quantified.inter (Z x Z)|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= (|INTER Z Z| (lambda ((c |Z|))     (|set.in Z| c (|set.intent Z| (lambda ((x |Z|)) (or (= x 2)(= x 4))))))  (lambda ((c |Z|)) (|set.intent Z| (lambda ((x |Z|))     (and
      true
      (<= x c)))))) (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)(= x 2))))))
  :named |Goal|))
(check-sat)
(exit)
