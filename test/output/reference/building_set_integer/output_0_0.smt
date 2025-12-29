(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.diff Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.diff Z| s t))
       (and (|set.in Z| e s) (not (|set.in Z| e t)))))
  :named |ax.set.in.diff Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(assert (!
  (not
    (= (|set.diff Z| INTEGER (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 0)))) INTEGER))
  :named |Goal|))
(check-sat)
(exit)
