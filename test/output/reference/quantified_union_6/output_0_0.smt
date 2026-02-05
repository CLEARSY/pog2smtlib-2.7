(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (@ p x))))
  :named |ax:set.in.intent POW Z|))
(declare-fun |UNION POW Z Z| (|? POW Z| (-> |POW Z| |POW Z|)) |POW Z|)
(assert (!
  (forall ((P |? POW Z|)(E (-> |POW Z| |POW Z|))(x |Z|))
    (= (|set.in Z| x (|UNION POW Z Z| P E))
       (exists ((e |POW Z|)) (and (@ P e) (|set.in Z| x (E e))))))
  :named |ax.set.in.quantified.union (POW Z x Z)|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (@ p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= (|UNION POW Z Z| (lambda ((_c0 |POW Z|))     (= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (or (= _c1 2)(= _c1 4)))))) (lambda ((_c0 |POW Z|)) (|set.intent Z| (lambda ((_c1 |Z|))     (and
      true
      (<= _c1 3)
      (|set.in Z| _c1 _c0)))))) (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 2)))))
  :named |Goal|))
(check-sat)
(exit)
