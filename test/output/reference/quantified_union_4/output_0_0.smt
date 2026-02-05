(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |POW Z| () (P |Z|))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (@ p x))))
  :named |ax:set.in.intent (Z x POW Z)|))
(declare-fun |UNION (Z x POW Z) Z| (|? (Z x POW Z)| (-> |(Z x POW Z)| |POW Z|)) |POW Z|)
(assert (!
  (forall ((P |? (Z x POW Z)|)(E (-> |(Z x POW Z)| |POW Z|))(x |Z|))
    (= (|set.in Z| x (|UNION (Z x POW Z) Z| P E))
       (exists ((e |(Z x POW Z)|)) (and (@ P e) (|set.in Z| x (E e))))))
  :named |ax.set.in.quantified.union ((Z x POW Z) x Z)|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (@ p x))))
  :named |ax:set.in.intent Z|))
(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (@ p x))))
  :named |ax:set.in.intent POW Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= (|UNION (Z x POW Z) Z| (lambda ((_c0 |(Z x POW Z)|))     (and
      (|set.in Z| (fst _c0) (|set.intent Z| (lambda ((_c1 |Z|)) (or (= _c1 2)(= _c1 4)))))
      (|set.in POW Z| (snd _c0) (|set.intent POW Z| (lambda ((_c1 |POW Z|)) (= _c1 (|set.intent Z| (lambda ((_c2 |Z|)) (or (= _c2 0)(= _c2 1)(= _c2 10)))))))))) (lambda ((_c0 |(Z x POW Z)|)) (|set.intent Z| (lambda ((_c1 |Z|))     (and
      true
      (<= _c1 (fst _c0))
      (|set.in Z| _c1 (snd _c0))))))) (|set.intent Z| (lambda ((_c0 |Z|)) (or (= _c0 0)(= _c0 1))))))
  :named |Goal|))
(check-sat)
(exit)
