(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(declare-const vconst |POW Z|)
(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(declare-const vset |POW POW Z|)
(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (p x))))
  :named |ax:set.in.intent POW Z|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (= s t)
      (forall ((e |POW Z|)) (= (|set.in POW Z| e s) (|set.in POW Z| e t)))))
  :named |ax.set.eq POW Z|))
(assert (!
  (= vset (|set.intent POW Z| (lambda ((_c0 |POW Z|)) (or (= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (= _c1 1))))(= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (or (= _c1 2)(= _c1 3)))))(= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (or (= _c1 4)(= _c1 10)))))))))
  :named |Define:lprp:1|))
(assert (!
  (= vconst (|interval| 9 12))
  :named |Define:lprp:2|))
(assert (!
  (not
    (|set.in POW Z| vconst vset))
  :named |Goal|))
(check-sat)
(exit)
