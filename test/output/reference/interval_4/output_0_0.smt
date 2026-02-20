(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const co |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |interval| (|Z| |Z|) |POW Z|)
(assert (!
  (forall ((l |Z|)(u |Z|)(e |Z|))
    (= (|set.in Z| e (|interval| l u))
      (and (<= l e) (<= e u))))
  :named |ax.set.in.interval|))
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
    (= (|interval| co co) (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 co)))))
  :named |Goal|))
(check-sat)
(exit)
