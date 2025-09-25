(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(declare-const vset |POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (= s t)
      (forall ((e |POW Z|)) (= (|set.in POW Z| e s) (|set.in POW Z| e t)))))
  :named |ax.set.eq POW Z|))
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
(declare-fun |inter Z| (|POW POW Z|) |POW Z|)
(assert (!
  (forall ((E |POW POW Z|) (x |Z|))
    (= (|set.in Z| x (|inter Z| E))
       (forall ((e |POW Z|)) (=> (|set.in Z| x e) (|set.in POW Z| e E)))))
  :named |ax.set.in.generalized.intersection Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (= vset (|set.intent POW Z| (lambda ((x |POW Z|)) (or (= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)))))(= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 2)))))(= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)(= x 2)))))))))
  :named |Define:lprp:1|))
(assert (!
  (not
    (= (|inter Z| vset) (|set.intent Z| (lambda ((x |Z|)) (= x 0)))))
  :named |Goal|))
(check-sat)
(exit)
