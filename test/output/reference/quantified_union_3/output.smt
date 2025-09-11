(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x POW Z)|))

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(declare-fun |UNION (Z x POW Z) Z| (|? (Z x POW Z)| (-> |(Z x POW Z)| |POW Z|)) |POW Z|)
(assert (!
  (forall ((P |? (Z x POW Z)|)(E (-> |(Z x POW Z)| |POW Z|))(x |Z|))
    (= (|set.in Z| x (|UNION (Z x POW Z) Z| P E))
       (exists ((e |(Z x POW Z)|)) (and (P e) (|set.in Z| x (E e))))))
  :named |ax.set.in.quantified.union ((Z x POW Z) x Z)|))

(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (p x))))
  :named |ax:set.in.intent POW Z|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))
(assert (!
  (not (= (|UNION (Z x POW Z) Z| (lambda ((c |(Z x POW Z)|)) (and
(|set.in Z| (fst c) (|set.intent Z| (lambda ((x |Z|)) (or (= x 2)(= x 4)))))
(|set.in POW Z| (snd c) (|set.intent POW Z| (lambda ((x |POW Z|)) (= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)(= x 10))))))))
))  (lambda ((c |(Z x POW Z)|)) (|set.intent Z| (lambda ((x |Z|)) (and
true
(<= x (fst c))
(|set.in Z| x (snd c))
))))) (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 10))))))
  :named |Goal|)
)
(check-sat)
(exit)
