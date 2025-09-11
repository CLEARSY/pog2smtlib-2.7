(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |fun.eval Z POW Z| (|POW (Z x POW Z)| |Z|) |POW Z|)
 (assert (!
    (forall ((f |POW (Z x POW Z)|)(x |Z|))
        (|set.in (Z x POW Z)| (maplet x (|fun.eval Z POW Z| f x)) f))
    :named |ax.fun.eval (Z x POW Z)|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x POW Z)|))
(assert (!
  (not (= (|fun.eval Z POW Z| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 4))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 5))))))(= x (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 6)(= x 4))))))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 1)(= x 4))))))))) 3) (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 6)(= x 3))))))
  :named |Goal|)
)
(check-sat)
(exit)
