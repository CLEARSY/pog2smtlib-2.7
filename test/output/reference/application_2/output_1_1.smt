(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
(define-sort |POW POW (Z x POW Z)| () (P |POW (Z x POW Z)|))
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.subseteq (Z x POW Z)| (|POW (Z x POW Z)| |POW (Z x POW Z)|) Bool)
(assert (!
    (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
      (=
        (|set.subseteq (Z x POW Z)| s t)
        (forall ((e |(Z x POW Z)|)) (=> (|set.in (Z x POW Z)| e s) (|set.in (Z x POW Z)| e t)))
      )
    )
    :named |ax.set.subseteq (Z x POW Z)|))

(declare-fun |set.in POW (Z x POW Z)| (|POW (Z x POW Z)| |POW POW (Z x POW Z)|) Bool)

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |sub-sets (Z x POW Z)| (|POW (Z x POW Z)|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
    (=
      (|set.in POW (Z x POW Z)| s (|sub-sets (Z x POW Z)| t))
      (|set.subseteq (Z x POW Z)| s t)))
  :named |ax.sub-sets (Z x POW Z)|))

(declare-fun |set.product Z POW Z| (|POW Z| |POW POW Z|) |POW (Z x POW Z)|)
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW POW Z|))
    (forall ((p |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| p (|set.product Z POW Z| s1 s2))
        (and (|set.in Z| (fst p) s1) (|set.in POW Z| (snd p) s2)))))
  :named |ax.set.in.product.1 (Z x POW Z)|))
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW POW Z|))
    (forall ((x1 |Z|) (x2 |POW Z|))
      (= (|set.in (Z x POW Z)| (maplet x1 x2) (|set.product Z POW Z| s1 s2))
        (and (|set.in Z| x1 s1) (|set.in POW Z| x2 s2)))))
  :named |ax.set.in.product.2 (Z x POW Z)|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))

(declare-fun |relations Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW POW Z|))
    (= (|relations Z POW Z| X Y)
       (|sub-sets (Z x POW Z)| (|set.product Z POW Z| X Y))))
    :named |def.relations (Z x POW Z)|))

(declare-fun |functions Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW POW Z|))
    (forall ((f |POW (Z x POW Z)|))
      (= (|set.in POW (Z x POW Z)| f (|functions Z POW Z| X Y))
         (forall ((p1 |(Z x POW Z)|) (p2 |(Z x POW Z)|))
           (=> (and (|set.in (Z x POW Z)| p1 f) (|set.in (Z x POW Z)| p2 f) (= (fst p1) (fst p2)))
               (= (snd p1) (snd p2)))))))
:named |ax:set.in.functions (Z x POW Z)|))

(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x POW Z)|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(declare-fun |functions.partial Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW POW Z|))
    (forall ((f |POW (Z x POW Z)|))
      (= (|set.in POW (Z x POW Z)| f (|functions.partial Z POW Z| e1 e2))
         (and (|set.in POW (Z x POW Z)| f (|relations Z POW Z| e1 e2))
              (|set.in POW (Z x POW Z)| f (|functions Z POW Z| e1 e2))))))
  :named |ax:def.pfun (Z x POW Z)|)
)

(declare-fun |rel.range Z POW Z| (|POW (Z x POW Z)|) |POW POW Z|)
(assert (!
  (forall ((r |POW (Z x POW Z)|) (e |POW Z|))
    (= (|set.in POW Z| e (|rel.range Z POW Z| r))
       (exists ((x |Z|)) (|set.in (Z x POW Z)| (maplet x e) r))))
  :named |ax:set.in.range (Z x POW Z)|))

(declare-fun |rel.domain Z POW Z| (|POW (Z x POW Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x POW Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.domain Z POW Z| r))
       (exists ((y |POW Z|)) (|set.in (Z x POW Z)| (maplet e y) r))))
  :named |ax:set.in.domain (Z x POW Z)|))
(assert (!
  (not (|set.in POW (Z x POW Z)| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 4))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 5))))))(= x (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 6)(= x 4))))))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 1)(= x 4))))))))) (|functions.partial Z POW Z| (|rel.domain Z POW Z| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 4))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 5))))))(= x (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 6)(= x 4))))))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 1)(= x 4)))))))))) (|rel.range Z POW Z| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 4))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 3)(= x 5))))))(= x (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 6)(= x 4))))))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 1)(= x 4)))))))))))))
  :named |Goal|))
(check-sat)
(exit)
