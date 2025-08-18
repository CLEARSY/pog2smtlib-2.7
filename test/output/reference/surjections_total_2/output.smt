(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(define-sort |POW POW (Z x Z)| () (P |POW (Z x Z)|))
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.subseteq (Z x Z)| (|POW (Z x Z)| |POW (Z x Z)|) Bool)
(assert (!
    (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
      (=
        (|set.subseteq (Z x Z)| s t)
        (forall ((e |(Z x Z)|)) (=> (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t)))
      )
    )
    :named |ax.set.subseteq (Z x Z)|))

(declare-fun |set.in POW (Z x Z)| (|POW (Z x Z)| |POW POW (Z x Z)|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |sub-sets (Z x Z)| (|POW (Z x Z)|) |POW POW (Z x Z)|)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (|set.in POW (Z x Z)| s (|sub-sets (Z x Z)| t))
      (|set.subseteq (Z x Z)| s t)))
  :named |ax.sub-sets (Z x Z)|))

(declare-fun |set.product Z Z| (|POW Z| |POW Z|) |POW (Z x Z)|)
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW Z|))
    (forall ((p |(Z x Z)|))
      (= (|set.in (Z x Z)| p (|set.product Z Z| s1 s2))
        (and (|set.in Z| (fst p) s1) (|set.in Z| (snd p) s2)))))
  :named |ax.set.in.product.1 (Z x Z)|))
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW Z|))
    (forall ((x1 |Z|) (x2 |Z|))
      (= (|set.in (Z x Z)| (maplet x1 x2) (|set.product Z Z| s1 s2))
        (and (|set.in Z| x1 s1) (|set.in Z| x2 s2)))))
  :named |ax.set.in.product.2 (Z x Z)|))

(declare-fun |relations Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (= (|relations Z Z| X Y)
       (|sub-sets (Z x Z)| (|set.product Z Z| X Y))))
    :named |def.relations (Z x Z)|))

(declare-fun |functions Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|functions Z Z| X Y))
         (forall ((p1 |(Z x Z)|) (p2 |(Z x Z)|))
           (=> (and (|set.in (Z x Z)| p1 f) (|set.in (Z x Z)| p2 f) (= (fst p1) (fst p2)))
               (= (snd p1) (snd p2)))))))
:named |ax:set.in.functions (Z x Z)|))

(declare-fun |rel.domain Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.domain Z Z| r))
       (exists ((y |Z|)) (|set.in (Z x Z)| (maplet e y) r))))
  :named |ax:set.in.domain (Z x Z)|))

(declare-fun |rel.range Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range Z Z| r))
       (exists ((x |Z|)) (|set.in (Z x Z)| (maplet x e) r))))
  :named |ax:set.in.range (Z x Z)|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))

(declare-fun |functions.partial Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|functions.partial Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|relations Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|functions Z Z| e1 e2))))))
  :named |ax:def.pfun (Z x Z)|)
)

(declare-fun |relations.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|relations.total Z Z| X Y))
         (= (|rel.domain Z Z| f) X))))
 :named |ax:set.in.relations.total (Z x Z)|))

(declare-fun |surjections Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|surjections Z Z| X Y))
         (= (|rel.range Z Z| f) Y)
      )))
  :named |ax:set.in.surjections (Z x Z)|))

(declare-fun |functions.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|functions.total Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.partial Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|relations.total Z Z| e1 e2))))))
  :named |ax:def.tfun (Z x Z)|))

(declare-fun |surjections.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|surjections.total Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.total Z Z| e1 e2))
                (|set.in POW (Z x Z)| f (|surjections Z Z| e1 e2))))))
  :named |ax:def.tsurj (Z x Z)|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (|set.in POW (Z x Z)| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 0 1))(= x (maplet 1 2))(= x (maplet 2 2))(= x (maplet 3 0))))) (|surjections.total Z Z| (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)(= x 2)(= x 3)))) (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 1)(= x 2)))))))
  :named |Goal|)
)
(check-sat)
(exit)
