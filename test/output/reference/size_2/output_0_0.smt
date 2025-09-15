(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |((Z x POW Z) x Z)| () (C |(Z x POW Z)| |Z|))
(define-sort |POW ((Z x POW Z) x Z)| () (P |((Z x POW Z) x Z)|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.in ((Z x POW Z) x Z)| (|((Z x POW Z) x Z)| |POW ((Z x POW Z) x Z)|) Bool)

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
(define-sort |POW POW ((Z x POW Z) x Z)| () (P |POW ((Z x POW Z) x Z)|))

(declare-fun |rel.range (Z x POW Z) Z| (|POW ((Z x POW Z) x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW ((Z x POW Z) x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range (Z x POW Z) Z| r))
       (exists ((x |(Z x POW Z)|)) (|set.in ((Z x POW Z) x Z)| (maplet x e) r))))
  :named |ax:set.in.range ((Z x POW Z) x Z)|))

(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
    (=
      (= s t)
      (forall ((e |(Z x POW Z)|)) (= (|set.in (Z x POW Z)| e s) (|set.in (Z x POW Z)| e t)))
    )
  )
  :named |ax.set.eq (Z x POW Z)|))

(declare-fun |set.in POW ((Z x POW Z) x Z)| (|POW ((Z x POW Z) x Z)| |POW POW ((Z x POW Z) x Z)|) Bool)

(declare-fun |surjections (Z x POW Z) Z| (|POW (Z x POW Z)| |POW Z|) |POW POW ((Z x POW Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x POW Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x POW Z) x Z)|))
      (= (|set.in POW ((Z x POW Z) x Z)| f (|surjections (Z x POW Z) Z| X Y))
         (= (|rel.range (Z x POW Z) Z| f) Y)
      )))
  :named |ax:set.in.surjections ((Z x POW Z) x Z)|))

(declare-fun |injections (Z x POW Z) Z| (|POW (Z x POW Z)| |POW Z|) |POW POW ((Z x POW Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x POW Z)|) (Y |POW Z|) (f |POW ((Z x POW Z) x Z)|))
     (= (|set.in POW ((Z x POW Z) x Z)| f (|injections (Z x POW Z) Z| X Y))
        (forall ((p1 |((Z x POW Z) x Z)|) (p2 |((Z x POW Z) x Z)|))
          (=> (and (|set.in ((Z x POW Z) x Z)| p1 f) (|set.in ((Z x POW Z) x Z)| p2 f) (= (snd p1) (snd p2)))
              (= (fst p1) (fst p2))))))
  :named |ax:set.in.injections ((Z x POW Z) x Z)|))

(declare-datatype Cardinals ( ( Infinite ) ( Finite ( Value Int ) )))

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))

(declare-fun |bijections (Z x POW Z) Z| (|POW (Z x POW Z)| |POW Z|) |POW POW ((Z x POW Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x POW Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x POW Z) x Z)|))
      (= (|set.in POW ((Z x POW Z) x Z)| f (|bijections (Z x POW Z) Z| X Y))
         (and (|set.in POW ((Z x POW Z) x Z)| f (|injections (Z x POW Z) Z| X Y))
              (|set.in POW ((Z x POW Z) x Z)| f (|surjections (Z x POW Z) Z| X Y))))))
  :named |ax:set.in.bijections ((Z x POW Z) x Z)|))

(declare-fun |card (Z x POW Z)| (|POW (Z x POW Z)|) Cardinals)
(assert (!
  (forall ((s |POW (Z x POW Z)|))
    (or (= (|card (Z x POW Z)| s) Infinite)
        (exists ((f |POW ((Z x POW Z) x Z)|))
          (|set.in POW ((Z x POW Z) x Z)| f (|bijections (Z x POW Z) Z| s (|interval| 1 (Value (|card (Z x POW Z)| s))))))))
  :named |ax.card.definition (Z x POW Z)|))

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))

(declare-fun |size POW Z| (|POW (Z x POW Z)|) |Z|)
(assert (!
  (forall ((s |POW (Z x POW Z)|))
    (= (|size POW Z| s) (Value (|card (Z x POW Z)| s))))
  :named |ax.size.definition POW Z|))

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
(assert (!
  (not (= (|size POW Z| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 2)(= x 3))))))(= x (maplet 2 (|set.intent Z| (lambda ((x |Z|)) (or (= x 6)(= x 7)(= x 8))))))(= x (maplet 3 |set.empty Z|))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (= x 1))))))))) 4))
  :named |Goal|))
(check-sat)
(exit)
