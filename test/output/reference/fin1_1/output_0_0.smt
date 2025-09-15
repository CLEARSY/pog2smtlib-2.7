(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(declare-sort P 1)
(define-sort |(Z x Z)| () (C |Z| |Z|))
(define-sort |POW Z| () (P |Z|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(define-sort |POW POW (Z x Z)| () (P |POW (Z x Z)|))

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

(declare-fun |set.in POW (Z x Z)| (|POW (Z x Z)| |POW POW (Z x Z)|) Bool)

(declare-fun |surjections Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|surjections Z Z| X Y))
         (= (|rel.range Z Z| f) Y)
      )))
  :named |ax:set.in.surjections (Z x Z)|))

(declare-fun |injections Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|) (f |POW (Z x Z)|))
     (= (|set.in POW (Z x Z)| f (|injections Z Z| X Y))
        (forall ((p1 |(Z x Z)|) (p2 |(Z x Z)|))
          (=> (and (|set.in (Z x Z)| p1 f) (|set.in (Z x Z)| p2 f) (= (snd p1) (snd p2)))
              (= (fst p1) (fst p2))))))
  :named |ax:set.in.injections (Z x Z)|))
(define-sort |POW POW Z| () (P |POW Z|))

(declare-datatype Cardinals ( ( Infinite ) ( Finite ( Value Int ) )))

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))

(declare-fun |bijections Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|bijections Z Z| X Y))
         (and (|set.in POW (Z x Z)| f (|injections Z Z| X Y))
              (|set.in POW (Z x Z)| f (|surjections Z Z| X Y))))))
  :named |ax:set.in.bijections (Z x Z)|))
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)

(declare-fun |card Z| (|POW Z|) Cardinals)
(assert (!
  (forall ((s |POW Z|))
    (or (= (|card Z| s) Infinite)
        (exists ((f |POW (Z x Z)|))
          (|set.in POW (Z x Z)| f (|bijections Z Z| s (|interval| 1 (Value (|card Z| s))))))))
  :named |ax.card.definition Z|))

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))

(declare-fun |finite sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (= (|set.in POW Z| s (|finite sub-sets Z| t))
       (and
         (|set.in POW Z| s (|sub-sets Z| t))
         (not (= (|card Z| s) Infinite)))))
  :named |ax.finite sub-sets Z|))

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(declare-fun |set.subseteq POW Z| (|POW POW Z| |POW POW Z|) Bool)
(assert (!
    (forall ((s |POW POW Z|) (t |POW POW Z|))
      (=
        (|set.subseteq POW Z| s t)
        (forall ((e |POW Z|)) (=> (|set.in POW Z| e s) (|set.in POW Z| e t)))
      )
    )
    :named |ax.set.subseteq POW Z|))

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))

(declare-fun |non empty finite sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (= (|set.in POW Z| s (|non empty finite sub-sets Z| t))
       (and (|set.in POW Z| s (|finite sub-sets Z| t))
            (not  (= s |set.empty Z|)))))
  :named |ax.non empty finite sub-sets Z|))
(declare-const p1 |POW POW Z|)
(declare-const p2 |POW POW Z|)
(define-sort |(POW Z x Z)| () (C |POW Z| |Z|))
(define-sort |POW (POW Z x Z)| () (P |(POW Z x Z)|))

(declare-fun |set.in (POW Z x Z)| (|(POW Z x Z)| |POW (POW Z x Z)|) Bool)
(define-sort |POW POW (POW Z x Z)| () (P |POW (POW Z x Z)|))

(declare-fun |rel.range POW Z Z| (|POW (POW Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (POW Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range POW Z Z| r))
       (exists ((x |POW Z|)) (|set.in (POW Z x Z)| (maplet x e) r))))
  :named |ax:set.in.range (POW Z x Z)|))

(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (= s t)
      (forall ((e |POW Z|)) (= (|set.in POW Z| e s) (|set.in POW Z| e t)))
    )
  )
  :named |ax.set.eq POW Z|))

(declare-fun |set.in POW (POW Z x Z)| (|POW (POW Z x Z)| |POW POW (POW Z x Z)|) Bool)

(declare-fun |surjections POW Z Z| (|POW POW Z| |POW Z|) |POW POW (POW Z x Z)|)
(assert (!
  (forall ((X |POW POW Z|) (Y |POW Z|))
    (forall ((f |POW (POW Z x Z)|))
      (= (|set.in POW (POW Z x Z)| f (|surjections POW Z Z| X Y))
         (= (|rel.range POW Z Z| f) Y)
      )))
  :named |ax:set.in.surjections (POW Z x Z)|))

(declare-fun |injections POW Z Z| (|POW POW Z| |POW Z|) |POW POW (POW Z x Z)|)
(assert (!
  (forall ((X |POW POW Z|) (Y |POW Z|) (f |POW (POW Z x Z)|))
     (= (|set.in POW (POW Z x Z)| f (|injections POW Z Z| X Y))
        (forall ((p1 |(POW Z x Z)|) (p2 |(POW Z x Z)|))
          (=> (and (|set.in (POW Z x Z)| p1 f) (|set.in (POW Z x Z)| p2 f) (= (snd p1) (snd p2)))
              (= (fst p1) (fst p2))))))
  :named |ax:set.in.injections (POW Z x Z)|))
(define-sort |POW POW POW Z| () (P |POW POW Z|))

(declare-fun |bijections POW Z Z| (|POW POW Z| |POW Z|) |POW POW (POW Z x Z)|)
(assert (!
  (forall ((X |POW POW Z|) (Y |POW Z|))
    (forall ((f |POW (POW Z x Z)|))
      (= (|set.in POW (POW Z x Z)| f (|bijections POW Z Z| X Y))
         (and (|set.in POW (POW Z x Z)| f (|injections POW Z Z| X Y))
              (|set.in POW (POW Z x Z)| f (|surjections POW Z Z| X Y))))))
  :named |ax:set.in.bijections (POW Z x Z)|))

(declare-fun |set.in POW POW Z| (|POW POW Z| |POW POW POW Z|) Bool)

(declare-fun |card POW Z| (|POW POW Z|) Cardinals)
(assert (!
  (forall ((s |POW POW Z|))
    (or (= (|card POW Z| s) Infinite)
        (exists ((f |POW (POW Z x Z)|))
          (|set.in POW (POW Z x Z)| f (|bijections POW Z Z| s (|interval| 1 (Value (|card POW Z| s))))))))
  :named |ax.card.definition POW Z|))

(declare-fun |sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (|set.in POW POW Z| s (|sub-sets POW Z| t))
      (|set.subseteq POW Z| s t)))
  :named |ax.sub-sets POW Z|))

(declare-fun |finite sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (= (|set.in POW POW Z| s (|finite sub-sets POW Z| t))
       (and
         (|set.in POW POW Z| s (|sub-sets POW Z| t))
         (not (= (|card POW Z| s) Infinite)))))
  :named |ax.finite sub-sets POW Z|))

(declare-const |set.empty POW Z| |POW POW Z|)
(assert (!
  (forall ((e |POW Z|)) (not (|set.in POW Z| e |set.empty POW Z|)))
  :named |ax.set.in.empty POW Z|))
(declare-fun |set.subseteq POW POW Z| (|POW POW POW Z| |POW POW POW Z|) Bool)
(assert (!
    (forall ((s |POW POW POW Z|) (t |POW POW POW Z|))
      (=
        (|set.subseteq POW POW Z| s t)
        (forall ((e |POW POW Z|)) (=> (|set.in POW POW Z| e s) (|set.in POW POW Z| e t)))
      )
    )
    :named |ax.set.subseteq POW POW Z|))

(declare-fun |non empty finite sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (= (|set.in POW POW Z| s (|non empty finite sub-sets POW Z| t))
       (and (|set.in POW POW Z| s (|finite sub-sets POW Z| t))
            (not  (= s |set.empty POW Z|)))))
  :named |ax.non empty finite sub-sets POW Z|))
(assert (!
  (|set.subseteq POW Z| p1 (|non empty finite sub-sets Z| INTEGER))
  :named |Define:lprp:1|))
(assert (!
  (|set.subseteq POW Z| p2 (|non empty finite sub-sets Z| INTEGER))
  :named |Define:lprp:2|))
(assert (!
  (not (|set.subseteq POW POW Z| (|non empty finite sub-sets POW Z| p2) (|non empty finite sub-sets POW Z| p1)))
  :named |Goal|))
(check-sat)
(exit)
