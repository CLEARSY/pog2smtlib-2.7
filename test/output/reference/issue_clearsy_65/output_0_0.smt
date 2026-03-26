(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |POW Z| () (P |Z|))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(define-sort |((Z x Z) x Z)| () (C |(Z x Z)| |Z|))
(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(define-sort |POW ((Z x Z) x Z)| () (P |((Z x Z) x Z)|))
(define-sort |POW POW (Z x Z)| () (P |POW (Z x Z)|))
(define-sort |POW POW Z| () (P |POW Z|))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(declare-fun |set.in ((Z x Z) x Z)| (|((Z x Z) x Z)| |POW ((Z x Z) x Z)|) Bool)
(define-sort |POW POW ((Z x Z) x Z)| () (P |POW ((Z x Z) x Z)|))
(declare-fun |set.subseteq (Z x Z)| (|POW (Z x Z)| |POW (Z x Z)|) Bool)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|) (e |(Z x Z)|))
    (=>
      (and (|set.subseteq (Z x Z)| s t) (|set.in (Z x Z)| e s))
      (|set.in (Z x Z)| e t)))
  :named |ax.set.subseteq.elim (Z x Z)|))
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=>
      (forall ((e |(Z x Z)|)) (=> (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t)))
      (|set.subseteq (Z x Z)| s t)))
  :named |ax.set.subseteq.intro (Z x Z)|))
(declare-fun |set.in POW (Z x Z)| (|POW (Z x Z)| |POW POW (Z x Z)|) Bool)
(define-sort |((Z x Z) x POW Z)| () (C |(Z x Z)| |POW Z|))
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))
(declare-fun |rel.range (Z x Z) Z| (|POW ((Z x Z) x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW ((Z x Z) x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range (Z x Z) Z| r))
       (exists ((x |(Z x Z)|)) (|set.in ((Z x Z) x Z)| (maplet x e) r))))
  :named |ax:set.in.range ((Z x Z) x Z)|))
(declare-fun |set.in POW ((Z x Z) x Z)| (|POW ((Z x Z) x Z)| |POW POW ((Z x Z) x Z)|) Bool)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (= s t)
      (forall ((e |(Z x Z)|)) (= (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t)))))
  :named |ax.set.eq (Z x Z)|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(declare-fun |rel.range Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range Z Z| r))
       (exists ((x |Z|)) (|set.in (Z x Z)| (maplet x e) r))))
  :named |ax:set.in.range (Z x Z)|))
(declare-fun |sub-sets (Z x Z)| (|POW (Z x Z)|) |POW POW (Z x Z)|)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (|set.in POW (Z x Z)| s (|sub-sets (Z x Z)| t))
      (|set.subseteq (Z x Z)| s t)))
  :named |ax.sub-sets (Z x Z)|))
(declare-fun |set.product Z Z| (|POW Z| |POW Z|) |POW (Z x Z)|)
(assert (!
  (forall ((U |POW Z|)(V |POW Z|)(p |(Z x Z)|))
    (= (|set.in (Z x Z)| p (|set.product Z Z| U V))
      (and (|set.in Z| (fst p) U) (|set.in Z| (snd p) V))))
  :named |ax.set.product (Z x Z)|))
(define-sort |POW ((Z x Z) x POW Z)| () (P |((Z x Z) x POW Z)|))
(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
(define-sort |POW POW (Z x POW Z)| () (P |POW (Z x POW Z)|))
(declare-fun |surjections (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|surjections (Z x Z) Z| X Y))
         (= (|rel.range (Z x Z) Z| f) Y)
      )))
  :named |ax:set.in.surjections ((Z x Z) x Z)|))
(declare-fun |injections (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|) (f |POW ((Z x Z) x Z)|))
     (= (|set.in POW ((Z x Z) x Z)| f (|injections (Z x Z) Z| X Y))
        (forall ((p |((Z x Z) x Z)|) (q |((Z x Z) x Z)|))
          (=> (and (|set.in ((Z x Z) x Z)| p f) (|set.in ((Z x Z) x Z)| q f) (= (snd p) (snd q)))
              (= (fst p) (fst q))))))
  :named |ax:set.in.injections ((Z x Z) x Z)|))
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
        (forall ((p |(Z x Z)|) (q |(Z x Z)|))
          (=> (and (|set.in (Z x Z)| p f) (|set.in (Z x Z)| q f) (= (snd p) (snd q)))
              (= (fst p) (fst q))))))
  :named |ax:set.in.injections (Z x Z)|))
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
         (forall ((p |(Z x Z)|) (q |(Z x Z)|))
           (=> (and (|set.in (Z x Z)| p f) (|set.in (Z x Z)| q f) (= (fst p) (fst q)))
               (= (snd p) (snd q)))))))
:named |ax:set.in.functions (Z x Z)|))
(declare-fun |rel.domain Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.domain Z Z| r))
       (exists ((y |Z|)) (|set.in (Z x Z)| (maplet e y) r))))
  :named |ax:set.in.domain (Z x Z)|))
(declare-fun |set.in ((Z x Z) x POW Z)| (|((Z x Z) x POW Z)| |POW ((Z x Z) x POW Z)|) Bool)
(define-sort |POW POW ((Z x Z) x POW Z)| () (P |POW ((Z x Z) x POW Z)|))
(declare-fun |set.subseteq (Z x POW Z)| (|POW (Z x POW Z)| |POW (Z x POW Z)|) Bool)
(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|) (e |(Z x POW Z)|))
    (=>
      (and (|set.subseteq (Z x POW Z)| s t) (|set.in (Z x POW Z)| e s))
      (|set.in (Z x POW Z)| e t)))
  :named |ax.set.subseteq.elim (Z x POW Z)|))
(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
    (=>
      (forall ((e |(Z x POW Z)|)) (=> (|set.in (Z x POW Z)| e s) (|set.in (Z x POW Z)| e t)))
      (|set.subseteq (Z x POW Z)| s t)))
  :named |ax.set.subseteq.intro (Z x POW Z)|))
(declare-fun |set.in POW (Z x POW Z)| (|POW (Z x POW Z)| |POW POW (Z x POW Z)|) Bool)
(declare-fun |bijections (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|bijections (Z x Z) Z| X Y))
         (and (|set.in POW ((Z x Z) x Z)| f (|injections (Z x Z) Z| X Y))
              (|set.in POW ((Z x Z) x Z)| f (|surjections (Z x Z) Z| X Y))))))
  :named |ax:set.in.bijections ((Z x Z) x Z)|))
(declare-datatype Cardinals ( ( Infinite ) ( Finite ( Value Int ) )))
(declare-fun |interval| (|Z| |Z|) |POW Z|)
(assert (!
  (forall ((l |Z|)(u |Z|)(e |Z|))
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
(declare-fun |set.subseteq ((Z x Z) x POW Z)| (|POW ((Z x Z) x POW Z)| |POW ((Z x Z) x POW Z)|) Bool)
(assert (!
  (forall ((s |POW ((Z x Z) x POW Z)|) (t |POW ((Z x Z) x POW Z)|) (e |((Z x Z) x POW Z)|))
    (=>
      (and (|set.subseteq ((Z x Z) x POW Z)| s t) (|set.in ((Z x Z) x POW Z)| e s))
      (|set.in ((Z x Z) x POW Z)| e t)))
  :named |ax.set.subseteq.elim ((Z x Z) x POW Z)|))
(assert (!
  (forall ((s |POW ((Z x Z) x POW Z)|) (t |POW ((Z x Z) x POW Z)|))
    (=>
      (forall ((e |((Z x Z) x POW Z)|)) (=> (|set.in ((Z x Z) x POW Z)| e s) (|set.in ((Z x Z) x POW Z)| e t)))
      (|set.subseteq ((Z x Z) x POW Z)| s t)))
  :named |ax.set.subseteq.intro ((Z x Z) x POW Z)|))
(declare-fun |set.in POW ((Z x Z) x POW Z)| (|POW ((Z x Z) x POW Z)| |POW POW ((Z x Z) x POW Z)|) Bool)
(declare-fun |set.subseteq ((Z x Z) x Z)| (|POW ((Z x Z) x Z)| |POW ((Z x Z) x Z)|) Bool)
(assert (!
  (forall ((s |POW ((Z x Z) x Z)|) (t |POW ((Z x Z) x Z)|) (e |((Z x Z) x Z)|))
    (=>
      (and (|set.subseteq ((Z x Z) x Z)| s t) (|set.in ((Z x Z) x Z)| e s))
      (|set.in ((Z x Z) x Z)| e t)))
  :named |ax.set.subseteq.elim ((Z x Z) x Z)|))
(assert (!
  (forall ((s |POW ((Z x Z) x Z)|) (t |POW ((Z x Z) x Z)|))
    (=>
      (forall ((e |((Z x Z) x Z)|)) (=> (|set.in ((Z x Z) x Z)| e s) (|set.in ((Z x Z) x Z)| e t)))
      (|set.subseteq ((Z x Z) x Z)| s t)))
  :named |ax.set.subseteq.intro ((Z x Z) x Z)|))
(declare-fun |sub-sets (Z x POW Z)| (|POW (Z x POW Z)|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
    (=
      (|set.in POW (Z x POW Z)| s (|sub-sets (Z x POW Z)| t))
      (|set.subseteq (Z x POW Z)| s t)))
  :named |ax.sub-sets (Z x POW Z)|))
(declare-fun |set.product Z POW Z| (|POW Z| |POW POW Z|) |POW (Z x POW Z)|)
(assert (!
  (forall ((U |POW Z|)(V |POW POW Z|)(p |(Z x POW Z)|))
    (= (|set.in (Z x POW Z)| p (|set.product Z POW Z| U V))
      (and (|set.in Z| (fst p) U) (|set.in POW Z| (snd p) V))))
  :named |ax.set.product (Z x POW Z)|))
(declare-fun |set.subseteq POW (Z x Z)| (|POW POW (Z x Z)| |POW POW (Z x Z)|) Bool)
(assert (!
  (forall ((s |POW POW (Z x Z)|) (t |POW POW (Z x Z)|) (e |POW (Z x Z)|))
    (=>
      (and (|set.subseteq POW (Z x Z)| s t) (|set.in POW (Z x Z)| e s))
      (|set.in POW (Z x Z)| e t)))
  :named |ax.set.subseteq.elim POW (Z x Z)|))
(assert (!
  (forall ((s |POW POW (Z x Z)|) (t |POW POW (Z x Z)|))
    (=>
      (forall ((e |POW (Z x Z)|)) (=> (|set.in POW (Z x Z)| e s) (|set.in POW (Z x Z)| e t)))
      (|set.subseteq POW (Z x Z)| s t)))
  :named |ax.set.subseteq.intro POW (Z x Z)|))
(declare-fun |card (Z x Z)| (|POW (Z x Z)|) Cardinals)
(assert (!
  (forall ((s |POW (Z x Z)|))
    (or (= (|card (Z x Z)| s) Infinite)
        (exists ((f |POW ((Z x Z) x Z)|))
          (|set.in POW ((Z x Z) x Z)| f (|bijections (Z x Z) Z| s (|interval| 1 (Value (|card (Z x Z)| s))))))))
  :named |ax.card.definition (Z x Z)|))
(declare-fun |card Z| (|POW Z|) Cardinals)
(assert (!
  (forall ((s |POW Z|))
    (or (= (|card Z| s) Infinite)
        (exists ((f |POW (Z x Z)|))
          (|set.in POW (Z x Z)| f (|bijections Z Z| s (|interval| 1 (Value (|card Z| s))))))))
  :named |ax.card.definition Z|))
(declare-fun |functions.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|functions.total Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.partial Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|relations.total Z Z| e1 e2))))))
  :named |ax:def.tfun (Z x Z)|))
(declare-fun |sub-sets ((Z x Z) x POW Z)| (|POW ((Z x Z) x POW Z)|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((s |POW ((Z x Z) x POW Z)|) (t |POW ((Z x Z) x POW Z)|))
    (=
      (|set.in POW ((Z x Z) x POW Z)| s (|sub-sets ((Z x Z) x POW Z)| t))
      (|set.subseteq ((Z x Z) x POW Z)| s t)))
  :named |ax.sub-sets ((Z x Z) x POW Z)|))
(declare-fun |set.product (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((U |POW (Z x Z)|)(V |POW POW Z|)(p |((Z x Z) x POW Z)|))
    (= (|set.in ((Z x Z) x POW Z)| p (|set.product (Z x Z) POW Z| U V))
      (and (|set.in (Z x Z)| (fst p) U) (|set.in POW Z| (snd p) V))))
  :named |ax.set.product ((Z x Z) x POW Z)|))
(declare-fun |sub-sets ((Z x Z) x Z)| (|POW ((Z x Z) x Z)|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((s |POW ((Z x Z) x Z)|) (t |POW ((Z x Z) x Z)|))
    (=
      (|set.in POW ((Z x Z) x Z)| s (|sub-sets ((Z x Z) x Z)| t))
      (|set.subseteq ((Z x Z) x Z)| s t)))
  :named |ax.sub-sets ((Z x Z) x Z)|))
(declare-fun |set.product (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW ((Z x Z) x Z)|)
(assert (!
  (forall ((U |POW (Z x Z)|)(V |POW Z|)(p |((Z x Z) x Z)|))
    (= (|set.in ((Z x Z) x Z)| p (|set.product (Z x Z) Z| U V))
      (and (|set.in (Z x Z)| (fst p) U) (|set.in Z| (snd p) V))))
  :named |ax.set.product ((Z x Z) x Z)|))
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
         (forall ((p |(Z x POW Z)|) (q |(Z x POW Z)|))
           (=> (and (|set.in (Z x POW Z)| p f) (|set.in (Z x POW Z)| q f) (= (fst p) (fst q)))
               (= (snd p) (snd q)))))))
:named |ax:set.in.functions (Z x POW Z)|))
(declare-fun |rel.domain Z POW Z| (|POW (Z x POW Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x POW Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.domain Z POW Z| r))
       (exists ((y |POW Z|)) (|set.in (Z x POW Z)| (maplet e y) r))))
  :named |ax:set.in.domain (Z x POW Z)|))
(declare-const NATURAL1 |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NATURAL1) (<= 1 e)))
  :named |ax.set.in.NATURAL1|))
(declare-fun |seq Z| (|POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((E |POW Z|) (s |POW (Z x Z)|))
    (=>
      (|set.in POW (Z x Z)| s (|seq Z| E))
      ((_ is Finite) (|card (Z x Z)| s))))
  :named |ax.seq.is.finite Z|))
(assert (!
  (forall ((E |POW Z|))
    (|set.subseteq POW (Z x Z)|
      (|seq Z| E)
      (|functions.total Z Z| (|interval| 1 (Value (|card Z| E))) E)))
  :named |ax.seq.is.total.fun Z|))
(declare-fun |relations (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW POW Z|))
    (= (|relations (Z x Z) POW Z| X Y)
       (|sub-sets ((Z x Z) x POW Z)| (|set.product (Z x Z) POW Z| X Y))))
    :named |def.relations ((Z x Z) x POW Z)|))
(declare-fun |functions (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW POW Z|))
    (forall ((f |POW ((Z x Z) x POW Z)|))
      (= (|set.in POW ((Z x Z) x POW Z)| f (|functions (Z x Z) POW Z| X Y))
         (forall ((p |((Z x Z) x POW Z)|) (q |((Z x Z) x POW Z)|))
           (=> (and (|set.in ((Z x Z) x POW Z)| p f) (|set.in ((Z x Z) x POW Z)| q f) (= (fst p) (fst q)))
               (= (snd p) (snd q)))))))
:named |ax:set.in.functions ((Z x Z) x POW Z)|))
(declare-fun |rel.domain (Z x Z) POW Z| (|POW ((Z x Z) x POW Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((r |POW ((Z x Z) x POW Z)|) (e |(Z x Z)|))
    (= (|set.in (Z x Z)| e (|rel.domain (Z x Z) POW Z| r))
       (exists ((y |POW Z|)) (|set.in ((Z x Z) x POW Z)| (maplet e y) r))))
  :named |ax:set.in.domain ((Z x Z) x POW Z)|))
(declare-fun |functions (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|functions (Z x Z) Z| X Y))
         (forall ((p |((Z x Z) x Z)|) (q |((Z x Z) x Z)|))
           (=> (and (|set.in ((Z x Z) x Z)| p f) (|set.in ((Z x Z) x Z)| q f) (= (fst p) (fst q)))
               (= (snd p) (snd q)))))))
:named |ax:set.in.functions ((Z x Z) x Z)|))
(declare-fun |relations (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|))
    (= (|relations (Z x Z) Z| X Y)
       (|sub-sets ((Z x Z) x Z)| (|set.product (Z x Z) Z| X Y))))
    :named |def.relations ((Z x Z) x Z)|))
(declare-fun |rel.domain (Z x Z) Z| (|POW ((Z x Z) x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((r |POW ((Z x Z) x Z)|) (e |(Z x Z)|))
    (= (|set.in (Z x Z)| e (|rel.domain (Z x Z) Z| r))
       (exists ((y |Z|)) (|set.in ((Z x Z) x Z)| (maplet e y) r))))
  :named |ax:set.in.domain ((Z x Z) x Z)|))
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(declare-fun |functions.partial Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW POW Z|))
    (forall ((f |POW (Z x POW Z)|))
      (= (|set.in POW (Z x POW Z)| f (|functions.partial Z POW Z| e1 e2))
         (and (|set.in POW (Z x POW Z)| f (|relations Z POW Z| e1 e2))
              (|set.in POW (Z x POW Z)| f (|functions Z POW Z| e1 e2))))))
  :named |ax:def.pfun (Z x POW Z)|)
)
(declare-fun |relations.total Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW POW Z|))
    (forall ((f |POW (Z x POW Z)|))
      (= (|set.in POW (Z x POW Z)| f (|relations.total Z POW Z| X Y))
         (= (|rel.domain Z POW Z| f) X))))
 :named |ax:set.in.relations.total (Z x POW Z)|))
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|) (e |Z|))
    (=>
      (and (|set.subseteq Z| s t) (|set.in Z| e s))
      (|set.in Z| e t)))
  :named |ax.set.subseteq.elim Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=>
      (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      (|set.subseteq Z| s t)))
  :named |ax.set.subseteq.intro Z|))
(declare-fun |iseq Z| (|POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((E |POW Z|)(s |POW (Z x Z)|))
    (= (|set.in POW (Z x Z)| s (|iseq Z| E))
       (and (|set.in POW (Z x Z)| s (|seq Z| E))
            (|set.in POW (Z x Z)| s (|injections Z Z| NATURAL1 E)))))
  :named |ax.iseq Z|))
(define-const MAXINT |Z| 2147483647)
(declare-fun |functions.partial (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((e1 |POW (Z x Z)|) (e2 |POW POW Z|))
    (forall ((f |POW ((Z x Z) x POW Z)|))
      (= (|set.in POW ((Z x Z) x POW Z)| f (|functions.partial (Z x Z) POW Z| e1 e2))
         (and (|set.in POW ((Z x Z) x POW Z)| f (|relations (Z x Z) POW Z| e1 e2))
              (|set.in POW ((Z x Z) x POW Z)| f (|functions (Z x Z) POW Z| e1 e2))))))
  :named |ax:def.pfun ((Z x Z) x POW Z)|)
)
(declare-fun |relations.total (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW POW Z|))
    (forall ((f |POW ((Z x Z) x POW Z)|))
      (= (|set.in POW ((Z x Z) x POW Z)| f (|relations.total (Z x Z) POW Z| X Y))
         (= (|rel.domain (Z x Z) POW Z| f) X))))
 :named |ax:set.in.relations.total ((Z x Z) x POW Z)|))
(declare-fun |functions.partial (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((e1 |POW (Z x Z)|) (e2 |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|functions.partial (Z x Z) Z| e1 e2))
         (and (|set.in POW ((Z x Z) x Z)| f (|relations (Z x Z) Z| e1 e2))
              (|set.in POW ((Z x Z) x Z)| f (|functions (Z x Z) Z| e1 e2))))))
  :named |ax:def.pfun ((Z x Z) x Z)|)
)
(declare-fun |relations.total (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((X |POW (Z x Z)|) (Y |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|relations.total (Z x Z) Z| X Y))
         (= (|rel.domain (Z x Z) Z| f) X))))
 :named |ax:set.in.relations.total ((Z x Z) x Z)|))
(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (@ p x))))
  :named |ax:set.in.intent (Z x Z)|))
(define-const MININT |Z| (- 2147483648))
(declare-const s317 |POW (Z x Z)|)
(declare-const s592 |POW Z|)
(declare-const s249 |POW (Z x Z)|)
(declare-const s346 |POW (Z x Z)|)
(declare-const s357 |POW (Z x Z)|)
(declare-const s581 |POW Z|)
(declare-const s584 |POW Z|)
(declare-const s618 |POW Z|)
(declare-const s617 |POW Z|)
(declare-const s586 |POW (Z x Z)|)
(declare-const s520 |POW (Z x Z)|)
(declare-const s591 |POW Z|)
(declare-const s598 |POW Z|)
(declare-const s606 |POW Z|)
(declare-const s338 |POW (Z x Z)|)
(declare-const s339 |POW (Z x Z)|)
(declare-const s363 |POW (Z x Z)|)
(declare-const s607 |POW Z|)
(declare-const s610 |POW (Z x Z)|)
(declare-const s502 |POW (Z x Z)|)
(declare-const s542 |POW Z|)
(declare-const s328 |POW ((Z x Z) x Z)|)
(declare-const s496 |POW (Z x Z)|)
(declare-const s550 |POW (Z x Z)|)
(declare-const s495 |POW (Z x Z)|)
(declare-const s110 |POW Z|)
(declare-const s348 |POW (Z x POW Z)|)
(declare-const s390 |Z|)
(declare-const s227 |POW Z|)
(declare-const s487 |POW (Z x Z)|)
(declare-const s511 |POW (Z x Z)|)
(declare-const s485 |POW (Z x Z)|)
(declare-const s213 |Z|)
(declare-const s282 |Z|)
(declare-const s566 |POW Z|)
(declare-const s616 |POW Z|)
(declare-const s480 |POW (Z x Z)|)
(declare-const s594$1 |POW (Z x Z)|)
(declare-const s200 |POW Z|)
(declare-const s12 |POW Z|)
(declare-const s592$1 |POW Z|)
(declare-const s493 |POW (Z x Z)|)
(declare-const s322 |POW ((Z x Z) x Z)|)
(declare-const s221 |Z|)
(declare-const s479 |POW (Z x Z)|)
(declare-const s140 |POW Z|)
(declare-const s162 |POW ((Z x Z) x POW Z)|)
(declare-const s8 |Z|)
(declare-const s450 |POW (Z x POW Z)|)
(declare-const s549 |POW (Z x Z)|)
(declare-const s145 |Z|)
(declare-const s442 |POW (Z x Z)|)
(declare-const s449 |POW (Z x Z)|)
(declare-const s9 |Z|)
(declare-const s295 |POW ((Z x Z) x POW Z)|)
(declare-const s167 |POW (Z x Z)|)
(declare-const s508 |POW (Z x Z)|)
(declare-const s255 |POW Z|)
(declare-const s602$1 |POW (Z x Z)|)
(declare-const s580 |POW Z|)
(declare-const s615 |POW Z|)
(declare-const s447 |POW Z|)
(declare-const s269 |Z|)
(declare-const s539 |POW (Z x Z)|)
(declare-const s488 |POW (Z x Z)|)
(declare-const s534 |POW Z|)
(declare-const s444 |POW ((Z x Z) x Z)|)
(declare-const s104 |POW Z|)
(declare-const s412 |Z|)
(declare-const s545 |POW (Z x Z)|)
(declare-const s361 |POW (Z x POW Z)|)
(declare-const s160 |POW ((Z x Z) x Z)|)
(declare-const s271 |Z|)
(declare-const s529 |POW Z|)
(declare-const s446 |POW ((Z x Z) x Z)|)
(declare-const s611 |POW (Z x Z)|)
(declare-const s397 |Z|)
(declare-const s410 |Z|)
(declare-const s419 |Z|)
(declare-const s316 |POW Z|)
(declare-const s358 |POW (Z x POW Z)|)
(declare-const s273 |Z|)
(declare-const s613$1 |POW (Z x Z)|)
(declare-const s283 |POW (Z x Z)|)
(declare-const s351 |POW Z|)
(declare-const s272 |POW Z|)
(declare-const s352 |POW (Z x POW Z)|)
(declare-const s212 |POW Z|)
(declare-const s471 |POW (Z x Z)|)
(declare-const s333 |POW (Z x Z)|)
(declare-const s596$1 |POW Z|)
(declare-const s349 |POW (Z x Z)|)
(declare-const s499 |POW (Z x Z)|)
(declare-const s331 |POW ((Z x Z) x Z)|)
(declare-const s470 |POW (Z x Z)|)
(declare-const s196 |POW (Z x Z)|)
(declare-const s330 |POW ((Z x Z) x Z)|)
(declare-const s281 |POW Z|)
(declare-const s578 |POW (Z x Z)|)
(declare-const s600 |POW (Z x Z)|)
(declare-const s279 |POW (Z x Z)|)
(declare-const s329 |POW Z|)
(declare-const s577 |POW Z|)
(declare-const s350 |POW (Z x Z)|)
(declare-const s327 |POW ((Z x Z) x Z)|)
(declare-const s326 |POW ((Z x Z) x Z)|)
(declare-const s589 |POW Z|)
(declare-const s598$1 |POW Z|)
(declare-const s486 |POW Z|)
(declare-const s467 |POW Z|)
(declare-const s497 |POW Z|)
(declare-const s325 |POW ((Z x Z) x Z)|)
(declare-const s11 |Z|)
(declare-const s299 |POW Z|)
(declare-const s324 |POW ((Z x Z) x Z)|)
(declare-const s435 |Z|)
(declare-const s402 |Z|)
(declare-const s631 |Z|)
(declare-const s287 |POW Z|)
(declare-const s565 |POW Z|)
(declare-const s492 |POW (Z x Z)|)
(declare-const s209 |POW Z|)
(declare-const s563 |POW (Z x Z)|)
(declare-const s516 |POW (Z x Z)|)
(declare-const s366 |POW (Z x Z)|)
(declare-const s340 |POW Z|)
(declare-const s323 |POW ((Z x Z) x Z)|)
(declare-const s506 |POW (Z x Z)|)
(declare-const s192 |POW Z|)
(declare-const s132 |POW Z|)
(declare-const s179 |POW ((Z x Z) x Z)|)
(declare-const s408 |Z|)
(declare-const s504 |POW (Z x Z)|)
(declare-const s509 |POW (Z x Z)|)
(declare-const s177 |POW ((Z x Z) x Z)|)
(declare-const s256 |Z|)
(declare-const s503 |POW (Z x Z)|)
(declare-const s174 |POW (Z x Z)|)
(declare-const s178 |POW ((Z x Z) x Z)|)
(declare-const s168 |POW (Z x Z)|)
(declare-const s294 |POW Z|)
(declare-const s184 |POW Z|)
(declare-const s172 |POW ((Z x Z) x Z)|)
(declare-const s576 |POW Z|)
(declare-const s483 |POW (Z x Z)|)
(declare-const s289 |POW (Z x Z)|)
(declare-const s404 |Z|)
(declare-const s426 |Z|)
(declare-const s133 |POW Z|)
(declare-const s601 |POW (Z x Z)|)
(declare-const s141 |Z|)
(declare-const s170 |POW ((Z x Z) x Z)|)
(declare-const s482 |POW (Z x Z)|)
(declare-const s307 |POW (Z x Z)|)
(declare-const s604$1 |POW (Z x Z)|)
(declare-const s166 |POW ((Z x Z) x POW Z)|)
(declare-const s461 |Z|)
(declare-const s383 |Z|)
(declare-const s612 |POW (Z x Z)|)
(declare-const s143 |POW Z|)
(declare-const s468 |POW (Z x Z)|)
(declare-const s609$1 |POW (Z x Z)|)
(declare-const s540 |POW (Z x Z)|)
(declare-const s10 |Z|)
(declare-const s546 |POW (Z x Z)|)
(declare-const s354 |POW (Z x Z)|)
(declare-const s548 |POW (Z x Z)|)
(declare-const s225 |Z|)
(declare-const s144 |Z|)
(declare-const s7 |POW Z|)
(declare-const s332 |POW Z|)
(declare-const s386 |Z|)
(declare-const s518 |POW (Z x Z)|)
(declare-const s532 |Z|)
(declare-const s443 |POW (Z x Z)|)
(declare-const s551 |POW Z|)
(declare-const s321 |POW ((Z x Z) x Z)|)
(declare-const s406 |Z|)
(declare-const s453 |POW Z|)
(declare-const s26 |POW Z|)
(declare-const s538 |POW Z|)
(declare-const s619$1 |POW (Z x Z)|)
(declare-const s169 |POW ((Z x Z) x Z)|)
(declare-const s570 |POW Z|)
(declare-const s530 |POW (Z x Z)|)
(declare-const s460 |POW (Z x Z)|)
(declare-const s474 |POW (Z x Z)|)
(declare-const s597$1 |POW (Z x Z)|)
(declare-const s603$1 |POW (Z x Z)|)
(declare-const s286 |POW (Z x Z)|)
(declare-const s593 |POW Z|)
(declare-const s501 |POW (Z x Z)|)
(declare-const s459 |POW (Z x POW Z)|)
(declare-const s478 |POW (Z x Z)|)
(declare-const s466 |POW (Z x Z)|)
(declare-const s590 |POW Z|)
(declare-const s405 |Z|)
(declare-const s473 |POW (Z x Z)|)
(declare-const s312 |POW ((Z x Z) x POW Z)|)
(declare-const s454 |POW Z|)
(declare-const s571 |POW Z|)
(declare-const s36 |POW Z|)
(declare-const s438 |Z|)
(declare-const s191 |POW Z|)
(declare-const s579 |POW Z|)
(declare-const s108 |POW Z|)
(declare-const s475 |POW (Z x Z)|)
(declare-const s335 |POW ((Z x Z) x Z)|)
(declare-const s217 |POW Z|)
(declare-const s173 |POW (Z x Z)|)
(declare-const s597 |POW (Z x Z)|)
(declare-const s469 |POW (Z x Z)|)
(declare-const s462 |POW (Z x Z)|)
(declare-const s216 |POW Z|)
(declare-const s175 |POW ((Z x Z) x Z)|)
(declare-const s490 |POW (Z x Z)|)
(declare-const s491 |POW (Z x Z)|)
(declare-const s541 |POW (Z x Z)|)
(declare-const s345 |POW (Z x POW Z)|)
(declare-const s528 |POW (Z x Z)|)
(declare-const s369 |POW (Z x Z)|)
(declare-const s609 |POW (Z x Z)|)
(declare-const s257 |POW (Z x Z)|)
(declare-const s290 |POW (Z x POW Z)|)
(declare-const s380 |Z|)
(declare-const s602 |POW (Z x Z)|)
(declare-const s615$1 |POW Z|)
(declare-const s456 |POW (Z x Z)|)
(declare-const s513 |POW (Z x Z)|)
(declare-const s587 |POW Z|)
(declare-const s291 |POW (Z x Z)|)
(declare-const s552 |POW Z|)
(declare-const s305 |POW ((Z x Z) x Z)|)
(declare-const s599$1 |POW Z|)
(declare-const s604 |POW (Z x Z)|)
(declare-const s585 |POW (Z x Z)|)
(declare-const s51 |Z|)
(declare-const s599 |POW Z|)
(declare-const s457 |POW Z|)
(declare-const s320 |POW Z|)
(declare-const s608$1 |POW (Z x Z)|)
(declare-const s515 |POW (Z x Z)|)
(declare-const s308 |POW Z|)
(declare-const s403 |Z|)
(declare-const s547 |POW (Z x Z)|)
(declare-const s382 |Z|)
(declare-const s610$1 |POW (Z x Z)|)
(declare-const s477 |POW (Z x Z)|)
(declare-const s222 |POW (Z x Z)|)
(declare-const s367 |POW Z|)
(declare-const s347 |POW (Z x Z)|)
(declare-const s180 |POW ((Z x Z) x Z)|)
(declare-const s452 |POW (Z x Z)|)
(declare-const s284 |POW Z|)
(declare-const s428 |Z|)
(declare-const s498 |POW (Z x Z)|)
(declare-const s494 |POW (Z x Z)|)
(declare-const s455 |POW ((Z x Z) x Z)|)
(declare-const s394 |Z|)
(declare-const s481 |POW (Z x Z)|)
(declare-const s458 |POW (Z x Z)|)
(declare-const s106 |POW Z|)
(declare-const s176 |POW ((Z x Z) x Z)|)
(declare-const s223 |POW Z|)
(declare-const s138 |POW Z|)
(declare-const s379 |POW (Z x Z)|)
(declare-const s500 |POW (Z x Z)|)
(declare-const s298 |POW ((Z x Z) x Z)|)
(declare-const s360 |POW (Z x Z)|)
(declare-const s49 |POW Z|)
(declare-const s524 |POW (Z x Z)|)
(declare-const s159 |POW ((Z x Z) x Z)|)
(declare-const s142 |POW Z|)
(declare-const s603 |POW (Z x Z)|)
(declare-const s164 |POW ((Z x Z) x POW Z)|)
(declare-const s619 |POW (Z x Z)|)
(declare-const s613 |POW (Z x Z)|)
(declare-const s206 |POW Z|)
(declare-const s608 |POW (Z x Z)|)
(declare-const s531 |POW (Z x Z)|)
(declare-const s228 |Z|)
(declare-const s522 |POW Z|)
(declare-const s519 |POW Z|)
(declare-const s472 |POW (Z x Z)|)
(declare-const s618$1 |POW Z|)
(declare-const s617$1 |POW Z|)
(declare-const s122 |POW Z|)
(declare-const s527 |POW (Z x Z)|)
(declare-const s440 |POW (Z x Z)|)
(declare-const s514 |POW (Z x Z)|)
(declare-const s229 |POW Z|)
(declare-const s512 |POW (Z x Z)|)
(declare-const s183 |POW Z|)
(declare-const s432 |Z|)
(declare-const s194 |POW Z|)
(declare-const s371 |POW Z|)
(declare-const s510 |POW (Z x Z)|)
(declare-const s411 |Z|)
(declare-const s399 |Z|)
(declare-const s596 |POW Z|)
(declare-const s507 |POW (Z x Z)|)
(declare-const s313 |POW (Z x Z)|)
(declare-const s582 |POW Z|)
(declare-const s489 |POW Z|)
(declare-const s368 |POW (Z x Z)|)
(declare-const s416 |Z|)
(declare-const s611$1 |POW (Z x Z)|)
(declare-const s612$1 |POW (Z x Z)|)
(declare-const s285 |Z|)
(declare-const s300 |POW (Z x Z)|)
(declare-const s536 |POW Z|)
(declare-const s353 |POW (Z x Z)|)
(declare-const s337 |POW (Z x POW Z)|)
(declare-const s422 |Z|)
(declare-const s355 |POW (Z x POW Z)|)
(declare-const s77 |Z|)
(declare-const s311 |POW ((Z x Z) x Z)|)
(declare-const s413 |Z|)
(declare-const s224 |POW (Z x Z)|)
(declare-const s247 |POW Z|)
(declare-const s163 |POW ((Z x Z) x POW Z)|)
(declare-const s523 |POW (Z x Z)|)
(declare-const s484 |POW (Z x Z)|)
(declare-const s219 |POW (Z x Z)|)
(declare-const s505 |POW (Z x Z)|)
(declare-const s376 |POW Z|)
(declare-const s218 |POW (Z x Z)|)
(declare-const s296 |POW (Z x Z)|)
(declare-const s190 |POW (Z x Z)|)
(declare-const s241 |POW Z|)
(declare-const s301 |POW (Z x Z)|)
(declare-const s616$1 |POW Z|)
(declare-const s525 |POW Z|)
(declare-const s384 |Z|)
(declare-const s556 |POW Z|)
(declare-const s476 |POW (Z x Z)|)
(declare-const s74 |POW Z|)
(declare-const s266 |Z|)
(declare-const s569 |POW (Z x Z)|)
(declare-const s517 |POW (Z x Z)|)
(declare-const s161 |POW ((Z x Z) x Z)|)
(declare-const s146 |POW Z|)
(declare-const s314 |POW (Z x Z)|)
(declare-const s521 |POW (Z x Z)|)
(declare-const s302 |POW (Z x Z)|)
(declare-const s171 |POW ((Z x Z) x Z)|)
(declare-const s451 |POW (Z x Z)|)
(declare-const s445 |POW Z|)
(declare-const s293 |POW ((Z x Z) x Z)|)
(declare-const s165 |POW ((Z x Z) x POW Z)|)
(declare-const s583 |POW Z|)
(declare-const s594 |POW (Z x Z)|)
(declare-const s526 |POW (Z x Z)|)
(declare-const s315 |POW (Z x Z)|)
(declare-const s309 |POW (Z x Z)|)
(declare-const s537 |POW Z|)
(declare-const s306 |POW Z|)
(declare-const s304 |POW (Z x Z)|)
(declare-const s303 |POW (Z x Z)|)
(declare-const s130 |POW Z|)
(declare-const s336 |POW (Z x Z)|)
(declare-const s226 |POW (Z x Z)|)
(declare-const s370 |POW Z|)
(declare-const s334 |POW Z|)
(declare-const s116 |POW Z|)
(declare-const s288 |Z|)
(declare-const s231 |POW (Z x Z)|)
(declare-const s533 |POW Z|)
(declare-const s189 |POW Z|)
(declare-const s567 |POW Z|)
(declare-const s374 |POW Z|)
(declare-const s378 |POW Z|)
(declare-const s207 |Z|)
(declare-const s125 |POW Z|)
(declare-const s388 |Z|)
(declare-const s195 |Z|)
(declare-const s210 |Z|)
(declare-const s109 |POW Z|)
(declare-const s356 |POW (Z x Z)|)
(declare-const s280 |POW Z|)
(declare-const s398 |Z|)
(declare-const s243 |POW (Z x Z)|)
(declare-const s129 |POW Z|)
(declare-const s202 |POW (Z x Z)|)
(declare-const s373 |POW Z|)
(declare-const s318 |POW Z|)
(declare-const s593$1 |POW Z|)
(declare-const s208 |POW (Z x Z)|)
(declare-const s564 |POW Z|)
(declare-const s214 |POW (Z x Z)|)
(declare-const s535 |POW Z|)
(declare-const s274 |POW (Z x Z)|)
(declare-const s201 |Z|)
(declare-const s372 |POW Z|)
(declare-const s429 |Z|)
(declare-const s407 |Z|)
(declare-const s186 |POW Z|)
(declare-const s158 |POW Z|)
(declare-const s364 |POW (Z x Z)|)
(declare-const s220 |POW Z|)
(declare-const s211 |POW (Z x Z)|)
(declare-const s259 |POW (Z x Z)|)
(declare-const s185 |POW (Z x Z)|)
(declare-const s434 |Z|)
(declare-const s362 |POW (Z x Z)|)
(declare-const s588 |POW Z|)
(declare-const s230 |Z|)
(declare-const s120 |POW Z|)
(declare-const s319 |POW (Z x Z)|)
(declare-const s242 |Z|)
(declare-const s448 |POW (Z x Z)|)
(declare-const s395 |Z|)
(declare-const s258 |Z|)
(declare-const s157 |POW ((Z x Z) x Z)|)
(declare-const s268 |POW Z|)
(declare-const s400 |Z|)
(declare-const s605 |POW (Z x Z)|)
(declare-const s375 |POW (Z x Z)|)
(declare-const s377 |POW (Z x Z)|)
(declare-const s595 |POW Z|)
(declare-const s188 |POW (Z x Z)|)
(declare-const s391 |Z|)
(declare-const s392 |Z|)
(declare-const s393 |Z|)
(declare-const s187 |POW (Z x Z)|)
(declare-const s396 |Z|)
(declare-const s401 |Z|)
(declare-const s381 |Z|)
(declare-const s409 |Z|)
(declare-const s433 |Z|)
(declare-const s437 |Z|)
(declare-const s439 |Z|)
(declare-const s124 |POW Z|)
(declare-const s365 |POW (Z x Z)|)
(declare-const s441 |POW Z|)
(declare-const s61 |POW Z|)
(declare-const s270 |POW Z|)
(declare-const s568 |POW Z|)
(declare-const s595$1 |POW Z|)
(declare-const s573 |POW Z|)
(declare-const s600$1 |POW (Z x Z)|)
(declare-const s614$1 |POW Z|)
(declare-const s601$1 |POW (Z x Z)|)
(declare-const s605$1 |POW (Z x Z)|)
(declare-const s606$1 |POW Z|)
(declare-const s607$1 |POW Z|)
(declare-const s614 |POW Z|)
(declare-const s591$1 |POW Z|)
(declare-const s574 |POW Z|)
(declare-const s543 |POW Z|)
(declare-const s359 |POW (Z x Z)|)
(declare-const s544 |POW Z|)
(declare-const s553 |POW Z|)
(declare-const s554 |POW Z|)
(declare-const s572 |POW Z|)
(declare-const s344 |POW (Z x Z)|)
(declare-const s555 |POW Z|)
(declare-const s131 |POW Z|)
(declare-const s560 |POW Z|)
(declare-const s267 |POW (Z x Z)|)
(declare-const s385 |Z|)
(declare-const s128 |POW Z|)
(declare-const s430 |Z|)
(declare-const s421 |Z|)
(declare-const s418 |Z|)
(declare-const s248 |Z|)
(declare-const s427 |Z|)
(declare-const s387 |Z|)
(declare-const s389 |Z|)
(declare-const s415 |Z|)
(declare-const s414 |Z|)
(declare-const s417 |Z|)
(declare-const s423 |Z|)
(declare-const s424 |Z|)
(declare-const s425 |Z|)
(declare-const s420 |Z|)
(declare-const s436 |Z|)
(declare-const s623$1 |Z|)
(declare-const s431 |Z|)
(declare-fun |min| (|POW Z|) |Z|)
(assert (!
  (forall ((s |POW Z|))
    (=> (not (= s |set.empty Z|)) (|set.in Z| (|min| s) s)))
  :named |ax.min.is.member|))
 (assert (!
   (forall ((s |POW Z|))
     (forall ((e |Z|))
        (=> (|set.in Z| e s) (<= (|min| s) e))))
  :named |ax.min.is.ge|))
(declare-fun |max| (|POW Z|) |Z|)
(assert (!
  (forall ((s |POW Z|))
    (=> (not (= s |set.empty Z|)) (|set.in Z| (|max| s) s)))
  :named |ax.max.is.member|))
(assert (!
  (forall ((s |POW Z|))
    (forall ((e |Z|))
      (=> (|set.in Z| e s) (<= e (|max| s)))))
    :named |ax.max.is.ge|))
(declare-const NATURAL |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NATURAL) (<= 0 e)))
  :named |ax.set.in.NATURAL|))
(declare-fun |injections.partial Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|injections.partial Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.partial Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|injections Z Z| e1 e2))))))
  :named |ax:def.pinj (Z x Z)|))
(declare-fun |fun.eval Z POW Z| (|POW (Z x POW Z)| |Z|) |POW Z|)
(assert (!
  (forall ((f |POW (Z x POW Z)|)(x |Z|))
    (|set.in (Z x POW Z)| (maplet x (|fun.eval Z POW Z| f x)) f))
  :named |ax.fun.eval (Z x POW Z)|))
(declare-fun |functions.total Z POW Z| (|POW Z| |POW POW Z|) |POW POW (Z x POW Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW POW Z|))
    (forall ((f |POW (Z x POW Z)|))
      (= (|set.in POW (Z x POW Z)| f (|functions.total Z POW Z| e1 e2))
         (and (|set.in POW (Z x POW Z)| f (|functions.partial Z POW Z| e1 e2))
              (|set.in POW (Z x POW Z)| f (|relations.total Z POW Z| e1 e2))))))
  :named |ax:def.tfun (Z x POW Z)|))
(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))
(declare-fun |rel.image (Z x Z) Z| (|POW ((Z x Z) x Z)| |POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW ((Z x Z) x Z)|) (s |POW (Z x Z)|) (x |Z|))
    (= (|set.in Z| x (|rel.image (Z x Z) Z| r s))
       (exists ((y |(Z x Z)|)) (and (|set.in (Z x Z)| y s) (|set.in ((Z x Z) x Z)| (maplet y x) r)))))
  :named |ax:set.in.image ((Z x Z) x POW ((Z x Z) x Z))|))
(declare-fun |rel.image Z Z| (|POW (Z x Z)| |POW Z|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (s |POW Z|) (x |Z|))
    (= (|set.in Z| x (|rel.image Z Z| r s))
       (exists ((y |Z|)) (and (|set.in Z| y s) (|set.in (Z x Z)| (maplet y x) r)))))
  :named |ax:set.in.image (Z x POW (Z x Z))|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (@ p x))))
  :named |ax:set.in.intent Z|))
(declare-fun |rel.restrict.dom Z Z| (|POW Z| |POW (Z x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |POW Z|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|rel.restrict.dom Z Z| e r))
        (and (|set.in (Z x Z)| x r) (|set.in Z| (fst x) e)))))
  :named |ax:set.in.restrict.dom (Z x Z)|))
(declare-fun |perm Z| (|POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((E |POW Z|)(s |POW (Z x Z)|))
    (= (|set.in POW (Z x Z)| s (|perm Z| E))
       (and (|set.in POW (Z x Z)| s (|iseq Z| E))
            (|set.in POW (Z x Z)| s (|surjections Z Z| NATURAL1 E)))))
  :named |ax.perm Z|))
(declare-const NAT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT) (and (<= 0 e) (<= e MAXINT))))
  :named |ax.set.in.NAT|))
(declare-fun |fun.eval (Z x Z) POW Z| (|POW ((Z x Z) x POW Z)| |(Z x Z)|) |POW Z|)
(assert (!
  (forall ((f |POW ((Z x Z) x POW Z)|)(x |(Z x Z)|))
    (|set.in ((Z x Z) x POW Z)| (maplet x (|fun.eval (Z x Z) POW Z| f x)) f))
  :named |ax.fun.eval ((Z x Z) x POW Z)|))
(declare-fun |functions.total (Z x Z) POW Z| (|POW (Z x Z)| |POW POW Z|) |POW POW ((Z x Z) x POW Z)|)
(assert (!
  (forall ((e1 |POW (Z x Z)|) (e2 |POW POW Z|))
    (forall ((f |POW ((Z x Z) x POW Z)|))
      (= (|set.in POW ((Z x Z) x POW Z)| f (|functions.total (Z x Z) POW Z| e1 e2))
         (and (|set.in POW ((Z x Z) x POW Z)| f (|functions.partial (Z x Z) POW Z| e1 e2))
              (|set.in POW ((Z x Z) x POW Z)| f (|relations.total (Z x Z) POW Z| e1 e2))))))
  :named |ax:def.tfun ((Z x Z) x POW Z)|))
(declare-fun |functions.total (Z x Z) Z| (|POW (Z x Z)| |POW Z|) |POW POW ((Z x Z) x Z)|)
(assert (!
  (forall ((e1 |POW (Z x Z)|) (e2 |POW Z|))
    (forall ((f |POW ((Z x Z) x Z)|))
      (= (|set.in POW ((Z x Z) x Z)| f (|functions.total (Z x Z) Z| e1 e2))
         (and (|set.in POW ((Z x Z) x Z)| f (|functions.partial (Z x Z) Z| e1 e2))
              (|set.in POW ((Z x Z) x Z)| f (|relations.total (Z x Z) Z| e1 e2))))))
  :named |ax:def.tfun ((Z x Z) x Z)|))
(declare-fun |bijections.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|bijections.total Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.total Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|bijections Z Z| e1 e2))))))
  :named |ax:def.tbij (Z x Z)|))
(declare-const |set.empty (Z x Z)| |POW (Z x Z)|)
(assert (!
  (forall ((e |(Z x Z)|)) (not (|set.in (Z x Z)| e |set.empty (Z x Z)|)))
  :named |ax.set.in.empty (Z x Z)|))
(declare-fun |id Z| (|POW Z|) |POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|))
    (= (|id Z| X)
       (|set.intent (Z x Z)|
         (lambda ((x |(Z x Z)|))
           (and (|set.in Z| (fst x) X) (= (fst x) (snd x)))))))
  :named |def.id Z|))
(declare-fun |set.inter (Z x Z)| (|POW (Z x Z)| |POW (Z x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((e |(Z x Z)|) (s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (= (|set.in (Z x Z)| e (|set.inter (Z x Z)| s t))
       (and (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t))))
  :named |ax.set.in.inter (Z x Z)|))
(declare-fun |fun.eval Z Z| (|POW (Z x Z)| |Z|) |Z|)
(assert (!
  (forall ((f |POW (Z x Z)|)(x |Z|))
    (|set.in (Z x Z)| (maplet x (|fun.eval Z Z| f x)) f))
  :named |ax.fun.eval (Z x Z)|))
(declare-fun |set.diff Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.diff Z| s t))
       (and (|set.in Z| e s) (not (|set.in Z| e t)))))
  :named |ax.set.in.diff Z|))
(declare-fun |set.inter Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.inter Z| s t))
       (and (|set.in Z| e s) (|set.in Z| e t))))
  :named |ax.set.in.inter Z|))
(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))
(declare-const NAT1 |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT1) (and (<= 1 e) (<= e MAXINT))))
  :named |ax.set.in.NAT1|))
(declare-fun |injections.total Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((e1 |POW Z|) (e2 |POW Z|))
    (forall ((f |POW (Z x Z)|))
      (= (|set.in POW (Z x Z)| f (|injections.total Z Z| e1 e2))
         (and (|set.in POW (Z x Z)| f (|functions.total Z Z| e1 e2))
              (|set.in POW (Z x Z)| f (|injections Z Z| e1 e2))))))
 :named |ax:def.tinj (Z x Z)|))
(declare-fun |~ Z Z| (|POW (Z x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((R |POW (Z x Z)|))
    (= (|~ Z Z| R)
       (|set.intent (Z x Z)|
         (lambda ((x |(Z x Z)|))
           (|set.in (Z x Z)| (maplet (snd x) (fst x)) R)))))
  :named |def.reverse (Z x Z)|))
(declare-fun |set.union Z| (|POW Z| |POW Z|) |POW Z|)
(assert (!
  (forall ((e |Z|) (s |POW Z|) (t |POW Z|))
    (= (|set.in Z| e (|set.union Z| s t))
       (or (|set.in Z| e s) (|set.in Z| e t))))
  :named |ax.set.in.union Z|))
(define-sort |BOOL| () Bool)
(assert (!
  (|set.in Z| s631 s138)
  :named |Local_Hyp:0|))
(assert (!
  (|set.in Z| s631 s457)
  :named |Local_Hyp:1|))
(assert (!
  (not
  (|set.in Z| s631 (|rel.domain Z Z| s456)))
  :named |Local_Hyp:2|))
(assert (!
  (= s380 s51)
  :named |Local_Hyp:3|))
(assert (!
  (not
  (|set.in Z| s631 (|rel.domain Z Z| s470)))
  :named |Local_Hyp:9|))
(assert (!
  (= s216 (|set.intent Z| (lambda ((_c0 |Z|)) (or (= _c0 s10)(= _c0 s11)))))
  :named |Define:ctx:167|))
(assert (!
  (= s217 (|set.intent Z| (lambda ((_c0 |Z|)) (or (= _c0 s9)(= _c0 s10)(= _c0 s11)))))
  :named |Define:ctx:170|))
(assert (!
  (forall
  ((s310 |Z|))
  (=>
    (|set.in Z| s310 s294)
    (|set.subseteq (Z x Z)| (|set.product Z Z| (|rel.image (Z x Z) Z| s293 (|set.intent (Z x Z)| (lambda ((_c0 |(Z x Z)|)) (or (= _c0 (maplet s310 s10))(= _c0 (maplet s310 s11)))))) (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s310)))) (|rel.domain (Z x Z) Z| s298))))
  :named |Define:ctx:303|))
(assert (!
  (|set.in Z| s380 s49)
  :named |Define:ctx:397|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s455 (|functions.partial (Z x Z) Z| (|set.product Z Z| s284 s26) s216))
  :named |Define:ctx:508|))
(assert (!
  (|set.in POW (Z x Z)| s456 (|functions.partial Z Z| s457 s217))
  :named |Define:ctx:509|))
(assert (!
  (|set.in POW (Z x Z)| s458 (|relations Z Z| s457 s284))
  :named |Define:ctx:510|))
(assert (!
  (|set.in POW (Z x POW Z)| s459 (|functions.total Z POW Z| s457 (|sub-sets Z| s191)))
  :named |Define:ctx:511|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s457)
    (= (|rel.image Z Z| s458 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s460 (|fun.eval Z POW Z| s459 s292)))))
  :named |Define:ctx:513|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s457)
    (|set.subseteq Z| (|fun.eval Z POW Z| s459 s292) (|rel.domain Z Z| s460))))
  :named |Define:ctx:514|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s457)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s459 s292) s460) (|injections.partial Z Z| NATURAL s284))))
  :named |Define:ctx:515|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s457)
      (not
        (= (|fun.eval Z POW Z| s459 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s459 s292) (|interval| (|min| (|fun.eval Z POW Z| s459 s292)) (|max| (|fun.eval Z POW Z| s459 s292))))))
  :named |Define:ctx:516|))
(assert (!
  (|set.subseteq Z| s457 s138)
  :named |Define:ctx:517|))
(assert (!
  (|set.in Z| s461 s138)
  :named |Define:ctx:518|))
(assert (!
  (not
  (|set.in Z| s461 s457))
  :named |Define:ctx:519|))
(assert (!
  (|set.in POW (Z x Z)| s462 (|functions.partial Z Z| NAT s138))
  :named |Define:ctx:520|))
(assert (!
  (|set.in POW (Z x Z)| s462 (|perm Z| s457))
  :named |Define:ctx:521|))
(assert (!
  (|set.in POW (Z x Z)| s470 (|functions.partial Z Z| s457 s467))
  :named |Define:ctx:530|))
(assert (!
  (|set.in POW (Z x Z)| s471 (|functions.partial Z Z| s457 s467))
  :named |Define:ctx:531|))
(assert (!
  (|set.in POW (Z x Z)| s472 (|functions.partial Z Z| s457 s467))
  :named |Define:ctx:532|))
(assert (!
  (|set.in POW (Z x Z)| s473 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:533|))
(assert (!
  (|set.in POW (Z x Z)| s474 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:534|))
(assert (!
  (|set.in POW (Z x Z)| s475 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:535|))
(assert (!
  (|set.in POW (Z x Z)| s476 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:536|))
(assert (!
  (|set.in POW (Z x Z)| s477 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:537|))
(assert (!
  (|set.in POW (Z x Z)| s478 (|functions.partial Z Z| s457 s445))
  :named |Define:ctx:538|))
(assert (!
  (|set.in POW (Z x Z)| s608$1 (|functions.partial Z Z| s457 s217))
  :named |Define:imext:17|))
(assert (!
  (|set.in POW (Z x Z)| s609$1 (|functions.partial Z Z| s457 s216))
  :named |Define:imext:18|))
(assert (!
  (|set.in POW (Z x Z)| s545 (|relations Z Z| s457 s216))
  :named |Define:seext:13|))
(assert (!
  (|set.in POW (Z x Z)| s546 (|functions.partial Z Z| s457 s142))
  :named |Define:seext:14|))
(assert (!
  (|set.in POW (Z x Z)| s547 (|functions.partial Z Z| s457 s142))
  :named |Define:seext:15|))
(assert (!
  (|set.in POW (Z x Z)| s548 (|functions.partial Z Z| s457 s142))
  :named |Define:seext:16|))
(assert (!
  (|set.in POW (Z x Z)| s549 (|functions.partial Z Z| s457 s142))
  :named |Define:seext:17|))
(assert (!
  (|set.in POW (Z x Z)| s550 (|relations Z Z| s457 s216))
  :named |Define:seext:18|))
(assert (!
  (|set.subseteq Z| s551 s457)
  :named |Define:seext:19|))
(assert (!
  (|set.subseteq Z| s552 s457)
  :named |Define:seext:20|))
(assert (!
  (|set.in POW (Z x Z)| s569 (|functions.total Z Z| s284 s26))
  :named |Define:seext:35|))
(assert (!
  (|set.in POW (Z x Z)| s608 (|functions.partial Z Z| s457 s217))
  :named |Define:abs:17|))
(assert (!
  (|set.in POW (Z x Z)| s609 (|functions.partial Z Z| s457 s216))
  :named |Define:abs:18|))
(assert (!
  (|set.in POW (Z x Z)| s608 (|functions.partial Z Z| s457 s217))
  :named |Define:abs:54|))
(assert (!
  (|set.in POW (Z x Z)| s609 (|functions.partial Z Z| s457 s216))
  :named |Define:abs:55|))
(assert (!
  (= s142 (|interval| 0 s141))
  :named |Define:ctx:52|))
(assert (!
  (|set.subseteq Z| s143 s142)
  :named |Define:ctx:54|))
(assert (!
  (|set.subseteq Z| s142 s140)
  :named |Define:ctx:55|))
(assert (!
  (|set.subseteq Z| s142 NAT)
  :named |Define:ctx:56|))
(assert (!
  (|set.in Z| s144 s142)
  :named |Define:ctx:60|))
(assert (!
  (not
  (|set.in Z| s145 s142))
  :named |Define:ctx:63|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s159 (|functions.total (Z x Z) Z| (|set.product Z Z| s142 s142) s146))
  :named |Define:ctx:84|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s160 (|functions.partial (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:85|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s161 (|functions.total (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:86|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s162 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s142 s146) (|sub-sets Z| s142)))
  :named |Define:ctx:87|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s163 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s142 s142) (|sub-sets Z| s142)))
  :named |Define:ctx:88|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s164 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s142 s142) (|sub-sets Z| s142)))
  :named |Define:ctx:89|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s165 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s142 s142) (|sub-sets Z| s142)))
  :named |Define:ctx:90|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s166 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s142 s142) (|sub-sets Z| s142)))
  :named |Define:ctx:91|))
(assert (!
  (|set.in POW (Z x Z)| s167 (|relations Z Z| s142 s142))
  :named |Define:ctx:92|))
(assert (!
  (|set.in POW (Z x Z)| s168 (|relations Z Z| s142 s142))
  :named |Define:ctx:93|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s169 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:94|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s170 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:95|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s171 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:96|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s172 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:97|))
(assert (!
  (|set.in POW (Z x Z)| s173 (|relations Z Z| s142 s142))
  :named |Define:ctx:98|))
(assert (!
  (|set.in POW (Z x Z)| s174 (|relations Z Z| s142 s142))
  :named |Define:ctx:99|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s175 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:100|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s176 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:101|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s177 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:102|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s178 (|relations (Z x Z) Z| (|set.product Z Z| s142 s146) s142))
  :named |Define:ctx:103|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s179 (|functions.total (Z x Z) Z| (|set.product Z Z| s142 s142) s142))
  :named |Define:ctx:104|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s180 (|functions.total (Z x Z) Z| (|set.product Z Z| s142 s142) s142))
  :named |Define:ctx:105|))
(assert (!
  (= (|rel.domain (Z x Z) Z| s160) (|set.product Z Z| s142 (|interval| 0 s141)))
  :named |Define:ctx:106|))
(assert (!
  (|set.subseteq Z| s191 NAT)
  :named |Define:ctx:115|))
(assert (!
  (not
  (= s191 |set.empty Z|))
  :named |Define:ctx:116|))
(assert (!
  (= s191 (|interval| (|min| s191) (|max| s191)))
  :named |Define:ctx:117|))
(assert (!
  (not
  (|set.in Z| MAXINT s191))
  :named |Define:ctx:118|))
(assert (!
  (|set.subseteq Z| s216 s7)
  :named |Define:ctx:165|))
(assert (!
  (not
  (|set.in Z| s8 s216))
  :named |Define:ctx:166|))
(assert (!
  (|set.subseteq Z| s217 s7)
  :named |Define:ctx:168|))
(assert (!
  (not
  (|set.in Z| s8 s217))
  :named |Define:ctx:169|))
(assert (!
  (|set.in POW (Z x Z)| s218 (|bijections.total Z Z| s216 s216))
  :named |Define:ctx:171|))
(assert (!
  (= (|set.inter (Z x Z)| s218 (|id Z| s216)) |set.empty (Z x Z)|)
  :named |Define:ctx:172|))
(assert (!
  (not
  (|set.in Z| (|fun.eval Z Z| s219 s221) s216))
  :named |Define:ctx:174|))
(assert (!
  (|set.in POW (Z x Z)| s222 (|bijections.total Z Z| s223 (|set.diff Z| s7 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s9))))))
  :named |Define:ctx:175|))
(assert (!
  (|set.in POW (Z x Z)| s224 (|bijections.total Z Z| (|set.diff Z| s7 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s9)))) s223))
  :named |Define:ctx:176|))
(assert (!
  (not
  (|set.in Z| (|fun.eval Z Z| s222 s225) s216))
  :named |Define:ctx:178|))
(assert (!
  (|set.subseteq Z| s284 s133)
  :named |Define:ctx:270|))
(assert (!
  (not
  (|set.in Z| s285 s284))
  :named |Define:ctx:272|))
(assert (!
  (|set.in POW (Z x Z)| s286 (|perm Z| s284))
  :named |Define:ctx:274|))
(assert (!
  (|set.in POW (Z x POW Z)| s290 (|functions.total Z POW Z| s200 (|sub-sets Z| s191)))
  :named |Define:ctx:279|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s293 (|relations (Z x Z) Z| (|set.product Z Z| s294 s216) s200))
  :named |Define:ctx:285|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s295 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s294 s216) (|sub-sets Z| s191)))
  :named |Define:ctx:286|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s294)
      (|set.in Z| s297 s216))
    (= (|rel.image (Z x Z) Z| s293 (|set.intent (Z x Z)| (lambda ((_c0 |(Z x Z)|)) (= _c0 (maplet s292 s297))))) (|rel.image Z Z| s296 (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297))))))
  :named |Define:ctx:288|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s294)
      (|set.in Z| s297 s216))
    (|set.subseteq Z| (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297)) (|rel.domain Z Z| s296))))
  :named |Define:ctx:289|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s294)
      (|set.in Z| s297 s216))
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297)) s296) (|injections.partial Z Z| NATURAL s200))))
  :named |Define:ctx:290|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (not
        (= (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297)) |set.empty Z|))
      (|set.in Z| s292 s294)
      (|set.in Z| s297 s216))
    (= (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297)) (|interval| (|min| (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297))) (|max| (|fun.eval (Z x Z) POW Z| s295 (maplet s292 s297)))))))
  :named |Define:ctx:291|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s298 (|functions.partial (Z x Z) Z| (|set.product Z Z| s200 s294) s299))
  :named |Define:ctx:292|))
(assert (!
  (|set.in POW (Z x Z)| s300 (|functions.total Z Z| s200 s216))
  :named |Define:ctx:293|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s311 (|relations (Z x Z) Z| (|set.product Z Z| s229 s216) s229))
  :named |Define:ctx:304|))
(assert (!
  (|set.in POW ((Z x Z) x POW Z)| s312 (|functions.total (Z x Z) POW Z| (|set.product Z Z| s229 s216) (|sub-sets Z| s191)))
  :named |Define:ctx:305|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s229)
      (|set.in Z| s297 s216))
    (= (|rel.image (Z x Z) Z| s311 (|set.intent (Z x Z)| (lambda ((_c0 |(Z x Z)|)) (= _c0 (maplet s292 s297))))) (|rel.image Z Z| s313 (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297))))))
  :named |Define:ctx:307|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s229)
      (|set.in Z| s297 s216))
    (|set.subseteq Z| (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297)) (|rel.domain Z Z| s313))))
  :named |Define:ctx:308|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (|set.in Z| s292 s229)
      (|set.in Z| s297 s216))
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297)) s313) (|injections.partial Z Z| NATURAL s229))))
  :named |Define:ctx:309|))
(assert (!
  (forall
  ((s292 |Z|)(s297 |Z|))
  (=>
    (and
      (not
        (= (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297)) |set.empty Z|))
      (|set.in Z| s292 s229)
      (|set.in Z| s297 s216))
    (= (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297)) (|interval| (|min| (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297))) (|max| (|fun.eval (Z x Z) POW Z| s312 (maplet s292 s297)))))))
  :named |Define:ctx:310|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s321 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s184))
  :named |Define:ctx:315|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s323 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s229))
  :named |Define:ctx:317|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s324 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s209))
  :named |Define:ctx:318|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s325 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s206))
  :named |Define:ctx:319|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s326 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s229))
  :named |Define:ctx:320|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s327 (|functions.total (Z x Z) Z| (|set.product Z Z| s229 s216) s294))
  :named |Define:ctx:321|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s328 (|functions.total (Z x Z) Z| (|set.product Z Z| s229 s216) s329))
  :named |Define:ctx:322|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s330 (|functions.total (Z x Z) Z| (|set.product Z Z| s229 s216) s294))
  :named |Define:ctx:323|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s331 (|functions.total (Z x Z) Z| (|set.product Z Z| s229 s216) s329))
  :named |Define:ctx:324|))
(assert (!
  (|set.subseteq (Z x Z)| s333 (|set.product Z Z| s229 s216))
  :named |Define:ctx:326|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s335 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s216) s212))
  :named |Define:ctx:328|))
(assert (!
  (|set.in POW (Z x POW Z)| s337 (|functions.total Z POW Z| s212 (|sub-sets Z| s191)))
  :named |Define:ctx:330|))
(assert (!
  (forall
  ((s341 |Z|)(s342 |Z|)(s343 |Z|))
  (=>
    (and
      (|set.in Z| s341 s229)
      (|set.in Z| s342 s216)
      (|set.in Z| s343 s216)
      (|set.in (Z x Z)| (maplet s341 s342) (|rel.domain (Z x Z) Z| s324))
      (|set.in (Z x Z)| (maplet s341 s343) (|rel.domain (Z x Z) Z| s324)))
    (= s342 s343)))
  :named |Define:ctx:339|))
(assert (!
  (|set.in POW (Z x POW Z)| s345 (|functions.total Z POW Z| s241 (|sub-sets Z| s191)))
  :named |Define:ctx:341|))
(assert (!
  (|set.in POW (Z x POW Z)| s348 (|functions.total Z POW Z| s241 (|sub-sets Z| s191)))
  :named |Define:ctx:348|))
(assert (!
  (|set.in POW (Z x POW Z)| s352 (|functions.total Z POW Z| s241 (|sub-sets Z| s191)))
  :named |Define:ctx:355|))
(assert (!
  (|set.in POW (Z x POW Z)| s355 (|functions.total Z POW Z| s351 (|sub-sets Z| s191)))
  :named |Define:ctx:362|))
(assert (!
  (|set.in POW (Z x POW Z)| s358 (|functions.total Z POW Z| s351 (|sub-sets Z| s191)))
  :named |Define:ctx:369|))
(assert (!
  (|set.in POW (Z x POW Z)| s361 (|functions.total Z POW Z| s351 (|sub-sets Z| s191)))
  :named |Define:ctx:376|))
(assert (!
  (|set.in Z| s412 s142)
  :named |Define:ctx:458|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s444 (|functions.partial (Z x Z) Z| (|set.product Z Z| s272 s445) s281))
  :named |Define:ctx:493|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s446 (|functions.partial (Z x Z) Z| (|set.product Z Z| s272 s445) s447))
  :named |Define:ctx:494|))
(assert (!
  (|set.in POW (Z x Z)| s449 (|relations Z Z| s255 s284))
  :named |Define:ctx:497|))
(assert (!
  (|set.in POW (Z x Z)| s449 (|relations Z Z| s255 s284))
  :named |Define:ctx:498|))
(assert (!
  (|set.in POW (Z x Z)| s451 (|seq Z| s284))
  :named |Define:ctx:500|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s255)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s450 s292) s451) (|injections.partial Z Z| NATURAL s284))))
  :named |Define:ctx:503|))
(assert (!
  (|set.in POW (Z x Z)| s452 (|functions.total Z Z| s284 s36))
  :named |Define:ctx:505|))
(assert (!
  (|set.subseteq Z| s453 s284)
  :named |Define:ctx:506|))
(assert (!
  (|set.in POW (Z x Z)| s460 (|seq Z| s284))
  :named |Define:ctx:512|))
(assert (!
  (|set.in POW (Z x Z)| s466 (|functions.partial Z Z| s184 s467))
  :named |Define:ctx:527|))
(assert (!
  (|set.in POW (Z x Z)| s468 (|functions.partial Z Z| s184 s445))
  :named |Define:ctx:528|))
(assert (!
  (|set.in POW (Z x Z)| s469 (|functions.partial Z Z| s184 s445))
  :named |Define:ctx:529|))
(assert (!
  (|set.in POW (Z x Z)| s479 (|functions.partial Z Z| s241 s467))
  :named |Define:ctx:539|))
(assert (!
  (|set.in POW (Z x Z)| s480 (|functions.partial Z Z| s241 s445))
  :named |Define:ctx:540|))
(assert (!
  (|set.in POW (Z x Z)| s481 (|functions.partial Z Z| s241 s445))
  :named |Define:ctx:541|))
(assert (!
  (|set.in POW (Z x Z)| s482 (|functions.partial Z Z| s351 s467))
  :named |Define:ctx:542|))
(assert (!
  (|set.in POW (Z x Z)| s483 (|functions.partial Z Z| s351 s445))
  :named |Define:ctx:543|))
(assert (!
  (|set.in POW (Z x Z)| s484 (|functions.partial Z Z| s351 s445))
  :named |Define:ctx:544|))
(assert (!
  (|set.in POW (Z x Z)| s485 (|injections.partial Z Z| s486 s445))
  :named |Define:ctx:545|))
(assert (!
  (|set.in POW (Z x Z)| s487 (|injections.partial Z Z| s486 s445))
  :named |Define:ctx:546|))
(assert (!
  (|set.in POW (Z x Z)| s488 (|functions.partial Z Z| s489 s467))
  :named |Define:ctx:547|))
(assert (!
  (|set.in POW (Z x Z)| s490 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:548|))
(assert (!
  (|set.in POW (Z x Z)| s491 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:549|))
(assert (!
  (|set.in POW (Z x Z)| s492 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:550|))
(assert (!
  (|set.in POW (Z x Z)| s493 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:551|))
(assert (!
  (|set.in POW (Z x Z)| s494 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:552|))
(assert (!
  (|set.in POW (Z x Z)| s495 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:553|))
(assert (!
  (|set.in POW (Z x Z)| s496 (|functions.partial Z Z| s497 s445))
  :named |Define:ctx:554|))
(assert (!
  (|set.in POW (Z x Z)| s498 (|functions.partial Z Z| s497 s445))
  :named |Define:ctx:555|))
(assert (!
  (|set.in POW (Z x Z)| s499 (|functions.partial Z Z| s255 s467))
  :named |Define:ctx:556|))
(assert (!
  (|set.in POW (Z x Z)| s500 (|functions.partial Z Z| s255 s445))
  :named |Define:ctx:557|))
(assert (!
  (|set.in POW (Z x Z)| s501 (|functions.partial Z Z| s255 s445))
  :named |Define:ctx:558|))
(assert (!
  (|set.in POW (Z x Z)| s502 (|functions.partial Z Z| s255 s445))
  :named |Define:ctx:559|))
(assert (!
  (|set.in POW (Z x Z)| s503 (|functions.partial Z Z| s255 s445))
  :named |Define:ctx:560|))
(assert (!
  (|set.in POW (Z x Z)| s504 (|functions.partial Z Z| s284 s467))
  :named |Define:ctx:561|))
(assert (!
  (|set.in POW (Z x Z)| s505 (|functions.partial Z Z| s284 s445))
  :named |Define:ctx:562|))
(assert (!
  (|set.in POW (Z x Z)| s506 (|functions.partial Z Z| s284 s445))
  :named |Define:ctx:563|))
(assert (!
  (|set.in POW (Z x Z)| s507 (|functions.partial Z Z| s284 s445))
  :named |Define:ctx:564|))
(assert (!
  (|set.in POW (Z x Z)| s508 (|functions.partial Z Z| s284 s445))
  :named |Define:ctx:565|))
(assert (!
  (|set.in POW (Z x Z)| s509 (|functions.partial Z Z| s194 s467))
  :named |Define:ctx:566|))
(assert (!
  (|set.in POW (Z x Z)| s510 (|functions.partial Z Z| s194 s445))
  :named |Define:ctx:567|))
(assert (!
  (|set.in POW (Z x Z)| s511 (|functions.partial Z Z| s194 s445))
  :named |Define:ctx:568|))
(assert (!
  (|set.in POW (Z x Z)| s512 (|functions.partial Z Z| s194 s445))
  :named |Define:ctx:569|))
(assert (!
  (|set.in POW (Z x Z)| s513 (|functions.partial Z Z| s194 s445))
  :named |Define:ctx:570|))
(assert (!
  (|set.in POW (Z x Z)| s514 (|functions.partial Z Z| s200 s467))
  :named |Define:ctx:571|))
(assert (!
  (|set.in POW (Z x Z)| s515 (|functions.partial Z Z| s200 s445))
  :named |Define:ctx:572|))
(assert (!
  (|set.in POW (Z x Z)| s516 (|functions.partial Z Z| s200 s445))
  :named |Define:ctx:573|))
(assert (!
  (|set.in POW (Z x Z)| s517 (|functions.partial Z Z| s200 s445))
  :named |Define:ctx:574|))
(assert (!
  (|set.in POW (Z x Z)| s518 (|functions.total Z Z| s519 s467))
  :named |Define:ctx:575|))
(assert (!
  (|set.in POW (Z x Z)| s520 (|functions.total Z Z| s519 s445))
  :named |Define:ctx:576|))
(assert (!
  (|set.in POW (Z x Z)| s521 (|functions.partial Z Z| s522 s467))
  :named |Define:ctx:577|))
(assert (!
  (|set.in POW (Z x Z)| s523 (|functions.partial Z Z| s522 s445))
  :named |Define:ctx:578|))
(assert (!
  (|set.in POW (Z x Z)| s524 (|functions.total Z Z| s525 s467))
  :named |Define:ctx:579|))
(assert (!
  (|set.in POW (Z x Z)| s526 (|functions.total Z Z| s525 s445))
  :named |Define:ctx:580|))
(assert (!
  (|set.in POW (Z x Z)| s527 (|functions.partial Z Z| s489 s445))
  :named |Define:ctx:581|))
(assert (!
  (|set.in POW (Z x Z)| s528 (|functions.partial Z Z| s529 s467))
  :named |Define:ctx:582|))
(assert (!
  (|set.in POW (Z x Z)| s530 (|functions.partial Z Z| s529 s445))
  :named |Define:ctx:583|))
(assert (!
  (|set.in POW (Z x Z)| s531 (|functions.partial Z Z| s529 s445))
  :named |Define:ctx:584|))
(assert (!
  (|set.in POW (Z x Z)| s597$1 (|functions.partial Z Z| s200 s142))
  :named |Define:imext:6|))
(assert (!
  (|set.in POW (Z x Z)| s602$1 (|functions.total Z Z| s184 s142))
  :named |Define:imext:11|))
(assert (!
  (|set.in POW (Z x Z)| s610$1 (|functions.total Z Z| s184 s142))
  :named |Define:imext:19|))
(assert (!
  (|set.in POW (Z x Z)| s611$1 (|functions.total Z Z| s184 s142))
  :named |Define:imext:20|))
(assert (!
  (|set.in POW (Z x Z)| s612$1 (|functions.partial Z Z| s184 s142))
  :named |Define:imext:21|))
(assert (!
  (|set.in POW (Z x Z)| s613$1 (|functions.partial Z Z| s184 s142))
  :named |Define:imext:22|))
(assert (!
  (|set.in Z| s532 s142)
  :named |Define:seext:0|))
(assert (!
  (|set.in POW (Z x Z)| s539 (|functions.partial Z Z| s241 s142))
  :named |Define:seext:7|))
(assert (!
  (|set.in POW (Z x Z)| s540 (|functions.partial Z Z| s241 s142))
  :named |Define:seext:8|))
(assert (!
  (|set.in POW (Z x Z)| s563 (|functions.partial Z Z| s320 s142))
  :named |Define:seext:29|))
(assert (!
  (|set.subseteq Z| s565 s284)
  :named |Define:seext:31|))
(assert (!
  (|set.subseteq Z| s566 s284)
  :named |Define:seext:32|))
(assert (!
  (|set.in POW (Z x Z)| s578 (|functions.partial Z Z| s497 s142))
  :named |Define:seext:44|))
(assert (!
  (|set.in POW (Z x Z)| s585 (|functions.partial Z Z| s489 s142))
  :named |Define:seext:51|))
(assert (!
  (|set.subseteq Z| s191 NATURAL)
  :named |Define:seext:58|))
(assert (!
  (|set.in POW (Z x Z)| s597 (|functions.partial Z Z| s200 s142))
  :named |Define:abs:6|))
(assert (!
  (|set.in POW (Z x Z)| s602 (|functions.total Z Z| s184 s142))
  :named |Define:abs:11|))
(assert (!
  (|set.in POW (Z x Z)| s610 (|functions.total Z Z| s184 s142))
  :named |Define:abs:19|))
(assert (!
  (|set.in POW (Z x Z)| s611 (|functions.total Z Z| s184 s142))
  :named |Define:abs:20|))
(assert (!
  (|set.in POW (Z x Z)| s612 (|functions.partial Z Z| s184 s142))
  :named |Define:abs:21|))
(assert (!
  (|set.in POW (Z x Z)| s613 (|functions.partial Z Z| s184 s142))
  :named |Define:abs:22|))
(assert (!
  (|set.in POW (Z x Z)| s597 (|functions.partial Z Z| s200 s142))
  :named |Define:abs:41|))
(assert (!
  (|set.in POW (Z x Z)| s602 (|functions.total Z Z| s184 s142))
  :named |Define:abs:45|))
(assert (!
  (|set.in POW (Z x Z)| s610 (|functions.total Z Z| s184 s142))
  :named |Define:abs:46|))
(assert (!
  (|set.in POW (Z x Z)| s611 (|functions.total Z Z| s184 s142))
  :named |Define:abs:47|))
(assert (!
  (|set.in POW (Z x Z)| s612 (|functions.partial Z Z| s184 s142))
  :named |Define:abs:48|))
(assert (!
  (|set.in POW (Z x Z)| s613 (|functions.partial Z Z| s184 s142))
  :named |Define:abs:49|))
(assert (!
  (= s608 s608$1)
  :named |Define:inv:11|))
(assert (!
  (= s609 s609$1)
  :named |Define:inv:12|))
(assert (!
  (= s140 (|interval| (- s141) s141))
  :named |Define:ctx:51|))
(assert (!
  (= s143 (|interval| 1 s141))
  :named |Define:ctx:53|))
(assert (!
  (|set.subseteq Z| s143 NAT1)
  :named |Define:ctx:57|))
(assert (!
  (|set.subseteq Z| s140 INT)
  :named |Define:ctx:58|))
(assert (!
  (|set.in Z| s144 s140)
  :named |Define:ctx:59|))
(assert (!
  (not
  (|set.in Z| s144 s143))
  :named |Define:ctx:61|))
(assert (!
  (|set.in Z| s145 s140)
  :named |Define:ctx:62|))
(assert (!
  (= s146 (|interval| (- s141) s141))
  :named |Define:ctx:64|))
(assert (!
  (|set.subseteq Z| s146 INT)
  :named |Define:ctx:65|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s157 (|functions.partial (Z x Z) Z| (|set.product Z Z| s146 s146) s146))
  :named |Define:ctx:82|))
(assert (!
  (|set.subseteq Z| s158 s146)
  :named |Define:ctx:83|))
(assert (!
  (= (|rel.domain (Z x Z) Z| s157) (|set.intent (Z x Z)| (lambda ((_c0 |(Z x Z)|)) (and
  (|set.in Z| (fst _c0) s146)
  (|set.in Z| (snd _c0) s146)
  (>= (snd _c0) 0)))))
  :named |Define:ctx:107|))
(assert (!
  (|set.subseteq Z| s183 s184)
  :named |Define:ctx:108|))
(assert (!
  (|set.in POW (Z x Z)| s185 (|functions.total Z Z| s184 s186))
  :named |Define:ctx:109|))
(assert (!
  (|set.in POW (Z x Z)| s187 (|functions.total Z Z| s184 s186))
  :named |Define:ctx:110|))
(assert (!
  (|set.in POW (Z x Z)| s188 (|functions.partial Z Z| s184 s189))
  :named |Define:ctx:111|))
(assert (!
  (|set.in POW (Z x Z)| s190 (|functions.partial Z Z| s184 s189))
  :named |Define:ctx:112|))
(assert (!
  (|set.subseteq Z| s194 s104)
  :named |Define:ctx:127|))
(assert (!
  (not
  (|set.in Z| s195 s194))
  :named |Define:ctx:129|))
(assert (!
  (|set.in POW (Z x Z)| s196 (|perm Z| s194))
  :named |Define:ctx:131|))
(assert (!
  (|set.subseteq Z| s200 s106)
  :named |Define:ctx:137|))
(assert (!
  (not
  (|set.in Z| s201 s200))
  :named |Define:ctx:139|))
(assert (!
  (|set.in POW (Z x Z)| s202 (|perm Z| s200))
  :named |Define:ctx:141|))
(assert (!
  (|set.subseteq Z| s206 s108)
  :named |Define:ctx:147|))
(assert (!
  (not
  (|set.in Z| s207 s206))
  :named |Define:ctx:149|))
(assert (!
  (|set.in POW (Z x Z)| s208 (|perm Z| s206))
  :named |Define:ctx:151|))
(assert (!
  (|set.subseteq Z| s209 s109)
  :named |Define:ctx:152|))
(assert (!
  (not
  (|set.in Z| s210 s209))
  :named |Define:ctx:154|))
(assert (!
  (|set.in POW (Z x Z)| s211 (|perm Z| s209))
  :named |Define:ctx:156|))
(assert (!
  (|set.subseteq Z| s212 s110)
  :named |Define:ctx:157|))
(assert (!
  (not
  (|set.in Z| s213 s212))
  :named |Define:ctx:159|))
(assert (!
  (|set.in POW (Z x Z)| s214 (|perm Z| s212))
  :named |Define:ctx:161|))
(assert (!
  (|set.in POW (Z x Z)| s219 (|injections.total Z Z| s220 s7))
  :named |Define:ctx:173|))
(assert (!
  (= s222 (|~ Z Z| s224))
  :named |Define:ctx:177|))
(assert (!
  (= (|fun.eval Z Z| s226 s228) s221)
  :named |Define:ctx:180|))
(assert (!
  (|set.subseteq Z| s229 s116)
  :named |Define:ctx:181|))
(assert (!
  (not
  (|set.in Z| s230 s229))
  :named |Define:ctx:183|))
(assert (!
  (|set.in POW (Z x Z)| s231 (|perm Z| s229))
  :named |Define:ctx:185|))
(assert (!
  (|set.subseteq Z| s241 s120)
  :named |Define:ctx:201|))
(assert (!
  (not
  (|set.in Z| s242 s241))
  :named |Define:ctx:203|))
(assert (!
  (|set.in POW (Z x Z)| s243 (|perm Z| s241))
  :named |Define:ctx:205|))
(assert (!
  (|set.subseteq Z| s255 s124)
  :named |Define:ctx:222|))
(assert (!
  (not
  (|set.in Z| s256 s255))
  :named |Define:ctx:224|))
(assert (!
  (|set.in POW (Z x Z)| s257 (|perm Z| s255))
  :named |Define:ctx:226|))
(assert (!
  (|set.subseteq Z| s184 s125)
  :named |Define:ctx:227|))
(assert (!
  (not
  (|set.in Z| s258 s184))
  :named |Define:ctx:229|))
(assert (!
  (|set.in POW (Z x Z)| s259 (|perm Z| s184))
  :named |Define:ctx:231|))
(assert (!
  (|set.subseteq Z| s272 s131)
  :named |Define:ctx:253|))
(assert (!
  (not
  (|set.in Z| s273 s272))
  :named |Define:ctx:255|))
(assert (!
  (|set.in POW (Z x Z)| s274 (|perm Z| s272))
  :named |Define:ctx:257|))
(assert (!
  (|set.in POW (Z x Z)| s279 (|injections.total Z Z| s272 s280))
  :named |Define:ctx:264|))
(assert (!
  (|set.subseteq Z| s281 s132)
  :named |Define:ctx:265|))
(assert (!
  (not
  (|set.in Z| s282 s281))
  :named |Define:ctx:267|))
(assert (!
  (|set.in POW (Z x Z)| s283 (|perm Z| s281))
  :named |Define:ctx:269|))
(assert (!
  (|set.in Z| s285 s133)
  :named |Define:ctx:271|))
(assert (!
  (|set.in POW (Z x Z)| s286 (|functions.partial Z Z| NAT s133))
  :named |Define:ctx:273|))
(assert (!
  (|set.in Z| s288 s146)
  :named |Define:ctx:276|))
(assert (!
  (|set.in POW (Z x Z)| s289 (|relations Z Z| s200 s229))
  :named |Define:ctx:278|))
(assert (!
  (|set.in POW (Z x Z)| s291 (|seq Z| s229))
  :named |Define:ctx:280|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s200)
    (= (|rel.image Z Z| s289 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s291 (|fun.eval Z POW Z| s290 s292)))))
  :named |Define:ctx:281|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s200)
    (|set.subseteq Z| (|fun.eval Z POW Z| s290 s292) (|rel.domain Z Z| s291))))
  :named |Define:ctx:282|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s200)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s290 s292) s291) (|injections.partial Z Z| NATURAL s229))))
  :named |Define:ctx:283|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s200)
      (not
        (= (|fun.eval Z POW Z| s290 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s290 s292) (|interval| (|min| (|fun.eval Z POW Z| s290 s292)) (|max| (|fun.eval Z POW Z| s290 s292))))))
  :named |Define:ctx:284|))
(assert (!
  (|set.in POW (Z x Z)| s296 (|seq Z| s200))
  :named |Define:ctx:287|))
(assert (!
  (|set.in POW (Z x Z)| s301 (|functions.total Z Z| s200 s229))
  :named |Define:ctx:294|))
(assert (!
  (|set.in POW (Z x Z)| s302 (|functions.total Z Z| s200 s229))
  :named |Define:ctx:295|))
(assert (!
  (|set.in POW (Z x Z)| s303 (|injections.total Z Z| s209 s200))
  :named |Define:ctx:296|))
(assert (!
  (|set.in POW (Z x Z)| s304 (|functions.total Z Z| s255 s200))
  :named |Define:ctx:297|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s305 (|functions.partial (Z x Z) Z| (|set.product Z Z| s255 s184) s12))
  :named |Define:ctx:298|))
(assert (!
  (|set.subseteq Z| s306 s200)
  :named |Define:ctx:299|))
(assert (!
  (|set.in POW (Z x Z)| s307 (|functions.total Z Z| s200 s194))
  :named |Define:ctx:300|))
(assert (!
  (|set.subseteq Z| s308 s200)
  :named |Define:ctx:301|))
(assert (!
  (|set.in POW (Z x Z)| s309 (|functions.partial Z Z| s200 s241))
  :named |Define:ctx:302|))
(assert (!
  (|set.in POW (Z x Z)| s313 (|seq Z| s229))
  :named |Define:ctx:306|))
(assert (!
  (|set.in POW (Z x Z)| s314 (|functions.partial Z Z| s229 s184))
  :named |Define:ctx:311|))
(assert (!
  (|set.in POW (Z x Z)| s315 (|functions.partial Z Z| s229 s316))
  :named |Define:ctx:312|))
(assert (!
  (|set.in POW (Z x Z)| s317 (|functions.partial Z Z| s229 s318))
  :named |Define:ctx:313|))
(assert (!
  (|set.in POW (Z x Z)| s319 (|functions.partial Z Z| s229 s320))
  :named |Define:ctx:314|))
(assert (!
  (|set.in POW ((Z x Z) x Z)| s322 (|functions.partial (Z x Z) Z| (|set.product Z Z| s229 s12) s229))
  :named |Define:ctx:316|))
(assert (!
  (|set.subseteq Z| s332 s229)
  :named |Define:ctx:325|))
(assert (!
  (|set.subseteq Z| s334 s229)
  :named |Define:ctx:327|))
(assert (!
  (|set.in POW (Z x Z)| s336 (|relations Z Z| s212 s209))
  :named |Define:ctx:329|))
(assert (!
  (|set.in POW (Z x Z)| s338 (|seq Z| s209))
  :named |Define:ctx:331|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s212)
    (= (|rel.image Z Z| s336 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s338 (|fun.eval Z POW Z| s337 s292)))))
  :named |Define:ctx:332|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s212)
    (|set.subseteq Z| (|fun.eval Z POW Z| s337 s292) (|rel.domain Z Z| s338))))
  :named |Define:ctx:333|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s212)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s337 s292) s338) (|injections.partial Z Z| NATURAL s209))))
  :named |Define:ctx:334|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s212)
      (not
        (= (|fun.eval Z POW Z| s337 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s337 s292) (|interval| (|min| (|fun.eval Z POW Z| s337 s292)) (|max| (|fun.eval Z POW Z| s337 s292))))))
  :named |Define:ctx:335|))
(assert (!
  (|set.in POW (Z x Z)| s339 (|functions.partial Z Z| s229 s340))
  :named |Define:ctx:336|))
(assert (!
  (= (|set.inter (Z x Z)| (|rel.domain (Z x Z) Z| s323) (|rel.domain (Z x Z) Z| s321)) |set.empty (Z x Z)|)
  :named |Define:ctx:338|))
(assert (!
  (|set.in POW (Z x Z)| s344 (|relations Z Z| s241 s229))
  :named |Define:ctx:340|))
(assert (!
  (|set.in POW (Z x Z)| s346 (|seq Z| s229))
  :named |Define:ctx:342|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (= (|rel.image Z Z| s344 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s346 (|fun.eval Z POW Z| s345 s292)))))
  :named |Define:ctx:343|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.subseteq Z| (|fun.eval Z POW Z| s345 s292) (|rel.domain Z Z| s346))))
  :named |Define:ctx:344|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s345 s292) s346) (|injections.partial Z Z| NATURAL s229))))
  :named |Define:ctx:345|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s241)
      (not
        (= (|fun.eval Z POW Z| s345 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s345 s292) (|interval| (|min| (|fun.eval Z POW Z| s345 s292)) (|max| (|fun.eval Z POW Z| s345 s292))))))
  :named |Define:ctx:346|))
(assert (!
  (|set.in POW (Z x Z)| s347 (|relations Z Z| s241 s229))
  :named |Define:ctx:347|))
(assert (!
  (|set.in POW (Z x Z)| s349 (|seq Z| s229))
  :named |Define:ctx:349|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (= (|rel.image Z Z| s347 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s349 (|fun.eval Z POW Z| s348 s292)))))
  :named |Define:ctx:350|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.subseteq Z| (|fun.eval Z POW Z| s348 s292) (|rel.domain Z Z| s349))))
  :named |Define:ctx:351|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s348 s292) s349) (|injections.partial Z Z| NATURAL s229))))
  :named |Define:ctx:352|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s241)
      (not
        (= (|fun.eval Z POW Z| s348 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s348 s292) (|interval| (|min| (|fun.eval Z POW Z| s348 s292)) (|max| (|fun.eval Z POW Z| s348 s292))))))
  :named |Define:ctx:353|))
(assert (!
  (|set.in POW (Z x Z)| s350 (|relations Z Z| s241 s351))
  :named |Define:ctx:354|))
(assert (!
  (|set.in POW (Z x Z)| s353 (|seq Z| s351))
  :named |Define:ctx:356|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (= (|rel.image Z Z| s350 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s353 (|fun.eval Z POW Z| s352 s292)))))
  :named |Define:ctx:357|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.subseteq Z| (|fun.eval Z POW Z| s352 s292) (|rel.domain Z Z| s353))))
  :named |Define:ctx:358|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s241)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s352 s292) s353) (|injections.partial Z Z| NATURAL s351))))
  :named |Define:ctx:359|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s241)
      (not
        (= (|fun.eval Z POW Z| s352 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s352 s292) (|interval| (|min| (|fun.eval Z POW Z| s352 s292)) (|max| (|fun.eval Z POW Z| s352 s292))))))
  :named |Define:ctx:360|))
(assert (!
  (|set.in POW (Z x Z)| s354 (|relations Z Z| s351 s255))
  :named |Define:ctx:361|))
(assert (!
  (|set.in POW (Z x Z)| s356 (|seq Z| s255))
  :named |Define:ctx:363|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (= (|rel.image Z Z| s354 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s356 (|fun.eval Z POW Z| s355 s292)))))
  :named |Define:ctx:364|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.subseteq Z| (|fun.eval Z POW Z| s355 s292) (|rel.domain Z Z| s356))))
  :named |Define:ctx:365|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s355 s292) s356) (|injections.partial Z Z| NATURAL s255))))
  :named |Define:ctx:366|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s351)
      (not
        (= (|fun.eval Z POW Z| s355 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s355 s292) (|interval| (|min| (|fun.eval Z POW Z| s355 s292)) (|max| (|fun.eval Z POW Z| s355 s292))))))
  :named |Define:ctx:367|))
(assert (!
  (|set.in POW (Z x Z)| s357 (|relations Z Z| s351 s255))
  :named |Define:ctx:368|))
(assert (!
  (|set.in POW (Z x Z)| s359 (|seq Z| s255))
  :named |Define:ctx:370|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (= (|rel.image Z Z| s357 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s359 (|fun.eval Z POW Z| s358 s292)))))
  :named |Define:ctx:371|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.subseteq Z| (|fun.eval Z POW Z| s358 s292) (|rel.domain Z Z| s359))))
  :named |Define:ctx:372|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s358 s292) s359) (|injections.partial Z Z| NATURAL s255))))
  :named |Define:ctx:373|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s351)
      (not
        (= (|fun.eval Z POW Z| s358 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s358 s292) (|interval| (|min| (|fun.eval Z POW Z| s358 s292)) (|max| (|fun.eval Z POW Z| s358 s292))))))
  :named |Define:ctx:374|))
(assert (!
  (|set.in POW (Z x Z)| s360 (|relations Z Z| s351 s186))
  :named |Define:ctx:375|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (= (|rel.image Z Z| s360 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s362 (|fun.eval Z POW Z| s361 s292)))))
  :named |Define:ctx:378|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.subseteq Z| (|fun.eval Z POW Z| s361 s292) (|rel.domain Z Z| s362))))
  :named |Define:ctx:379|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s351)
    (|set.in POW (Z x Z)| (|rel.restrict.dom Z Z| (|fun.eval Z POW Z| s361 s292) s362) (|injections.partial Z Z| NATURAL s186))))
  :named |Define:ctx:380|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s351)
      (not
        (= (|fun.eval Z POW Z| s361 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s361 s292) (|interval| (|min| (|fun.eval Z POW Z| s361 s292)) (|max| (|fun.eval Z POW Z| s361 s292))))))
  :named |Define:ctx:381|))
(assert (!
  (|set.in POW (Z x Z)| s363 (|functions.total Z Z| s241 s287))
  :named |Define:ctx:382|))
(assert (!
  (|set.in POW (Z x Z)| s364 (|functions.partial Z Z| s241 s189))
  :named |Define:ctx:383|))
(assert (!
  (|set.in POW (Z x Z)| s365 (|functions.partial Z Z| s241 s189))
  :named |Define:ctx:384|))
(assert (!
  (|set.in POW (Z x Z)| s366 (|functions.partial Z Z| s241 s367))
  :named |Define:ctx:385|))
(assert (!
  (|set.in POW (Z x Z)| s368 (|functions.partial Z Z| s241 s247))
  :named |Define:ctx:386|))
(assert (!
  (|set.in POW (Z x Z)| s369 (|functions.partial Z Z| s241 s370))
  :named |Define:ctx:387|))
(assert (!
  (|set.subseteq Z| s371 s241)
  :named |Define:ctx:388|))
(assert (!
  (|set.subseteq Z| s372 s241)
  :named |Define:ctx:389|))
(assert (!
  (|set.subseteq Z| s373 s241)
  :named |Define:ctx:390|))
(assert (!
  (|set.subseteq Z| s374 s351)
  :named |Define:ctx:391|))
(assert (!
  (|set.in POW (Z x Z)| s375 (|functions.partial Z Z| s351 s376))
  :named |Define:ctx:392|))
(assert (!
  (|set.in POW (Z x Z)| s377 (|functions.partial Z Z| s351 s378))
  :named |Define:ctx:393|))
(assert (!
  (|set.in Z| s381 s146)
  :named |Define:ctx:398|))
(assert (!
  (|set.in Z| s382 s146)
  :named |Define:ctx:400|))
(assert (!
  (|set.in Z| s383 s146)
  :named |Define:ctx:402|))
(assert (!
  (|set.in Z| s384 s146)
  :named |Define:ctx:404|))
(assert (!
  (|set.in Z| s388 s146)
  :named |Define:ctx:409|))
(assert (!
  (|set.in Z| s390 s146)
  :named |Define:ctx:412|))
(assert (!
  (|set.in Z| s391 s146)
  :named |Define:ctx:414|))
(assert (!
  (|set.in Z| s392 s146)
  :named |Define:ctx:416|))
(assert (!
  (|set.in Z| s393 s146)
  :named |Define:ctx:418|))
(assert (!
  (|set.in Z| s394 s146)
  :named |Define:ctx:420|))
(assert (!
  (|set.in Z| s395 s146)
  :named |Define:ctx:422|))
(assert (!
  (|set.in Z| s396 s146)
  :named |Define:ctx:424|))
(assert (!
  (|set.in Z| s397 s146)
  :named |Define:ctx:426|))
(assert (!
  (|set.in Z| s398 s146)
  :named |Define:ctx:428|))
(assert (!
  (|set.in Z| s399 s146)
  :named |Define:ctx:430|))
(assert (!
  (|set.in Z| s400 s146)
  :named |Define:ctx:432|))
(assert (!
  (|set.in Z| s401 s146)
  :named |Define:ctx:434|))
(assert (!
  (|set.in Z| s402 s146)
  :named |Define:ctx:437|))
(assert (!
  (|set.in Z| s403 s146)
  :named |Define:ctx:439|))
(assert (!
  (|set.in Z| s404 s146)
  :named |Define:ctx:441|))
(assert (!
  (|set.in Z| s405 s146)
  :named |Define:ctx:443|))
(assert (!
  (|set.in Z| s406 s146)
  :named |Define:ctx:445|))
(assert (!
  (|set.in Z| s407 s146)
  :named |Define:ctx:447|))
(assert (!
  (|set.in Z| s408 s146)
  :named |Define:ctx:449|))
(assert (!
  (|set.in Z| s409 s146)
  :named |Define:ctx:451|))
(assert (!
  (|set.in Z| s410 s146)
  :named |Define:ctx:453|))
(assert (!
  (|set.in Z| s411 s146)
  :named |Define:ctx:455|))
(assert (!
  (|set.in Z| s412 s140)
  :named |Define:ctx:457|))
(assert (!
  (|set.in Z| s413 s146)
  :named |Define:ctx:459|))
(assert (!
  (|set.in Z| s422 s146)
  :named |Define:ctx:469|))
(assert (!
  (|set.in Z| s433 s146)
  :named |Define:ctx:480|))
(assert (!
  (|set.in Z| s434 s146)
  :named |Define:ctx:482|))
(assert (!
  (|set.in Z| (+ s433 s434) s146)
  :named |Define:ctx:484|))
(assert (!
  (|set.in Z| s437 s146)
  :named |Define:ctx:487|))
(assert (!
  (|set.in Z| s438 s146)
  :named |Define:ctx:488|))
(assert (!
  (|set.in Z| s439 s146)
  :named |Define:ctx:489|))
(assert (!
  (|set.in POW (Z x Z)| s440 (|functions.total Z Z| s272 s441))
  :named |Define:ctx:490|))
(assert (!
  (|set.in POW (Z x Z)| s442 (|injections.total Z Z| s272 s268))
  :named |Define:ctx:491|))
(assert (!
  (|set.in POW (Z x Z)| s443 (|injections.partial Z Z| s194 s270))
  :named |Define:ctx:492|))
(assert (!
  (= (|rel.domain (Z x Z) Z| s444) (|rel.domain (Z x Z) Z| s446))
  :named |Define:ctx:495|))
(assert (!
  (|set.in POW (Z x Z)| s448 (|functions.partial Z Z| s194 s272))
  :named |Define:ctx:496|))
(assert (!
  (|set.in POW (Z x POW Z)| s450 (|functions.total Z POW Z| s255 (|sub-sets Z| s192)))
  :named |Define:ctx:499|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s255)
    (= (|rel.image Z Z| s449 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s292)))) (|rel.image Z Z| s451 (|fun.eval Z POW Z| s450 s292)))))
  :named |Define:ctx:501|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (|set.in Z| s292 s255)
    (|set.subseteq Z| (|fun.eval Z POW Z| s450 s292) (|rel.domain Z Z| s451))))
  :named |Define:ctx:502|))
(assert (!
  (forall
  ((s292 |Z|))
  (=>
    (and
      (|set.in Z| s292 s255)
      (not
        (= (|fun.eval Z POW Z| s450 s292) |set.empty Z|)))
    (= (|fun.eval Z POW Z| s450 s292) (|interval| (|min| (|fun.eval Z POW Z| s450 s292)) (|max| (|fun.eval Z POW Z| s450 s292))))))
  :named |Define:ctx:504|))
(assert (!
  (|set.subseteq Z| s454 s255)
  :named |Define:ctx:507|))
(assert (!
  (|set.subseteq Z| (|rel.domain Z Z| s484) (|rel.domain Z Z| s483))
  :named |Define:ctx:585|))
(assert (!
  (|set.subseteq Z| (|rel.domain Z Z| s511) (|rel.domain Z Z| s509))
  :named |Define:ctx:586|))
(assert (!
  (= (|rel.domain Z Z| s523) (|rel.domain Z Z| s521))
  :named |Define:ctx:587|))
(assert (!
  (= (|rel.domain Z Z| s488) (|rel.domain Z Z| s490))
  :named |Define:ctx:588|))
(assert (!
  (= (|rel.domain Z Z| s490) (|rel.domain Z Z| s491))
  :named |Define:ctx:589|))
(assert (!
  (= (|rel.domain Z Z| s491) (|rel.domain Z Z| s492))
  :named |Define:ctx:590|))
(assert (!
  (= (|rel.domain Z Z| s492) (|rel.domain Z Z| s493))
  :named |Define:ctx:591|))
(assert (!
  (= (|rel.domain Z Z| s493) (|rel.domain Z Z| s494))
  :named |Define:ctx:592|))
(assert (!
  (= (|rel.domain Z Z| s494) (|rel.domain Z Z| s495))
  :named |Define:ctx:593|))
(assert (!
  (= (|set.inter Z| (|rel.range Z Z| s487) (|rel.range Z Z| s485)) |set.empty Z|)
  :named |Define:ctx:594|))
(assert (!
  (|set.subseteq Z| s591$1 s200)
  :named |Define:imext:0|))
(assert (!
  (|set.subseteq Z| s592$1 s200)
  :named |Define:imext:1|))
(assert (!
  (|set.subseteq Z| s593$1 s200)
  :named |Define:imext:2|))
(assert (!
  (|set.in POW (Z x Z)| s594$1 (|functions.total Z Z| s200 s287))
  :named |Define:imext:3|))
(assert (!
  (|set.subseteq Z| s595$1 s194)
  :named |Define:imext:4|))
(assert (!
  (|set.subseteq Z| s596$1 s200)
  :named |Define:imext:5|))
(assert (!
  (|set.subseteq Z| s598$1 s200)
  :named |Define:imext:7|))
(assert (!
  (|set.in POW (Z x Z)| s600$1 (|functions.total Z Z| s184 s12))
  :named |Define:imext:9|))
(assert (!
  (|set.in POW (Z x Z)| s601$1 (|functions.total Z Z| s184 s12))
  :named |Define:imext:10|))
(assert (!
  (|set.in POW (Z x Z)| s603$1 (|functions.total Z Z| s184 s74))
  :named |Define:imext:12|))
(assert (!
  (|set.in POW (Z x Z)| s604$1 (|functions.partial Z Z| s184 s255))
  :named |Define:imext:13|))
(assert (!
  (|set.in POW (Z x Z)| s605$1 (|functions.partial Z Z| s194 s255))
  :named |Define:imext:14|))
(assert (!
  (|set.subseteq Z| s606$1 s200)
  :named |Define:imext:15|))
(assert (!
  (|set.subseteq Z| s607$1 s200)
  :named |Define:imext:16|))
(assert (!
  (|set.subseteq Z| s614$1 s184)
  :named |Define:imext:23|))
(assert (!
  (|set.subseteq Z| s615$1 s184)
  :named |Define:imext:24|))
(assert (!
  (|set.subseteq Z| s616$1 s184)
  :named |Define:imext:25|))
(assert (!
  (|set.subseteq Z| s617$1 s184)
  :named |Define:imext:26|))
(assert (!
  (|set.subseteq Z| s618$1 s200)
  :named |Define:imext:27|))
(assert (!
  (|set.in POW (Z x Z)| s619$1 (|functions.total Z Z| s200 s287))
  :named |Define:imext:28|))
(assert (!
  (|set.subseteq Z| s533 s525)
  :named |Define:seext:1|))
(assert (!
  (|set.subseteq Z| s534 s519)
  :named |Define:seext:2|))
(assert (!
  (|set.subseteq Z| s535 s255)
  :named |Define:seext:3|))
(assert (!
  (|set.subseteq Z| s536 s200)
  :named |Define:seext:4|))
(assert (!
  (|set.subseteq Z| s537 s241)
  :named |Define:seext:5|))
(assert (!
  (|set.subseteq Z| s538 s241)
  :named |Define:seext:6|))
(assert (!
  (|set.in POW (Z x Z)| s541 (|functions.total Z Z| s184 s12))
  :named |Define:seext:9|))
(assert (!
  (|set.subseteq Z| s542 s351)
  :named |Define:seext:10|))
(assert (!
  (|set.subseteq Z| s543 s194)
  :named |Define:seext:11|))
(assert (!
  (|set.subseteq Z| s544 s194)
  :named |Define:seext:12|))
(assert (!
  (|set.subseteq Z| s553 s229)
  :named |Define:seext:21|))
(assert (!
  (|set.subseteq Z| s554 s229)
  :named |Define:seext:22|))
(assert (!
  (|set.subseteq Z| s555 s229)
  :named |Define:seext:23|))
(assert (!
  (|set.subseteq Z| s556 s194)
  :named |Define:seext:24|))
(assert (!
  (|set.subseteq Z| s560 s320)
  :named |Define:seext:27|))
(assert (!
  (|set.subseteq Z| s564 s241)
  :named |Define:seext:30|))
(assert (!
  (|set.subseteq Z| s567 s194)
  :named |Define:seext:33|))
(assert (!
  (|set.subseteq Z| s568 s522)
  :named |Define:seext:34|))
(assert (!
  (|set.subseteq Z| s570 s200)
  :named |Define:seext:36|))
(assert (!
  (|set.subseteq Z| s571 s255)
  :named |Define:seext:37|))
(assert (!
  (|set.subseteq Z| s572 s200)
  :named |Define:seext:38|))
(assert (!
  (|set.subseteq Z| s573 s200)
  :named |Define:seext:39|))
(assert (!
  (|set.subseteq Z| s574 s489)
  :named |Define:seext:40|))
(assert (!
  (|set.subseteq Z| s576 s497)
  :named |Define:seext:42|))
(assert (!
  (|set.subseteq Z| s577 s497)
  :named |Define:seext:43|))
(assert (!
  (|set.subseteq Z| s579 s489)
  :named |Define:seext:45|))
(assert (!
  (|set.subseteq Z| s580 s489)
  :named |Define:seext:46|))
(assert (!
  (|set.subseteq Z| s581 s489)
  :named |Define:seext:47|))
(assert (!
  (|set.subseteq Z| s582 s489)
  :named |Define:seext:48|))
(assert (!
  (|set.subseteq Z| s583 s489)
  :named |Define:seext:49|))
(assert (!
  (|set.subseteq Z| s584 s489)
  :named |Define:seext:50|))
(assert (!
  (|set.in POW (Z x Z)| s586 (|functions.partial Z Z| s316 s146))
  :named |Define:seext:52|))
(assert (!
  (|set.subseteq Z| s587 s529)
  :named |Define:seext:53|))
(assert (!
  (|set.subseteq Z| s588 s529)
  :named |Define:seext:54|))
(assert (!
  (|set.subseteq Z| s589 s255)
  :named |Define:seext:55|))
(assert (!
  (|set.subseteq Z| s590 s255)
  :named |Define:seext:56|))
(assert (!
  (|set.subseteq Z| s591 s200)
  :named |Define:abs:0|))
(assert (!
  (|set.subseteq Z| s592 s200)
  :named |Define:abs:1|))
(assert (!
  (|set.subseteq Z| s593 s200)
  :named |Define:abs:2|))
(assert (!
  (|set.in POW (Z x Z)| s594 (|functions.total Z Z| s200 s287))
  :named |Define:abs:3|))
(assert (!
  (|set.subseteq Z| s595 s194)
  :named |Define:abs:4|))
(assert (!
  (|set.subseteq Z| s596 s200)
  :named |Define:abs:5|))
(assert (!
  (|set.subseteq Z| s598 s200)
  :named |Define:abs:7|))
(assert (!
  (|set.in POW (Z x Z)| s600 (|functions.total Z Z| s184 s12))
  :named |Define:abs:9|))
(assert (!
  (|set.in POW (Z x Z)| s601 (|functions.total Z Z| s184 s12))
  :named |Define:abs:10|))
(assert (!
  (|set.in POW (Z x Z)| s603 (|functions.total Z Z| s184 s74))
  :named |Define:abs:12|))
(assert (!
  (|set.in POW (Z x Z)| s604 (|functions.partial Z Z| s184 s255))
  :named |Define:abs:13|))
(assert (!
  (|set.in POW (Z x Z)| s605 (|functions.partial Z Z| s194 s255))
  :named |Define:abs:14|))
(assert (!
  (|set.subseteq Z| s606 s200)
  :named |Define:abs:15|))
(assert (!
  (|set.subseteq Z| s607 s200)
  :named |Define:abs:16|))
(assert (!
  (|set.subseteq Z| s614 s184)
  :named |Define:abs:23|))
(assert (!
  (|set.subseteq Z| s615 s184)
  :named |Define:abs:24|))
(assert (!
  (|set.subseteq Z| s616 s184)
  :named |Define:abs:25|))
(assert (!
  (|set.subseteq Z| s617 s184)
  :named |Define:abs:26|))
(assert (!
  (|set.subseteq Z| s618 s200)
  :named |Define:abs:27|))
(assert (!
  (|set.in POW (Z x Z)| s619 (|functions.total Z Z| s200 s287))
  :named |Define:abs:28|))
(assert (!
  (|set.subseteq Z| s598 s200)
  :named |Define:abs:30|))
(assert (!
  (|set.in POW (Z x Z)| s605 (|functions.partial Z Z| s194 s255))
  :named |Define:abs:31|))
(assert (!
  (|set.subseteq Z| s606 s200)
  :named |Define:abs:32|))
(assert (!
  (|set.subseteq Z| s607 s200)
  :named |Define:abs:33|))
(assert (!
  (|set.subseteq Z| s618 s200)
  :named |Define:abs:34|))
(assert (!
  (|set.subseteq Z| s591 s200)
  :named |Define:abs:35|))
(assert (!
  (|set.subseteq Z| s592 s200)
  :named |Define:abs:36|))
(assert (!
  (|set.subseteq Z| s593 s200)
  :named |Define:abs:37|))
(assert (!
  (|set.in POW (Z x Z)| s594 (|functions.total Z Z| s200 s287))
  :named |Define:abs:38|))
(assert (!
  (|set.subseteq Z| s595 s194)
  :named |Define:abs:39|))
(assert (!
  (|set.subseteq Z| s596 s200)
  :named |Define:abs:40|))
(assert (!
  (|set.in POW (Z x Z)| s603 (|functions.total Z Z| s184 s74))
  :named |Define:abs:43|))
(assert (!
  (|set.in POW (Z x Z)| s601 (|functions.total Z Z| s184 s12))
  :named |Define:abs:44|))
(assert (!
  (|set.subseteq Z| s614 s184)
  :named |Define:abs:50|))
(assert (!
  (|set.subseteq Z| s615 s184)
  :named |Define:abs:51|))
(assert (!
  (|set.subseteq Z| s616 s184)
  :named |Define:abs:52|))
(assert (!
  (|set.subseteq Z| s617 s184)
  :named |Define:abs:53|))
(assert (!
  (= s597 s597$1)
  :named |Define:inv:4|))
(assert (!
  (= s602 s602$1)
  :named |Define:inv:16|))
(assert (!
  (= s610 s610$1)
  :named |Define:inv:19|))
(assert (!
  (= s611 s611$1)
  :named |Define:inv:20|))
(assert (!
  (= s612 s612$1)
  :named |Define:inv:21|))
(assert (!
  (= s613 s613$1)
  :named |Define:inv:22|))
(assert (!
  (= (|set.union Z| (|rel.range Z Z| s185) (|rel.range Z Z| s187)) s186)
  :named |Define:ctx:113|))
(assert (!
  (= (|set.inter Z| (|rel.range Z Z| s185) (|rel.range Z Z| s187)) |set.empty Z|)
  :named |Define:ctx:114|))
(assert (!
  (|set.subseteq Z| s192 NAT)
  :named |Define:ctx:119|))
(assert (!
  (not
  (= s192 |set.empty Z|))
  :named |Define:ctx:120|))
(assert (!
  (= s192 (|interval| (|min| s192) (|max| s192)))
  :named |Define:ctx:121|))
(assert (!
  (not
  (|set.in Z| MAXINT s192))
  :named |Define:ctx:122|))
(assert (!
  (|set.in Z| s195 s104)
  :named |Define:ctx:128|))
(assert (!
  (|set.in POW (Z x Z)| s196 (|functions.partial Z Z| NAT s104))
  :named |Define:ctx:130|))
(assert (!
  (|set.in Z| s201 s106)
  :named |Define:ctx:138|))
(assert (!
  (|set.in POW (Z x Z)| s202 (|functions.partial Z Z| NAT s106))
  :named |Define:ctx:140|))
(assert (!
  (|set.in Z| s207 s108)
  :named |Define:ctx:148|))
(assert (!
  (|set.in POW (Z x Z)| s208 (|functions.partial Z Z| NAT s108))
  :named |Define:ctx:150|))
(assert (!
  (|set.in Z| s210 s109)
  :named |Define:ctx:153|))
(assert (!
  (|set.in POW (Z x Z)| s211 (|functions.partial Z Z| NAT s109))
  :named |Define:ctx:155|))
(assert (!
  (|set.in Z| s213 s110)
  :named |Define:ctx:158|))
(assert (!
  (|set.in POW (Z x Z)| s214 (|functions.partial Z Z| NAT s110))
  :named |Define:ctx:160|))
(assert (!
  (|set.in POW (Z x Z)| s226 (|functions.total Z Z| s227 s220))
  :named |Define:ctx:179|))
(assert (!
  (|set.in Z| s230 s116)
  :named |Define:ctx:182|))
(assert (!
  (|set.in POW (Z x Z)| s231 (|functions.partial Z Z| NAT s116))
  :named |Define:ctx:184|))
(assert (!
  (|set.in Z| s242 s120)
  :named |Define:ctx:202|))
(assert (!
  (|set.in POW (Z x Z)| s243 (|functions.partial Z Z| NAT s120))
  :named |Define:ctx:204|))
(assert (!
  (|set.subseteq Z| s247 s122)
  :named |Define:ctx:211|))
(assert (!
  (not
  (|set.in Z| s248 s247))
  :named |Define:ctx:213|))
(assert (!
  (|set.in POW (Z x Z)| s249 (|perm Z| s247))
  :named |Define:ctx:215|))
(assert (!
  (|set.in Z| s256 s124)
  :named |Define:ctx:223|))
(assert (!
  (|set.in POW (Z x Z)| s257 (|functions.partial Z Z| NAT s124))
  :named |Define:ctx:225|))
(assert (!
  (|set.in Z| s258 s125)
  :named |Define:ctx:228|))
(assert (!
  (|set.in POW (Z x Z)| s259 (|functions.partial Z Z| NAT s125))
  :named |Define:ctx:230|))
(assert (!
  (|set.subseteq Z| s186 s128)
  :named |Define:ctx:242|))
(assert (!
  (not
  (|set.in Z| s266 s186))
  :named |Define:ctx:244|))
(assert (!
  (|set.in POW (Z x Z)| s267 (|perm Z| s186))
  :named |Define:ctx:246|))
(assert (!
  (|set.subseteq Z| s268 s129)
  :named |Define:ctx:247|))
(assert (!
  (not
  (|set.in Z| s269 s268))
  :named |Define:ctx:249|))
(assert (!
  (|set.subseteq Z| s270 s130)
  :named |Define:ctx:250|))
(assert (!
  (not
  (|set.in Z| s271 s270))
  :named |Define:ctx:252|))
(assert (!
  (|set.in Z| s273 s131)
  :named |Define:ctx:254|))
(assert (!
  (|set.in POW (Z x Z)| s274 (|functions.partial Z Z| NAT s131))
  :named |Define:ctx:256|))
(assert (!
  (|set.in Z| s282 s132)
  :named |Define:ctx:266|))
(assert (!
  (|set.in POW (Z x Z)| s283 (|functions.partial Z Z| NAT s132))
  :named |Define:ctx:268|))
(assert (!
  (= s287 NATURAL)
  :named |Define:ctx:275|))
(assert (!
  (= s288 0)
  :named |Define:ctx:277|))
(assert (!
  (= (|rel.range Z Z| s339) s340)
  :named |Define:ctx:337|))
(assert (!
  (|set.in POW (Z x Z)| s362 (|seq Z| s186))
  :named |Define:ctx:377|))
(assert (!
  (|set.in POW (Z x Z)| s379 (|functions.total Z Z| s374 s61))
  :named |Define:ctx:394|))
(assert (!
  (= (|rel.domain Z Z| s375) s374)
  :named |Define:ctx:395|))
(assert (!
  (= (|rel.domain Z Z| s377) s374)
  :named |Define:ctx:396|))
(assert (!
  (> s381 0)
  :named |Define:ctx:399|))
(assert (!
  (> s382 0)
  :named |Define:ctx:401|))
(assert (!
  (> s383 0)
  :named |Define:ctx:403|))
(assert (!
  (> s384 0)
  :named |Define:ctx:405|))
(assert (!
  (|set.in Z| s385 s287)
  :named |Define:ctx:406|))
(assert (!
  (|set.in Z| s386 s287)
  :named |Define:ctx:407|))
(assert (!
  (|set.in Z| s387 s287)
  :named |Define:ctx:408|))
(assert (!
  (> s388 0)
  :named |Define:ctx:410|))
(assert (!
  (|set.in Z| s389 s287)
  :named |Define:ctx:411|))
(assert (!
  (> s390 0)
  :named |Define:ctx:413|))
(assert (!
  (> s391 0)
  :named |Define:ctx:415|))
(assert (!
  (> s392 0)
  :named |Define:ctx:417|))
(assert (!
  (> s393 0)
  :named |Define:ctx:419|))
(assert (!
  (> s394 0)
  :named |Define:ctx:421|))
(assert (!
  (> s395 0)
  :named |Define:ctx:423|))
(assert (!
  (> s396 0)
  :named |Define:ctx:425|))
(assert (!
  (> s397 0)
  :named |Define:ctx:427|))
(assert (!
  (> s398 0)
  :named |Define:ctx:429|))
(assert (!
  (> s399 0)
  :named |Define:ctx:431|))
(assert (!
  (> s400 0)
  :named |Define:ctx:433|))
(assert (!
  (> s401 0)
  :named |Define:ctx:435|))
(assert (!
  (< s392 s401)
  :named |Define:ctx:436|))
(assert (!
  (> s402 0)
  :named |Define:ctx:438|))
(assert (!
  (> s403 0)
  :named |Define:ctx:440|))
(assert (!
  (> s404 0)
  :named |Define:ctx:442|))
(assert (!
  (> s405 0)
  :named |Define:ctx:444|))
(assert (!
  (> s406 0)
  :named |Define:ctx:446|))
(assert (!
  (> s407 0)
  :named |Define:ctx:448|))
(assert (!
  (> s408 0)
  :named |Define:ctx:450|))
(assert (!
  (> s409 0)
  :named |Define:ctx:452|))
(assert (!
  (> s410 0)
  :named |Define:ctx:454|))
(assert (!
  (> s411 0)
  :named |Define:ctx:456|))
(assert (!
  (> s413 0)
  :named |Define:ctx:460|))
(assert (!
  (|set.in Z| s414 s287)
  :named |Define:ctx:461|))
(assert (!
  (|set.in Z| s415 s287)
  :named |Define:ctx:462|))
(assert (!
  (|set.in Z| s416 s287)
  :named |Define:ctx:463|))
(assert (!
  (|set.in Z| s417 s287)
  :named |Define:ctx:464|))
(assert (!
  (|set.in Z| s418 s287)
  :named |Define:ctx:465|))
(assert (!
  (|set.in Z| s419 s287)
  :named |Define:ctx:466|))
(assert (!
  (|set.in Z| s420 s287)
  :named |Define:ctx:467|))
(assert (!
  (|set.in Z| s421 s287)
  :named |Define:ctx:468|))
(assert (!
  (|set.in Z| s423 s287)
  :named |Define:ctx:470|))
(assert (!
  (|set.in Z| s424 s287)
  :named |Define:ctx:471|))
(assert (!
  (|set.in Z| s425 s287)
  :named |Define:ctx:472|))
(assert (!
  (|set.in Z| s426 s287)
  :named |Define:ctx:473|))
(assert (!
  (|set.in Z| s427 s287)
  :named |Define:ctx:474|))
(assert (!
  (|set.in Z| s428 s287)
  :named |Define:ctx:475|))
(assert (!
  (|set.in Z| s429 s287)
  :named |Define:ctx:476|))
(assert (!
  (|set.in Z| s430 s287)
  :named |Define:ctx:477|))
(assert (!
  (|set.in Z| s431 s287)
  :named |Define:ctx:478|))
(assert (!
  (|set.in Z| s432 s287)
  :named |Define:ctx:479|))
(assert (!
  (> s433 0)
  :named |Define:ctx:481|))
(assert (!
  (>= s434 0)
  :named |Define:ctx:483|))
(assert (!
  (|set.in Z| s435 s287)
  :named |Define:ctx:485|))
(assert (!
  (|set.in Z| s436 s287)
  :named |Define:ctx:486|))
(assert (!
  (|set.subseteq Z| s599$1 s186)
  :named |Define:imext:8|))
(assert (!
  (|set.subseteq Z| (|rel.image Z Z| (|~ Z Z| s603$1) (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s77)))) (|rel.domain Z Z| s604$1))
  :named |Define:imext:29|))
(assert (!
  (|set.in Z| s623$1 s124)
  :named |Define:imext:33|))
(assert (!
  (|set.subseteq Z| s192 NATURAL)
  :named |Define:seext:59|))
(assert (!
  (|set.subseteq Z| s599 s186)
  :named |Define:abs:8|))
(assert (!
  (|set.subseteq Z| (|rel.image Z Z| (|~ Z Z| s603) (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s77)))) (|rel.domain Z Z| s604))
  :named |Define:abs:29|))
(assert (!
  (|set.subseteq Z| s599 s186)
  :named |Define:abs:42|))
(assert (!
  (= s591 s591$1)
  :named |Define:inv:0|))
(assert (!
  (= s598 s598$1)
  :named |Define:inv:1|))
(assert (!
  (= s592 s592$1)
  :named |Define:inv:2|))
(assert (!
  (= s596 s596$1)
  :named |Define:inv:3|))
(assert (!
  (= s605 s605$1)
  :named |Define:inv:5|))
(assert (!
  (= s606 s606$1)
  :named |Define:inv:6|))
(assert (!
  (= s607 s607$1)
  :named |Define:inv:7|))
(assert (!
  (= s593 s593$1)
  :named |Define:inv:8|))
(assert (!
  (= s594 s594$1)
  :named |Define:inv:9|))
(assert (!
  (= s595 s595$1)
  :named |Define:inv:10|))
(assert (!
  (= s601 s601$1)
  :named |Define:inv:13|))
(assert (!
  (= s600 s600$1)
  :named |Define:inv:14|))
(assert (!
  (= s603 s603$1)
  :named |Define:inv:17|))
(assert (!
  (= s604 s604$1)
  :named |Define:inv:18|))
(assert (!
  (= s614 s614$1)
  :named |Define:inv:23|))
(assert (!
  (= s615 s615$1)
  :named |Define:inv:24|))
(assert (!
  (= s616 s616$1)
  :named |Define:inv:25|))
(assert (!
  (= s617 s617$1)
  :named |Define:inv:26|))
(assert (!
  (= s618 s618$1)
  :named |Define:inv:27|))
(assert (!
  (= s619 s619$1)
  :named |Define:inv:28|))
(assert (!
  (|set.in Z| s248 s122)
  :named |Define:ctx:212|))
(assert (!
  (|set.in POW (Z x Z)| s249 (|functions.partial Z Z| NAT s122))
  :named |Define:ctx:214|))
(assert (!
  (|set.in Z| s266 s128)
  :named |Define:ctx:243|))
(assert (!
  (|set.in POW (Z x Z)| s267 (|functions.partial Z Z| NAT s128))
  :named |Define:ctx:245|))
(assert (!
  (|set.in Z| s269 s129)
  :named |Define:ctx:248|))
(assert (!
  (|set.in Z| s271 s130)
  :named |Define:ctx:251|))
(assert (!
  (= s599 s599$1)
  :named |Define:inv:15|))
(assert (!
  (not
    (exists
      ((s620 |BOOL|)(s621 |BOOL|))
      (and
        (= s620         (|set.in Z| s10 (|rel.image (Z x Z) Z| s455 (|rel.restrict.dom Z Z| (|rel.image Z Z| s458 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s631)))) s569))))
        (= s621         (|set.in Z| s11 (|rel.image (Z x Z) Z| s455 (|rel.restrict.dom Z Z| (|rel.image Z Z| s458 (|set.intent Z| (lambda ((_c0 |Z|)) (= _c0 s631)))) s569)))))))
  :named |Goal|))
(check-sat)
(exit)
