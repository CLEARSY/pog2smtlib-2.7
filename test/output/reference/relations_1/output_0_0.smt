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

(define-const MAXINT |Z| 2147483647)

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

(declare-const NAT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT) (and (<= 0 e) (<= e MAXINT))))
  :named |ax.set.in.NAT|))

(declare-fun |relations Z Z| (|POW Z| |POW Z|) |POW POW (Z x Z)|)
(assert (!
  (forall ((X |POW Z|) (Y |POW Z|))
    (= (|relations Z Z| X Y)
       (|sub-sets (Z x Z)| (|set.product Z Z| X Y))))
    :named |def.relations (Z x Z)|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))

(declare-const NAT1 |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT1) (and (<= 1 e) (<= e MAXINT))))
  :named |ax.set.in.NAT1|))
(assert (!
  (not (|set.in POW (Z x Z)| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 2))(= x (maplet 0 2))))) (|relations Z Z| NAT1 NAT)))
  :named |Goal|))
(check-sat)
(exit)
