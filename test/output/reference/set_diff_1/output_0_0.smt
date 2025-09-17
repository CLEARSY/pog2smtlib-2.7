(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(define-sort |(Z x POW (Z x Z))| () (C |Z| |POW (Z x Z)|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(define-sort |POW POW (Z x Z)| () (P |POW (Z x Z)|))
(define-sort |POW (Z x POW (Z x Z))| () (P |(Z x POW (Z x Z))|))
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
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in (Z x POW (Z x Z))| (|(Z x POW (Z x Z))| |POW (Z x POW (Z x Z))|) Bool)
(define-sort |POW POW (Z x POW (Z x Z))| () (P |POW (Z x POW (Z x Z))|))

(declare-fun |sub-sets (Z x Z)| (|POW (Z x Z)|) |POW POW (Z x Z)|)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (|set.in POW (Z x Z)| s (|sub-sets (Z x Z)| t))
      (|set.subseteq (Z x Z)| s t)))
  :named |ax.sub-sets (Z x Z)|))

(declare-const |set.empty (Z x Z)| |POW (Z x Z)|)
(assert (!
  (forall ((e |(Z x Z)|)) (not (|set.in (Z x Z)| e |set.empty (Z x Z)|)))
  :named |ax.set.in.empty (Z x Z)|))

(define-const MININT |Z| (- 2147483648))

(define-const MAXINT |Z| 2147483647)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.subseteq (Z x POW (Z x Z))| (|POW (Z x POW (Z x Z))| |POW (Z x POW (Z x Z))|) Bool)
(assert (!
    (forall ((s |POW (Z x POW (Z x Z))|) (t |POW (Z x POW (Z x Z))|))
      (=
        (|set.subseteq (Z x POW (Z x Z))| s t)
        (forall ((e |(Z x POW (Z x Z))|)) (=> (|set.in (Z x POW (Z x Z))| e s) (|set.in (Z x POW (Z x Z))| e t)))
      )
    )
    :named |ax.set.subseteq (Z x POW (Z x Z))|))

(declare-fun |set.in POW (Z x POW (Z x Z))| (|POW (Z x POW (Z x Z))| |POW POW (Z x POW (Z x Z))|) Bool)

(declare-fun |non empty sub-sets (Z x Z)| (|POW (Z x Z)|) |POW POW (Z x Z)|)
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (= (|set.in POW (Z x Z)| s (|non empty sub-sets (Z x Z)| t))
       (and (|set.in POW (Z x Z)| s (|sub-sets (Z x Z)| t))
            (not (= s |set.empty (Z x Z)|)))))
  :named |ax.non empty sub-sets (Z x Z)|))

(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))

(declare-const NAT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT) (and (<= 0 e) (<= e MAXINT))))
  :named |ax.set.in.NAT|))

(declare-fun |set.product Z POW (Z x Z)| (|POW Z| |POW POW (Z x Z)|) |POW (Z x POW (Z x Z))|)
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW POW (Z x Z)|))
    (forall ((p |(Z x POW (Z x Z))|))
      (= (|set.in (Z x POW (Z x Z))| p (|set.product Z POW (Z x Z)| s1 s2))
        (and (|set.in Z| (fst p) s1) (|set.in POW (Z x Z)| (snd p) s2)))))
  :named |ax.set.in.product.1 (Z x POW (Z x Z))|))
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW POW (Z x Z)|))
    (forall ((x1 |Z|) (x2 |POW (Z x Z)|))
      (= (|set.in (Z x POW (Z x Z))| (maplet x1 x2) (|set.product Z POW (Z x Z)| s1 s2))
        (and (|set.in Z| x1 s1) (|set.in POW (Z x Z)| x2 s2)))))
  :named |ax.set.in.product.2 (Z x POW (Z x Z))|))

(declare-fun |sub-sets (Z x POW (Z x Z))| (|POW (Z x POW (Z x Z))|) |POW POW (Z x POW (Z x Z))|)
(assert (!
  (forall ((s |POW (Z x POW (Z x Z))|) (t |POW (Z x POW (Z x Z))|))
    (=
      (|set.in POW (Z x POW (Z x Z))| s (|sub-sets (Z x POW (Z x Z))| t))
      (|set.subseteq (Z x POW (Z x Z))| s t)))
  :named |ax.sub-sets (Z x POW (Z x Z))|))

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

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(declare-const d2 |POW (Z x POW (Z x Z))|)
(declare-const d3 |(Z x POW (Z x Z))|)
(declare-const d1 |POW (Z x POW (Z x Z))|)

(declare-fun |set.diff (Z x POW (Z x Z))| (|POW (Z x POW (Z x Z))| |POW (Z x POW (Z x Z))|) |POW (Z x POW (Z x Z))|)
(assert (!
  (forall ((e |(Z x POW (Z x Z))|) (s |POW (Z x POW (Z x Z))|) (t |POW (Z x POW (Z x Z))|))
    (= (|set.in (Z x POW (Z x Z))| e (|set.diff (Z x POW (Z x Z))| s t))
       (and (|set.in (Z x POW (Z x Z))| e s) (not (|set.in (Z x POW (Z x Z))| e t)))))
  :named |ax.set.in.diff (Z x POW (Z x Z))|))
(assert (!
  (|set.in POW (Z x POW (Z x Z))| d1 (|sub-sets (Z x POW (Z x Z))| (|set.product Z POW (Z x Z)| INTEGER (|non empty sub-sets (Z x Z)| (|set.product Z Z| INT NAT)))))
  :named |Define:lprp:1|))
(assert (!
  (|set.in POW (Z x POW (Z x Z))| d2 (|sub-sets (Z x POW (Z x Z))| (|set.product Z POW (Z x Z)| INTEGER (|non empty sub-sets (Z x Z)| (|set.product Z Z| INT NAT)))))
  :named |Define:lprp:2|))
(assert (!
  (|set.in (Z x POW (Z x Z))| d3 d1)
  :named |Define:lprp:3|))
(assert (!
  (|set.in (Z x POW (Z x Z))| d3 d2)
  :named |Define:lprp:4|))
(assert (!
  (not (|set.in (Z x POW (Z x Z))| d3 (|set.diff (Z x POW (Z x Z))| d1 d2)))
  :named |Goal|))
(check-sat)
(exit)
