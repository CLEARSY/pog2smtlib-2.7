(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |REAL| () Real)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW REAL| () (P |REAL|))
(declare-const c2 |POW Z|)
(declare-const c3 |POW REAL|)
(declare-const c1 |POW Z|)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x REAL)| () (C |Z| |REAL|))
(define-sort |POW (Z x REAL)| () (P |(Z x REAL)|))

(declare-fun |set.in (Z x REAL)| (|(Z x REAL)| |POW (Z x REAL)|) Bool)

(declare-fun |set.in REAL| (|REAL| |POW REAL|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.product Z REAL| (|POW Z| |POW REAL|) |POW (Z x REAL)|)
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW REAL|))
    (forall ((p |(Z x REAL)|))
      (= (|set.in (Z x REAL)| p (|set.product Z REAL| s1 s2))
        (and (|set.in Z| (fst p) s1) (|set.in REAL| (snd p) s2)))))
  :named |ax.set.in.product.1 (Z x REAL)|))
(assert (!
  (forall ((s1 |POW Z|) (s2 |POW REAL|))
    (forall ((x1 |Z|) (x2 |REAL|))
      (= (|set.in (Z x REAL)| (maplet x1 x2) (|set.product Z REAL| s1 s2))
        (and (|set.in Z| x1 s1) (|set.in REAL| x2 s2)))))
  :named |ax.set.in.product.2 (Z x REAL)|))
(declare-fun |set.subseteq (Z x REAL)| (|POW (Z x REAL)| |POW (Z x REAL)|) Bool)
(assert (!
    (forall ((s |POW (Z x REAL)|) (t |POW (Z x REAL)|))
      (=
        (|set.subseteq (Z x REAL)| s t)
        (forall ((e |(Z x REAL)|)) (=> (|set.in (Z x REAL)| e s) (|set.in (Z x REAL)| e t)))
      )
    )
    :named |ax.set.subseteq (Z x REAL)|))
(assert (!
  (not (|set.subseteq (Z x REAL)| (|set.product Z REAL| c1 c3) (|set.product Z REAL| c2 c3)))
  :named |Goal|))
(check-sat)
(exit)
