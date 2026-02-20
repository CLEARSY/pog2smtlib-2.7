(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |REAL| () Real)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW REAL| () (P |REAL|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const c2 |POW Z|)
(declare-const c3 |POW REAL|)
(declare-const c1 |POW Z|)
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
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x REAL)| () (C |Z| |REAL|))
(declare-fun |set.in REAL| (|REAL| |POW REAL|) Bool)
(define-sort |POW (Z x REAL)| () (P |(Z x REAL)|))
(declare-fun |set.in (Z x REAL)| (|(Z x REAL)| |POW (Z x REAL)|) Bool)
(declare-fun |set.product Z REAL| (|POW Z| |POW REAL|) |POW (Z x REAL)|)
(assert (!
  (forall ((U |POW Z|)(V |POW REAL|)(p |(Z x REAL)|))
    (= (|set.in (Z x REAL)| p (|set.product Z REAL| U V))
      (and (|set.in Z| (fst p) U) (|set.in REAL| (snd p) V))))
  :named |ax.set.product (Z x REAL)|))
(declare-fun |set.subseteq (Z x REAL)| (|POW (Z x REAL)| |POW (Z x REAL)|) Bool)
(assert (!
  (forall ((s |POW (Z x REAL)|) (t |POW (Z x REAL)|) (e |(Z x REAL)|))
    (=>
      (and (|set.subseteq (Z x REAL)| s t) (|set.in (Z x REAL)| e s))
      (|set.in (Z x REAL)| e t)))
  :named |ax.set.subseteq.elim (Z x REAL)|))
(assert (!
  (forall ((s |POW (Z x REAL)|) (t |POW (Z x REAL)|))
    (=>
      (forall ((e |(Z x REAL)|)) (=> (|set.in (Z x REAL)| e s) (|set.in (Z x REAL)| e t)))
      (|set.subseteq (Z x REAL)| s t)))
  :named |ax.set.subseteq.intro (Z x REAL)|))
(assert (!
  (|set.subseteq Z| c1 c2)
  :named |Define:lprp:4|))
(assert (!
  (not
    (|set.subseteq (Z x REAL)| (|set.product Z REAL| c1 c3) (|set.product Z REAL| c2 c3)))
  :named |Goal|))
(check-sat)
(exit)
