(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const s2 |POW Z|)
(declare-const s1 |POW Z|)
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(declare-fun |rel.range Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range Z Z| r))
       (exists ((x |Z|)) (|set.in (Z x Z)| (maplet x e) r))))
  :named |ax:set.in.range (Z x Z)|))
(declare-fun |set.product Z Z| (|POW Z| |POW Z|) |POW (Z x Z)|)
(assert (!
  (forall ((U |POW Z|)(V |POW Z|)(p |(Z x Z)|))
    (= (|set.in (Z x Z)| p (|set.product Z Z| U V))
      (and (|set.in Z| (fst p) U) (|set.in Z| (snd p) V))))
  :named |ax.set.product (Z x Z)|))
(assert (!
  (not
  (= s1 |set.empty Z|))
  :named |Define:lprp:3|))
(assert (!
  (not
    (= (|rel.range Z Z| (|set.product Z Z| s1 s2)) s2))
  :named |Goal|))
(check-sat)
(exit)
