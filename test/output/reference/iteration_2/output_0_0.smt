(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |POW Z| () (P |Z|))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(declare-fun |relcomp Z Z Z| (|POW (Z x Z)| |POW (Z x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((r |POW (Z x Z)|) (s |POW (Z x Z)|) (p |(Z x Z)|))
    (= (|set.in (Z x Z)| p (|relcomp Z Z Z| r s))
       (exists ((y |Z|))
         (and
           (|set.in (Z x Z)| (maplet (fst p) y) r)
           (|set.in (Z x Z)| (maplet y (snd p)) s)))))
  :named |ax.set.in.relcomp ((Z x Z) x Z)|))
(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(declare-const |set.empty (Z x Z)| |POW (Z x Z)|)
(assert (!
  (forall ((e |(Z x Z)|)) (not (|set.in (Z x Z)| e |set.empty (Z x Z)|)))
  :named |ax.set.in.empty (Z x Z)|))
(declare-fun |iterate Z| (|POW (Z x Z)| |Z|) |POW (Z x Z)|)
(assert (!
  (forall ((R |POW (Z x Z)|)) (= (|iterate Z| R 1) R))
  :named |ax.set.iterate.1 Z|))
(assert (!
  (forall ((R |POW (Z x Z)|)(n |Z|))
    (= (|iterate Z| R (+ n 1)) (|relcomp Z Z Z| R (|iterate Z| R n))))
  :named |ax.set.iterate.n+1 Z|))
(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (= s t)
      (forall ((e |(Z x Z)|)) (= (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t)))))
  :named |ax.set.eq (Z x Z)|))
(assert (!
  (not
    (= (|iterate Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (= x (maplet 1 0)))) 2) |set.empty (Z x Z)|))
  :named |Goal|))
(check-sat)
(exit)
