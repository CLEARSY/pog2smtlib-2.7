(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)
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

(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(assert (!
  (not (|set.in (Z x POW Z)| (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2))))) (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (and
(|set.in Z| (fst x) INTEGER)
(|set.in POW Z| (snd x) (|sub-sets Z| INTEGER))
(= (snd x) (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)))))
(|set.in Z| (fst x) (snd x))
)))))
  :named |Goal|)
)
(check-sat)
(exit)
