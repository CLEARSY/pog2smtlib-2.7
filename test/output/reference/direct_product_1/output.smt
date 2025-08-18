(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(define-sort |(Z x (Z x POW Z))| () (C |Z| |(Z x POW Z)|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(define-sort |POW (Z x (Z x POW Z))| () (P |(Z x (Z x POW Z))|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |set.in (Z x (Z x POW Z))| (|(Z x (Z x POW Z))| |POW (Z x (Z x POW Z))|) Bool)

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x POW Z)|))

(declare-fun |directproduct Z Z POW Z| (|POW (Z x Z)| |POW (Z x POW Z)|) |POW (Z x (Z x POW Z))|)
(assert (!
  (forall ((R1 |POW (Z x Z)|) (R2 |POW (Z x POW Z)|) (p |(Z x (Z x POW Z))|))
    (= (|set.in (Z x (Z x POW Z))| p (|directproduct Z Z POW Z| R1 R2))
       (and
         (|set.in (Z x Z)| (maplet (fst p) (fst (snd p))) R1)
         (|set.in (Z x POW Z)| (maplet (fst p) (snd (snd p))) R2)
       )
    )
  )
  :named |ax.set.in.directproduct ((Z x Z) x POW Z)|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (|set.in (Z x (Z x POW Z))| (maplet 1 (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (or (= x 9)))))) (|directproduct Z Z POW Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 3))(= x (maplet 5 4))))) (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 10))))))(= x (maplet 4 (|set.intent Z| (lambda ((x |Z|)) (or (= x 9))))))))))))
  :named |Goal|)
)
(check-sat)
(exit)
