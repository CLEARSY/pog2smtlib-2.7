(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |(Z x (Z x Z))| () (C |Z| |(Z x Z)|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(define-sort |POW (Z x (Z x Z))| () (P |(Z x (Z x Z))|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |set.in (Z x (Z x Z))| (|(Z x (Z x Z))| |POW (Z x (Z x Z))|) Bool)

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))

(declare-fun |directproduct Z Z Z| (|POW (Z x Z)| |POW (Z x Z)|) |POW (Z x (Z x Z))|)
(assert (!
  (forall ((R1 |POW (Z x Z)|) (R2 |POW (Z x Z)|) (p |(Z x (Z x Z))|))
    (= (|set.in (Z x (Z x Z))| p (|directproduct Z Z Z| R1 R2))
       (and
         (|set.in (Z x Z)| (maplet (fst p) (fst (snd p))) R1)
         (|set.in (Z x Z)| (maplet (fst p) (snd (snd p))) R2)
       )
    )
  )
  :named |ax.set.in.directproduct ((Z x Z) x Z)|))
(assert (!
  (not (|set.in (Z x (Z x Z))| (maplet 1 (maplet 3 10)) (|directproduct Z Z Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 3))(= x (maplet 5 4))))) (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 10))(= x (maplet 4 9))))))))
  :named |Goal|))
(check-sat)
(exit)
