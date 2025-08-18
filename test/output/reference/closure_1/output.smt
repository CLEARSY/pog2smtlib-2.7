(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |closure Z| (|POW (Z x Z)|) |POW (Z x Z)|)
(assert (!
  (forall ((R |POW (Z x Z)|)(p |(Z x Z)|))
    (= (|set.in (Z x Z)| p (|closure Z| R))
       (or (= (fst p) (snd p))
           (|set.in (Z x Z)| p (|closure Z| R)))))
  :named |ax.closure Z|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (= (|closure Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 3))(= x (maplet 2 1))(= x (maplet 2 2))(= x (maplet 3 3)))))) (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 3))(= x (maplet 2 1))(= x (maplet 2 2))(= x (maplet 2 3))(= x (maplet 3 2)))))))
  :named |Goal|)
)
(check-sat)
(exit)
