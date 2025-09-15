(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))

(assert (!
  (forall ((s |POW (Z x Z)|) (t |POW (Z x Z)|))
    (=
      (= s t)
      (forall ((e |(Z x Z)|)) (= (|set.in (Z x Z)| e s) (|set.in (Z x Z)| e t)))
    )
  )
  :named |ax.set.eq (Z x Z)|))

(declare-const |set.empty (Z x Z)| |POW (Z x Z)|)
(assert (!
  (forall ((e |(Z x Z)|)) (not (|set.in (Z x Z)| e |set.empty (Z x Z)|)))
  :named |ax.set.in.empty (Z x Z)|))
(assert (!
  (not (not (= (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 5))(= x (maplet 2 4))(= x (maplet 3 7))(= x (maplet 4 8))))) |set.empty (Z x Z)|)))
  :named |Goal|))
(check-sat)
(exit)
