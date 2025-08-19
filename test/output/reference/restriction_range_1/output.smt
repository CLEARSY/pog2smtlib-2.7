(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(declare-sort P 1)
(define-sort |(Z x Z)| () (C |Z| |Z|))
(define-sort |POW Z| () (P |Z|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |rel.restrict.ran Z Z| (|POW (Z x Z)| |POW Z|) |POW (Z x Z)|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |POW Z|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|rel.restrict.ran Z Z| r e))
         (and (|set.in (Z x Z)| x r) (|set.in Z| (snd x) e)))))
  :named |ax:set.in.restrict.ran (Z x Z)|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (= (|rel.restrict.ran Z Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 2 1))(= x (maplet 3 1))(= x (maplet 5 5))))) (|set.intent Z| (lambda ((x |Z|)) (or (= x 1))))) (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 2 1)))))))
  :named |Goal|)
)
(check-sat)
(exit)
