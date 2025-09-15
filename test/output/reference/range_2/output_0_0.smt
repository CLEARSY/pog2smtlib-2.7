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

(declare-fun |rel.range Z Z| (|POW (Z x Z)|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (e |Z|))
    (= (|set.in Z| e (|rel.range Z Z| r))
       (exists ((x |Z|)) (|set.in (Z x Z)| (maplet x e) r))))
  :named |ax:set.in.range (Z x Z)|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (|set.in Z| 1 (|rel.range Z Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 1 1))(= x (maplet 2 2))))))))
  :named |Goal|))
(check-sat)
(exit)
