(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(POW Z x Z)| () (C |POW Z| |Z|))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (POW Z x Z)| () (P |(POW Z x Z)|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in (POW Z x Z)| (|(POW Z x Z)| |POW (POW Z x Z)|) Bool)

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)

(define-sort |? (POW Z x Z)| () (-> |(POW Z x Z)| Bool))
(declare-const |set.intent (POW Z x Z)| (-> |? (POW Z x Z)| |POW (POW Z x Z)|))
(assert (!
  (forall ((p |? (POW Z x Z)|))
    (forall ((x |(POW Z x Z)|))
      (= (|set.in (POW Z x Z)| x (|set.intent (POW Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (POW Z x Z)|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(define-sort |? (Z x POW Z)| () (-> |(Z x POW Z)| Bool))
(declare-const |set.intent (Z x POW Z)| (-> |? (Z x POW Z)| |POW (Z x POW Z)|))
(assert (!
  (forall ((p |? (Z x POW Z)|))
    (forall ((x |(Z x POW Z)|))
      (= (|set.in (Z x POW Z)| x (|set.intent (Z x POW Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x POW Z)|))

(declare-const |set.empty (POW Z x Z)| |POW (POW Z x Z)|)
(assert (!
  (forall ((e |(POW Z x Z)|)) (not (|set.in (POW Z x Z)| e |set.empty (POW Z x Z)|)))
  :named |ax.set.in.empty (POW Z x Z)|))

(declare-fun |~ Z POW Z| (|POW (Z x POW Z)|) |POW (POW Z x Z)|)
(assert (!
  (forall ((R |POW (Z x POW Z)|))
    (= (|~ Z POW Z| R)
       (|set.intent (POW Z x Z)|
         (lambda ((x |(POW Z x Z)|))
           (|set.in (Z x POW Z)| (maplet (snd x) (fst x)) R)))))
  :named |def.reverse (Z x POW Z)|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (not (= (|~ Z POW Z| (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (= x 3)))))(= x (maplet 2 (|set.intent Z| (lambda ((x |Z|)) (= x 4)))))(= x (maplet 2 (|set.intent Z| (lambda ((x |Z|)) (= x 7)))))(= x (maplet 3 (|set.intent Z| (lambda ((x |Z|)) (= x 3))))))))) |set.empty (POW Z x Z)|))
  :named |Goal|)
)
(check-sat)
(exit)
