(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |rel.image Z Z| (|POW (Z x Z)| |POW Z|) |POW Z|)
(assert (!
  (forall ((r |POW (Z x Z)|) (s |POW Z|) (x |Z|))
    (= (|set.in Z| x (|rel.image Z Z| r s))
       (exists ((y |Z|)) (and (|set.in Z| y s) (|set.in (Z x Z)| (maplet y x) r)))))
  :named |ax:set.in.image (Z x POW (Z x Z))|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))
    )
  )
  :named |ax.set.eq Z|))

(define-sort |? (Z x Z)| () (-> |(Z x Z)| Bool))
(declare-const |set.intent (Z x Z)| (-> |? (Z x Z)| |POW (Z x Z)|))
(assert (!
  (forall ((p |? (Z x Z)|))
    (forall ((x |(Z x Z)|))
      (= (|set.in (Z x Z)| x (|set.intent (Z x Z)| p))
         (p x))))
  :named |ax:set.in.intent (Z x Z)|))
(assert (!
  (not (= (|rel.image Z Z| (|set.intent (Z x Z)| (lambda ((x |(Z x Z)|)) (or (= x (maplet 0 1))(= x (maplet 1 1))(= x (maplet 1 6))(= x (maplet 4 1))))) (|set.intent Z| (lambda ((x |Z|)) (= x 0)))) (|set.intent Z| (lambda ((x |Z|)) (= x 1)))))
  :named |Goal|))
(check-sat)
(exit)
