(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |POW Z| () (P |Z|))
(define-sort |(Z x Z)| () (C |Z| |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)

(declare-fun |set.lambda Z Z| (|? Z| (-> |Z| |Z|)) |POW (Z x Z)|)
(assert (!
  (forall ((P |? Z|)(E (-> |Z| |Z|)))
    (forall ((p |(Z x Z)|))
      (= (|set.in (Z x Z)| p (|set.lambda Z Z| P E))
         (and (P (fst p))
              (= (snd p) (E (fst p)))))))
    :named |ax.set.in.lambda|))

(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(assert (!
  (not (|set.in (Z x Z)| (maplet 1 1) (|set.lambda Z Z| (lambda ((c |Z|)) (|set.in Z| c INTEGER))  (lambda ((c |Z|)) (+ c 1)))))
  :named |Goal|)
)
(check-sat)
(exit)
