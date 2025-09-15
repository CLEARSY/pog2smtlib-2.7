(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x POW Z)| () (C |Z| |POW Z|))
(define-sort |POW (Z x POW Z)| () (P |(Z x POW Z)|))

(declare-fun |set.in (Z x POW Z)| (|(Z x POW Z)| |POW (Z x POW Z)|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const func |POW (Z x POW Z)|)

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

(assert (!
  (forall ((s |POW (Z x POW Z)|) (t |POW (Z x POW Z)|))
    (=
      (= s t)
      (forall ((e |(Z x POW Z)|)) (= (|set.in (Z x POW Z)| e s) (|set.in (Z x POW Z)| e t)))
    )
  )
  :named |ax.set.eq (Z x POW Z)|))
(define-sort |POW POW Z| () (P |POW Z|))
(define-sort |(Z x POW POW Z)| () (C |Z| |POW POW Z|))
(define-sort |POW (Z x POW POW Z)| () (P |(Z x POW POW Z)|))

(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)

(declare-fun |set.in (Z x POW POW Z)| (|(Z x POW POW Z)| |POW (Z x POW POW Z)|) Bool)

(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (p x))))
  :named |ax:set.in.intent POW Z|))

(declare-fun |fnc Z POW Z| (|POW (Z x POW Z)|) |POW (Z x POW POW Z)|)
(assert (!
(forall ((r |POW (Z x POW Z)|)(p |(Z x POW POW Z)|))
  (= (|set.in (Z x POW POW Z)| p (|fnc Z POW Z| r))
     (and (exists ((y |POW Z|)) (|set.in (Z x POW Z)| (maplet (fst p) y) r))
          (forall ((y |POW Z|))
            (= (|set.in POW Z| y (snd p))
               (|set.in (Z x POW Z)| (maplet (fst p) y) r))))))
  :named |ax.set.in.fnc (Z x POW Z)|))
(assert (!
  (= func (|set.intent (Z x POW Z)| (lambda ((x |(Z x POW Z)|)) (or (= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 4))))))(= x (maplet 0 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 4)(= x 6)(= x 7))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 5)(= x 4))))))(= x (maplet 1 (|set.intent Z| (lambda ((x |Z|)) (= x 1)))))(= x (maplet 2 (|set.intent Z| (lambda ((x |Z|)) (or (= x 6)(= x 8)(= x 5))))))))))
  :named |Define:lprp:1|))
(assert (!
  (not (|set.in (Z x POW POW Z)| (maplet 0 (|set.intent POW Z| (lambda ((x |POW Z|)) (or (= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 4)))))(= x (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)(= x 4)(= x 6)(= x 7))))))))) (|fnc Z POW Z| func)))
  :named |Goal|))
(check-sat)
(exit)
