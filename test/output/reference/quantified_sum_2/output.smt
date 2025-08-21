(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |(Z x Z)| () (C |Z| |Z|))

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))

(declare-fun |SIGMA| (|POW Z|) |Z|)
(assert (!
  (= 0 (|SIGMA| |set.empty Z|))
  :named |ax.sigma.empty|))
(assert (!
  (forall ((s |POW Z|))
    (forall ((e |Z|))
      (= (|set.in Z| e s)
        (= (|SIGMA| s)
          (+ e
             (|SIGMA|
               (|set.intent Z|
                 (lambda ((x |Z|)) (and (|set.in Z| x s) (not (= x e)))))))))))
  :named |ax.sigma.incr|))

(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(assert (!
  (not (= (|SIGMA| (|set.intent Z| (lambda ((c |Z|)) (exists ((y |(Z x Z)|)) (and (and
(|set.in Z| (fst y) (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 2)))))
(|set.in Z| (snd y) (|set.intent Z| (lambda ((x |Z|)) (or (= x 0)(= x 3)(= x 4)))))
) (= c (+ (fst y) (snd y)))))))) 23))
  :named |Goal|)
)
(check-sat)
(exit)
