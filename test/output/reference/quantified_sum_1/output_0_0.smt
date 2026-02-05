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
         (@ p x))))
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
  (not
    (= (|SIGMA| (|set.intent Z| (lambda ((_c0 |Z|)) (exists ((_c1 |(Z x Z)|)) (and     (and
      (|set.in Z| (fst _c1) (|set.intent Z| (lambda ((_c2 |Z|)) (or (= _c2 1)(= _c2 2)))))
      (|set.in Z| (snd _c1) (|set.intent Z| (lambda ((_c2 |Z|)) (or (= _c2 0)(= _c2 3)(= _c2 4)))))) (= _c0 (+ (fst _c1) (snd _c1)))))))) 22))
  :named |Goal|))
(check-sat)
(exit)
