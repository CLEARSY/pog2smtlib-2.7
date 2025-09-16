(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(declare-sort P 1)
(define-sort |POW REAL| () (P |REAL|))
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(declare-fun |set.in REAL| (|REAL| |POW REAL|) Bool)
(define-sort |(REAL x REAL)| () (C |REAL| |REAL|))
(declare-const |set.empty REAL| |POW REAL|)
(assert (!
  (forall ((e |REAL|)) (not (|set.in REAL| e |set.empty REAL|)))
  :named |ax.set.in.empty REAL|))
(define-sort |? REAL| () (-> |REAL| Bool))
(declare-const |set.intent REAL| (-> |? REAL| |POW REAL|))
(assert (!
  (forall ((p |? REAL|))
    (forall ((x |REAL|))
      (= (|set.in REAL| x (|set.intent REAL| p))
         (p x))))
  :named |ax:set.in.intent REAL|))
(define-sort |POW (REAL x REAL)| () (P |(REAL x REAL)|))
(declare-fun |rPI| (|POW REAL|) |REAL|)
(assert (!
  (= 1 (|rPI| |set.empty REAL|))
  :named |ax.rpi.empty|)
)
(assert (!
  (forall ((s |POW REAL|))
    (forall ((e |REAL|))
      (= (|set.in REAL| e s)
        (= (|rPI| s)
          (* e
             (|rPI|
               (|set.intent REAL|
                 (lambda ((x |REAL|)) (and (|set.in REAL| x s) (not (= x e)))))))))))
  :named |ax.rpi.incr|)
)
(declare-fun |set.in (REAL x REAL)| (|(REAL x REAL)| |POW (REAL x REAL)|) Bool)
(assert (!
  (not
    (= (|rPI| (|set.intent REAL| (lambda ((c |REAL|)) (exists ((y |(REAL x REAL)|)) (and     (and
      (|set.in REAL| (fst y) (|set.intent REAL| (lambda ((x |REAL|)) (= x 1.0))))
      (|set.in REAL| (snd y) (|set.intent REAL| (lambda ((x |REAL|)) (or (= x 3.0)(= x 4.0)))))) (= c (+ (fst y) (snd y)))))))) 11.0))
  :named |Goal|))
(check-sat)
(exit)
