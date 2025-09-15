(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))

(declare-fun |min| (|POW Z|) |Z|)
(assert (!
  (forall ((s |POW Z|))
    (=> (not (= s |set.empty Z|)) (|set.in Z| (|min| s) s)))
  :named |ax.min.is.member|))
 (assert (!
   (forall ((s |POW Z|))
     (forall ((e |Z|))
        (=> (|set.in Z| e s) (<= (|min| s) e))))
  :named |ax.min.is.ge|))

(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (not (= (|min| (|set.intent Z| (lambda ((x |Z|)) (or (= x 1)(= x 60)(= x 0)(= x 5)(= x 3))))) 0))
  :named |Goal|))
(check-sat)
(exit)
