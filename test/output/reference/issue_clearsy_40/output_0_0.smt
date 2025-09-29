(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(define-sort |BOOL| () Bool)
(define-const MININT |Z| (- 2147483648))
(define-const MAXINT |Z| 2147483647)
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const s864 |BOOL|)
(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (not
    (= INT INT))
  :named |Goal|))
(check-sat)
(exit)
