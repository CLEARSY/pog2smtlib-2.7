(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const v1 |Z|)

(define-const MININT |Z| (- 2147483648))
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(define-const MAXINT |Z| 2147483647)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-const INT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e INT) (and (<= MININT e) (<= e MAXINT))))
  :named |ax.set.in.INT|))
(assert (!
  (< v1 MININT)
  :named |Define:lprp:2|)
)
(assert (!
  (not (|set.in Z| v1 INT))
  :named |Goal|)
)
(check-sat)
(exit)
