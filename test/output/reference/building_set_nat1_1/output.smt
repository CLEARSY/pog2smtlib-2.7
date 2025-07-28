(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-const v1 |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(define-const MAXINT |Z| 2147483647)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-const NAT1 |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT1) (and (<= 1 e) (<= e MAXINT))))
  :named |ax.set.in.NAT1|))
(assert (!
  (< v1 0)
  :named |Define:lprp:2|)
)
(assert (!
  (not (|set.in Z| v1 NAT1))
  :named |Goal|)
)
(check-sat)
(exit)
