(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const v1 |Z|)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))

(define-const MAXINT |Z| 2147483647)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-const NAT |POW Z|)
(assert (!
  (forall ((e |Z|)) (= (|set.in Z| e NAT) (and (<= 0 e) (<= e MAXINT))))
  :named |ax.set.in.NAT|))
(assert (!
  (< 2 v1)
  :named |Define:lprp:2|))
(assert (!
  (< v1 5)
  :named |Define:lprp:3|))
(assert (!
  (not (|set.in Z| v1 NAT))
  :named |Goal|))
(check-sat)
(exit)
