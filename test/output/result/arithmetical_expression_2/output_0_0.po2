(set-option :print-success false)
(set-logic ALL)
(define-sort |Z| () Int)
(declare-const cint |Z|)

(define-const MAXINT |Z| 2147483647)
(assert (!
  (not (= cint MAXINT))
  :named |Goal|)
)
(check-sat)
(exit)
