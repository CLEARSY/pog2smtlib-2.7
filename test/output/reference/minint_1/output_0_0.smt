(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)

(define-const MININT |Z| (- 2147483648))
(assert (!
  (not (= MININT 0))
  :named |Goal|))
(check-sat)
(exit)
