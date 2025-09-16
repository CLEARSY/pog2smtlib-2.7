(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-const cint |Z|)
(define-const MININT |Z| (- 2147483648))
(assert (!
  (not
    (= cint MININT))
  :named |Goal|))
(check-sat)
(exit)
