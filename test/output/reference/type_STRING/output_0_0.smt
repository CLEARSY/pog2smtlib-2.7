(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(define-sort |STRING| () String)
(declare-const va |Z|)
(declare-const str |STRING|)
(assert (!
  (< 0 va)
  :named |Define:inv:2|))
(assert (!
  (not
    (< 0 (+ va 1)))
  :named |Goal|))
(check-sat)
(exit)
