(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(define-sort |Z| () Int)
(define-fun-rec |real.exp| ((n |REAL|) (p |Z|)) |REAL|
 (ite (= p 0)
    1.0
    (ite (> p 0)
        (* n (|real.exp| n (- p 1)))
        0.0))
 )
 (assert (!
  (not
    (= (|real.exp| 2.0 3) 8.0))
  :named |Goal|))
(check-sat)
(exit)
