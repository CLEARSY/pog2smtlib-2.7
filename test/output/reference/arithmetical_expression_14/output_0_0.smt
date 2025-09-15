(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)

(define-fun-rec |int.exp| ((n |Z|) (p |Z|)) |Z|
 (ite (= p 0)
    1
    (ite (> p 0)
        (* n (|int.exp| n (- p 1)))
        0)))
(assert (!
  (not (= (|int.exp| 2 3) 8))
  :named |Goal|))
(check-sat)
(exit)
