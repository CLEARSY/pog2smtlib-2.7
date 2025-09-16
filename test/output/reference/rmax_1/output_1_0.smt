(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(declare-sort P 1)
(define-sort |POW REAL| () (P |REAL|))
(declare-fun |set.in REAL| (|REAL| |POW REAL|) Bool)
(define-sort |? REAL| () (-> |REAL| Bool))
(declare-const |set.intent REAL| (-> |? REAL| |POW REAL|))
(assert (!
  (forall ((p |? REAL|))
    (forall ((x |REAL|))
      (= (|set.in REAL| x (|set.intent REAL| p))
         (p x))))
  :named |ax:set.in.intent REAL|))
(assert (!
  (not
    (exists
      ((xx |REAL|))
      (and
        (|set.in REAL| xx (|set.intent REAL| (lambda ((x |REAL|)) (or (= x 1.0)(= x 60.0)(= x 0.0)(= x 5.0)(= x 3.0)))))
        (forall
          ((yy |REAL|))
          (=>
            (|set.in REAL| yy (|set.intent REAL| (lambda ((x |REAL|)) (or (= x 1.0)(= x 60.0)(= x 0.0)(= x 5.0)(= x 3.0)))))
            (>= xx yy))))))
  :named |Goal|))
(check-sat)
(exit)
