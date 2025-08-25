(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)

(declare-fun |real.div| (|REAL| |REAL|) |REAL|)
(assert (!
  (forall ((a |REAL|) (b |REAL|))
    (and
      (=> (and (<= 0 a) (< 0 b))
        (= (|real.div| a b) (/ a b)))
      (=> (and (<= 0 a) (< b 0))
        (= (|real.div| a b) (- (/ a (- b)))))
      (=> (and (< a 0) (< 0 b))
        (= (|real.div| a b) (- (/ (- a) b))))
      (=> (and (<= a 0) (< b 0))
        (= (|real.div| a b) (/ a b)))))
  :named |ax.real.div :1|))
(assert (!
  (not (= (|real.div| 5.0 2.0) 2.5))
  :named |Goal|)
)
(check-sat)
(exit)
