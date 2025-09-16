(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |(Z x Z)| () (C |Z| |Z|))
(declare-sort P 1)
(define-sort |POW (Z x Z)| () (P |(Z x Z)|))
(declare-fun |set.in (Z x Z)| (|(Z x Z)| |POW (Z x Z)|) Bool)
(declare-fun |fun.eval Z Z| (|POW (Z x Z)| |Z|) |Z|)
 (assert (!
    (forall ((f |POW (Z x Z)|)(x |Z|))
        (|set.in (Z x Z)| (maplet x (|fun.eval Z Z| f x)) f))
    :named |ax.fun.eval (Z x Z)|))
(declare-const |int.succ| |POW (Z x Z)|)
(assert (!
  (forall ((x |(Z x Z)|))
      (=
        (|set.in (Z x Z)| x |int.succ|)
        (= (snd x) (+ (fst x) 1))
      )
  )
  :named |ax:int.succ|))
(assert (!
  (not
    (= (|fun.eval Z Z| |int.succ| 2) 3))
  :named |Goal|))
(check-sat)
(exit)
