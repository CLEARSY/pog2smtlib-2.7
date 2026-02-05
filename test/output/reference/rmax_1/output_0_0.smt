(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |REAL| () Real)
(declare-sort P 1)
(define-sort |POW REAL| () (P |REAL|))
(declare-fun |set.in REAL| (|REAL| |POW REAL|) Bool)
(declare-const |set.empty REAL| |POW REAL|)
(assert (!
  (forall ((e |REAL|)) (not (|set.in REAL| e |set.empty REAL|)))
  :named |ax.set.in.empty REAL|))
(declare-fun |rmax| (|POW REAL|) |REAL|)
(assert (!
  (forall ((s |POW REAL|))
    (=> (not (= s |set.empty REAL|)) (|set.in REAL| (|rmax| s) s)))
  :named |ax.rmax.is.member|))
(assert (!
  (forall ((s |POW REAL|))
    (forall ((e |REAL|))
      (=> (|set.in REAL| e s) (<= e (|rmax| s)))))
    :named |ax.rmax.is.ge|))
(define-sort |? REAL| () (-> |REAL| Bool))
(declare-const |set.intent REAL| (-> |? REAL| |POW REAL|))
(assert (!
  (forall ((p |? REAL|))
    (forall ((x |REAL|))
      (= (|set.in REAL| x (|set.intent REAL| p))
         (@ p x))))
  :named |ax:set.in.intent REAL|))
(assert (!
  (not
    (= (|rmax| (|set.intent REAL| (lambda ((_c0 |REAL|)) (or (= _c0 1.0)(= _c0 60.0)(= _c0 0.0)(= _c0 5.0)(= _c0 3.0))))) 5.0))
  :named |Goal|))
(check-sat)
(exit)
