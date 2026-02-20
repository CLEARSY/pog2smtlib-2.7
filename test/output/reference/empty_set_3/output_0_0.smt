(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(declare-sort P 1)
(define-sort |POW BOOL| () (P |BOOL|))
(declare-const vset |POW BOOL|)
(declare-fun |set.in BOOL| (|BOOL| |POW BOOL|) Bool)
(declare-const |set.empty BOOL| |POW BOOL|)
(assert (!
  (forall ((e |BOOL|)) (not (|set.in BOOL| e |set.empty BOOL|)))
  :named |ax.set.in.empty BOOL|))
(declare-fun |set.subseteq BOOL| (|POW BOOL| |POW BOOL|) Bool)
(assert (!
  (forall ((s |POW BOOL|) (t |POW BOOL|) (e |BOOL|))
    (=>
      (and (|set.subseteq BOOL| s t) (|set.in BOOL| e s))
      (|set.in BOOL| e t)))
  :named |ax.set.subseteq.elim BOOL|))
(assert (!
  (forall ((s |POW BOOL|) (t |POW BOOL|))
    (=>
      (forall ((e |BOOL|)) (=> (|set.in BOOL| e s) (|set.in BOOL| e t)))
      (|set.subseteq BOOL| s t)))
  :named |ax.set.subseteq.intro BOOL|))
(assert (!
  (not
    (|set.subseteq BOOL| vset |set.empty BOOL|))
  :named |Goal|))
(check-sat)
(exit)
