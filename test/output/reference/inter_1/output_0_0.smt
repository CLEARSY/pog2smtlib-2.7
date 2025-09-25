(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const elt |Z|)
(declare-const vset1 |POW POW Z|)
(declare-const vset2 |POW Z|)
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(declare-fun |inter Z| (|POW POW Z|) |POW Z|)
(assert (!
  (forall ((E |POW POW Z|) (x |Z|))
    (= (|set.in Z| x (|inter Z| E))
       (forall ((e |POW Z|)) (=> (|set.in Z| x e) (|set.in POW Z| e E)))))
  :named |ax.set.in.generalized.intersection Z|))
(assert (!
  (|set.in POW Z| vset2 vset1)
  :named |Define:lprp:3|))
(assert (!
  (|set.in Z| elt vset2)
  :named |Define:lprp:4|))
(assert (!
  (not
    (|set.in Z| elt (|inter Z| vset1)))
  :named |Goal|))
(check-sat)
(exit)
