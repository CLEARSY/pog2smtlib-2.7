(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |STRING| () String)
(declare-sort P 1)
(define-sort |POW STRING| () (P |STRING|))

(declare-fun |set.in STRING| (|STRING| |POW STRING|) Bool)

(declare-const STRING |POW STRING|)
(assert (!
  (forall ((e |STRING|)) (|set.in STRING| e STRING))
  :named |ax.set.in.STRING|))
(assert (!
  (not (|set.in STRING| "E" STRING))
  :named |Goal|)
)
(check-sat)
(exit)
