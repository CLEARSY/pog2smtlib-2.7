(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(define-sort |Z| () Int)
(declare-datatype |struct(Note : Z, Suffisant : BOOL)| ((|record struct(Note : Z, Suffisant : BOOL)| (Note Z) (Suffisant BOOL))))
(assert (!
  (not
    (= (|record struct(Note : Z, Suffisant : BOOL)| 21 true) (|record struct(Note : Z, Suffisant : BOOL)| (* 3 7) true)))
  :named |Goal|))
(check-sat)
(exit)
