(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(define-sort |Z| () Int)
(declare-datatype |struct(Note, Suffisant)| ((|rec(Note, Suffisant)| (Note |Z|)(Suffisant |BOOL|))))
(assert (!
  (not
    (= (Suffisant (|rec(Note, Suffisant)|19 true)) true))
  :named |Goal|))
(check-sat)
(exit)
