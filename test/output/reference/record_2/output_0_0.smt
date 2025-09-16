(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(define-sort |Z| () Int)
(declare-datatype |struct(Note, Suffisant)| ((|rec(Note, Suffisant)| (Note |Z|)(Suffisant |BOOL|))))
(assert (!
  (not
    (= (|rec(Note, Suffisant)|21 true) (|rec(Note, Suffisant)|(* 3 7) true)))
  :named |Goal|))
(check-sat)
(exit)
