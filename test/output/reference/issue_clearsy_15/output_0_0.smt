(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(declare-datatype |struct(f0, f1, f2)| ((|rec(f0, f1, f2)| (f0 |BOOL|)(f1 |BOOL|)(f2 |BOOL|))))
(declare-const co |struct(f0, f1, f2)|)
(assert (!
  (not
    (= (+ 1 1) 2))
  :named |Goal|))
(check-sat)
(exit)
