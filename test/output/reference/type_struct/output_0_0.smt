(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(declare-datatype |struct(f0 : BOOL, f1 : BOOL, f2 : BOOL)| ((|record struct(f0 : BOOL, f1 : BOOL, f2 : BOOL)| (f0 BOOL) (f1 BOOL) (f2 BOOL))))
(declare-const co |struct(f0 : BOOL, f1 : BOOL, f2 : BOOL)|)
(assert (!
  (not
    (= co (|record struct(f0 : BOOL, f1 : BOOL, f2 : BOOL)| false false false)))
  :named |Goal|))
(check-sat)
(exit)
