(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |POW Z| () (P |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(define-sort |POW POW Z| () (P |POW Z|))
(declare-fun |set.in POW Z| (|POW Z| |POW POW Z|) Bool)
(define-sort |POW POW POW Z| () (P |POW POW Z|))
(declare-fun |set.subseteq POW Z| (|POW POW Z| |POW POW Z|) Bool)
(assert (!
    (forall ((s |POW POW Z|) (t |POW POW Z|))
      (=
        (|set.subseteq POW Z| s t)
        (forall ((e |POW Z|)) (=> (|set.in POW Z| e s) (|set.in POW Z| e t)))
      )
    )
    :named |ax.set.subseteq POW Z|))
(declare-fun |set.in POW POW Z| (|POW POW Z| |POW POW POW Z|) Bool)
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))
(declare-fun |sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (|set.in POW POW Z| s (|sub-sets POW Z| t))
      (|set.subseteq POW Z| s t)))
  :named |ax.sub-sets POW Z|))
(declare-const |set.empty POW Z| |POW POW Z|)
(assert (!
  (forall ((e |POW Z|)) (not (|set.in POW Z| e |set.empty POW Z|)))
  :named |ax.set.in.empty POW Z|))
(declare-fun |sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (|set.in POW Z| s (|sub-sets Z| t))
      (|set.subseteq Z| s t)))
  :named |ax.sub-sets Z|))
(declare-const |set.empty Z| |POW Z|)
(assert (!
  (forall ((e |Z|)) (not (|set.in Z| e |set.empty Z|)))
  :named |ax.set.in.empty Z|))
(declare-const vset |POW POW Z|)
(define-sort |? POW Z| () (-> |POW Z| Bool))
(declare-const |set.intent POW Z| (-> |? POW Z| |POW POW Z|))
(assert (!
  (forall ((p |? POW Z|))
    (forall ((x |POW Z|))
      (= (|set.in POW Z| x (|set.intent POW Z| p))
         (p x))))
  :named |ax:set.in.intent POW Z|))
(define-sort |? Z| () (-> |Z| Bool))
(declare-const |set.intent Z| (-> |? Z| |POW Z|))
(assert (!
  (forall ((p |? Z|))
    (forall ((x |Z|))
      (= (|set.in Z| x (|set.intent Z| p))
         (p x))))
  :named |ax:set.in.intent Z|))
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (=
      (= s t)
      (forall ((e |POW Z|)) (= (|set.in POW Z| e s) (|set.in POW Z| e t)))))
  :named |ax.set.eq POW Z|))
(declare-fun |non empty sub-sets POW Z| (|POW POW Z|) |POW POW POW Z|)
(assert (!
  (forall ((s |POW POW Z|) (t |POW POW Z|))
    (= (|set.in POW POW Z| s (|non empty sub-sets POW Z| t))
       (and (|set.in POW POW Z| s (|sub-sets POW Z| t))
            (not (= s |set.empty POW Z|)))))
  :named |ax.non empty sub-sets POW Z|))
(declare-fun |non empty sub-sets Z| (|POW Z|) |POW POW Z|)
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (= (|set.in POW Z| s (|non empty sub-sets Z| t))
       (and (|set.in POW Z| s (|sub-sets Z| t))
            (not (= s |set.empty Z|)))))
  :named |ax.non empty sub-sets Z|))
(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(declare-fun |union Z| (|POW POW Z|) |POW Z|)
(assert (!
  (forall ((E |POW POW Z|) (x |Z|))
    (= (|set.in Z| x (|union Z| E))
       (exists ((e |POW Z|)) (and (|set.in Z| x e) (|set.in POW Z| e E)))))
  :named |ax.set.in.generalized.union Z|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(assert (!
  (|set.in POW POW Z| vset (|non empty sub-sets POW Z| (|non empty sub-sets Z| INTEGER)))
  :named |Define:lprp:1|))
(assert (!
  (= vset (|set.intent POW Z| (lambda ((_c0 |POW Z|)) (or (= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (= _c1 0))))(= _c0 (|set.intent Z| (lambda ((_c1 |Z|)) (or (= _c1 1)(= _c1 2)))))))))
  :named |Define:lprp:2|))
(assert (!
  (not
    (= (|union Z| vset) (|set.intent Z| (lambda ((_c0 |Z|)) (or (= _c0 0)(= _c0 1)(= _c0 2))))))
  :named |Goal|))
(check-sat)
(exit)
