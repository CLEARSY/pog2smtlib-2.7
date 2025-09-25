(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-datatype |struct(x1, y1)| ((|rec(x1, y1)| (x1 |Z|)(y1 |Z|))))
(declare-sort P 1)
(declare-datatype |struct(x2, y2)| ((|rec(x2, y2)| (x2 |struct(x1, y1)|)(y2 |struct(x1, y1)|))))
(define-sort |POW struct(x2, y2)| () (P |struct(x2, y2)|))
(define-sort |POW struct(x1, y1)| () (P |struct(x1, y1)|))
(declare-fun |set.in struct(x2, y2)| (|struct(x2, y2)| |POW struct(x2, y2)|) Bool)
(declare-fun |set.in struct(x1, y1)| (|struct(x1, y1)| |POW struct(x1, y1)|) Bool)
(define-sort |POW Z| () (P |Z|))
(define-sort |? struct(x2, y2)| () (-> |struct(x2, y2)| Bool))
(declare-const |set.intent struct(x2, y2)| (-> |? struct(x2, y2)| |POW struct(x2, y2)|))
(assert (!
  (forall ((p |? struct(x2, y2)|))
    (forall ((x |struct(x2, y2)|))
      (= (|set.in struct(x2, y2)| x (|set.intent struct(x2, y2)| p))
         (p x))))
  :named |ax:set.in.intent struct(x2, y2)|))
(define-sort |? struct(x1, y1)| () (-> |struct(x1, y1)| Bool))
(declare-const |set.intent struct(x1, y1)| (-> |? struct(x1, y1)| |POW struct(x1, y1)|))
(assert (!
  (forall ((p |? struct(x1, y1)|))
    (forall ((x |struct(x1, y1)|))
      (= (|set.in struct(x1, y1)| x (|set.intent struct(x1, y1)| p))
         (p x))))
  :named |ax:set.in.intent struct(x1, y1)|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-const |struct struct(x2, y2)| (-> |? struct(x2, y2)| |POW struct(x2, y2)|))
(assert (!
  (forall ((p |? struct(x2, y2)|))
    (forall ((x |struct(x2, y2)|))
      (= (|set.in struct(x2, y2)| x (|struct struct(x2, y2)| p))
         (p x))))
  :named |ax.struct.definition struct(x2, y2)|))
(declare-const struct2 |POW struct(x2, y2)|)
(assert (!
  (forall ((s |POW struct(x2, y2)|) (t |POW struct(x2, y2)|))
    (=
      (= s t)
      (forall ((e |struct(x2, y2)|)) (= (|set.in struct(x2, y2)| e s) (|set.in struct(x2, y2)| e t)))))
  :named |ax.set.eq struct(x2, y2)|))
(declare-const record22 |struct(x2, y2)|)
(declare-const record12 |struct(x1, y1)|)
(declare-const struct1 |POW struct(x1, y1)|)
(declare-const |struct struct(x1, y1)| (-> |? struct(x1, y1)| |POW struct(x1, y1)|))
(assert (!
  (forall ((p |? struct(x1, y1)|))
    (forall ((x |struct(x1, y1)|))
      (= (|set.in struct(x1, y1)| x (|struct struct(x1, y1)| p))
         (p x))))
  :named |ax.struct.definition struct(x1, y1)|))
(declare-const record11 |struct(x1, y1)|)
(declare-const record21 |struct(x2, y2)|)
(declare-const INTEGER |POW Z|)
(assert (!
  (forall ((e |Z|)) (|set.in Z| e INTEGER))
  :named |ax.set.in.INTEGER|))
(assert (!
  (forall ((s |POW struct(x1, y1)|) (t |POW struct(x1, y1)|))
    (=
      (= s t)
      (forall ((e |struct(x1, y1)|)) (= (|set.in struct(x1, y1)| e s) (|set.in struct(x1, y1)| e t)))))
  :named |ax.set.eq struct(x1, y1)|))
(assert (!
  (= struct1 (|struct struct(x1, y1)| (lambda ((x |struct(x1, y1)|)) (and (|set.in Z| (x1 x) INTEGER)(|set.in Z| (y1 x) INTEGER)))))
  :named |Define:lprp:1|))
(assert (!
  (= struct2 (|struct struct(x2, y2)| (lambda ((x |struct(x2, y2)|)) (and (|set.in struct(x1, y1)| (x2 x) struct1)(|set.in struct(x1, y1)| (y2 x) struct1)))))
  :named |Define:lprp:2|))
(assert (!
  (= record11 (|rec(x1, y1)|1 1))
  :named |Define:lprp:3|))
(assert (!
  (= record12 (|rec(x1, y1)|1 1))
  :named |Define:lprp:4|))
(assert (!
  (= record21 (|rec(x2, y2)|record11 record12))
  :named |Define:lprp:5|))
(assert (!
  (= record22 (|rec(x2, y2)|record12 record11))
  :named |Define:lprp:6|))
(assert (!
  (= (x1 record11) 1)
  :named |Hypothesis:1|))
(assert (!
  (not
    (= (x1 (x2 record21)) 1))
  :named |Goal|))
(check-sat)
(exit)
