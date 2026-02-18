(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |Z| () Int)
(declare-sort P 1)
(define-sort |BOOL| () Bool)
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
(define-sort |POW Z| () (P |Z|))
(define-sort |POW BOOL| () (P |BOOL|))
(define-sort |(BOOL x Z)| () (C |BOOL| |Z|))
(declare-fun |set.in Z| (|Z| |POW Z|) Bool)
(declare-fun |set.in BOOL| (|BOOL| |POW BOOL|) Bool)
(define-sort |POW (BOOL x Z)| () (P |(BOOL x Z)|))
(declare-fun |set.in (BOOL x Z)| (|(BOOL x Z)| |POW (BOOL x Z)|) Bool)
(define-sort |POW POW (BOOL x Z)| () (P |POW (BOOL x Z)|))
(declare-fun |set.subseteq (BOOL x Z)| (|POW (BOOL x Z)| |POW (BOOL x Z)|) Bool)
(assert (!
    (forall ((s |POW (BOOL x Z)|) (t |POW (BOOL x Z)|))
      (=
        (|set.subseteq (BOOL x Z)| s t)
        (forall ((e |(BOOL x Z)|)) (=> (|set.in (BOOL x Z)| e s) (|set.in (BOOL x Z)| e t)))
      )
    )
    :named |ax.set.subseteq (BOOL x Z)|))
(declare-fun |set.in POW (BOOL x Z)| (|POW (BOOL x Z)| |POW POW (BOOL x Z)|) Bool)
(declare-fun |sub-sets (BOOL x Z)| (|POW (BOOL x Z)|) |POW POW (BOOL x Z)|)
(assert (!
  (forall ((s |POW (BOOL x Z)|) (t |POW (BOOL x Z)|))
    (=
      (|set.in POW (BOOL x Z)| s (|sub-sets (BOOL x Z)| t))
      (|set.subseteq (BOOL x Z)| s t)))
  :named |ax.sub-sets (BOOL x Z)|))
(declare-fun |set.product BOOL Z| (|POW BOOL| |POW Z|) |POW (BOOL x Z)|)
(assert (!
  (forall ((s1 |POW BOOL|) (s2 |POW Z|))
    (forall ((p |(BOOL x Z)|))
      (= (|set.in (BOOL x Z)| p (|set.product BOOL Z| s1 s2))
        (and (|set.in BOOL| (fst p) s1) (|set.in Z| (snd p) s2)))))
  :named |ax.set.in.product.1 (BOOL x Z)|))
(assert (!
  (forall ((s1 |POW BOOL|) (s2 |POW Z|))
    (forall ((x1 |BOOL|) (x2 |Z|))
      (= (|set.in (BOOL x Z)| (maplet x1 x2) (|set.product BOOL Z| s1 s2))
        (and (|set.in BOOL| x1 s1) (|set.in Z| x2 s2)))))
  :named |ax.set.in.product.2 (BOOL x Z)|))
(declare-fun |relations BOOL Z| (|POW BOOL| |POW Z|) |POW POW (BOOL x Z)|)
(assert (!
  (forall ((X |POW BOOL|) (Y |POW Z|))
    (= (|relations BOOL Z| X Y)
       (|sub-sets (BOOL x Z)| (|set.product BOOL Z| X Y))))
    :named |def.relations (BOOL x Z)|))
(declare-fun |functions BOOL Z| (|POW BOOL| |POW Z|) |POW POW (BOOL x Z)|)
(assert (!
  (forall ((X |POW BOOL|) (Y |POW Z|))
    (forall ((f |POW (BOOL x Z)|))
      (= (|set.in POW (BOOL x Z)| f (|functions BOOL Z| X Y))
         (forall ((p |(BOOL x Z)|) (q |(BOOL x Z)|))
           (=> (and (|set.in (BOOL x Z)| p f) (|set.in (BOOL x Z)| q f) (= (fst p) (fst q)))
               (= (snd p) (snd q)))))))
:named |ax:set.in.functions (BOOL x Z)|))
(declare-const s10 |Z|)
(declare-const s15 |BOOL|)
(declare-const s11 |POW Z|)
(declare-const s9 |Z|)
(declare-const s14 |Z|)
(declare-const s12 |POW (BOOL x Z)|)
(declare-const s5 |POW Z|)
(declare-const s13 |Z|)
(define-sort |? (BOOL x Z)| () (-> |(BOOL x Z)| Bool))
(declare-const |set.intent (BOOL x Z)| (-> |? (BOOL x Z)| |POW (BOOL x Z)|))
(assert (!
  (forall ((p |? (BOOL x Z)|))
    (forall ((x |(BOOL x Z)|))
      (= (|set.in (BOOL x Z)| x (|set.intent (BOOL x Z)| p))
         (@ p x))))
  :named |ax:set.in.intent (BOOL x Z)|))
(assert (!
  (forall ((s |POW (BOOL x Z)|) (t |POW (BOOL x Z)|))
    (=
      (= s t)
      (forall ((e |(BOOL x Z)|)) (= (|set.in (BOOL x Z)| e s) (|set.in (BOOL x Z)| e t)))))
  :named |ax.set.eq (BOOL x Z)|))
(declare-fun |set.subseteq Z| (|POW Z| |POW Z|) Bool)
(assert (!
    (forall ((s |POW Z|) (t |POW Z|))
      (=
        (|set.subseteq Z| s t)
        (forall ((e |Z|)) (=> (|set.in Z| e s) (|set.in Z| e t)))
      )
    )
    :named |ax.set.subseteq Z|))
(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
(assert (!
  (forall ((s |POW Z|) (t |POW Z|))
    (=
      (= s t)
      (forall ((e |Z|)) (= (|set.in Z| e s) (|set.in Z| e t)))))
  :named |ax.set.eq Z|))
(declare-fun |functions.partial BOOL Z| (|POW BOOL| |POW Z|) |POW POW (BOOL x Z)|)
(assert (!
  (forall ((e1 |POW BOOL|) (e2 |POW Z|))
    (forall ((f |POW (BOOL x Z)|))
      (= (|set.in POW (BOOL x Z)| f (|functions.partial BOOL Z| e1 e2))
         (and (|set.in POW (BOOL x Z)| f (|relations BOOL Z| e1 e2))
              (|set.in POW (BOOL x Z)| f (|functions BOOL Z| e1 e2))))))
  :named |ax:def.pfun (BOOL x Z)|)
)
(declare-const BOOL |POW BOOL|)
(assert (!
  (forall ((e |BOOL|)) (|set.in BOOL| e BOOL))
  :named |ax.set.in.BOOL|))
(declare-const s13$1 |Z|)
(assert (!
  (= s5 (|interval| 0 255))
  :named |Define:ctx:2|))
(assert (!
  (|set.in Z| s9 s5)
  :named |Define:ctx:3|))
(assert (!
  (|set.in Z| s10 s5)
  :named |Define:ctx:4|))
(assert (!
  (|set.subseteq Z| s11 s5)
  :named |Define:ctx:5|))
(assert (!
  (= s12 (|set.intent (BOOL x Z)| (lambda ((_c0 |(BOOL x Z)|)) (or (= _c0 (maplet true s9))(= _c0 (maplet false s10))))))
  :named |Define:ctx:6|))
(assert (!
  (|set.in POW (BOOL x Z)| s12 (|functions.partial BOOL Z| BOOL s5))
  :named |Define:seext:1|))
(assert (!
  (|set.in Z| s13 s5)
  :named |Define:inv:1|))
(assert (!
  (|set.in Z| s14 s5)
  :named |Define:inv:2|))
(assert (!
  (= s15 true)
  :named |Hypothesis:1|))
(assert (!
  (|set.in Z| s13$1 s11)
  :named |Local_Hyp:0|))
(assert (!
  (not
    (|set.in Z| s13$1 s5))
  :named |Goal|))
(check-sat)
(exit)
