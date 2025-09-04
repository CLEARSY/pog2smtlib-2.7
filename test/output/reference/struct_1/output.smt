(set-option :print-success false)
(set-logic HO_ALL)
(define-sort |BOOL| () Bool)
(define-sort |Z| () Int)
(declare-datatype |struct(Note : Z, Suffisant : BOOL)| ((|record struct(Note : Z, Suffisant : BOOL)| (Note Z) (Suffisant BOOL))))
(declare-sort P 1)
(define-sort |POW struct(Note : Z, Suffisant : BOOL)| () (P |struct(Note : Z, Suffisant : BOOL)|))
(define-sort |POW Z| () (P |Z|))
(define-sort |POW BOOL| () (P |BOOL|))

(declare-fun |set.in struct(Note : Z, Suffisant : BOOL)| (|struct(Note : Z, Suffisant : BOOL)| |POW struct(Note : Z, Suffisant : BOOL)|) Bool)

(declare-fun |set.in Z| (|Z| |POW Z|) Bool)

(declare-fun |set.in BOOL| (|BOOL| |POW BOOL|) Bool)

(define-sort |? struct(Note : Z, Suffisant : BOOL)| () (-> |struct(Note : Z, Suffisant : BOOL)| Bool))
(declare-const |set.intent struct(Note : Z, Suffisant : BOOL)| (-> |? struct(Note : Z, Suffisant : BOOL)| |POW struct(Note : Z, Suffisant : BOOL)|))
(assert (!
  (forall ((p |? struct(Note : Z, Suffisant : BOOL)|))
    (forall ((x |struct(Note : Z, Suffisant : BOOL)|))
      (= (|set.in struct(Note : Z, Suffisant : BOOL)| x (|set.intent struct(Note : Z, Suffisant : BOOL)| p))
         (p x))))
  :named |ax:set.in.intent struct(Note : Z, Suffisant : BOOL)|))

(declare-fun |interval| (|Z| |Z|) |POW Z|)
 (assert (!
    (forall ((l |Z|) (u |Z|) (e |Z|))
        (= (|set.in Z| e (|interval| l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))

(declare-const BOOL |POW BOOL|)
(assert (!
  (forall ((e |BOOL|)) (|set.in BOOL| e BOOL))
  :named |ax.set.in.BOOL|))

(declare-const |struct struct(Note : Z, Suffisant : BOOL)| (-> |? struct(Note : Z, Suffisant : BOOL)| |POW struct(Note : Z, Suffisant : BOOL)|))
(assert (!
  (forall ((p |? struct(Note : Z, Suffisant : BOOL)|))
    (forall ((x |struct(Note : Z, Suffisant : BOOL)|))
      (= (|set.in struct(Note : Z, Suffisant : BOOL)| x (|struct struct(Note : Z, Suffisant : BOOL)| p))
         (p x))))
  :named |ax.struct.definition struct(Note : Z, Suffisant : BOOL)|))
(assert (!
  (not (|set.in struct(Note : Z, Suffisant : BOOL)| (|record struct(Note : Z, Suffisant : BOOL)| 21 false) (|struct struct(Note : Z, Suffisant : BOOL)| (lambda ((x |struct(Note : Z, Suffisant : BOOL)|)) (and (|set.in Z| (Note x) (|interval| 0 20))(|set.in BOOL| (Suffisant x) BOOL))))))
  :named |Goal|)
)
(check-sat)
(exit)
