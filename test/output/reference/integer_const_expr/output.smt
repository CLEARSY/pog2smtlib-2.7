(set-option :print-success false)
(set-logic ALL)
; Prelude

(declare-sort P 1)


(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))

; Opaque formulas
; Defines
(define-fun |def_B definitions| () Bool true)
(define-fun |def_ctx| () Bool true)
(define-fun |def_seext| () Bool true)
(define-fun |def_lprp| () Bool true)
(define-fun |def_inprp| () Bool true)
(define-fun |def_inext| () Bool true)
(define-fun |def_inv| () Bool true)
(define-fun |def_ass| () Bool  (= (+ 0 1) (+ 2 1)))
(define-fun |def_cst| () Bool true)
(define-fun |def_sets| () Bool true)
; PO group 0 
(assert |def_B definitions|)
(assert |def_ctx|)
(assert |def_cst|)
(assert |def_lprp|)
(assert |def_inprp|)
(assert |def_inext|)
(assert |def_seext|)
(assert |def_inv|)
; PO 1 in group 0
(assert (not (= (+ 0 1) (+ 2 1))))
(check-sat)
(exit)