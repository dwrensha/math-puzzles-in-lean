(param (A B C D) polygon)

(assert (cong A D C D))
(assert (= (uangle D A B) (uangle A B C)))

(define M point (midp B C)))
(define E point (inter-ll (line D M) (line A B)))

; problem statement notes that this constraint is not actually needed
;(assert (< (uangle D A B) 1.57 ))

; define these just so they get drawn
(define L1 line (line C E))
(define L2 line (line A C))

(eval (= (uangle B E C) (uangle D A C)))
