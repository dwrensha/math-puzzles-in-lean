(param (A B C) triangle)
(param D point (on-seg A B))
(param E point (on-seg A B))

(assert (= (mul (div (dist A D) (dist D B)) (div (dist A E) (dist E B))) (mul (div (dist A C) (dist C B)) (div (dist A C) (dist C B)))))

; define these just so they get drawn
(define L1 line (line C E))
(define L2 line (line C D))

(eval (= (uangle A C D) (uangle B C E)))