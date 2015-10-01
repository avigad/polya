; this file encodes many of the examples from Polya in ACL2.
; commented examples are not solved by ACL2 with the given settings.

(include-book "arithmetic-5/top" :dir :system)
(include-book "make-event/proof-by-arith" :dir :system)
 (set-default-hints   
  '((nonlinearp-default-hint 
     stable-under-simplificationp hist pspv)))


(local (defstub expnt (*) => *))
(local (skip-proofs (defthm exp-type (implies (rationalp x0) (rationalp (expnt x0))) :rule-classes (:type-prescription))))
(local (skip-proofs (defthm exp-mon (implies (and (rationalp x0) (rationalp x1) (> x0 x1)) (> (expnt x0) (expnt x1)) ) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-mon2 (implies (and (rationalp x0) (rationalp x1) (>= x0 x1)) (>= (expnt x0) (expnt x1)) ) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-pos (implies (rationalp x0) (> (expnt x0) 0) ) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-zero (implies (and (rationalp x0) (> x0 0)) (> (expnt x0) 1 )) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-zero1 (implies (and (rationalp x0) (>= x0 0)) (>= (expnt x0) 1 )) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-sum (implies (and (rationalp x) (rationalp y)) (= (expnt (+ x y)) (* (expnt x) (expnt y)))) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm exp-prod (implies (and (rationalp x) (rationalp y)) (= (expnt (* x y)) (expt (expnt x) y))) :rule-classes (:forward-chaining))))
      
(local (defstub logrm (*) => *))
(local (skip-proofs (defthm log-type (implies (rationalp x0) (rationalp (logrm x0))) :rule-classes (:type-prescription))))  
(local (skip-proofs (defthm log-mon (implies (and (rationalp x0) (rationalp x1) (> x0 x1) (> x1 0)) (> (logrm x0) (logrm x1)) ) :rule-classes (:forward-chaining))))
(local (skip-proofs (defthm log-one (implies (and (rationalp x0) (> x0 1)) (> (logrm x0) 0)) :rule-classes (:forward-chaining))))
  
(encapsulate () (local (defthm thm-0 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (> u 0) (< u v) (< v 1) (>= x 2) (<= x y) ) (< (* 2 (* (expt u 2) x)) (* v (expt y 2)))) :rule-classes nil)))

;(encapsulate () (local (defthm thm-1 (implies (and (rationalp y) (rationalp x) (> x 1) ) (>= (* (+ 1 (expt y 2)) x) (+ 1 (expt y 2)))) :rule-classes nil)))

(encapsulate () (local (defthm thm-2 (implies (and (rationalp x) (> x 0) (< x 1) ) (> (expt (+ (* -1 x) 1) -1) (expt (+ (* -1 (expt x 2)) 1) -1))) :rule-classes nil)))

;(encapsulate () (local (defthm thm-3 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp z) (> u 0) (< u v) (> z 0) (< (+ 1 z) w) ) (< (expt (+ u v z) 3) (expt (+ u v w 1) 5))) :rule-classes nil)))

;(encapsulate () (local (defthm thm-4 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp z) (> u 0) (< u v) (> z 0) (< (+ 1 z) w) ) (< (expt (+ u v z) 33) (expt (+ u v w 1) 55))) :rule-classes nil)))

;(encapsulate () (local (defthm thm-5 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp z) (> u 0) (< u (expt (+ 23 (expt v 2)) 3)) (> z 0) (< (+ 1 z) w) ) (< (expt (+ u (expt (+ 23 (expt v 2)) 3) z) 3) (expt (+ u (expt (+ 23 (expt v 2)) 3) w 1) 5))) :rule-classes nil)))

(encapsulate () 

(local (defstub f (* ) => *))

(local (skip-proofs (defthm f-type (implies (rationalp x0) (rationalp (f x0))) :rule-classes (:type-prescription))))

(local (skip-proofs (defthm ax-0 (implies (rationalp x) (<= (f x) 1)) :rule-classes (:forward-chaining))))

(local (proof-by-arith (defthm thm-6 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp x) (< u v) (> w 0) ) (< (+ u (* w (f x))) (+ v w))) :rule-classes nil)))
)

(encapsulate () 

(local (defstub f (* ) => *))

(local (skip-proofs (defthm f-type (implies (rationalp x0) (rationalp (f x0))) :rule-classes (:type-prescription))))

(local (skip-proofs (defthm ax-0 (implies (and (rationalp x) (rationalp y) (>= x y)) (>= (f x) (f y))) :rule-classes (:forward-chaining))))

(local (proof-by-arith (defthm thm-7 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (< u v) (<= x y) ) (< (+ u (f x)) (+ v (f y)))) :rule-classes nil)))
)

(encapsulate () 

(local (defstub f (* ) => *))

(local (skip-proofs (defthm f-type (implies (rationalp x0) (rationalp (f x0))) :rule-classes (:type-prescription))))

(local (skip-proofs (defthm ax-0 (implies (rationalp x) (<= (f x) 2)) :rule-classes (:forward-chaining))))

(local (proof-by-arith (defthm thm-8 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp x) (< u v) (> w 0) ) (< (+ u (* w (+ -1 (f x)))) (+ v w))) :rule-classes nil)))
)

(encapsulate () 

(local (defstub f (* ) => *))

(local (skip-proofs (defthm f-type (implies (rationalp x0) (rationalp (f x0))) :rule-classes (:type-prescription))))

(local (skip-proofs (defthm ax-0 (implies (and (rationalp x) (rationalp y) (>= x y)) (>= (f x) (f y))) :rule-classes (:forward-chaining))))

(local (proof-by-arith (defthm thm-9 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (< u v) (> v 1) (<= x y) ) (< (+ (f x) u) (+ (expt v 2) (f y)))) :rule-classes nil)))
)

(encapsulate () 

(local (defstub f (* ) => *))

(local (skip-proofs (defthm f-type (implies (rationalp x0) (rationalp (f x0))) :rule-classes (:type-prescription))))

(local (skip-proofs (defthm ax-0 (implies (and (rationalp x) (rationalp y) (>= x y)) (>= (f x) (f y))) :rule-classes (:forward-chaining))))

(local (proof-by-arith (defthm thm-10 (implies (and (rationalp s) (rationalp u) (rationalp w) (rationalp v) (rationalp y) (rationalp x) (< u v) (> w 1) (> s 2) (< (* (/ 1 3) (+ w s)) v) (<= x y) ) (< (+ (f x) u) (+ (expt v 2) (f y)))) :rule-classes nil)))
)

#|(encapsulate () 

(local (proof-by-arith (defthm thm-11 (implies (and (rationalp w) (rationalp y) (rationalp x) (rationalp z) (> z (expnt x)) (> w (expnt y)) ) (> (* (expt w 2) (expt z 3)) (expnt (+ (* 3 x) (* 2 y))))) :rule-classes nil)))
)#\
#|
(encapsulate () 







(local (proof-by-arith (defthm thm-12 (implies (and (rationalp a) (rationalp c) (rationalp b) (> a 1) (!= b 0) (> c 0) (> (logrm (expt b 2)) 4) (> (logrm c) 1) ) (> (logrm (* (expt c 3) (expt b 2) a)) 7)) :rule-classes nil)))
)

(encapsulate () 







(local (proof-by-arith (defthm thm-13 (implies (and (rationalp x) (rationalp u) (rationalp v) (> u 0) (> v 0) (> x 0) (> (logrm x) (+ (* 2 u) v)) ) (> x 1)) :rule-classes nil)))
)|#

(encapsulate () 







(local (proof-by-arith (defthm thm-14 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (< x y) (<= u v) ) (<= (+ u (min (+ (* 2 u) x) (+ (* 2 v) y))) (+ (* 3 v) x))) :rule-classes nil)))
)
#|
(encapsulate () 

(local (defstub root_3 (* ) => *))

(local (skip-proofs (defthm root_3-type (implies (rationalp x0) (rationalp (root_3 x0))) :rule-classes (:type-prescription))))



(local (proof-by-arith (defthm thm-15 (implies (and (rationalp u) (rationalp v) (> u 0) (> v 1) ) (> (root_3 (* (expt v 4) (expt u 9))) (* v (expt u 3)))) :rule-classes nil)))
)|#

(encapsulate () 







(local  (defthm thm-16 (implies (and (rationalp y) (rationalp x) (> y 0) ) (< (abs (+ (* 3 x) (* 2 y) 5)) (+ (* 4 (abs x)) (* 3 y) 6))) :rule-classes nil))
)

#|(encapsulate () 







(local (proof-by-arith (defthm thm-17 (implies (and (rationalp y) (rationalp x) ) (>= (expnt (max (abs x) y)) 1)) :rule-classes nil)))
)|#

#|(encapsulate () 







(local (proof-by-arith (defthm thm-18 (implies (and (rationalp y) (rationalp x) (> y (max 2 (* 3 x))) (> x 0) ) (> (expnt (+ (* 4 y) (* -3 x))) (expnt 6))) :rule-classes nil)))
)|#

#|(encapsulate () 







(local (proof-by-arith (defthm thm-19 (implies (and (rationalp y) (rationalp x) (> y 0) ) (> (logrm (+ 1 (abs x) y)) 0)) :rule-classes nil)))
)|#

;fails
;(encapsulate () (local (defthm thm-24 (implies (and (rationalp c) (rationalp x) (rationalp K) (rationalp eps) (rationalp n) (>= n 0) (< n (* (/ 1 2) (* K x))) (> c 0) (> eps 0) (< eps 1) ) (< (* (+ (* (/ 1 3) (* eps (expt (+ 3 c) -1))) 1) n) (* K x))) :rule-classes nil)))

;fails- takes too long
;(encapsulate () (local (defthm thm-25 (implies (and (rationalp y) (rationalp x) (> x 0) (< x y) ) (< (* (+ 1 (expt x 2)) (expt (expt (+ 2 y) 17) -1)) (* (+ 2 (expt y 2)) (expt (expt (+ 2 x) 10) -1)))) :rule-classes nil)))

(encapsulate () (local (defthm thm-29 (implies (and (rationalp y) (rationalp x) (> x 0) (> y 0) (< y 1) (> (* x y) (+ x y)) ) nil) :rule-classes nil)))

; fails- takes too long
;(encapsulate () (local (defthm thm-30 (implies (and (rationalp y) (rationalp x) (> x 0) (> y 0) (< y 1) (> (* (expt x 150) (expt y 150)) (+ (expt x 150) (expt y 150))) ) nil) :rule-classes nil)))

;(encapsulate () (local (defthm thm-31 (implies (and (rationalp y) (rationalp x) (> x 0) (> y -1) (< y 0) (> (* (expt (+ 1 y) 150) (expt x 150)) (+ (expt x 150) (expt (+ 1 y) 150))) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-35 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 0) (< y z) ) (< (* x y) (* x z))) :rule-classes nil)))

(encapsulate () (local (defthm thm-36 (implies (and (rationalp w) (rationalp y) (rationalp x) (rationalp z) (> x 0) (< (* x z y) 0) (> (* x w) 0) ) (> w (* y z))) :rule-classes nil)))

;fails- can't factor
;(encapsulate () (local (defthm thm-38 (implies (and (rationalp x) (< (+ (* 2 x) (expt x 2) 1) 0) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-39 (implies (and (rationalp y) (rationalp x) (rationalp z) (rationalp w) (<= (* x (+ y z)) 0) (> (+ y z) 0) (>= x 0) (> (* x w) 0) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-40 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (> x 0) (< x (* 3 y)) (< u v) (< v 0) (> (expt v 2) 1) (< (expt v 2) x) ) (< (+ (* 9 (* u (expt y 2))) 1) (+ (* v (expt x 2)) x))) :rule-classes nil)))

; fails
;(encapsulate () (local (defthm thm-41 (implies (and (rationalp r) (rationalp u) (rationalp w) (rationalp v) (rationalp y) (rationalp x) (rationalp z) (> x 0) (< x y) (> u 0) (< u v) (> (+ w z) 0) (< (+ w z) (+ -1 r)) ) (< (+ u (* (expt (+ 1 x) 2) (+ (* 2 w) (* 2 z) 3))) (+ (* 2 v) (* (expt (+ 1 y) 2) (+ (* 2 r) 1))))) :rule-classes nil)))

; fails after a while
;(encapsulate () (local (defthm thm-42 (implies (and (rationalp y) (rationalp x) (< (+ x (expt y -1)) 2) (< y 0) (> (* y (expt x -1)) 1) (>= x -2) (<= x 2) (>= y -2) (<= y 2) ) (<= (* (expt x 2) (expt y -1)) (+ (* -1 x) 1))) :rule-classes nil)))

(encapsulate () (local (defthm thm-43 (implies (and (rationalp u) (rationalp w) (rationalp v) (rationalp y) (rationalp x) (rationalp z) (> u 0) (< u v) (> x 1) (< x y) (> w 0) (< w z) ) (< (+ u (* x w)) (+ v (* z (expt y 2))))) :rule-classes nil)))

;fails after a while
;(encapsulate () (local (defthm thm-44 (implies (and (rationalp y) (rationalp x) (< (+ x (expt y -1)) 2) (< y 0) (> (* y (expt x -1)) 1) (>= x -2) (<= x 2) (>= y -2) (<= y 2) (> (* (expt x 2) (expt y -1)) (+ (* -1 x) 1)) ) nil) :rule-classes nil)))

; fails
;(encapsulate () (local (defthm thm-45 (implies (and (rationalp r) (rationalp u) (rationalp w) (rationalp v) (rationalp y) (rationalp x) (rationalp z) (> x 0) (< x y) (> u 0) (< u v) (> (+ w z) 0) (< (+ w z) (+ -1 r)) (>= (+ u (* (expt (+ 1 x) 2) (+ (* 2 w) (* 2 z) 3))) (+ (* 2 v) (* (expt (+ 1 y) 2) (+ (* 2 r) 1)))) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-46 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (> x 0) (< x (* 3 y)) (< u v) (< v 0) (> (expt v 2) 1) (< (expt v 2) x) (>= (+ (* 9 (* u (expt y 2))) 1) (+ (* v (expt x 2)) x)) ) nil) :rule-classes nil)))

; fails
;(encapsulate () (local (defthm thm-47 (implies (and (rationalp u) (rationalp v) (rationalp y) (rationalp x) (> x 0) (< x (* 3 y)) (< u v) (< v 0) (> (expt v 2) 1) (< (expt v 2) x) (< (+ (* 9 (* u (expt y 2))) 1) (+ (* v (expt x 2)) x)) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-48 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 1) (> y 1) (> z 1) (<= (* x (+ 1 (* z y))) 1) ) nil) :rule-classes nil)))

; fails
;(encapsulate () (local (defthm thm-49 (implies (and (rationalp a) (rationalp c) (rationalp b) (rationalp d) (rationalp x) (<= a (* (/ 1 2) (* x b))) (> c 0) (> d 0) (< d 1) (>= (* (+ (* (/ 1 3) (* d (expt (+ 3 c) -1))) 1) a) (* b x)) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-50 (implies (and (rationalp u) (rationalp y) (rationalp x) (< x 1) (> y 1) (> (* x y) 1) (>= (+ u x) (+ 1 y)) (< (* (expt x 2) y) (+ (* -1 (* u x y)) 2)) ) nil) :rule-classes nil)))

; fails (6 sec)
;(encapsulate () (local (defthm thm-51 (implies (and (rationalp a) (rationalp b) (> (expt a 21) 0) (< (expt a 3) 1) (> (expt b 55) 0) (< b 1) (< (+ a b) (* a b)) ) nil) :rule-classes nil)))

(encapsulate () (local (defthm thm-52 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 0) (< y z) (< y 0) (> z 0) ) (< (* x y) (* x z))) :rule-classes nil)))

(encapsulate () (local (defthm thm-53 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 0) (< y z) (= y 0) (> z 0) ) (< (* x y) (* x z))) :rule-classes nil)))

(encapsulate () (local (defthm thm-54 (implies (and (rationalp y) (rationalp x) (> x 1) ) (>= (+ 1 (* x (expt y 2))) (+ 1 (expt y 2)))) :rule-classes nil)))

(encapsulate () (local (defthm thm-55 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 1) (= z (expt y 2)) ) (>= (+ 1 (* z x)) (+ 1 z))) :rule-classes nil)))

(encapsulate () (local (defthm thm-56 (implies (and (rationalp w) (rationalp y) (rationalp x) (rationalp z) (> x 0) (< (* x z y) 0) (> (* x w) 0) ) (> w (* y z))) :rule-classes nil)))

(encapsulate () (local (defthm thm-57 (implies (and (rationalp w) (rationalp y) (rationalp x) (rationalp z) (= x z) (= y w) (> x 0) (> y 0) ) (= (* x y) (* z w))) :rule-classes nil)))

(encapsulate () (local (defthm thm-58 (implies (and (rationalp y) (rationalp x) (> x (* 2 y)) (= x (* 3 y)) ) (> y 0)) :rule-classes nil)))

;fails
;(encapsulate () (local (defthm thm-84 (implies (and (rationalp x) (>= x -1) (<= x 1) ) (>= (+ (* 4 (expt x 3)) (* -3 x)) -1)) :rule-classes nil)))

;fails
;(encapsulate () (local (defthm thm-85 (implies (and (rationalp x) (>= x -1) (<= x 1) ) (<= (+ (* 4 (expt x 3)) (* -3 x)) 1)) :rule-classes nil)))

;fails
;(encapsulate () (local (defthm thm-86 (implies (and (rationalp y) (rationalp x) (rationalp z) (> x 0) (> y 0) (> z 0) ) (>= (+ (* (expt x 2) (expt (expt y 2) -1)) (* (expt y 2) (expt (expt z 2) -1)) (* (expt z 2) (expt (expt x 2) -1))) (+ (* x (expt z -1)) (* y (expt x -1)) (* z (expt y -1))))) :rule-classes nil)))

;fails
;(encapsulate () (local (defthm thm-87 (implies (and (rationalp a) (rationalp c) (rationalp b) (> a 0) (> b 0) (> c 0) ) (<= (+ (* b a (expt (+ a b) -1)) (* c b (expt (+ b c) -1)) (* c a (expt (+ a c) -1))) (* (/ 3 2) (* (+ (* a b) (* b c) (* c a)) (expt (+ a b c) -1))))) :rule-classes nil)))

;fails
;(encapsulate () (local (defthm thm-88 (implies (and (rationalp a) (rationalp c) (rationalp b) (> a 0) (> b 0) (> c 0) ) (>= (+ (* a (expt (+ b c) -1)) (* b (expt (+ c a) -1)) (* c (expt (+ a b) -1))) (/ 3 2))) :rule-classes nil)))
