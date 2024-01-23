; benchmark generated from python API
(set-info :status unknown)
(declare-fun v0 () Int)
(declare-fun v2 () Int)
(declare-fun v1 () Int)
(declare-fun v3 () Int)
(assert
 (= v0 0))
(assert
 (or (= v2 (mod (+ v0 1) 4))))
(assert
 (or (= v3 (mod (+ v1 1) 4))))
(assert
 (or (= v1 (mod (+ v2 1) 4))))
(assert
 (or (= v0 (mod (+ v3 1) 4))))
(check-sat)
