(set-logic ALL)
(declare-fun x () String)
(assert (< (str.len x) 4294967296))
(assert (>= (to_real (str.len x)) 4294967296.0))
(check-sat)
