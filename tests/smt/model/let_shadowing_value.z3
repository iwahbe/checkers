;; edited by hand: an inner let shadows an outer one (Z3 simplifies it to 2)
sat
((x (let ((a 1)) (let ((a 2)) a))))
