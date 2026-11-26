(set-option :reproducible-resource-limit 1)(set-logic ALL)(declare-const x Int)(assert (not (> (* x (* x x)) 7)))(check-sat)(get-value (x))
