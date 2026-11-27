module sealed_use

# Sealing (#537): outside `sealed_lib`, only signatures, postconditions and
# exported lemmas are visible, unless a function is `transparent`.

import sealed_lib (double, triple, quad)

fn by_post x -> y : x~Int, y~Int, y == 2 * x
    double x

fn by_lemma x -> y : x~Int, y~Int, y == 3 * x
    have sealed_lib.triple_is x
    triple x

fn by_transparency x -> y : x~Int, y~Int, y == 4 * x
    quad x

fn sealed_body x -> y : x~Int, y~Int, y == 3 * x
    triple x

# The note is given wherever the sealed function is in what is to be proved:
# inside an `if` too (#665), where a counterexample would say nothing true.
lemma sealed_in_if x b : x~Int, b~Bool
    ensures (if b then triple x else 3 * x) == 3 * x
