module declarations

‸

# Declarations (D142): above the first one, `import` too.
fn one -> n : n~Int
    1

‸

export ‸

# A lemma's body: `let` or `ensures`, then `proof`.
lemma l xs : xs~List Int
    ‸

lemma k xs : xs~List Int
    ensures xs == xs
    ‸

# A class's or instance's members.
class Size a
    fn size x -> n : x~a, n~Nat
    ‸
