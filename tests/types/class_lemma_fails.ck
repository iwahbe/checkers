module class_lemma_fails

# An instance whose function doesn't satisfy the class's lemmas: each is
# reported at the instance, with the class's statement and a counterexample
# (D136).

record Odd
    n~Int

instance Ord Odd
    fn le p q
        p.n != q.n
    lemma total p q
        proof
            auto
