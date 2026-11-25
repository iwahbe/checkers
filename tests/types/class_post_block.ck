module class_post_block

# The class's postcondition is a `match` on several lines, inherited from
# the standard library: shown in full, once for both values returned.
export record Wrap s
    inner~s

instance Seq (Wrap s) : Seq s
    type Elem = Seq.Elem s
    fn size w
        Seq.size w.inner
    fn uncons w
        match w.inner
            []        -> None
            x :: rest -> Some (x, Wrap rest)
