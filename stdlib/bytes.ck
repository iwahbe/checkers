# bytes.ck — immutable byte strings.
module std.bytes

# Whether `word` occurs in `src` starting at `i`; if it does, it fits.
export fn matches_at src i word -> r : src~Bytes, i~Nat, word~Bytes, r~Bool,
                                       r implies i + len word <= len src
    __builtin

# The bytes from `i` up to (not including) `j`.
export fn slice src i j -> r : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src,
                               r~Bytes, len r == j - i
    __builtin

# The byte strings one after another, in time linear in the result.
export fn concat parts -> r : parts~List Bytes, r~Bytes
    __builtin

# The prover sees only lengths in the signatures above; these axioms say
# which bytes `slice` and `concat` give.

# Byte `k` of a slice is byte `i + k` of the source.
export lemma slice_at src i j k : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src, k~Nat, k < j - i
    ensures (slice src i j)[k] == src[i + k]
    proof
        __builtin

# Slicing out the middle of three byte strings gives the middle one.
export lemma slice_append pre mid post : pre~Bytes, mid~Bytes, post~Bytes
    ensures slice (pre ++ mid ++ post) (len pre) (len pre + len mid) == mid
    proof
        __builtin

# No parts make no bytes.
export lemma concat_nil
    ensures concat [] == b""
    proof
        __builtin

# The parts joined are the first part, then the rest joined.
export lemma concat_cons x xs : x~Bytes, xs~List Bytes
    ensures concat (x :: xs) == x ++ concat xs
    proof
        __builtin

# The axioms on a few byte strings, against the builtins themselves.
check slice b"abcde" 1 4 == b"bcd" and (slice b"abcde" 1 4)[2] == b"abcde"[3]
check slice (b"ab" ++ b"cde" ++ b"f") 2 5 == b"cde" and slice b"" 0 0 == b""
check concat [] == b"" and concat [b"ab", b"", b"c"] == b"ab" ++ concat [b"", b"c"]
