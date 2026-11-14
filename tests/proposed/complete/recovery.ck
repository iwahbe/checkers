module recovery

record Point
    x~Int
    y~Int

# (1) A statement that doesn't parse: the body is still checked.
fn after p -> n : p~Point, n~Int
    let q = p
    let r =
    q.x + r
# Today: E0100 at `let r =`, and `after`'s body is dropped: no hover,
# highlighting or completion inside it.
# Proposed: the same E0100; `let r = <hole>`, `r` of unknown type, so
# `q.x + r` raises nothing more; `q` and `r` are in the index.

# (2) A trailing `.`: only this line is affected.
fn half p -> n : p~Point, n~Int
    p.

lemma kept xs : xs~List Int
    ensures xs == xs
# Today: E0100 "expected a field or member name after `.`, found
# `lemma`" at `lemma`, and `kept` is lost.
# Proposed: E0100 "expected a field or member name after `.`, found end
# of line" at the end of `p.`; `kept` is checked.

# (3) An unclosed bracket: closed at the next declaration.
fn open p -> n : p~Point, n~Int
    after (p

fn later -> n : n~Int
    0
# Today: E0100 "expected `)`, found `fn`" at `fn later`, and `later` is
# lost: inside the bracket, line breaks are ignored.
# Proposed: E0004 "`(` is never closed" at the `(`; `later` is checked.
