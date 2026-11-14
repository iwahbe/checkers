module recovery

# Recovery from syntax errors inside a body (D142 e): the rest of the body,
# and the declarations after it, are still checked.

record Point
    x~Int
    y~Int

# (1) A statement that doesn't parse becomes a hole: `r` is still bound,
# nothing more is said about it, and the next statement is checked (its
# unknown field is reported).
fn after p -> n : p~Point, n~Int
    let q = p
    let r =
    let s = q.z
    q.x + r

# The block's last expression: the body is a hole.
fn last p -> n : p~Point, n~Int
    let q = p
    q.x +

# (2) A trailing `.` is an error on its own line: `kept` is checked (its
# false postcondition is reported).
fn half p -> n : p~Point, n~Int
    p.

lemma kept xs : xs~List Int
    ensures xs == xs ++ [1]

# (3) An unclosed bracket is closed by the next declaration: `later` is
# checked (its type error is reported).
fn open p -> n : p~Point, n~Int
    after (p

fn later -> n : n~Int
    "zero"

# Or by the next statement.
fn inner p -> n : p~Point, n~Int
    let a = after (p
    let b = nowhere
    a
