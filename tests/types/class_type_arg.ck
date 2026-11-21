module class_type_arg

# A class's function may take one of the class's parameters explicitly,
# as a `ghost Type`: the use names the type, which decides the instance.

class TryFrom s t
    fn try_from x t -> r : x~s, t~ghost Type, r~Option t

fn as_type t x -> r : t~ghost Type, x~t, r~t
    x

# Here `t` is `Int`.
instance TryFrom String Int
    fn try_from x t
        as_type (Option t) (if x == "" then None else Some 12)

instance TryFrom String Bool
    fn try_from x t
        if x == "yes" then Some True else None

fn at_int -> r : r~Option Int
    try_from "12" Int

check at_int == Some 12

# No expected type: the type passed decides.
check try_from "yes" Bool == Some True

# A clause can name a type passed explicitly, so a function can forward it.
fn forward x t -> r : x~String, t~ghost Type, TryFrom String t, r~Option t
    try_from x t

check forward "7" Int == Some 12

# The same through a one-parameter class.
class Parse a
    fn parse s -> r : s~String, r~Option a

instance Parse Int
    fn parse s
        if s == "" then None else Some 3

fn parse_as s t -> r : s~String, t~ghost Type, Parse t, r~Option t
    parse s

check parse_as "3" Int == Some 3

# No instance for the type passed.
fn missing -> r : r~Option (List Int)
    try_from "1" (List Int)

# The type passed differs from the type expected.
fn differs -> r : r~Option Bool
    try_from "1" Int

# Partly applied, the type is passed later, as to any function taking one.
fn later -> r : r~Option Int
    let f = try_from "1"
    f Int

check later == Some 12

# The type passed later differs from the type expected.
fn later_differs -> r : r~Option Bool
    let f = try_from "1"
    f Int

# A known instance's function is visible to the prover.
fn proved -> r : r~Option Bool, r == Some True
    try_from "yes" Bool
