module class_alias_positions

# How a function parameter's check at a refinement alias is reported, by
# where the instance gives values of the class's type: as a function's
# results (`Visit`; `Nest`'s, of two arguments), a value's parts
# (`Wrap`), or to a function its argument is given (`Pass`).

class Visit t
    fn visit f -> b : f~((Int -> t) -> Bool), b~Bool

instance Visit Int
    fn visit f
        f (\x -> x)

class Nest t
    fn nest f -> b : f~((Int -> Int -> t) -> Bool), b~Bool

instance Nest Int
    fn nest f
        f (\x y -> x)

class Wrap t
    fn wrap f -> b : f~(Option t -> Bool), b~Bool

instance Wrap Int
    fn wrap f
        f (Some (-1))

class Pass t
    fn pass f -> b : f~(((t -> Bool) -> Bool) -> Bool), b~Bool

instance Pass Int
    fn pass f
        f (\g -> g (-1))

fn on_visit g -> b : g~(Int -> Nat), b~Bool
    g 0 == 0

fn on_nest g -> b : g~(Int -> Int -> Nat), b~Bool
    g 0 0 == 0

fn on_wrap o -> b : o~Option Nat, b~Bool
    match o
        Some n -> n == 0
        None   -> True

fn on_pass h -> b : h~((Nat -> Bool) -> Bool), b~Bool
    h (\n -> n == 0)

fn by_visit -> b : b~Bool
    Visit.visit on_visit

fn by_nest -> b : b~Bool
    Nest.nest on_nest

fn by_wrap -> b : b~Bool
    Wrap.wrap on_wrap

fn by_pass -> b : b~Bool
    Pass.pass on_pass
