module positivity_computed

# Strict positivity looks inside a type computed by an `if` or a `match`
# (#665): the field may have the type of any arm.

# Left of an `->` in one arm.
enum Bad
    Mk b f : b~Bool, f~(if b then (Bad -> Nat) else Nat)    # error E0354

record Neg a
    run~(a -> Nat)

# As an argument of a type that uses it negatively.
enum Held
    Hold b f : b~Bool, f~Neg (if b then Held else Nat)      # error E0354

# A parameter's polarity is worked out through the arms too, so `Hide` is
# not positive in `v`.
record Hide v
    b~Bool
    f~(if b then (v -> Nat) else Nat)

enum Through
    Wrap x : x~Hide Through                                 # error E0354

# Fine: positive in every arm.
enum Good
    Leaf
    Node b kids : b~Bool, kids~(if b then List Good else Nat)

# Marks (#511) are checked the same way.
export abstract record Plus +v : v~Type
    b~Bool
    f~(if b then (v -> Nat) else Nat)                       # error E0359

export abstract record PlusHeld +v : v~Type
    b~Bool
    f~Neg (if b then v else Nat)                            # error E0359

export abstract record Minus -v : v~Type
    b~Bool
    f~(if b then v else Nat)                                # error E0359

export abstract record PlusFine +v : v~Type
    b~Bool
    f~(if b then List v else Nat)

export abstract record MinusFine -v : v~Type
    b~Bool
    f~(if b then (v -> Nat) else Nat)
