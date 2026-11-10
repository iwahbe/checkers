module polarity

# D16: abstract types mark their parameters' polarity; the module checks it.

# Fine: `v` is a field, so strictly positive.
export abstract record Box +v : v~Type
    item~v

# Fine: `v` only ever goes into the function.
export abstract record Sink -v : v~Type
    put~(v -> Nat)

# A `Box Json` may hold a `Json`, because `Box` is marked `+`.
enum Json
    Null
    Boxed b : b~Box Json

# An unmarked parameter promises nothing, so a recursive type can't go there.
export abstract record Cell v : v~Type
    item~v

enum Tree
    Leaf
    Node c : c~Cell Tree                   # error E0354

export abstract record Bad +v : v~Type
    f~(v -> Nat)                                # error E0359: `v` left of `->`

export abstract record AlsoBad -v : v~Type
    x~v                                         # error E0359: `v` positive

# Not strictly positive, so not `+`: `v` is to the left of an `->` twice.
export abstract record Twice +v : v~Type
    g~((v -> Nat) -> Nat)                       # error E0359

record Plain +v : v~Type                        # error E0360: not abstract
    x~v
