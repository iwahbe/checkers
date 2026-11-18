module positivity

enum Bad
    Wrap f : f~(Bad -> Nat)

enum Good
    Leaf
    Node kids : kids~List Good

enum Fine
    Stop
    Fn f : f~(Nat -> Fine)

# To the left of two `->`s is still to the left of an `->` (D182).
enum Twice
    Base
    Mk f : f~((Twice -> Nat) -> Nat)
