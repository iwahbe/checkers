module positivity

enum Bad
    Wrap f : f~(Bad -> Nat)

enum Good
    Leaf
    Node kids : kids~List Good

enum Fine
    Fn f : f~(Nat -> Fine)
