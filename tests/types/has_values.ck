module has_values

enum Stream
    Done
    Next f : f~(Nat -> Stream)

enum Rose
    Node kids : kids~List Rose

enum Maybe a
    Nothing
    Just x : x~a

enum Tree
    Branch kid : kid~Maybe Tree

enum Even
    Zero
    AfterOdd odd : odd~Odd

enum Odd
    AfterEven even : even~Even

enum Perfect a
    Leaf x     : x~a
    Twice rest : rest~Perfect (a, a)

enum Empty

enum Absurd
    FromEmpty f : f~(Empty -> Absurd)

enum Grid
    Cells cells : cells~Array Grid

record Holder
    kids~List Holder

enum Uses
    UsesEmpty e : e~Empty

lemma same t u k : t~Stream, u~Stream, k~Nat, t == u
    ensures u == t
