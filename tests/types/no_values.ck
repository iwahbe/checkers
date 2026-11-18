module no_values

enum Fine
    Fn f : f~(Nat -> Fine)

enum Direct
    Again next : next~Direct

record Chain
    next~Chain

enum Paired
    Pair p : p~(Nat, Paired)

enum Ping
    ToPong pong : pong~Pong

enum Pong
    ToPing ping : ping~Ping

enum Box a
    Hold x : x~a

enum Boxed
    Boxes b : b~Box Boxed

enum Generic a
    More x rest : x~a, rest~Generic a

enum Nested a
    Deeper x : x~Nested (a, a)

enum Empty

enum NeedsEmpty
    Stuck e rest : e~Empty, rest~NeedsEmpty
