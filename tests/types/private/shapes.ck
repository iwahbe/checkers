module private.shapes

export fn area w h -> a : w~Nat, h~Nat, a~Nat
    w * h

fn perimeter w h -> p : w~Nat, h~Nat, p~Nat
    2 * (w + h)

record Corner
    x~Nat
    y~Nat
