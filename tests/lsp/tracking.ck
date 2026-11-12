module tracking

fn twice n -> r : n~Nat, r~Nat
    n + n

let FOUR = twice 2
let EIGHT = twice FOUR
