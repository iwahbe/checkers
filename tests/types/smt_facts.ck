module smt_facts

# Facts the prover gets from types (§7.3): a refinement alias's predicates,
# the range of a byte, and record invariants that mention the record's
# value parameters.

import std.cursor (Parsed)

fn small b -> r : b~U8, r~Bool, r
    b < 256                                 # U8's predicate

fn byte src i -> r : src~Bytes, i~Nat, i < len src, r~Bool, r
    src[i] < 256                            # every element of Bytes is a U8

fn after src i p -> j : src~Bytes, i~Nat, p~Parsed Nat src i, j~Nat, j <= len src
    p.stop                                  # Parsed's invariant: stop <= len src

fn wrong src i p -> j : src~Bytes, i~Nat, p~Parsed Nat src i, j~Nat, j < len src
    p.stop
