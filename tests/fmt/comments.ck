# Comments: kept, re-indented, trailing ones aligned (D92).
module comments

import std.list   # lists
import std.string                 # strings
import std.bytes # bytes

fn f x : x~Nat
      # about the first line
      let y = x + 1   # one
      let z = y * 2 # two

      # a run of one
      y + z   # three
  # back at the top level, about g

fn g x : x~Nat
    match x
        0 -> 1
        # between arms
        _ -> 2
        # after the last arm, still in the match
    # in g's body, after the match
