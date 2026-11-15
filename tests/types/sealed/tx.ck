# A transaction whose representation only this module sees.
module sealed.tx

import std.list

export abstract record Tx
    log~List String

export abstract enum State
    Fresh
    Done note : note~String

export fn begin -> t : t~Tx
    Tx []

export fn commit t -> n : t~Tx, n~Nat
    list.length t.log
