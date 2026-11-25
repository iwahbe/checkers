# time.ck — readings of a monotonic clock, and durations (SPEC §8.2).
module std.time

import std.system (Clock)
import std.string (Display, display, Digits)

# A reading of the monotonic clock: what `now` gives. Its only use is the
# time between two readings (`since`), or a reading later than another by
# a duration (`add`); no number can be taken out of it. It is not the time
# of day, and it counts while the machine is suspended.
export abstract enum Instant
    Reading ns : ns~Nat

# A length of time, in whole nanoseconds. It is never negative.
export record Duration
    ns~Nat

# What the clock reads now. Readings never go backwards.
export fn now c -> t : c~Clock, t~Instant
    Reading (monotonic c)

# The time from `earlier` to `later`: zero if `earlier` is after `later`.
export fn since later earlier -> d : later~Instant, earlier~Instant, d~Duration
    match later
        Reading a ->
            match earlier
                Reading b -> Duration (if a >= b then a - b else 0)

# The reading `d` after `t`.
export fn add t d -> u : t~Instant, d~Duration, u~Instant
    match t
        Reading a -> Reading (a + d.ns)

# `n` milliseconds.
export fn millis n -> d : n~Nat, d~Duration
    Duration (n * 1000000)

# `n` seconds.
export fn secs n -> d : n~Nat, d~Duration
    Duration (n * 1000000000)

# Waits for `d` at least. A behaviour that sleeps holds no thread.
export fn sleep c d : c~Clock, d~Duration
    sleep_ns c d.ns

# The monotonic clock, in nanoseconds since some time before the program
# started: `CLOCK_BOOTTIME` on Linux, `CLOCK_MONOTONIC_RAW` on macOS.
fn monotonic c -> n : c~Clock, n~Nat
    __builtin

# Waits for `n` nanoseconds at least, by that clock.
fn sleep_ns c n : c~Clock, n~Nat
    __builtin

# Earlier readings first.
instance Ord Instant
    transparent fn le x y
        match x
            Reading a ->
                match y
                    Reading b -> a <= b

# Shorter durations first.
instance Ord Duration
    transparent fn le x y
        x.ns <= y.ns

instance Add Duration
    transparent fn add x y
        Duration (x.ns + y.ns)

# ── Showing durations ────────────────────────────────────────────────────────

# A unit that `display` shows a duration in.
export enum Unit
    Nanos    # ns
    Micros   # µs
    Millis   # ms
    Seconds  # s
    Minutes  # m
    Hours    # h

# How many nanoseconds one `u` is.
fn size u -> n : u~Unit, n~Nat, n > 0
    match u
        Nanos   -> 1
        Micros  -> 1000
        Millis  -> 1000000
        Seconds -> 1000000000
        Minutes -> 60000000000
        Hours   -> 3600000000000

# The unit's symbol.
fn symbol u -> s : u~Unit, s~String
    match u
        Nanos   -> "ns"
        Micros  -> "µs"
        Millis  -> "ms"
        Seconds -> "s"
        Minutes -> "m"
        Hours   -> "h"

# Without units, in the largest of ns, µs, ms and s in which it is at least
# 1, as an exact decimal: `1.5s`, `250ms`, `1.000000001s`, `0ns`. With
# units, they split it: each unit given has a whole count but the smallest,
# which has the rest as a decimal (`[Hours, Minutes, Seconds]` shows
# `0h0m3.5s`). Each unit in the list shows its part, in the list's order,
# repeats included. A rest in minutes or hours that no decimal writes
# exactly is cut off at 11 or 13 places: `1.66666666666m` for 100 s.
instance Display Duration
    type Options = Unit
    fn display d us
        match us
            [] -> part d.ns [natural d.ns] (natural d.ns)
            _  -> parts d.ns us us

# The unit Rust's `Debug` shows `n` nanoseconds in.
fn natural n -> u : n~Nat, u~Unit
    if n >= 1000000000
        Seconds
    else if n >= 1000000
        Millis
    else if n >= 1000
        Micros
    else
        Nanos

# Each unit of `rest` with its part of `n` nanoseconds, split by `all`.
fn parts n all rest -> s : n~Nat, all~List Unit, rest~List Unit, s~String
    match rest
        []        -> ""
        u :: more -> part n all u ++ parts n all more

# `u`'s part of `n` nanoseconds split by the units `all`, with its symbol.
fn part n all u -> s : n~Nat, all~List Unit, u~Unit, s~String
    let m = above all u 0
    let left = if m == 0 then n else n % m
    let shown = if smallest all u then decimal left (size u) else display (left / size u) []
    shown ++ symbol u

# The size of the smallest unit of `us` larger than `u`, or of `best` if
# that is smaller and not 0; 0 if there is none.
fn above us u best -> r : us~List Unit, u~Unit, best~Nat, r~Nat
    match us
        []        -> best
        v :: more ->
            let s = size v
            above more u (if s > size u and (best == 0 or s < best) then s else best)

# Whether no unit of `us` is smaller than `u`.
fn smallest us u -> r : us~List Unit, u~Unit, r~Bool
    match us
        []        -> True
        v :: more -> size v >= size u and smallest more u

# `n / m` as a decimal with no zeros at its end, to the fewest places `k`
# with `10^k >= m`, cut off toward zero. That is exact whenever `n / m` is
# a decimal at all (`m` is a unit's size), and otherwise one nanosecond is
# still more than the last place.
fn decimal n m -> s : n~Nat, m~Nat, m > 0, s~String
    let k = places m
    let scaled = n * pow10 k / m
    let whole = scaled / pow10 k
    let (frac, k) = trim (scaled % pow10 k) k
    if k == 0 then display whole [] else display whole [] ++ "." ++ display frac [Digits k]

# The fewest places `k` with `10^k >= m`.
fn places m -> k : m~Nat, k~Nat
    decreasing m
    if m <= 1 then 0 else 1 + places ((m + 9) / 10)

# `10^k`.
fn pow10 k -> p : k~Nat, p~Nat, p >= 1
    decreasing k
    if k == 0 then 1 else 10 * pow10 (k - 1)

# `f` with `k` places, without the zeros at its end.
fn trim f k -> r : f~Nat, k~Nat, r~(Nat, Nat)
    decreasing k
    if k > 0 and f % 10 == 0 then trim (f / 10) (k - 1) else (f, k)
