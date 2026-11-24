# Concurrency

Values are immutable, so sharing them between threads never races, and pure code may run in parallel freely (`par`). What needs coordinating is **state** that several tasks change: a table of jobs, a log, a counter. For that, Checkers has behaviour-oriented concurrency, as in the Verona project: state lives in **cowns** (concurrent owners), and **behaviours** get exclusive access to the cowns they name. Programs built this way have no data races and no deadlocks, by construction.

There are no locks. A behaviour that waits, for input, a pipe, a child process or a future's value, is set aside, and its thread runs other behaviours meanwhile; nothing it can wait for can be waiting for it.

## Cowns

`cown.new v sched` (from `std.cown`, with the `Sched` capability) creates a `Cown a` holding `v`. The handle may be shared freely: copied, captured, passed to other functions. The value it holds is reachable only inside a behaviour that names the cown.

A cown can't hold a resource (E0405): a resource has one owner at a time, and passes from owner to owner through calls and the functions given to `future.fork` ([Capabilities](effects.md#resources)).

## `when`

```text
stmt ::= 'when' lname '=' expr { ',' lname '=' expr } 'using' lname NL INDENT block DEDENT
```

`when x = c using sched` followed by a block **schedules** a behaviour on the cown `c` and continues at once. The behaviour runs when it holds all the cowns it names, at once; inside it, each name is bound to its cown's current value, and the block's value is the cowns' new values: one value for one cown, a tuple in the order listed for several. `when` is a line of a block, never its last (E0117), and needs the scheduler capability after `using` (E0112).

```checkers
module counter

import std.system (System, ExitCode)
import std.cown
import std.string (format)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, sched } = sys
    let hits = cown.new 0 sched
    let misses = cown.new 0 sched
    when h = hits using sched
        h + 1
    when h = hits, m = misses using sched
        terminal.print_line format"hits: {h}, misses: {m}" term
        (h, m + 1)
    Success
```

A behaviour's body may use authority capabilities from around it (`term` above), and may schedule further behaviours. A resource it uses moves into it, and is no longer available outside.

**Guarantees.**

1. **No data races.** A cown's value is reachable only inside a behaviour holding that cown.
2. **No deadlocks.** A behaviour acquires all its cowns at once, so there is no order of locks to get wrong.
3. **Causal order.** Two behaviours that name a common cown run in the order they were scheduled.

Behaviours that share no cown may run at the same time, in either order.

### Invariants

A cown's value type may be a refinement: a `Cown Log`, where `type Log = entries~List String, len entries <= 100`. Each behaviour must hand back a value of that type, which is an obligation ([Proofs](proofs.md)); inside the behaviour, the invariant of each cown it holds is a fact. This is how a protocol is proved: keep its state in a cown whose type is its invariant, and change it only with functions that are proved to keep it.

A cown's type never changes, even to a weaker refinement: a `Cown Nat` is never a `Cown Log`, nor the other way round. Give the type where the cown is created, in the signature of the function that creates it.

```checkers
import std.cown (Cown, Sched)

type Log = entries~List String, len entries <= 100

fn new_log sched -> c : sched~Sched, c~Cown Log
    cown.new [] sched

fn add msg log sched -> u : msg~String, log~Cown Log, sched~Sched, u~Unit
    when l = log using sched
        if len l < 100 then msg :: l else l
    ()
```

## Futures

`std.future` runs work in parallel and gives its result later, as a `Future a`:

| Function | Gives |
|---|---|
| `future.fork sched f`, `f~own (Unit -> a)` | a `Future a`, filled by a behaviour that runs `f ()` |
| `future.join x` | the value of a future `x`, or the values of a tuple of futures: `(Future a, Future b)` gives `(a, b)` |
| `future.ready v` | a `Future a` already filled with `v` |

`join` gives the values once the futures are filled. Until then the behaviour that called it waits, as one reading a pipe does: its thread runs other behaviours, and it keeps any cowns it holds. Which values `join` gives is worked out from the futures' types: `future.join (a, b, c)` with `a~Future Nat`, `b~Future String` and `c~Future Nat` is a `(Nat, String, Nat)`.

```checkers
module sums

import std.system (System, ExitCode)
import std.future (Future)

fn sum xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        x :: rest -> x + sum rest

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let sched = sys.sched
    let a = future.fork sched $ \_ ->
        sum [1, 2, 3]
    let b = future.fork sched $ \_ ->
        sum [4, 5, 6]
    let (x, y) = future.join (a, b)
    if x + y == 21 then Success else Failure 1
```

The function given to `fork` is a [one-shot closure](effects.md#one-shot-closures): it runs once, so it may use a resource, which moves into the behaviour. A block becomes a function after `$`: `future.fork sched $ \_ ->` followed by the block.

**Still no deadlock.** A future is filled only by its own `fork`, whose function holds no cowns, and that function can only wait for futures that existed before it. So waits never form a cycle, and a `join` always ends, even in a `when` body. What waiting costs is time: while a `when` body waits, the behaviours queued on its cowns wait too.

A future may be joined any number of times, each join getting its value; a future of a resource must be joined exactly once, like any resource.

## `par`

```text
expr ::= 'par' '(' expr ',' expr { ',' expr } ')'
```

`par (e1, e2, …)` evaluates the components of a tuple of two or more (E0115) in parallel and gives the tuple. The components must be pure: no capabilities, no `partial` calls. To the prover `par t` is just `t`, so a function using `par` keeps its proofs and can be used in specifications.

```checkers
fn fib n -> r : n~Nat, r~Nat
    if n < 2 then n else fib (n - 1) + fib (n - 2)

fn both -> r : r~(Nat, Nat)
    par (fib 20, fib 21)

check both == (6765, 10946)
```

## Ending the program

The process exits once `main` has returned and no behaviour remains scheduled or running. If `main` returns a `Future ExitCode`, the program's exit code is that future's value.

## Running behaviours

Behaviours run on a pool of threads, by default one per core: `checkers run --threads N` sets the number, and a built executable reads `CHECKERS_THREADS`. With one thread, behaviours run in the order they were scheduled, one at a time, so output is deterministic. `main` runs as a behaviour too.

- A behaviour that waits (to read a pipe or the terminal, for a child to finish) is parked, and keeps its cowns; its thread runs other behaviours until it can go on. Nothing in the program changes for this: there is no `async`.
- Each call that writes to the terminal is atomic: lines from different behaviours never interleave within a call.
- The components of `par` run on threads of their own when some are free, and on the current thread otherwise.

**Actors** are a library on top of cowns (`std.actor`): an actor is a cown holding its state, and `actor.send a f sched` schedules `f` on it, so its messages are handled one at a time, in the order sent.
