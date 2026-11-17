# Behaviours that wait don't hold a thread (D113, §13.8). Four readers each
# wait for a child's output; the children answer only once the writer,
# scheduled after the readers, gives them their input. If a waiting reader
# held its thread, the writer would never run, on one thread or on several.
module waits

import std.future
import std.system (System, ExitCode, Proc)
import std.terminal (Term)
import std.files (File)
import std.proc (Streams, Spawned, Pipe, Inherit, Child)

# A child `cat`: its input, its output, and the child.
record Kid
    input~File
    output~File
    child~Child

partial fn kids n p -> r : n~Nat, p~Proc, r~List Kid
    if n == 0
        []
    else
        match proc.spawn "cat" [] (Streams Pipe Pipe Inherit) p
            Ok (Spawned child i o ()) -> Kid i o child :: kids (n - 1) p
            Err _                     -> []

partial fn cleanup ks : ks~List Kid
    match ks
        []                -> ()
        Kid i o c :: rest ->
            files.close i
            files.close o
            let _ = proc.wait c
            cleanup rest

# What a reader read, and the child's exit code.
enum Slot
    Read text code : text~Bytes, code~Nat
    Failed

# Read the child's output to its end, then wait for it.
partial fn read out child -> s : out~File, child~Child, s~Slot
    let (text, out) = files.read_rest out
    files.close out
    let code = match proc.wait child
        Ok n  -> n
        Err _ -> 99
    match text
        Ok t  -> Read t code
        Err _ -> Failed

# Give each child its line, then close its input.
partial fn feed ins n : ins~List File, n~Nat
    match ins
        []        -> ()
        w :: rest ->
            let (_, w) = files.write_line ("line " ++ format n) w
            files.close w
            feed rest (n + 1)

# What a slot holds, as text.
fn shown s -> r : s~Slot, r~String
    match s
        Read t code -> format t ++ " " ++ format code
        Failed      -> "failed"

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p, sched } = sys
    match kids 4 p
        [Kid i1 o1 c1, Kid i2 o2 c2, Kid i3 o3 c3, Kid i4 o4 c4] ->
            let a = future.fork sched $ \_ ->
                read o1 c1
            let b = future.fork sched $ \_ ->
                read o2 c2
            let c = future.fork sched $ \_ ->
                read o3 c3
            let d = future.fork sched $ \_ ->
                read o4 c4
            let _ = future.fork sched $ \_ ->
                feed [i1, i2, i3, i4] 1
            let (x, y, z, w) = future.join (a, b, c, d)
            terminal.print_line (shown x) term
            terminal.print_line (shown y) term
            terminal.print_line (shown z) term
            terminal.print_line (shown w) term
            Success
        other                                                    ->
            cleanup other
            terminal.eprint_line "could not start the children" term
            Failure 1
