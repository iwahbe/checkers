# Behaviours that wait don't hold a thread (D113, §13.8). Four readers each
# wait for a child's output; the children answer only once the writer,
# scheduled after the readers, gives them their input. If a waiting reader
# held its thread, the writer would never run, on one thread or on several.
module waits

import std.system (System, ExitCode, Proc)
import std.terminal (Term)
import std.files (File)
import std.proc (Streams, Spawned, Pipe, Inherit, Child)
import std.cown (Cown, Sched)

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

# A reader's cown: the child and its output, then what it read.
enum Slot
    Waiting out child : out~File, child~Child
    Read text code    : text~Bytes, code~Nat
    Failed

partial fn reader c sched : c~Cown Slot, sched~Sched
    when s = c using sched
        match s
            Waiting out child ->
                text <- files.read_rest out
                files.close out
                let code = match proc.wait child
                    Ok n  -> n
                    Err _ -> 99
                match text
                    Ok t  -> Read t code
                    Err _ -> Failed
            other             -> other
    ()

# Give each child its line, then close its input.
partial fn feed ins n : ins~List File, n~Nat
    match ins
        []        -> ()
        w :: rest ->
            _ <- files.write_line ("line " ++ format n) w
            files.close w
            feed rest (n + 1)

# What a slot holds, as text, and the slot back.
partial fn shown s -> r : s~Slot, r~(String, Slot)
    match s
        Read t code       -> (format t ++ " " ++ format code, Read t code)
        Waiting out child -> ("still waiting", Waiting out child)
        Failed            -> ("failed", Failed)

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p, sched } = sys
    match kids 4 p
        [Kid i1 o1 c1, Kid i2 o2 c2, Kid i3 o3 c3, Kid i4 o4 c4] ->
            let a = cown.new (Waiting o1 c1) sched
            let b = cown.new (Waiting o2 c2) sched
            let c = cown.new (Waiting o3 c3) sched
            let d = cown.new (Waiting o4 c4) sched
            reader a sched
            reader b sched
            reader c sched
            reader d sched
            let inputs = cown.new [i1, i2, i3, i4] sched
            when ins = inputs using sched
                feed ins 1
                []
            when x = a, y = b, z = c, w = d using sched
                let (sx, x) = shown x
                let (sy, y) = shown y
                let (sz, z) = shown z
                let (sw, w) = shown w
                terminal.print_line sx term
                terminal.print_line sy term
                terminal.print_line sz term
                terminal.print_line sw term
                (x, y, z, w)
            Success
        other                                                    ->
            cleanup other
            terminal.eprint_line "could not start the children" term
            Failure 1
