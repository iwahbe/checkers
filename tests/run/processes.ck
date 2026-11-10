# Child processes (D112): `run` gives a child input and collects its output;
# `spawn` gives back a `File` for each stream asked for as a `Pipe`, and the
# checker makes the program close each and wait for the child.
module processes

import std.system (System, ExitCode, Proc)
import std.terminal (Term)
import std.files (IoError)
import std.proc (Streams, Spawned, Inherit, Pipe, Discard)
import std.bytes

partial fn show_run program args input p term -> r : program~String, args~List String, input~Bytes,
                                                     p~Proc, term~Term, r~Unit
    match proc.run program args input p
        Ok o  -> terminal.print_line ("code " ++ format o.code ++ ", out " ++ format o.stdout ++ ", err " ++ format o.stderr) term
        Err e -> terminal.print_line ("can't run " ++ program ++ ": " ++ files.describe e) term

# A child that writes far more than a pipe holds, while its input is still
# being written: `run` reads and writes at once, so nothing stalls.
fn big n -> b : n~Nat, b~Bytes
    bytes.concat (blocks n)

fn blocks n -> bs : n~Nat, bs~List Bytes
    decreasing n
    if n == 0 then [] else b"0123456789abcdef" :: blocks (n - 1)

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, proc = p } = sys
    show_run "tr" ["a-z", "A-Z"] b"shout\n" p term
    show_run "sh" ["-c", "echo out; echo err >&2; exit 3"] b"" p term
    show_run "no-such-program-checkers" [] b"" p term
    match proc.run "sh" ["-c", "cat; echo done >&2"] (big 16384) p
        Ok o  -> terminal.print_line ("big: " ++ format (len o.stdout) ++ " out, " ++ format (len o.stderr) ++ " err") term
        Err e -> terminal.print_line (files.describe e) term
    # Both directions piped; standard error shared with this program.
    match proc.spawn "sh" ["-c", "read x; echo got $x; echo to stderr >&2"] (Streams Pipe Pipe Inherit) p
        Ok (Spawned child to from ()) ->
            _ <- files.write_line "hello" to
            files.close to
            got <- files.read_rest from
            files.close from
            terminal.print_line (format got ++ ", " ++ format (proc.wait child)) term
        Err e                         -> terminal.print_line (files.describe e) term
    # Output discarded; only the exit code.
    match proc.spawn "sh" ["-c", "echo nobody sees this; exit 5"] (Streams Discard Discard Discard) p
        Ok (Spawned child () () ()) -> terminal.print_line ("discarded, " ++ format (proc.wait child)) term
        Err e                       -> terminal.print_line (files.describe e) term
    # Output shared with this program, after what it has printed so far.
    match proc.spawn "echo" ["inherited"] (Streams Inherit Inherit Inherit) p
        Ok (Spawned child () () ()) -> terminal.print_line ("then " ++ format (proc.wait child)) term
        Err e                       -> terminal.print_line (files.describe e) term
    Success
