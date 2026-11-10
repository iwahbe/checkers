# proc.ck — running other programs (SPEC §8.1, §8.4, D90, D97, D112).
module std.proc

import std.system (Proc)
import std.files (IoError, File)

# Run `program` with `args`, sharing this program's standard input, output
# and error, and wait for it: its exit code (128 + the signal, if a signal
# ended it). A `program` without a `/` is looked up on `PATH`.
export fn exec program args p -> r : program~String, args~List String, p~Proc, r~Result Nat IoError
    __builtin

# What a child finished with.
export record Output
    code~Nat
    stdout~Bytes
    stderr~Bytes

# Run `program` with `input` as its standard input, and wait for it: its exit
# code and everything it wrote. Its input is written while its output is
# read, so a child that fills a pipe can't stall.
export fn run program args input p -> r : program~String, args~List String, input~Bytes, p~Proc,
                                          r~Result Output IoError
    __builtin

# A running child: a resource, so it must be waited for.
export abstract enum Child

# What a child's standard stream is connected to.
export enum Stream
    Inherit
    Pipe
    Discard

export record Streams
    stdin~Stream
    stdout~Stream
    stderr~Stream

# What this program gets for a stream: its end of the pipe if the stream is
# piped, nothing otherwise.
export transparent fn pipe_end s -> t : s~Stream, t~Type
    match s
        Pipe -> File
        _    -> Unit

# A started child, with a `File` for each stream asked for as a `Pipe`.
export record Spawned ss : ss~ghost Streams
    child~Child
    stdin~pipe_end ss.stdin
    stdout~pipe_end ss.stdout
    stderr~pipe_end ss.stderr

# Start `program`; `Inherit` shares this program's stream, `Discard` connects
# the stream to nothing.
export fn spawn program args ss p -> r : program~String, args~List String, ss~Streams, p~Proc,
                                         r~Result (Spawned ss) IoError
    __builtin

# Wait for the child to finish: its exit code (128 + the signal, if a signal
# ended it). Close the pipe to its standard input first, or a child reading
# it may never finish.
export fn wait c -> r : c~Child, r~Result Nat IoError
    __builtin
