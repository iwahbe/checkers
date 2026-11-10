module tools_stdlib

# The standard library additions for the build tool and formatter (D90).

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Entry)
import std.string
import std.bytes
import std.env
import std.proc

fn show_entries es term : es~List Entry, term~Term
    match es
        []        -> ()
        e :: rest ->
            terminal.print_line (e.name ++ (if e.dir then "/" else "")) term
            show_entries rest term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, fs, env = e, proc = p } = sys
    terminal.write "no newline, " term
    terminal.write_bytes b"then bytes\n" term
    terminal.print_line (string.concat ["con", "cat", "", "enated"]) term
    let src = b"hello, world"
    terminal.print_line (format (bytes.slice src 7 12)) term
    terminal.print_line (format (bytes.concat [b"ab", b"", b"cd"])) term
    terminal.print_line (format (string.from_utf8 b"caf\xc3\xa9")) term
    terminal.print_line (format (string.from_utf8 b"\xff")) term
    match files.list "data" fs
        Ok es -> show_entries es term
        Err x -> terminal.print_line (files.describe x) term
    match files.list "missing" fs
        Ok _  -> terminal.print_line "?" term
        Err x -> terminal.print_line (files.describe x) term
    match env.get "PATH" e
        Some _ -> terminal.print_line "PATH: set" term
        None   -> terminal.print_line "PATH: unset" term
    terminal.print_line (format (env.get "CHECKERS_TEST_UNSET" e)) term
    match env.executable e
        Some _ -> terminal.print_line "executable: known" term
        None   -> terminal.print_line "executable: unknown" term
    terminal.print_line (format (proc.exec "sh" ["-c", "echo from a child; exit 3"] p)) term
    match proc.exec "no-such-program-checkers" [] p
        Ok _  -> terminal.print_line "?" term
        Err x -> terminal.print_line (files.describe x) term
    Success
