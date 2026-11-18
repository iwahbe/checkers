module create_dirs_dot

# `create_dirs` creates missing parents whatever `.` components the path has,
# as `mkdir -p` does (issue #6).

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Fs, IoError)
import std.proc

fn report what r term : what~String, r~Result Unit IoError, term~Term
    match r
        Ok _  -> terminal.print_line (what ++ ": ok") term
        Err e -> terminal.print_line (what ++ ": " ++ files.describe e) term

fn is_dir path fs -> s : path~String, fs~Fs, s~String
    match files.list path fs
        Ok _  -> path ++ ": a directory"
        Err e -> path ++ ": " ++ files.describe e

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, fs, proc = p } = sys
    let _ = proc.exec "rm" ["-rf", "dirs.tmp"] p
    report "dirs.tmp/a/." (files.create_dirs "dirs.tmp/a/." fs) term
    report "dirs.tmp/b/./c" (files.create_dirs "dirs.tmp/b/./c" fs) term
    report "./dirs.tmp/d/e/./." (files.create_dirs "./dirs.tmp/d/e/./." fs) term
    report "dirs.tmp/a/. again" (files.create_dirs "dirs.tmp/a/." fs) term
    report "." (files.create_dirs "." fs) term
    let inside = files.within "dirs.tmp" fs
    report "within: f/." (files.create_dirs "f/." inside) term
    report "within: ../g/." (files.create_dirs "../g/." inside) term
    terminal.print_line (is_dir "dirs.tmp/a" fs) term
    terminal.print_line (is_dir "dirs.tmp/b/c" fs) term
    terminal.print_line (is_dir "dirs.tmp/d/e" fs) term
    terminal.print_line (is_dir "dirs.tmp/f" fs) term
    terminal.print_line (is_dir "dirs.tmp/g" fs) term
    let _ = proc.exec "rm" ["-rf", "dirs.tmp"] p
    Success
