module within_links

# An `Fs` confined by `files.within` follows a symbolic link that stays
# inside its directory, relative or absolute, and refuses one whose
# resolution leaves it, for every operation on paths.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files (Fs, IoError)
import std.string (debug)
import std.proc

fn report what r term : what~String, r~Result a IoError, term~Term
    match r
        Ok _  -> terminal.print_line (what ++ ": ok") term
        Err e -> terminal.print_line (what ++ ": " ++ files.describe e) term

fn read what path fs term : what~String, path~String, fs~Fs, term~Term
    match files.read path fs
        Ok b  -> terminal.print_line (what ++ ": " ++ debug b) term
        Err e -> terminal.print_line (what ++ ": " ++ files.describe e) term

fn open path fs term : path~String, fs~Fs, term~Term
    match files.open path fs
        Ok f  ->
            files.close f
            terminal.print_line ("open " ++ path ++ ": ok") term
        Err e -> terminal.print_line ("open " ++ path ++ ": " ++ files.describe e) term

fn create path fs term : path~String, fs~Fs, term~Term
    match files.create path fs
        Ok f  ->
            files.close f
            terminal.print_line ("create " ++ path ++ ": ok") term
        Err e -> terminal.print_line ("create " ++ path ++ ": " ++ files.describe e) term

fn setup -> s : s~String
    "rm -rf links.tmp && mkdir -p links.tmp/root/sub links.tmp/outside"
        ++ " && echo secret > links.tmp/outside/secret.txt"
        ++ " && echo inside > links.tmp/root/sub/inside.txt"
        ++ " && ln -s ../outside links.tmp/root/relative"
        ++ " && ln -s \"$PWD/links.tmp/outside\" links.tmp/root/absolute"
        ++ " && ln -s \"$PWD/links.tmp/root/../outside\" links.tmp/root/through"
        ++ " && ln -s ../../outside links.tmp/root/sub/nested"
        ++ " && ln -s sub/../../outside links.tmp/root/dotdot"
        ++ " && ln -s relative links.tmp/root/chain"
        ++ " && ln -s ../outside/made.txt links.tmp/root/dangling"
        ++ " && ln -s loop links.tmp/root/loop"
        ++ " && ln -s sub links.tmp/root/to_sub"
        ++ " && ln -s sub/inside.txt links.tmp/root/to_file"
        ++ " && ln -s ../sub/./inside.txt links.tmp/root/sub/up"
        ++ " && ln -s sub/nothing.txt links.tmp/root/to_new"
        ++ " && ln -s \"$PWD/links.tmp/root/sub\" links.tmp/root/absolute_in"
        ++ " && ln -s root links.tmp/alias"
        ++ " && ln -s \"$PWD/links.tmp/alias/sub/inside.txt\" links.tmp/root/around"

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, fs, proc = p } = sys
    report "setup" (proc.exec "sh" ["-c", setup] p) term
    let root = files.within "links.tmp/root" fs
    # Leaving the directory: refused.
    read "relative" "relative/secret.txt" root term
    read "absolute" "absolute/secret.txt" root term
    read "through" "through/secret.txt" root term
    read "nested" "sub/nested/secret.txt" root term
    read "dotdot" "dotdot/secret.txt" root term
    read "chain" "chain/secret.txt" root term
    read "loop" "loop" root term
    open "relative/secret.txt" root term
    create "relative/made.txt" root term
    create "dangling" root term
    report "write dangling" (files.write "dangling" b"x" root) term
    report "list relative" (files.list "relative" root) term
    report "create_dirs relative/new" (files.create_dirs "relative/new" root) term
    report "create_dirs sub/nested/new" (files.create_dirs "sub/nested/new" root) term
    read "within relative" "secret.txt" (files.within "relative" root) term
    read "within .." "outside/secret.txt" (files.within ".." root) term
    read "within missing" "x" (files.within "missing" root) term
    read "a path with .." "sub/../to_file" root term
    # Nothing was made outside it.
    report "outside/made.txt" (files.read "links.tmp/outside/made.txt" fs) term
    report "outside/new" (files.list "links.tmp/outside/new" fs) term
    # Staying inside: followed.
    read "to_sub" "to_sub/inside.txt" root term
    read "to_file" "to_file" root term
    read "up" "sub/up" root term
    read "absolute_in" "absolute_in/inside.txt" root term
    read "around" "around" root term
    read "within to_sub" "inside.txt" (files.within "to_sub" root) term
    report "list to_sub" (files.list "to_sub" root) term
    report "write to_new" (files.write "to_new" b"new" root) term
    read "sub/nothing.txt" "sub/nothing.txt" root term
    report "create_dirs to_sub/a/b" (files.create_dirs "to_sub/a/b" root) term
    report "list sub/a/b" (files.list "sub/a/b" root) term
    open "to_sub/inside.txt" root term
    create "to_sub/created.txt" root term
    # A directory made after `within`: reached once it is there.
    let later = files.within "later" root
    read "later, before" "x" later term
    report "create_dirs later" (files.create_dirs "later" root) term
    report "write later/x" (files.write "later/x" b"x" root) term
    read "later, after" "x" later term
    report "cleanup" (proc.exec "rm" ["-rf", "links.tmp"] p) term
    Success
