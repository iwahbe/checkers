# checkers.ck — `checkers`, the build tool (D95, SPEC §15.1). It passes the
# compiler's commands to `ckc` and has commands of its own: `fmt`.

module checkers

import system (System, ExitCode)
import terminal (Term)
import system (Env, Proc)
import env
import files
import proc
import string
import bytes
import fmt

let VERSION = "0.1.0"

let USAGE = string.concat [
    "checkers — the Checkers build tool\n\n",
    "USAGE:\n",
    "    checkers check|run|build|trust|stage|parse ...   run the compiler, `ckc` (see `ckc --help`)\n",
    "    checkers fmt [--check] [PATH]...                 format .ck files (see `checkers fmt --help`)\n",
    "    checkers fmt -                                   format standard input\n",
    "    checkers --version\n\n",
    "`ckc` is found through CKC, else next to `checkers`, else on PATH."]

fn compiler_command c : c~String
    c == "check" or c == "run" or c == "build" or c == "trust" or c == "stage" or c == "parse"

fn exit_code n -> c : n~Nat, c~ExitCode
    if n == 0 then Success else if n < 256 then Failure n else Failure 1

# The position of the last `/` before `i` in `b`.
fn last_slash b i -> r : b~Bytes, i~Nat, i <= len b, r~Option (k~Nat, k < len b)
    decreasing i
    if i == 0 then None else if b[i - 1] == '/' then Some (i - 1) else last_slash b (i - 1)

# `ckc` in the directory of the running program.
fn beside exe -> r : exe~Option String, r~Option String
    match exe
        None -> None
        Some path ->
            let b = string.bytes path
            match last_slash b (len b)
                None -> None
                Some k ->
                    match string.from_utf8 (bytes.slice b 0 (k + 1))
                        Some dir -> Some (dir ++ "ckc")
                        None -> None

fn report program e term -> code : program~String, e~files.IoError, term~Term, code~ExitCode
    terminal.eprint_line ("checkers: could not run `" ++ program ++ "`: " ++ files.describe e) term
    Failure 2

partial fn compiler args e p term -> code : args~List String, e~Env, p~Proc, term~Term, code~ExitCode
    match env.get "CKC" e
        Some c ->
            match proc.exec c args p
                Ok n -> exit_code n
                Err x -> report c x term
        None ->
            let on_path = \u ->
                match proc.exec "ckc" args p
                    Ok n -> exit_code n
                    Err x -> report "ckc" x term
            match beside (env.executable e)
                None -> on_path ()
                Some c ->
                    match proc.exec c args p
                        Ok n -> exit_code n
                        Err _ -> on_path ()

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, fs, env = e, proc = p } = sys
    match args
        "fmt" :: rest -> fmt.run rest term fs
        ["--version"] ->
            terminal.print_line ("checkers " ++ VERSION) term
            Success
        ["--help"] ->
            terminal.print_line USAGE term
            Success
        [] ->
            terminal.print_line USAGE term
            Success
        c :: _ ->
            if compiler_command c
                compiler args e p term
            else
                terminal.eprint_line ("checkers: unknown command `" ++ c ++ "`\n\n" ++ USAGE) term
                Failure 2
