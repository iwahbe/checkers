# system.ck — the root capability and exit codes (SPEC §8.2).
module std.system

import std.terminal (Term)
import std.files (Fs)
import std.cown (Sched)

# The authority to read environment variables and the program's own path.
export abstract enum Env
# The authority to run other programs.
export abstract enum Proc
# The authority to use the network.
export abstract enum Net
# The authority to read the clock.
export abstract enum Clock

# Everything a program may do, given to `main`: one capability for each
# kind of effect. Pass on only the ones a function needs.
export record System
    term~Term
    fs~Fs
    env~Env
    proc~Proc
    net~Net
    clock~Clock
    sched~Sched

# How a program ends: `Success` (0) or `Failure n`.
export enum ExitCode
    Success
    Failure n : n~U8, n > 0
