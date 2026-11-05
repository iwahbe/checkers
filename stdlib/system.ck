# system.ck — the root capability and exit codes (SPEC §8.2).
module system

import terminal (Term)
import files (Fs)
import cown (Sched)

export abstract enum Env
export abstract enum Proc
export abstract enum Net
export abstract enum Clock

export record System
    term~Term
    fs~Fs
    env~Env
    proc~Proc
    net~Net
    clock~Clock
    sched~Sched

export enum ExitCode
    Success
    Failure n : n~U8, n > 0
