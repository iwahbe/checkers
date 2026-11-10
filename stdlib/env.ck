# env.ck — the environment the program was started in (SPEC §8.1, D90).
module env

import system (Env)

# An environment variable, if it is set (and is UTF-8).
export fn get name e -> r : name~String, e~Env, r~Option String
    __builtin

# The path of the running program, if the operating system says.
export fn executable e -> r : e~Env, r~Option String
    __builtin
