# term_checks.ck — `check`s of `term.fits`, the statement a datatype's
# acceptance rests on: witnesses that are values of their sort fit it, and
# witnesses that aren't (a later or the same datatype's kept witness, a
# different datatype's, a wrong number of fields or arguments, a field of
# the wrong sort, a constructor that isn't there, a parameter out of range)
# don't. Every `ckc check` of this file runs them.

module term_checks

import smtlib (Query)
import term (Sort, Int, Bool, Arr, Data, Param, Sig, Context)
import term (Witness, WTrue, WZero, WEmpty, WElement, WConst, WParam, WCon, WOf)

fn context src -> c : src~Bytes, c~Context
    match smtlib.parse src
        Ok q  -> q.context
        Err _ -> term.empty

# Datatypes `P` (0), `Box` (1) and `L` (2), each declared by its own command.
let P_DECL = b"(declare-datatypes ((P 0)) (((p (x Int) (y Bool)))))"
let BOX_DECL = b"(declare-datatypes ((Box 1)) ((par (A) ((box (unbox A))))))"
let L_DECL = b"(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))"
let DATA = b"(set-logic ALL)" ++ P_DECL ++ BOX_DECL ++ L_DECL ++ b"(assert (not false))(check-sat)"

let SIG = term.signature (context DATA)

fn fits first np w s -> r : first~Nat, np~Nat, w~Witness, s~Sort, r~Bool
    term.fits SIG first np w s

let P = Data 0 []
let L = Data 2 []

# The kept witnesses: `p 0 true`, `box A`, `nil`.
check len SIG.values == 3
fn kept e -> w : e~Nat, w~Option Witness
    if e < len SIG.values then Some SIG.values[e] else None

check kept 0 == Some (WCon 0 [WZero, WTrue])
check kept 1 == Some (WCon 0 [WParam 0])
check kept 2 == Some (WCon 0 [])

# ── Values of their sort fit ─────────────────────────────────────────────────

check fits 3 0 WTrue Bool
check fits 3 0 WZero Int
check fits 3 0 (WConst WZero) (Arr Int Int)
check fits 3 0 (WConst WZero) (Arr Bool Int)
check fits 3 0 (WCon 0 [WZero, WTrue]) P
check fits 3 0 (WCon 0 []) L
check fits 3 0 (WCon 1 [WZero, WCon 0 []]) L
check fits 3 0 (WCon 0 [WZero]) (Data 1 [Int])
check fits 3 1 (WCon 0 [WParam 0]) (Data 1 [Param 0])
check fits 3 0 (WCon 0 [WCon 0 [WZero, WTrue]]) (Data 1 [P])
check fits 3 0 (WOf 0 []) P
check fits 3 0 (WOf 1 [WZero]) (Data 1 [Int])
check fits 3 0 (WCon 1 [WZero, WOf 2 []]) L

# ── Witnesses that aren't values don't ───────────────────────────────────────

# Of another sort.
check not (fits 3 0 WTrue Int)
check not (fits 3 0 WZero Bool)
check not (fits 3 0 WEmpty Int)
check not (fits 3 0 WElement Int)
check not (fits 3 0 (WConst WTrue) (Arr Int Int))
check not (fits 3 0 (WCon 0 []) Int)

# A field of the wrong sort; the wrong number of fields.
check not (fits 3 0 (WCon 0 [WTrue, WTrue]) P)
check not (fits 3 0 (WCon 0 [WZero]) P)
check not (fits 3 0 (WCon 0 [WZero, WTrue, WTrue]) P)
check not (fits 3 0 (WCon 1 [WZero, WTrue]) L)
check not (fits 3 0 (WCon 0 [WTrue]) (Data 1 [Int]))

# A constructor that isn't there; a datatype that isn't there.
check not (fits 3 0 (WCon 1 [WZero, WTrue]) P)
check not (fits 3 0 (WCon 2 []) L)
check not (fits 3 0 (WCon 0 []) (Data 9 []))
check not (fits 3 0 (WOf 9 []) (Data 9 []))

# The wrong number of arguments to the datatype.
check not (fits 3 0 (WCon 0 [WZero]) (Data 1 []))
check not (fits 3 0 (WCon 0 [WZero, WTrue]) (Data 0 [Int]))
check not (fits 3 0 (WOf 1 []) (Data 1 [Int]))
check not (fits 3 0 (WOf 1 [WZero, WZero]) (Data 1 [Int]))

# A parameter out of range, or another parameter.
check not (fits 3 0 (WParam 0) (Param 0))
check not (fits 3 1 (WParam 1) (Param 1))
check fits 3 2 (WParam 1) (Param 1)
check not (fits 3 2 (WParam 0) (Param 1))
check not (fits 3 0 (WCon 0 [WParam 0]) (Data 1 [Param 0]))

# Another datatype's kept witness, the same one's (not yet accepted), a
# later one's, and an accepted one's at an argument of the wrong sort.
check not (fits 3 0 (WOf 0 []) L)
check not (fits 2 0 (WOf 2 []) L)
check not (fits 1 0 (WOf 2 []) L)
check not (fits 0 0 (WOf 0 []) P)
check not (fits 2 0 (WCon 1 [WZero, WOf 2 []]) L)
check not (fits 3 0 (WOf 1 [WTrue]) (Data 1 [Int]))
