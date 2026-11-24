#!/usr/bin/env bash
# Ask Z3 each query of tests/smt/model/ (the golden tests of `smt.model`'s
# semantics) and write its answer beside it as NAME.z3. A query whose name
# starts with `full_` is asked with `(get-model)` after it, as
# `main models --z3` does. With --check, ask
# again and fail if an answer differs from the one kept. An answer whose
# first line is `;; edited` was changed by hand on purpose (it says why)
# and is left alone.
#
# Needs a `z3` executable: Z3 5.3.3 (`pip install z3-solver==5.3.3`).
set -euo pipefail
cd "$(dirname "$0")/.."
check=0
if [ "${1:-}" = "--check" ]; then check=1; fi
version=$(z3 -version)
case "$version" in
    *"5.3.3"*) ;;
    *) echo "smt-model-answers: expected Z3 5.3.3, found: $version" >&2; exit 2 ;;
esac
status=0
for q in tests/smt/model/*.smt2; do
    a="${q%.smt2}.z3"
    if [ -f "$a" ] && head -1 "$a" | grep -q '^;; edited'; then continue; fi
    if [[ "$(basename "$q")" == full_* ]]; then
        out=$(cat "$q" <(echo "(get-model)") | z3 -in)
    else
        out=$(z3 -in < "$q")
    fi
    if [ $check = 1 ]; then
        if [ "$out" != "$(cat "$a")" ]; then echo "differs: $a" >&2; status=1; fi
    else
        printf '%s\n' "$out" > "$a"
    fi
done
exit $status
