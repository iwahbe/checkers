#!/usr/bin/env bash
# Regenerate the corpus of SMT queries (SPEC §7.2): every query Z3 is asked
# while checking examples/, tools/checkers.ck and tests/{types,run,stress}
# (with the standard-library modules they load), and Z3's answer to each.
#
#   scripts/corpus.sh DIR [cargo build flags…]
#
# DIR is emptied first. `ckc` is built with `cargo build --release` and the
# flags given (`--no-default-features` to link an installed Z3, AGENTS.md),
# unless CKC names a `ckc` to use. CORPUS_JOBS (default 2) programs are
# checked at once.
#
# Prints the number of distinct queries, the number of Z3 calls (each
# program's distinct queries, summed: `ckc` asks Z3 once per distinct query
# per program), and Z3's answers by kind. Fails if a query or an answer came
# out two ways.
set -euo pipefail

if [ $# -lt 1 ]; then
    echo "usage: scripts/corpus.sh DIR [cargo build flags…]" >&2
    exit 2
fi
out=$1
shift
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

if [ -z "${CKC:-}" ]; then
    cargo build --release --bin ckc "$@" >&2
    CKC=$root/target/release/ckc
fi

rm -rf "$out"
mkdir -p "$out"
out=$(cd "$out" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

files=(examples/*.ck tools/checkers.ck tests/types/*.ck tests/run/*.ck tests/stress/*.ck)
# Each program writes its own corpus, so that its queries can be counted;
# they are merged below. The result is the same whatever the order.
printf '%s\n' "${files[@]}" | CKC=$CKC WORK=$work xargs -P "${CORPUS_JOBS:-2}" -I{} sh -c '
    name=$(echo "{}" | tr / _)
    CHECKERS_SMT_CORPUS=$WORK/$name "$CKC" check --no-cache "{}" >/dev/null 2>"$WORK/$name.err" || true
'

status=0
if grep -h '^corpus: ' "$work"/*.err >&2; then
    status=1
fi
calls=0
for f in "${files[@]}"; do
    p=$work/$(echo "$f" | tr / _)
    [ -d "$p" ] || continue
    calls=$((calls + $(find "$p" -name '*.smt2' | wc -l)))
    # A file another program wrote already must be the same.
    if diff -rq "$p" "$out" | grep '^Files ' >&2; then
        status=1
    fi
    cp -R "$p"/. "$out"/
done

queries=$(find "$out" -name '*.smt2' -printf '%f\n' | sort -u | wc -l)
files_written=$(find "$out" -name '*.smt2' | wc -l)
answers() { find "$out" -name '*.z3' -exec sed -s -n 2p {} + | grep -c "^$1" || true; }

echo "programs checked: ${#files[@]}"
echo "Z3:               $(cat "$out/z3-version")"
echo "distinct queries: $queries (in $files_written files, by module)"
echo "Z3 calls:         $calls"
echo "answers:          $(answers unsat) unsat, $(answers sat) sat, $(answers unknown) unknown, $(answers '(error') rejected"
echo "cut off:          $(grep -rl '^;; work cut off' "$out" --include='*.z3' | wc -l)"
echo "size:             $(du -s --apparent-size --block-size=1 "$out" | cut -f1) bytes"
exit $status
