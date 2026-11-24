# Leading the solver project (#72)

This file exists only on the integration branch `smt`. It is a process detail:
**delete it in the last commit before `smt` is offered to `main`**, and never
copy it elsewhere in the tree. Ian wrote the goals; the leader keeps the rest
current (edit it by pull request to `smt`, like any other change).

## Goal

Drive https://github.com/iwahbe/checkers/issues/72 to the point where replacing
Z3 is viable: every line of the issue's "bar to switch" holds, measured, on
`smt`. Removing Z3 and merging `smt` into `main` are Ian's.

Do not cut corners. A slower honest result beats a faster one that hides a gap.

## Roles

- **Leader:** one session, woken hourly by a scheduled task. It plans, spawns
  workers, reviews and merges their pull requests into `smt`, and keeps the
  issues true. It writes no solver code itself.
- **Workers:** one session per sub-issue, model `claude-opus-5-5`, created with
  `create_session` in the leader's environment (`checkers`), with
  `source_url` the repository, `source_revision: smt`, and its own
  `outcome_branch` (`smt-<issue>-<slug>`). At most 3 at a time.
- **Ian:** decides. Everything in #72 not marked decided is still
  **(proposed)**; so is anything a worker designs. He reviews the spec,
  examples and compiler output, not the implementation (AGENTS.md).

## State lives in GitHub

The leader's context is lost on compaction or replacement, so nothing may live
only there.

- #72 is the tracker. Each work item is a sub-issue of #72 with: what done
  means (a command and its expected result), what it depends on, its state
  (`ready`, `in progress`, `blocked on #N`, `in review`, `done`), and, while a
  worker has it, the worker's session id and branch in a comment.
- On every wake, rebuild the picture from the sub-issues, the open pull
  requests against `smt`, and `list_sessions` with `children: true`. Trust
  those over memory.
- Every comment the leader or a worker posts ends with the footer the session
  instructions require, and says it was written by an AI agent.

## Each wake

1. Read #72's sub-issues and comments since the last wake. Act on anything
   Ian wrote first; his word overrides this file.
2. For each worker: `get_session` (a `failed` bucket or a disconnected worker
   needs action), then its pull request. A worker idle with no pull request
   and no question has stalled: read its last events and message it or replace
   it. Archive workers whose work is merged or abandoned.
3. Review pull requests that are ready (below). Merge or send back.
4. Spawn workers for `ready` sub-issues, most blocking first, up to the limit.
5. Update the sub-issues' states. Once a day, post a short status comment on
   #72: merged since yesterday, in flight, blocked and on what, decisions
   waiting for Ian, and the comparison table once it exists.
6. If nothing can move without Ian, say exactly what is needed in that comment
   and end the turn. Do not invent work.

## Rules for all work

1. **Never work around a Checkers bug.** If the compiler, prover, runtime,
   formatter or a tool is wrong, or says something unhelpful where it should
   help, stop that line of work. File an issue as SPEC §12 asks ("found X,
   expected Y", the smallest `.ck` that shows it, abstracted from the solver),
   search for a duplicate first, mark the sub-issue `blocked on #N`, and pick up
   something else. A separate worker fixes the bug in `ckc` (golden test
   first, AGENTS.md) by pull request to `main`'s usual process: branch from
   `main`, pull request to `main`, Ian merges. `smt` then merges `main`.
2. **A missing `std` lemma or constraint is a bug in `std`.** If an exported
   `std` function's signature doesn't state what the solver needs to know
   about it, or the lemma about it doesn't exist, do not restate or re-prove
   it in the solver package, and do not write a local copy of the function.
   File it and fix it in `std`, as in rule 1.
3. **A workaround is anything written differently because the direct way
   failed for a reason that isn't the solver's own.** When unsure, it is one.
   The pull request description lists every place the author did this
   knowingly; the right number is zero.
4. **No `admit`, no `partial`, no trusted escape** in the solver package,
   at any stage, not even temporarily on `smt`. A proof that isn't finished
   is a pull request that isn't ready. `checks_sound` is never weakened to
   make it provable; a change to its statement is a decision for Ian.
5. **Never raise a Z3 work limit, skip, delete or loosen a test, or accept a
   changed `.out` unread** to get green.
6. **The spec comes first.** Behaviour that changes `ckc` or the language goes
   in SPEC.md before the code. A design choice #72 leaves open, or gets wrong,
   becomes a `proposal` issue with the options and a recommendation; work that
   depends on it waits or proceeds only on the part every option shares.
7. **Measure, don't estimate.** A claim about coverage or speed comes with the
   command that produced it.
8. AGENTS.md applies in full: golden tests, formatting, clippy, zero
   diagnostics in `examples/`.

## Decided by Ian (11/19/2026)

- #72's design is accepted far enough to build on.
- The leader may merge workers' pull requests into `smt`. `main` stays Ian's.
- Model limits (#72, open question 1): state them as a lemma if a lemma can
  say it; documentation only for what a lemma can't. Make this a sub-issue
  that first finds out which.
- Building `checks_sound` (open question 2): start with both. While
  confidence is being built, the package's own obligations are checked by Z3
  and by our solver.
- The work unit and its limits are not a question: set them when the core
  exists.
- Sequences (open question 3): #87, changing the encoding in `ckc` first, is
  closed as not planned (measured on Z3: slower, and proofs lost). The
  encoding stays; the solver gets a sequence procedure (#89, order-of-work
  step 7), after steps 1–6. Its design is a proposal for Ian before any code.
- The package lives at `smt/` and is called `smt` (#80).
- How the corpus is stored (#81) is the leader's to decide.
- A `forall` without `:pattern` (#82): the leader's to decide, without
  cutting corners on correctness. Decided: `parse` accepts it as an axiom
  with no patterns. It is never dropped; `Valid` comes only through the
  certificate; a query with one is never `Invalid` unless `smt.model` shows
  the model satisfies it (else `Unknown`); the comparison tool reports these
  queries as their own row. How a model is checked against one is a design
  to propose under #84.

## Merging into `smt`

A pull request is ready when all of these hold. Check them yourself in a
clean checkout of the branch; do not take the worker's word.

- `cargo test --no-default-features` passes (all tests, not only the unit
  tests CI runs on pull requests), and `cargo clippy` is clean.
- The solver package checks with zero diagnostics and no `admit`.
- Its sub-issue's "done" command gives the expected result.
- Once the comparison tool exists: no bug row (`Valid` against Z3's `sat`,
  `Invalid` against `unsat`), and no query that was answered before is now
  `Unknown` without a reason in the description.
- Rules 1–5: read the diff for workarounds. Ask a fresh reviewer agent for a
  second reading of anything touching `smt.cert` or `smt.model`, giving it the
  diff and not your opinion.
- The description says `Part of #N` (never `Closes #72`).

Then merge. Keep `smt` current by merging `main` into it; never rebase or
force-push `smt`.

CI: pull requests into `smt` need only the Linux job (macOS minutes run out),
and should run the integration tests there too. Changing `ci.yml` for that is
the first pull request; it must leave `main`'s jobs as they are.

## First wake

1. Read #72, SPEC §7, AGENTS.md, `src/verify/`.
2. Fix CI for `smt` as above.
3. Write the plan as sub-issues of #72, following its "Order of work", with
   the golden corpus and the comparison tool first: nothing else can be
   judged without them. Where the package lives and what it is called are
   proposals for Ian.
4. Spawn the first workers.
