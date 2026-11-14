# Completion cases (D142, proposed)

Each `.ck` file marks the cursor with `‸` and lists, in comments, what
`ckc complete` should give there. The lists name the candidates that
matter; "the prelude's names" stands for the rest of what is in scope.
`recovery.ck` shows the diagnostics D142 (e) would give instead of
today's. When D142 is decided these become `tests/complete/` (the cursor
written as `-- complete LINE COL` in a header) and `tests/lsp/` sessions.
