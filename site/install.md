# Install

Checkers runs on Linux (x86-64) and macOS (Apple silicon).

## From a release

Each release has an archive per platform on [GitHub](https://github.com/iwahbe/checkers/releases), with its SHA-256 and a provenance attestation:

```
tar -xzf checkers-v0.0.1-x86_64-linux.tar.gz
export PATH="$PWD/checkers-v0.0.1-x86_64-linux/bin:$PATH"
checkers --version
```

The archive holds `bin/ckc` (the compiler), `bin/checkers` (the build tool) and `lib/checkers/std` (the standard library, where `ckc` looks for it). Verify an archive with `gh attestation verify FILE --repo iwahbe/checkers`.

## From source

You need Rust (1.98 or later), CMake and a C++ compiler: the Z3 prover is built from source and linked in, so the first build takes several minutes.

```
git clone https://github.com/iwahbe/checkers
cd checkers
cargo build --release
target/release/ckc build tools/checkers.ck -o target/release/checkers
```

`checkers` finds `ckc` next to it, and `ckc` finds the standard library in the repository.

## A first program

```checkers
module hello

import std.system (System, ExitCode)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "hello" sys.term
    Success
```

```
checkers run hello.ck
```

## Editors

`checkers lsp` is a language server. With Emacs and Eglot:

```
(define-derived-mode checkers-mode prog-mode "Checkers")
(add-to-list 'auto-mode-alist '("\\.ck\\'" . checkers-mode))
(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs '(checkers-mode "checkers" "lsp")))
```

Any editor that speaks the Language Server Protocol can run `checkers lsp` the same way.
