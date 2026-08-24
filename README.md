# mtg

A [Lean 4](https://lean-lang.org/) project built with the
[Lake](https://github.com/leanprover/lean4/tree/master/src/lake) build tool.

## Prerequisites

Lean is managed by [`elan`](https://github.com/leanprover/elan), the Lean
toolchain manager. Installing `elan` and then running any Lake command inside
this repository automatically downloads the exact toolchain pinned in
[`lean-toolchain`](./lean-toolchain).

Install `elan` (once per machine):

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
```

Make sure `~/.elan/bin` is on your `PATH` (the installer adds this to your
shell profile; for the current shell run `export PATH="$HOME/.elan/bin:$PATH"`).

## Build

```sh
lake build
```

## Run

```sh
lake exe mtg
```

## Project layout

| Path | Purpose |
| --- | --- |
| `lakefile.toml` | Lake package manifest (library `Mtg`, executable `mtg`). |
| `lean-toolchain` | Pinned Lean toolchain version. |
| `Mtg.lean`, `Mtg/` | The `Mtg` library. |
| `Main.lean` | Executable entry point. |
