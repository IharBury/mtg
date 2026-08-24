# Mtg.Engine

A [Lean 4](https://lean-lang.org/) rules engine for
[*Magic: The Gathering*](https://magic.wizards.com/), built with
[Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

The engine follows the *Magic: The Gathering* Comprehensive Rules **effective
7 August 2026**. The official text is published by Wizards of the Coast at:

<https://media.wizards.com/2026/downloads/MagicCompRules%2020260819.txt>

## Prerequisites

Lean is managed by [`elan`](https://github.com/leanprover/elan). Installing
`elan` and then running any Lake command inside this repository downloads the
toolchain pinned in [`lean-toolchain`](./lean-toolchain).

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

## Build

```sh
lake build
```

## Demo

`Mtg.Demo` is a console application that starts a two-player constructed game
and either runs a heuristic demonstration or lets you play interactively:

```sh
lake exe mtg-demo
lake exe mtg-demo -- --interactive
lake exe mtg-demo -- --seed 42 --fuel 200
```

## Project layout

| Path | Purpose |
| --- | --- |
| `lakefile.toml` | Lake package (`Mtg.Engine` library, `mtg-demo` executable). |
| `lean-toolchain` | Pinned Lean toolchain version. |
| `Mtg/Engine.lean`, `Mtg/Engine/` | The `Mtg.Engine` library. |
| `Mtg/Demo.lean` | Console demonstration (`Mtg.Demo`). |

## Current coverage

The first slice of the engine models the two-player constructed game:

- colors and mana (CR 105–107, 202)
- cards, types, zones, and turn structure (CR 108–110, 205, 300, 400, 500)
- starting a game, opening hands, first-turn skipped draw (CR 103, 103.8a)
- ending a game via life, empty library, or concession (CR 104, 704.5)
- playing lands, tapping for mana, casting creatures and simple instants
- combat declaration and combat damage
- a console demo with a heuristic opponent
