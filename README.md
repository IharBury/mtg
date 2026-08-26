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

`Mtg.Demo` is a console application that starts a two-player game using the
[Hobbit Welcome Decks](https://magic.wizards.com/en/news/announcements/the-hobbit-welcome-decks)
(40-card limited) and either runs a heuristic demonstration or lets you play
interactively:

```sh
lake exe mtg-demo
lake exe mtg-demo -- --interactive
lake exe mtg-demo -- --interactive --visible
lake exe mtg-demo -- --interactive --input opening.txt
lake exe mtg-demo -- --interactive --output session.txt
lake exe mtg-demo -- --multiplayer
lake exe mtg-demo -- --multiplayer --visible
lake exe mtg-demo -- --multiplayer --input opening.txt
lake exe mtg-demo -- --multiplayer --output session.txt
lake exe mtg-demo -- --seed 42 --fuel 200
```

`--interactive` is Chandra against a heuristic Nissa. `--multiplayer` lets you
issue every player's actions from the console; the prompt names who must act.
In either interactive mode, `first <name>` chooses who takes the first turn
(CR 103.1) before libraries are shuffled and opening hands are drawn. Auto
mode always has Chandra start.
`--input FILE` (one command per line) runs those commands first in either
interactive mode, then further commands come from the console. `--output FILE`
writes every command from the input file and from the console (one per line),
so a session can be replayed with `--input`. Put `first Chandra` or
`first Nissa` at the top of an input file.

In either interactive mode, `visible` prints the board as the acting player
sees it (other players' hand sizes but not the cards themselves). `visible on`
(or the `--visible` flag) keeps `state` and later log/zone updates in that
player view. With `--interactive`, that player is always Chandra; with
`--multiplayer`, the view follows whoever currently must act.

## Project layout

| Path | Purpose |
| --- | --- |
| `lakefile.toml` | Lake package (`Mtg.Engine` library, `MtgDemo` demo library, `mtg-demo` executable). |
| `lean-toolchain` | Pinned Lean toolchain version. |
| `Mtg/Engine.lean`, `Mtg/Engine/` | The `Mtg.Engine` library. |
| `Mtg/Engine/Catalog/` | Oracle cards used by the demo decks (engine remains card-agnostic). |
| `Mtg/Demo.lean`, `Mtg/Demo/` | Console demonstration, text rendering, and Welcome Deck lists. |

## Current coverage

The first slice of the engine models the two-player game:

- colors and mana (CR 105–107, 202)
- cards, types, zones, and turn structure (CR 108–110, 205, 300, 400, 500)
- starting a game, choosing who takes the first turn, opening hands, London
  mulligans, first-turn skipped draw (CR 103, 103.1, 103.5, 103.8a)
- ending a game via life, empty library, or concession (CR 104, 704.5)
- playing lands, including additional land plays this turn (CR 305.2b), activating mana abilities (including `{T}: Add` for each
  permanent of a listed type, and `{T}: Add` X mana of any color equal to
  power that may be spent only on Elf spells and abilities), activating other abilities of
  permanents (CR 602, including modal abilities at 601.2b / 700.2), playing
  granted cards from exile, and casting spells (CR 601.2, including choosing
  modes at 601.2b / 700.2, announcing targets at 601.2c, additional costs
  such as sacrificing an artifact or creature at 601.2f / 601.2h, and mana
  abilities at 601.2g)
- combat declaration and combat damage assignment (CR 510.1c–d)
- static abilities that grant trample, pump other creatures of listed types,
  pump an enchanted or equipped creature,
  set power and toughness equal to the number of lands you control (in all
  zones), or restrict blocking unless you control a Goblin or Orc; attack
  triggers that pump power, set another creature's base power and toughness,
  give another creature +2/+0 and trample, scry, or scry when you attack with one
  or more Elves; scry triggers that pump for each card looked at;
  becomes-blocked triggers that damage blocking
  creatures, flash, Aura spells that enchant a creature, Equipment (including
  Equip), enters triggers that scry (any number to the bottom, the rest on
  top in any order), draw a card, search the library for a Forest card, may
  discard a card to draw, or deal damage
  divided as you choose among one, two, or three targets (including whenever
  a creature enters or attacks), return an Elf card from your graveyard and
  gain life equal to its power, pumps when another Elf you control enters,
  landfall triggers that
  put +1/+1 counters on a target creature you control, activated pumps
  that last until end of turn, activated abilities that put +1/+1
  counters on the source, dies triggers that deal damage equal
  to last-known power to a creature an opponent controls, cast triggers that
  deal damage to each opponent when you cast an instant or sorcery, and
  adventurer cards (casting an Adventure, then the creature from exile)
- modal instants, destroy, +1/+1 counters, hexproof, vigilance, until-end-of-turn
  keyword grants, destroying permanents or dealing damage with activated
  abilities, a creature you control dealing damage equal to its power to a
  creature an opponent controls, and lasting type-changing animations (a permanent that becomes
  a Bear creature with power and toughness equal to lands you control)
- cleanup without priority except the CR 514.3a state-based-action window
- a console demo with a heuristic opponent or multiplayer interactive play,
  including choosing the starting player (CR 103.1)
