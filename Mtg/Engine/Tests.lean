import Mtg.Engine.Tests.Fixtures
import Mtg.Engine.Tests.Events

/-!
# Compile-time smoke tests for the engine.

This module re-exports the `Mtg.Engine.Tests.*` files. Declarations stay in
`namespace Mtg.Engine.Tests`, so `import Mtg.Engine.Tests` and `Tests.started`
keep working.

- `Helpers`: fixtures, start-of-game setup, and idle-action helpers
- `CardText`: catalog summary and printed-text smoke tests
- `Turns`: turn structure, cleanup, and basic combat or bolt smoke tests
- `Mulligans`: London mulligans, multiplayer combat, and Brawl
- `Activation`: activated abilities, exile play, granted trample, and becomes-blocked
- `Auras`: mana helpers, counters, Auras, the legend rule, and enters triggers
- `Combat`: modal activation, combat damage assignment, and Warg Tactics
- `Equipment`: Equipment, attach choices, and Beorn's Hospitality
- `Damage`: divided damage, activated pumps, and dies triggers
- `AttackTriggers`: attack triggers that copy P/T, grant trample, or scry
- `Adventures`: adventurer cards and blocking restrictions
- `CastTriggers`: cast triggers, additional costs, and activated keyword grants
- `Elves`: Elf lords, scry pumps, and restricted-mana abilities
- `Pathmaker`: mana-payment heuristics and characteristic-defining P/T
- `Fight`: fight spells, landfall pumps, and APNAP dies triggers
- `Removal`: unblockable, exile-instead, Ferocious, and draw-and-lose-life
- `Abilities`: additional costs, graveyard activations, mass effects, and MSH smokes
- `Cycling`: typecycling, menace, cost reductions, and linked exile
- `Targets`: optional and sequential spell targets
- `Effects`: tokens, sequenced resolution effects, and Sagas
- `Leaving`: a player leaving a multiplayer game (CR 800.4)
- `Marvel`: MSH connive, teamwork, Power-up, and wards
- `CatalogSmoke`: the supported catalog names the MSH cards those tests use
- `ParseOracle`: printed-card parsing, Oracle normalization, and argument reading
- `MayCast`: casting from a graveyard, from hand, and from an impulse
- `Draw`: fixed draws, counted draws, mana spent, and the opponent's draw offer
- `ReturnToHand`: graveyard cards, permanents, milled subtypes, and the source
- `Put`: linked exile, a graveyard nonland, the source, noted lands,
  a discarded land, and cards from hand via unified `ObjectExpr`
- `AddMana`: printed mana, and {G} for each charge counter on the source
- `Destroy`: opponents' artifacts and enchantments, a permanent dealt
  damage, and the announced creature noted for amass
- `Discard`: the controller's cards or hand, each opponent, the announced
  opponent, and a discard after mana was spent
- `TriggerFight`: the source fighting up to one creature, and the
  Equipment host dealing damage equal to its power
- `Grant`: double strike for equipped attackers, and protection from
  everything when the source was cast
- `GainLife`: a fixed amount, the targeted card's power, one life per
  permanent destroyed, one life per other creature, and life per attached
  Equipment via unified `ValueExpr`
- `LoseLife`: a fixed amount for the controller, the announced opponent,
  or each opponent, and one life per burden counter on the source
- `Mill`: the controller, the announced player, the player who lost life,
  remembered cards, and each opponent
- `RemoveCounters`: a hope counter from the source, and every counter
  from the enchanted creature
- `RevealFromHand`: the opponent's hand with an exile until the source
  leaves, and a counted reveal from the announced player's hand
- `RevealLibrary`: the top cards and a random creature, revealing until a
  creature, revealing until a Saga, and exiling until an instant or sorcery
- `SearchLibrary`: a Forest onto the battlefield, a basic land into hand,
  a basic land you may put on top, and a Dragon from hand or library
- `Tap`: any number of Humans, the enchanted creature, and the announced
  permanent while it is still on the battlefield
- `Lose`: indestructible until end of turn, and all abilities while the
  source remains
- `Cant`: can't be blocked this turn, and can't untap while you control
  the source
- `PutOnLibrary`: which card is put on a library via unified `ObjectExpr`
- `SetBasePT`: a fixed base power and toughness, and another creature's
  base power and toughness equal to this creature's via unified `ValueExpr`
  and `ObjectExpr`
- `Untap`: the announced permanent, the source, the enchanted creature,
  the target while the source remains, and each attacking creature
- `Modes`: Alliance, Gollum, and chosen up-to-X modes
- `Chapter`: printed Saga chapters resolved via unified `Instruction`
- `Count`: `Condition.cmp` compares two `ValueExpr`s, including how many objects an `ObjectExpr` names
- `Step`: upkeep, end-step, and first-main triggers
- `Death`: dies triggers
- `ThisAttack`: attack triggers
- `EnterOrAttack`: enters-or-attacks triggers
- `Watch`: watch triggers
- `YouAttack`: “whenever you attack” triggers
- `Casting`: “whenever you cast …” triggers
- `Resource`: draw, discard, life, and +1/+1-counter triggers
- `Reflexive`: a reflexive queued now, after the Plan is sacrificed, after a mill, and an attack pump armed for this turn
- `Pay`: mana, and a sacrificed or discarded object, paid via unified `CostSpec`
- `Sacrifice`: who sacrifices and which permanent via unified `ObjectExpr`
- `PutCounters`: what counter is put and who receives it via unified `CounterOp` and `ObjectExpr`
- `BecomeArtifact`: who becomes an artifact until end of turn via unified `ObjectExpr`
- `BecomePrepared`: who becomes prepared via unified `ObjectExpr`
- `Exile`: which cards are exiled via unified `ObjectExpr`
- `EvalExpr`: Phase 2 pure expression algebra (`Expr`), Stage-4 sub-grammars, live + LKI `EvalExpr`, generalized `TokenSpec`, and `ManaSpec`
- `CostKeywords`: Phase 4 compositional `CostSpec`, parameterized `KeywordAbility`, CR 122.1b keyword counters, Layer 3 text changes, CR 606.5–6 net loyalty, `StaticAbility.cantBeBlocked`, and compositional `Ward`
- `ActivatedMana`: Phase 5 unified `ActivatedAbility`, CR 305.6–7 intrinsic basic-land mana & subtype-setting removal, CR 605.1a 4-criteria mana abilities, per-ability Boast/Exhaust/Power-up limits, extended `SpellRiderSpec`, declarative cost reductions, and CR 106.7 Reflecting Pool / Exotic Orchard
- `StaticAbilities`: Phase 6 stratified 6-constructor `StaticAbility`, Layer 3 text changes, Layer 6 Humility & CR 613.8 dependency, CR 707.9d copy CDA stripping, Layer 7a/7b ordering, command-zone statics, CR 303.4a Aura `enchantRestriction`, migrated keywords/Boast/split-second, and novel parsed static abilities
- `TriggeredAbilities`: Phase 7 unified `TriggerPattern` & pattern-driven `matchTriggers`, CR 603.10a–f look-back & `.or` two-pass deduplication, CR 603.4 `interveningIf?` vs. CR 603.2 `.whenCond`, CR 605.1b triggered mana abilities, CR 700.1 `BatchGrouping`, CR 714.2b/d dynamic Layer-6 Saga chapters, per-trigger modal choices (`Instruction.chooseModes`), Path of Ancestry via `triggeredAbilities`, and `CardDef.modellingError?` trigger validation
- `Interpreter`: Phase 8 unified `Instruction` AST, lexical `ContinuationFrame.stepEnv` (CR 608.2c / 614.6) across non-commuting CR 616.1 replacements, excess damage, compositional Recruit, CR 701.44a/c & CR 400.3 Explore, folded Empower Jace, unified `ModalSpec` & Layer-3 `HasTextChange`, `GrantedAbility` tokens, and Stage-4 `Parser.parseInstructionEffect`
- `Events`: the game event log, conditions read from it, and trigger and replacement matching
-/
