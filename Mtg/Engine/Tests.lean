import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.CardText
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Mulligans
import Mtg.Engine.Tests.Activation
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Combat
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Damage
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.CastTriggers
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Fight
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Cycling
import Mtg.Engine.Tests.Targets
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Leaving
import Mtg.Engine.Tests.Marvel
import Mtg.Engine.Tests.CatalogSmoke
import Mtg.Engine.Tests.RealityFracture
import Mtg.Engine.Tests.RealityFractureCommander
import Mtg.Engine.Tests.ParseOracle
import Mtg.Engine.Tests.MayCast
import Mtg.Engine.Tests.Draw
import Mtg.Engine.Tests.ReturnToHand
import Mtg.Engine.Tests.Put
import Mtg.Engine.Tests.AddMana
import Mtg.Engine.Tests.Destroy
import Mtg.Engine.Tests.Discard
import Mtg.Engine.Tests.TriggerFight
import Mtg.Engine.Tests.Grant
import Mtg.Engine.Tests.GainLife
import Mtg.Engine.Tests.LoseLife
import Mtg.Engine.Tests.Mill
import Mtg.Engine.Tests.RemoveCounters
import Mtg.Engine.Tests.RevealFromHand
import Mtg.Engine.Tests.RevealLibrary
import Mtg.Engine.Tests.SearchLibrary
import Mtg.Engine.Tests.Tap
import Mtg.Engine.Tests.Lose
import Mtg.Engine.Tests.PutOnLibrary
import Mtg.Engine.Tests.SetBasePT
import Mtg.Engine.Tests.Untap
import Mtg.Engine.Tests.Modes
import Mtg.Engine.Tests.Chapter
import Mtg.Engine.Tests.Step
import Mtg.Engine.Tests.Death
import Mtg.Engine.Tests.ThisAttack
import Mtg.Engine.Tests.EnterOrAttack
import Mtg.Engine.Tests.Watch
import Mtg.Engine.Tests.YouAttack
import Mtg.Engine.Tests.Casting

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
- `Put`: putting linked exile, graveyard cards, noted lands, discarded
  lands, and cards from hand onto the battlefield
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
  permanent destroyed, and one life per other creature
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
- `PutOnLibrary`: the announced permanent on top or on the bottom of its
  owner's library, and a card from hand on the bottom
- `SetBasePT`: a fixed base power and toughness, and another creature's
  base power and toughness equal to this creature's
- `Untap`: the announced permanent, the source, the enchanted creature,
  the target while the source remains, and each attacking creature
- `Modes`: Alliance, Gollum, and chosen up-to-X modes
- `Chapter`: printed Saga chapters resolved by the other trigger constructors
- `Step`: upkeep, end-step, and first-main triggers that used to resolve as `step`
- `Death`: dies triggers that used to resolve as `death`
- `ThisAttack`: attack triggers that used to resolve as `thisAttack`
- `EnterOrAttack`: enters-or-attacks triggers that used to resolve as `enterOrAttack`
- `Watch`: watch triggers that used to resolve as `watch`
- `YouAttack`: “whenever you attack” triggers that used to resolve as `youAttacking`
- `Casting`: “whenever you cast …” triggers that used to resolve as `casting`
-/
