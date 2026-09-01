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
- `Marvel`: MSH connive, teamwork, Power-up, wards, and remaining catalog interactions
-/
