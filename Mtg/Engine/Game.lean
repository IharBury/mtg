import Mtg.Engine.Game.Status
import Mtg.Engine.Game.Object
import Mtg.Engine.Game.Stack
import Mtg.Engine.Game.Pending
import Mtg.Engine.Game.Player
import Mtg.Engine.Game.Core
import Mtg.Engine.Game.Designations
import Mtg.Engine.Game.Phasing
import Mtg.Engine.Game.BasePT
import Mtg.Engine.Game.Allocation
import Mtg.Engine.Game.Tokens
import Mtg.Engine.Game.Attachments
import Mtg.Engine.Game.StatBonuses
import Mtg.Engine.Game.Movement
import Mtg.Engine.Game.Leaving
import Mtg.Engine.Game.Library
import Mtg.Engine.Game.Keywords
import Mtg.Engine.Game.PowerToughness
import Mtg.Engine.Game.CombatAssignment
import Mtg.Engine.Game.StateBasedActions
import Mtg.Engine.Game.Timing
import Mtg.Engine.Game.Targeting
import Mtg.Engine.Game.Triggers
import Mtg.Engine.Game.Entering
import Mtg.Engine.Game.LandsAndMana
import Mtg.Engine.Game.SpellTargets
import Mtg.Engine.Game.Casting
import Mtg.Engine.Game.Choices
import Mtg.Engine.Game.Costs
import Mtg.Engine.Game.CastSpell
import Mtg.Engine.Game.Activation
import Mtg.Engine.Game.SacrificeDiscard
import Mtg.Engine.Game.Damage
import Mtg.Engine.Game.Pumps
import Mtg.Engine.Game.LibrarySearch
import Mtg.Engine.Game.ResolutionHelpers
import Mtg.Engine.Game.ResolutionEffects
import Mtg.Engine.Game.ModeledTriggers
import Mtg.Engine.Game.EffectResolution
import Mtg.Engine.Game.CastExtras
import Mtg.Engine.Game.Chapters
import Mtg.Engine.Game.TriggeredAbilities
import Mtg.Engine.Game.SpellResolution
import Mtg.Engine.Game.Combat
import Mtg.Engine.Game.Turns
import Mtg.Engine.Game.PriorityActions
import Mtg.Engine.Game.Mulligans
import Mtg.Engine.Game.Decisions
import Mtg.Engine.Game.Actions
import Mtg.Engine.Game.Start

/-!
# Game state and rules engine

Encodes starting a game (CR 103), including the London mulligan (CR 103.5,
including the free first mulligan in multiplayer and Brawl, CR 103.5c),
ending a game (CR 104), a player leaving a multiplayer game (CR 800.4),
priority (CR 117), playing lands (CR 116.2a / 305),
including additional land plays this turn (CR 305.2b),
casting the spells we model (CR 601), including choosing modes of modal spells
and abilities (CR 601.2b / 700.2), announcing a value for `{X}`
(CR 107.3a / 601.2b), announcing additional or alternative costs
(CR 601.2b) before targets (CR 601.2c), dividing
damage among those targets (CR 601.2d), then determining and paying costs
including sacrificing an artifact or creature (CR 601.2f / 601.2h) or paying life (CR 118.3b / 119.4),
drawing cards and losing life (CR 121 / 118.3a),
and activating mana abilities while
paying (CR 601.2g), activating non-mana abilities of permanents, cards in hand
(typecycling, CR 702.29), and graveyard cards (CR 602),
including destroying permanents (CR 701.7), equip (CR 702.6), and lasting
type-changing animations (CR 205.1a / 611.2a), static abilities that grant
trample, pump other creatures of listed types, pump an enchanted or equipped
creature, set power and toughness
equal to lands you control in all zones (CR 604.3 / 208.2a), restrict blocking unless you control certain
creature types (CR 604 / 208.2a / 613.3 / 509.1b), or prevent blocking except by
two or more (menace, CR 702.111) or N or more creatures, until-end-of-turn
effects that prevent creatures without flying from blocking, can't-be-blocked
if power is N or less, and can't-be-blocked
(CR 509.1b / 611.2a), until-end-of-turn
layer-7b base P/T setting (CR 613.3b), Aura spells (CR 303.4),
Equipment (CR 301.5), flash (CR 702.8), hexproof (CR 702.11),
indestructible (CR 702.12), deathtouch (CR 702.2 / 704.5h), lifelink (CR 702.15),
menace (CR 702.111), scry (CR 701.20),
discard (CR 701.9), destroy (CR 701.8), including a target artifact or land or
creature (and its controller losing life), mass until-end-of-turn P/T changes,
drawing and losing life, +1/+1 counters (CR 122), until-end-of-turn
keyword grants and losses, replacement effects that exile a creature instead of
dying this turn (CR 614.1 / 614.6 / 700.4), attack triggers (CR 508.2 / 603), including scrying, copying this
creature's P/T onto another creature you control, giving another creature
+2/+0 and trample, or gaining life while you control a creature with power 4
or greater (Ferocious), becomes-blocked triggers
(CR 509.5c / 603), enters triggers (CR 603.6a), including searching the library
for a Forest card (CR 701.19 / 305.7), drawing, scrying, optional
discard-to-draw, damage divided as you choose when a creature enters or
attacks (CR 601.2d), returning an Elf card from your graveyard to gain
life equal to its power (CR 701.19 / 118.2), each player sacrificing a creature,
a target opponent sacrificing a creature of their choice, each opponent discarding a card,
and exiling a card from an opponent's graveyard while opponents lose life,
another-Elf-enters pumps
(CR 603.6a), landfall triggers that put +1/+1 counters or pump the source
until end of turn (CR 603.6a / 603.3d / 601.2c),
triggered abilities waiting until a player would receive priority and
going on the stack in APNAP order (CR 603.3 / 603.3b),
dies triggers that deal damage equal to last-known power (CR 700.4 / 113.7a)
or give an opposing creature -1 / -1, and “whenever one or more other creatures die”
scry triggers,
cast triggers that deal damage to each opponent when you cast an instant or
sorcery (CR 601.2i / 603.3), attack-with-Elves scry triggers and scry pumps
for each card looked at (CR 508.2 / 701.20 / 603),
vigilance (CR 702.20), `{T}: Add` mana equal to power of any color with an
Elf-only spending restriction (CR 106.10 / 605),
activated pumps that last until end of turn (including paying life),
activated abilities that
put +1/+1 counters on the source, making a target creature unblockable
until end of turn (CR 602 / 611.2a / 122 / 509.1b / 118.3b), and graveyard
activations that return the card to the battlefield tapped or to hand
(CR 404 / 602), including only if you control a legendary creature,
adventurer cards including casting an Adventure and later the permanent
(CR 715), playing exiled creature cards with mana of any type
(CR 118.12 / 400.7), cost reductions if a creature died this turn or if the
target was dealt damage this turn (CR 118.7 / 601.2f), additional costs that
sacrifice an artifact or creature, discard a card, or pay extra generic mana (announced at
CR 601.2b, determined and paid at 601.2f–h),
typecycling from hand (CR 702.29: discard this card, search for a land type,
put it into your hand, then shuffle),
combat (CR 506–510, including combat damage assignment under
CR 510.1c–d, deathtouch as lethal for trample, CR 702.2c / 702.19b, and lifelink,
CR 702.15b), Saga lore counters and chapter abilities (CR 714), cleanup
(CR 514.3), and the state-based actions we implement
(CR 704.5, including deathtouch, CR 704.5h, the legend rule, CR 704.5j,
and sacrificing a Saga after its final chapter, CR 714.4),
and a player leaving a multiplayer game (CR 800.4 and 800.4a–p).

This module re-exports the `Mtg.Engine.Game.*` files, one per abstraction:

- `Status`: Permanent status (CR 110.5)
- `Object`: Game objects (CR 109)
- `Stack`: Stack entries and proposed casts (CR 405 / 601)
- `Pending`: Pending decisions
- `Player`: Players, actions, and setup (CR 102 / 103)
- `Core`: Game state core
- `Designations`: Player designations
- `Phasing`: Attachments in play and phasing (CR 702.26)
- `BasePT`: Characteristic-defining P/T (CR 604.3)
- `Allocation`: Object allocation
- `Tokens`: Tokens (CR 111)
- `Attachments`: Attach and unattach (CR 701.3)
- `StatBonuses`: Continuous stat bonuses (CR 613)
- `Movement`: Zone changes (CR 400)
- `Leaving`: Game end and leaving the game (CR 104 / 800.4)
- `Library`: Draws, shuffles, and library order (CR 121)
- `Keywords`: Current keywords (CR 613.1f)
- `PowerToughness`: Current power and toughness (CR 613.4)
- `CombatAssignment`: Combat damage assignment (CR 510.1)
- `StateBasedActions`: State-based actions (CR 704)
- `Timing`: Priority and play timing (CR 117 / 116.2a)
- `Targeting`: Legal targets (CR 115)
- `Triggers`: Triggered abilities onto the stack (CR 603.3)
- `Entering`: Cast and enters triggers (CR 601.2i / 603.6a)
- `LandsAndMana`: Playing lands and mana abilities (CR 305 / 605)
- `SpellTargets`: Announcing targets and modes (CR 601.2b–d)
- `Casting`: Casting legality and payment (CR 601)
- `Choices`: Resolution choices
- `Costs`: Total costs (CR 601.2f–h)
- `CastSpell`: The casting process (CR 601.2)
- `Activation`: Activating abilities (CR 602)
- `SacrificeDiscard`: Sacrifice and discard prompts (CR 701.17 / 701.9)
- `Damage`: Damage, destruction, and life (CR 120 / 119)
- `Pumps`: Pumps, grants, and counters (CR 613.4c / 122)
- `LibrarySearch`: Searching the library (CR 701.19)
- `ResolutionHelpers`: Resolution target helpers (CR 608.2b)
- `ResolutionEffects`: Named resolution effects
- `ModeledTriggers`: Modeled trigger resolution
- `EffectResolution`: Unified effect resolution (CR 608)
- `CastExtras`: Optional costs, cascade, and the Ring
- `Chapters`: Saga chapter resolution (CR 714.3)
- `TriggeredAbilities`: Triggered-ability resolution (CR 603)
- `SpellResolution`: Spell resolution (CR 608)
- `Combat`: Combat (CR 506–510)
- `Turns`: Turn structure (CR 500 / 514)
- `PriorityActions`: Passing, paying, and conceding
- `Mulligans`: Opening hands and mulligans (CR 103.4–5)
- `Decisions`: Decision handlers
- `Actions`: Applying player actions
- `Start`: Starting a game (CR 103)
-/
