import Mtg.Engine.Color
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, keywords, and the static,
triggered, activated, and spell abilities we currently model.
-/

namespace Mtg.Engine

/-- Keyword abilities that the engine currently understands. -/
structure Keywords where
  flash : Bool := false
  haste : Bool := false
  vigilance : Bool := false
  flying : Bool := false
  /-- This creature can't be blocked (printed or granted until end of turn). -/
  cantBeBlocked : Bool := false
  /-- This creature can't be blocked except by two or more creatures (CR 702.111). -/
  menace : Bool := false
  hexproof : Bool := false
  indestructible : Bool := false
  reach : Bool := false
  trample : Bool := false
  deathtouch : Bool := false
  defender : Bool := false
  /-- Damage this source deals causes its controller to gain that much life (CR 702.15). -/
  lifelink : Bool := false
  /-- This creature deals combat damage before creatures without first strike
  (CR 702.7). -/
  firstStrike : Bool := false
  /-- This creature can't be blocked as long as the defending player controls
  an Island (CR 702.14). -/
  islandwalk : Bool := false
deriving BEq, Repr, Inhabited

namespace Keywords

def none : Keywords := {}

/-- One modeled keyword: how to read it, write it, and print its Oracle name.
`merge` and `toList` fold this table so a new keyword is one row here plus a
field on `Keywords` and a `Keyword.*` value. -/
structure Field where
  get : Keywords → Bool
  set : Keywords → Bool → Keywords
  name : String

def fields : List Field := [
  ⟨(·.flash), fun k b => { k with flash := b }, "flash"⟩,
  ⟨(·.haste), fun k b => { k with haste := b }, "haste"⟩,
  ⟨(·.vigilance), fun k b => { k with vigilance := b }, "vigilance"⟩,
  ⟨(·.flying), fun k b => { k with flying := b }, "flying"⟩,
  ⟨(·.cantBeBlocked), fun k b => { k with cantBeBlocked := b }, "can't be blocked"⟩,
  ⟨(·.menace), fun k b => { k with menace := b }, "menace"⟩,
  ⟨(·.hexproof), fun k b => { k with hexproof := b }, "hexproof"⟩,
  ⟨(·.indestructible), fun k b => { k with indestructible := b }, "indestructible"⟩,
  ⟨(·.reach), fun k b => { k with reach := b }, "reach"⟩,
  ⟨(·.trample), fun k b => { k with trample := b }, "trample"⟩,
  ⟨(·.deathtouch), fun k b => { k with deathtouch := b }, "deathtouch"⟩,
  ⟨(·.defender), fun k b => { k with defender := b }, "defender"⟩,
  ⟨(·.lifelink), fun k b => { k with lifelink := b }, "lifelink"⟩,
  ⟨(·.firstStrike), fun k b => { k with firstStrike := b }, "first strike"⟩,
  ⟨(·.islandwalk), fun k b => { k with islandwalk := b }, "islandwalk"⟩
]

/-- Union of two keyword sets (printed or granted). -/
def merge (a b : Keywords) : Keywords :=
  fields.foldl (fun acc f => f.set acc (f.get a || f.get b)) none

/-- `name` when `b` is true, otherwise nothing. -/
def flag (b : Bool) (name : String) : List String :=
  if b then [name] else []

def toList (k : Keywords) : List String :=
  fields.foldl (fun acc f => acc ++ flag (f.get k) f.name) []

instance : ToString Keywords where
  toString k :=
    let ks := k.toList
    if ks.isEmpty then "" else String.intercalate ", " ks

end Keywords

/- Singleton keyword values. Named separately from `Keywords` so they do not
clash with the structure fields of the same name. Combine with `Keywords.merge`. -/
namespace Keyword
def flash : Keywords := { Keywords.none with flash := true }
def haste : Keywords := { Keywords.none with haste := true }
def vigilance : Keywords := { Keywords.none with vigilance := true }
def flying : Keywords := { Keywords.none with flying := true }
def cantBeBlocked : Keywords := { Keywords.none with cantBeBlocked := true }
def menace : Keywords := { Keywords.none with menace := true }
def hexproof : Keywords := { Keywords.none with hexproof := true }
def indestructible : Keywords := { Keywords.none with indestructible := true }
def reach : Keywords := { Keywords.none with reach := true }
def trample : Keywords := { Keywords.none with trample := true }
def deathtouch : Keywords := { Keywords.none with deathtouch := true }
def defender : Keywords := { Keywords.none with defender := true }
def lifelink : Keywords := { Keywords.none with lifelink := true }
def firstStrike : Keywords := { Keywords.none with firstStrike := true }
def islandwalk : Keywords := { Keywords.none with islandwalk := true }
end Keyword

/-- Whom a spell, activated ability, or triggered ability may target
(CR 115.1 / 601.2c / 603.3d). Adding a targeting shape here is a compile error
in `EffectTargetKind.spec` and `Game.legalTargetsForAtomicKind` rather than
silently offering no targets. Multiple instances of the word “target” list
each slot in `spec` and are announced sequentially. Multiple targets of one
instance are chosen together. -/
inductive EffectTargetKind where
  /-- No target. -/
  | none
  /-- Target creature you control. -/
  | creatureYouControl
  /-- Another target creature you control (not the source). -/
  | anotherCreatureYouControl
  /-- Another target creature (any controller, not the source). -/
  | anotherCreature
  /-- A player or a creature (e.g. damage to any target). -/
  | playerOrCreature
  /-- Target Elf card in your graveyard. -/
  | elfInYourGraveyard
  /-- Target creature an opponent controls. -/
  | oppCreature
  /-- Target creature (any controller). -/
  | creature
  /-- Target creature with flying. -/
  | creatureWithFlying
  /-- Target artifact or land. -/
  | artifactOrLand
  /-- Target colorless nonland permanent. -/
  | colorlessNonland
  /-- First a creature you control, then a creature an opponent controls. -/
  | creatureYouControlThenOppCreature
  /-- Target player (any player). -/
  | player
  /-- Target opponent. -/
  | opponent
  /-- Target card in an opponent's graveyard. -/
  | oppGraveyardCard
  /-- Target artifact or enchantment. -/
  | artifactOrEnchantment
  /-- Target artifact or creature you control. -/
  | artifactOrCreatureYouControl
  /-- Target nonland permanent. -/
  | nonland
  /-- Target nonland permanent an opponent controls. -/
  | oppNonland
  /-- Target attacking creature without flying. -/
  | attackingCreatureWithoutFlying
  /-- Target creature you control with this subtype (e.g. Equip Human). -/
  | creatureYouControlSubtype (subtype : String)
  /-- A spell on the stack. -/
  | spell
  /-- A creature spell on the stack. -/
  | creatureSpell
  /-- A creature spell with power or toughness at most `n`. -/
  | creatureSpellPTAtMost (n : Nat)
  /-- Target creature defending player controls. -/
  | defendingPlayerCreature
  /-- Two target nonland permanents that share a card type. -/
  | twoNonlandsSharingType
deriving Repr, Inhabited, BEq, DecidableEq

/-- Default demonstration-agent choice among legal targets (CR 601.2c).
Adding a targeting shape is a compile error here rather than silently
picking the first legal target in `Game.preferredTarget`. -/
inductive TargetPreference where
  /-- A permanent the caster controls. -/
  | own
  /-- A permanent an opponent controls. -/
  | opponent
  /-- The opposing player, else the first legal target. -/
  | opponentPlayer
  /-- The last legal target (e.g. a graveyard card). -/
  | last
  /-- Own permanent if any, otherwise an opponent's. -/
  | ownThenOpponent
  /-- This player (e.g. a “target player draws” you want to hit yourself with). -/
  | selfPlayer
deriving Repr, Inhabited, BEq, DecidableEq

namespace EffectTargetKind

/-- Count, Oracle noun, demonstration-agent preference, and per-instance
slots for a targeting shape. Exhaustive so a new constructor is a compile
error here rather than silently using `targetCount` 1, an empty noun, or
`.opponent`. Multiple instances of the word “target” list each slot so Game
does not restate them; those slots are announced sequentially. -/
structure Spec where
  count : Nat := 1
  noun : String := ""
  prefer : TargetPreference := .opponent
  /-- Kind of each instance of the word “target”. Empty means this kind is
  itself the (one) instance. -/
  slots : Array EffectTargetKind := #[]
deriving Repr, Inhabited, BEq

/-- Classification of this targeting shape. `targetCount`, `noun`, and
`defaultPreference` read this table. -/
def spec : EffectTargetKind → Spec
  | .none =>
    { count := 0, prefer := .own }
  | .creatureYouControl =>
    { noun := "target creature you control", prefer := .own }
  | .anotherCreatureYouControl =>
    { noun := "another target creature you control", prefer := .own }
  | .anotherCreature =>
    { noun := "another target creature" }
  | .playerOrCreature =>
    { noun := "any target", prefer := .opponentPlayer }
  | .elfInYourGraveyard =>
    { noun := "target Elf card from your graveyard", prefer := .last }
  | .oppCreature =>
    { noun := "target creature an opponent controls" }
  | .creature =>
    { noun := "target creature" }
  | .creatureWithFlying =>
    { noun := "target creature with flying" }
  | .artifactOrLand =>
    { noun := "target artifact or land" }
  | .colorlessNonland =>
    { noun := "target colorless nonland permanent" }
  | .creatureYouControlThenOppCreature =>
    { count := 2
      noun := "target creature you control and a creature an opponent controls"
      prefer := .ownThenOpponent
      slots := #[.creatureYouControl, .oppCreature] }
  | .player =>
    { noun := "target player", prefer := .opponentPlayer }
  | .opponent =>
    { noun := "target opponent", prefer := .opponentPlayer }
  | .oppGraveyardCard =>
    { noun := "target card from an opponent's graveyard", prefer := .last }
  | .artifactOrEnchantment =>
    { noun := "target artifact or enchantment" }
  | .artifactOrCreatureYouControl =>
    { noun := "target artifact or creature you control", prefer := .own }
  | .nonland =>
    { noun := "target nonland permanent", prefer := .ownThenOpponent }
  | .oppNonland =>
    { noun := "target nonland permanent an opponent controls" }
  | .attackingCreatureWithoutFlying =>
    { noun := "target attacking creature without flying", prefer := .own }
  | .creatureYouControlSubtype subtype =>
    { noun := s!"target {subtype} you control", prefer := .own }
  | .spell =>
    { noun := "target spell" }
  | .creatureSpell =>
    { noun := "target creature spell" }
  | .creatureSpellPTAtMost n =>
    { noun := s!"target creature spell with power or toughness {n} or less" }
  | .defendingPlayerCreature =>
    { noun := "target creature defending player controls" }
  | .twoNonlandsSharingType =>
    { count := 2
      noun := "two target nonland permanents that share a card type"
      prefer := .ownThenOpponent
      slots := #[.nonland, .nonland] }

/-- How many targets must be announced for this shape (CR 601.2c). -/
def targetCount (k : EffectTargetKind) : Nat :=
  k.spec.count

/-- Oracle-style noun phrase for this targeting shape. -/
def noun (k : EffectTargetKind) : String :=
  k.spec.noun

/-- Default demonstration-agent preference for this targeting shape. -/
def defaultPreference (k : EffectTargetKind) : TargetPreference :=
  k.spec.prefer

/-- Kind of the `i`th instance of the word “target” (0-based). Atomic shapes
return themselves for every slot. -/
def slotKind (k : EffectTargetKind) (i : Nat) : EffectTargetKind :=
  k.spec.slots[i]?.getD k

end EffectTargetKind

/-- Targeting shape plus a default-choice hint used by the demonstration agent. -/
structure EffectTargeting where
  kind : EffectTargetKind := .none
  prefer : TargetPreference := .own
deriving Repr, Inhabited, BEq

namespace EffectTargeting

/-- Targeting shape; `prefer` defaults from `kind` unless overridden. -/
def of (kind : EffectTargetKind)
    (prefer : TargetPreference := kind.defaultPreference) : EffectTargeting :=
  { kind, prefer }

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (t : EffectTargeting) : Nat :=
  t.kind.targetCount

/-- True when announcing this shape requires choosing a target (CR 115.1). -/
def requiresTarget (t : EffectTargeting) : Bool :=
  t.targetCount != 0

end EffectTargeting

/-- Types that classify targeting through `EffectTargeting`. `targetKind`,
`targetCount`, and `requiresTarget` are derived here so spell, ability, and
trigger wrappers do not restate them. -/
class HasTargeting (α : Type) where
  targeting : α → EffectTargeting

namespace HasTargeting
variable {α : Type} [HasTargeting α]

def targetKind (e : α) : EffectTargetKind := targeting e |>.kind
def targetCount (e : α) : Nat := targeting e |>.targetCount
def requiresTarget (e : α) : Bool := targeting e |>.requiresTarget

end HasTargeting

/-- First character uppercased (ASCII), for ability sentences. -/
def capitalizeAscii (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- English for `n` cards (`a card` vs `2 cards`). -/
def cardPhrase (n : Nat) : String :=
  if n == 1 then "a card" else s!"{n} cards"

/-- English for putting `n` +1/+1 counters on a creature. -/
def plusOnePlusOneCountersPhrase (n : Nat) : String :=
  if n == 1 then "a +1/+1 counter" else s!"{n} +1/+1 counters"

/-- One-shot effect of a spell on resolution. Targeting is stored on the stack object. -/
inductive SpellEffect where
  /-- Deal `amount` damage to the chosen target (player or creature). -/
  | dealDamage (amount : Nat)
  /-- Target creature gets +P/+T until end of turn. -/
  | pump (power toughness : Int)
  /-- Destroy target creature with flying (CR 701.8). -/
  | destroyCreatureWithFlying
  /-- Destroy target creature (CR 701.8). -/
  | destroyCreature
  /-- Put a +1/+1 counter on target creature you control. It gains trample and
  hexproof until end of turn. -/
  | plusOnePlusOneTrampleHexproof
  /-- Deal `amount` damage to target creature (e.g. Spew Flame). -/
  | dealDamageToCreature (amount : Nat)
  /-- Deal `amount` damage to target creature. That creature loses
  indestructible until end of turn. If it would die this turn, exile it instead
  (e.g. Smite the Deathless). -/
  | dealDamageLoseIndestructibleExile (amount : Nat)
  /-- Target creature you control deals damage equal to its power to target
  creature an opponent controls (e.g. Quarrel). -/
  | creatureYouControlDealsPowerToOppCreature
  /-- You may play an additional land this turn (e.g. Till and Tend). -/
  | playAdditionalLandThisTurn
  /-- Destroy target artifact or land. Creatures without flying can't block
  this turn (e.g. Fire of Orthanc). -/
  | destroyArtifactOrLandNonflyersCantBlock
  /-- Destroy target creature. Its controller loses `life` life
  (e.g. Bitter Downfall). -/
  | destroyTargetCreatureControllerLosesLife (life : Nat)
  /-- All creatures get +P/+T until end of turn (e.g. Languish). -/
  | allCreaturesGet (power toughness : Int)
  /-- You draw `cards` cards and lose `life` life (e.g. Night's Whisper).
  Loss of life is not damage (CR 118.3a / 120.3). -/
  | drawAndLoseLife (cards life : Nat)
  /-- Target player draws `cards` cards and loses `life` life
  (e.g. Reverent Howl). -/
  | targetPlayerDrawLoseLife (cards life : Nat)
  /-- Creatures target player controls get +P/+T until end of turn
  (e.g. Gnashing of Teeth). -/
  | creaturesTargetPlayerGet (power toughness : Int)
  /-- Target creature gets +P/+T and gains lifelink until end of turn. -/
  | pumpAndLifelink (power toughness : Int)
  /-- Target creature gets +P/+T until end of turn. If it would die this turn,
  exile it instead (e.g. Gnashing of Teeth). -/
  | pumpAndExileIfDies (power toughness : Int)
  /-- Exile all creature cards from target player's graveyard. You may cast
  those cards for as long as they remain exiled, and mana of any type can be
  spent to cast them (e.g. Shadow of the Enemy). -/
  | exileGraveyardCreaturesGrantCast
  /-- Draw `n` cards (e.g. Lórien Revealed). -/
  | draw (n : Nat)
  /-- Draw `n` cards, then discard a card (e.g. Confusticate and Bebother). -/
  | drawThenDiscard (n : Nat)
  /-- Scry `n` (e.g. Take a Glance). -/
  | scry (n : Nat)
  /-- Tap target creature. Scry `scryN`, then draw `drawN` (e.g. Hithlain Knots). -/
  | tapScryDraw (scryN drawN : Nat)
  /-- Tap one or two target creatures (e.g. Gaze in Wonder). -/
  | tapOneOrTwoCreatures
  /-- Target artifact or creature you control gains hexproof and indestructible
  until end of turn (e.g. Concerted Care). -/
  | grantHexproofIndestructible
  /-- Put a +1/+1 counter on up to one target creature. Target player gains
  `life` life (e.g. Meager Meal). -/
  | plusOneUpToOneAndPlayerGainsLife (life : Nat)
  /-- Counter target spell. -/
  | counterSpell
  /-- Counter target spell unless its controller pays `{n}`. -/
  | counterUnlessPays (n : Nat)
  /-- Counter target creature spell with power or toughness `n` or less. -/
  | counterCreatureSpellPTAtMost (n : Nat)
  /-- Counter target spell. If a permanent spell is countered this way, exile
  it instead. You may cast that card without paying its mana cost for as long
  as it remains exiled (e.g. Thranduil's Decree). -/
  | counterExilePermanentMayCast
  /-- Target creature's owner puts it on the top or bottom of their library. -/
  | putOnTopOrBottom
  /-- Untap target creature you control. It gets +P/+T. If it's a Dwarf, you
  may attach an Equipment you control to it (e.g. Vow to Erebor). -/
  | untapPumpMaybeAttach (power toughness : Int)
  /-- Exchange control of two target nonland permanents that share a card type. -/
  | exchangeControlSharingType
deriving Repr, Inhabited, BEq

/-- How the demonstration agent classifies a spell when choosing what to cast.
Adding a constructor is a compile error in `SpellEffect.spec` rather than
silently skipping the new effect. -/
inductive SpellCastKind where
  /-- Damage to any target (player or creature). -/
  | burn
  /-- Damage to a creature only (including Smite-style follow-ups). -/
  | creatureDamage
  /-- A creature you control deals its power to an opposing creature. -/
  | fight
  /-- Destroy target creature with flying. -/
  | destroyFlying
  /-- Destroy target creature. -/
  | destroyCreature
  /-- Destroy target artifact or land. -/
  | destroyArtifactOrLand
  /-- Until-end-of-turn pump or +1/+1 with keyword grants. -/
  | pump
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- Mass until-end-of-turn P/T change. -/
  | massPump
  /-- Draw cards, optionally losing life (e.g. Night's Whisper). -/
  | draw
  /-- Counter a spell. -/
  | counter
deriving Repr, Inhabited, BEq, DecidableEq

/-- Signed power/toughness bonus for Oracle-style reminders (`+1` vs `-1`). -/
def signedStat (n : Int) : String :=
  if n < 0 then toString n else s!"+{n}"

/-- What a spell, activated ability, or trigger does to a permanent
(CR 608.2b). Shared so `Game.applyPermanentAction` is one match, whether the
permanent is an announced target or the ability's source. -/
inductive PermanentAction where
  /-- Until-end-of-turn +P/+T. -/
  | pump (power toughness : Int)
  /-- Until-end-of-turn +P/+T and trample. -/
  | pumpAndTrample (power toughness : Int)
  /-- Destroy the permanent (CR 701.7). -/
  | destroy
  /-- Put `n` +1/+1 counters on the permanent (CR 122.1). -/
  | plusOne (n : Nat)
  /-- A +1/+1 counter plus trample and hexproof until end of turn. -/
  | plusOnePlusOneTrampleHexproof
  /-- Deal `amount` damage. -/
  | dealDamage (amount : Nat)
  /-- Damage plus lose-indestructible and exile-if-dies this turn. -/
  | dealDamageLoseIndestructibleExile (amount : Nat)
  /-- Destroy, then creatures without flying can't block this turn. -/
  | destroyThenNonflyersCantBlock
  /-- The permanent can't be blocked this turn. -/
  | cantBeBlocked
  /-- Until-end-of-turn +P/+T and lifelink. -/
  | pumpAndLifelink (power toughness : Int)
  /-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
  | pumpAndExileIfDies (power toughness : Int)
  /-- Grant these keywords until end of turn. -/
  | grantKeywords (k : Keywords)
  /-- Tap the permanent. -/
  | tap
  /-- Untap the permanent. -/
  | untap
deriving Repr, Inhabited, BEq

namespace PermanentAction

/-- Oracle-style text for this action on `noun` (e.g. `target creature`).
`sentence` capitalizes the first letter for activated-ability lines. -/
def toNotation (action : PermanentAction) (noun : String) (sentence := false) : String :=
  let damage (n : Nat) : String := s!"deals {n} damage to {noun}"
  let raw :=
    match action with
    | .pump p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn"
    | .pumpAndTrample p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    | .destroy => s!"destroy {noun}"
    | .plusOne n => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
    | .plusOnePlusOneTrampleHexproof =>
      s!"put a +1/+1 counter on {noun}. It gains trample and hexproof until end of turn"
    | .dealDamage n => damage n
    | .dealDamageLoseIndestructibleExile n =>
      s!"{damage n}. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
    | .destroyThenNonflyersCantBlock =>
      s!"destroy {noun}. Creatures without flying can't block this turn"
    | .cantBeBlocked => s!"{noun} can't be blocked this turn"
    | .pumpAndLifelink p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} and gains lifelink until end of turn"
    | .pumpAndExileIfDies p t =>
      s!"{noun} gets {signedStat p}/{signedStat t} until end of turn. If that creature would die this turn, exile it instead"
    | .grantKeywords k =>
      let joined :=
        match k.toList with
        | [a, b] => s!"{a} and {b}"
        | ks => String.intercalate ", " ks
      s!"{noun} gains {joined} until end of turn"
    | .tap => s!"tap {noun}"
    | .untap => s!"untap {noun}"
  if sentence then capitalizeAscii raw else raw

end PermanentAction

/-- How a spell resolves (CR 608). Grouped so `Game.applyEffect` matches a
handful of shapes instead of every `SpellEffect` constructor. Burn and
creature-only damage both use `onPermanent (.dealDamage n)`; Game applies
that action to a player or a creature when the targeting shape allows it. -/
inductive SpellResolution where
  /-- You may play an additional land this turn. -/
  | extraLand
  /-- A creature you control deals its power to an opposing creature. -/
  | fight
  /-- Affect a still-legal target. Damage can hit a player or a creature;
  other actions require a permanent. -/
  | onPermanent (action : PermanentAction)
  /-- All creatures get +P/+T until end of turn. -/
  | allCreaturesPump (power toughness : Int)
  /-- You draw `cards` cards and lose `life` life. Loss of life is not
  damage (CR 118.3a / 120.3). -/
  | drawAndLoseLife (cards life : Nat)
  /-- The targeted player draws `cards` and loses `life` life. -/
  | playerDrawLoseLife (cards life : Nat)
  /-- Creatures the targeted player controls get +P/+T until end of turn. -/
  | creaturesOfPlayerPump (power toughness : Int)
  /-- Destroy the targeted creature; its controller loses `life` life. -/
  | destroyAndControllerLosesLife (life : Nat)
  /-- Exile creature cards from the targeted player's graveyard and grant
  permission to cast them, spending mana as though it were any type. -/
  | exileGraveyardCreaturesGrantCast
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Draw `n` cards, then discard a card. -/
  | drawThenDiscard (n : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Tap the target, then scry and draw. -/
  | tapScryDraw (scryN drawN : Nat)
  /-- Tap each targeted creature (one or two). -/
  | tapTargets
  /-- Counter the targeted spell. -/
  | counter
  /-- Counter unless the controller pays `{n}`. -/
  | counterUnlessPays (n : Nat)
  /-- Counter; exile a permanent spell and grant a free cast. -/
  | counterExilePermanentMayCast
  /-- Owner puts the targeted creature on top or bottom of their library. -/
  | putOnTopOrBottom
  /-- Untap, pump, and maybe attach Equipment if the target is a Dwarf. -/
  | untapPumpMaybeAttach (power toughness : Int)
  /-- Exchange control of the two targeted permanents. -/
  | exchangeControl
  /-- Put a +1/+1 counter on an optional creature target; a player gains life. -/
  | plusOneAndPlayerGainsLife (life : Nat)
deriving Repr, Inhabited, BEq

/-- Targeting, demonstration-agent classification, and resolution of a spell
effect. Exhaustive so a new constructor is a compile error in `SpellEffect.spec`
rather than silently skipped in `Game` or the agent. -/
structure SpellMeta where
  targeting : EffectTargeting := .of .none
  castKind : SpellCastKind := .extraLand
  preferAsDefaultMode : Bool := false
  resolution : SpellResolution := .extraLand
  /-- Upper bound on announced targets. `0` means `targeting`’s `targetCount`
  (required count equals the maximum). Gaze in Wonder uses `2` with a
  required count of `1` (“one or two”). -/
  maxTargets : Nat := 0
deriving Repr, Inhabited, BEq

namespace SpellEffect

def signedStat := Mtg.Engine.signedStat

/-- Classification of this spell. Exhaustive so a new constructor is a compile
error here rather than silently matching no targets, skipping the agent, or
doing nothing on resolution. -/
def spec : SpellEffect → SpellMeta
  | .dealDamage n =>
    { targeting := .of .playerOrCreature, castKind := .burn,
      resolution := .onPermanent (.dealDamage n) }
  | .pump p t =>
    { targeting := .of .creature .own, castKind := .pump,
      resolution := .onPermanent (.pump p t) }
  | .destroyCreatureWithFlying =>
    { targeting := .of .creatureWithFlying, castKind := .destroyFlying,
      preferAsDefaultMode := true, resolution := .onPermanent .destroy }
  | .destroyCreature =>
    { targeting := .of .creature, castKind := .destroyCreature,
      resolution := .onPermanent .destroy }
  | .plusOnePlusOneTrampleHexproof =>
    { targeting := .of .creatureYouControl, castKind := .pump,
      resolution := .onPermanent .plusOnePlusOneTrampleHexproof }
  | .dealDamageToCreature n =>
    { targeting := .of .creature, castKind := .creatureDamage,
      resolution := .onPermanent (.dealDamage n) }
  | .dealDamageLoseIndestructibleExile n =>
    { targeting := .of .creature, castKind := .creatureDamage,
      resolution := .onPermanent (.dealDamageLoseIndestructibleExile n) }
  | .creatureYouControlDealsPowerToOppCreature =>
    { targeting := .of .creatureYouControlThenOppCreature, castKind := .fight,
      resolution := .fight }
  | .playAdditionalLandThisTurn =>
    { targeting := .of .none, castKind := .extraLand, resolution := .extraLand }
  | .destroyArtifactOrLandNonflyersCantBlock =>
    { targeting := .of .artifactOrLand, castKind := .destroyArtifactOrLand,
      resolution := .onPermanent .destroyThenNonflyersCantBlock }
  | .destroyTargetCreatureControllerLosesLife n =>
    { targeting := .of .creature, castKind := .destroyCreature,
      preferAsDefaultMode := true, resolution := .destroyAndControllerLosesLife n }
  | .allCreaturesGet p t =>
    { targeting := .of .none, castKind := .massPump,
      resolution := .allCreaturesPump p t }
  | .drawAndLoseLife cards life =>
    { targeting := .of .none, castKind := .draw,
      resolution := .drawAndLoseLife cards life }
  | .targetPlayerDrawLoseLife cards life =>
    { targeting := .of .player .selfPlayer, castKind := .draw,
      resolution := .playerDrawLoseLife cards life }
  | .creaturesTargetPlayerGet p t =>
    { targeting := .of .player, castKind := .massPump,
      resolution := .creaturesOfPlayerPump p t }
  | .pumpAndLifelink p t =>
    { targeting := .of .creature .own, castKind := .pump,
      resolution := .onPermanent (.pumpAndLifelink p t) }
  | .pumpAndExileIfDies p t =>
    { targeting := .of .creature, castKind := .pump,
      preferAsDefaultMode := true, resolution := .onPermanent (.pumpAndExileIfDies p t) }
  | .exileGraveyardCreaturesGrantCast =>
    { targeting := .of .player, castKind := .draw,
      resolution := .exileGraveyardCreaturesGrantCast }
  | .draw n =>
    { targeting := .of .none, castKind := .draw, resolution := .draw n }
  | .drawThenDiscard n =>
    { targeting := .of .none, castKind := .draw, resolution := .drawThenDiscard n }
  | .scry n =>
    { targeting := .of .none, castKind := .draw, resolution := .scry n }
  | .tapScryDraw scryN drawN =>
    { targeting := .of .creature, castKind := .draw,
      resolution := .tapScryDraw scryN drawN }
  | .tapOneOrTwoCreatures =>
    { targeting := .of .creature, castKind := .pump, resolution := .tapTargets,
      maxTargets := 2 }
  | .grantHexproofIndestructible =>
    { targeting := .of .artifactOrCreatureYouControl, castKind := .pump,
      resolution := .onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible)) }
  | .plusOneUpToOneAndPlayerGainsLife n =>
    { targeting := .of .player .selfPlayer, castKind := .pump,
      resolution := .plusOneAndPlayerGainsLife n }
  | .counterSpell =>
    { targeting := .of .spell, castKind := .counter, resolution := .counter }
  | .counterUnlessPays n =>
    { targeting := .of .spell, castKind := .counter, resolution := .counterUnlessPays n }
  | .counterCreatureSpellPTAtMost n =>
    { targeting := .of (.creatureSpellPTAtMost n), castKind := .counter,
      resolution := .counter }
  | .counterExilePermanentMayCast =>
    { targeting := .of .spell, castKind := .counter,
      resolution := .counterExilePermanentMayCast }
  | .putOnTopOrBottom =>
    { targeting := .of .creature, castKind := .counter,
      resolution := .putOnTopOrBottom }
  | .untapPumpMaybeAttach p t =>
    { targeting := .of .creatureYouControl, castKind := .pump,
      resolution := .untapPumpMaybeAttach p t }
  | .exchangeControlSharingType =>
    { targeting := .of .twoNonlandsSharingType, castKind := .counter,
      resolution := .exchangeControl }

instance : HasTargeting SpellEffect where
  targeting e := e.spec.targeting

/-- Classification of this spell effect's targeting (CR 115.1 / 601.2c). -/
def targeting (e : SpellEffect) : EffectTargeting :=
  HasTargeting.targeting e

/-- Whom this effect may target when announced (CR 115.1 / 601.2c). -/
def targetKind (e : SpellEffect) : EffectTargetKind :=
  HasTargeting.targetKind e

/-- How many targets must be announced for this effect (CR 601.2c). -/
def targetCount (e : SpellEffect) : Nat :=
  HasTargeting.targetCount e

/-- Maximum targets that may be announced (CR 601.2c). Equals `targetCount`
unless `spec.maxTargets` is set (e.g. “one or two”). -/
def maxTargetCount (e : SpellEffect) : Nat :=
  if e.spec.maxTargets == 0 then e.targetCount else e.spec.maxTargets

/-- True when announcing this effect requires choosing a target (CR 115.1 / 601.2c). -/
def requiresTarget (e : SpellEffect) : Bool :=
  HasTargeting.requiresTarget e

/-- Demonstration-agent category for this effect. -/
def castKind (e : SpellEffect) : SpellCastKind :=
  e.spec.castKind

/-- True when the demonstration agent prefers this mode of a modal spell. -/
def preferAsDefaultMode (e : SpellEffect) : Bool :=
  e.spec.preferAsDefaultMode

/-- How this effect resolves (CR 608). -/
def resolution (e : SpellEffect) : SpellResolution :=
  e.spec.resolution

/-- Oracle-style reminder from targeting and resolution, so a new constructor
only updates `spec`. -/
def toNotation (e : SpellEffect) : String :=
  let noun := e.targetKind.noun
  match e.resolution with
  | .fight =>
    "target creature you control deals damage equal to its power to target creature an opponent controls"
  | .extraLand => "you may play an additional land this turn"
  | .drawAndLoseLife cards life =>
    s!"you draw {cardPhrase cards} and lose {life} life"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .allCreaturesPump p t =>
    s!"all creatures get {signedStat p}/{signedStat t} until end of turn"
  | .playerDrawLoseLife cards life =>
    s!"{noun} draws {cardPhrase cards} and loses {life} life"
  | .creaturesOfPlayerPump p t =>
    s!"creatures {noun} controls get {signedStat p}/{signedStat t} until end of turn"
  | .destroyAndControllerLosesLife n =>
    s!"destroy {noun}. Its controller loses {n} life"
  | .exileGraveyardCreaturesGrantCast =>
    "exile all creature cards from target player's graveyard. You may cast spells from among those cards for as long as they remain exiled, and mana of any type can be spent to cast them"
  | .draw n => s!"draw {cardPhrase n}"
  | .drawThenDiscard n => s!"draw {cardPhrase n}, then discard a card"
  | .scry n => s!"scry {n}"
  | .tapScryDraw scryN drawN =>
    s!"tap {noun}. Scry {scryN}. Draw {cardPhrase drawN}"
  | .tapTargets => "tap one or two target creatures"
  | .counter => s!"counter {noun}"
  | .counterUnlessPays n =>
    s!"counter {noun} unless its controller pays \{{n}}"
  | .counterExilePermanentMayCast =>
    s!"counter {noun}. If a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard. You may cast that card without paying its mana cost for as long as it remains exiled"
  | .putOnTopOrBottom =>
    s!"{noun}'s owner puts it on their choice of the top or bottom of their library"
  | .untapPumpMaybeAttach p t =>
    s!"untap {noun}. It gets {signedStat p}/{signedStat t} until end of turn. If it's a Dwarf, you may attach an Equipment you control to it"
  | .exchangeControl =>
    "exchange control of two target nonland permanents that share a card type"
  | .plusOneAndPlayerGainsLife n =>
    s!"put a +1/+1 counter on up to one target creature. {capitalizeAscii noun} gains {n} life"

instance : ToString SpellEffect where
  toString := toNotation

end SpellEffect

/-- One-shot effect of an activated ability on resolution (CR 602, 608). -/
inductive AbilityEffect where
  /-- Search your library for a basic land card, put it onto the battlefield
  tapped, then shuffle (e.g. Wayfarer's Bauble). -/
  | searchBasicLandTapped
  /-- Search your library for a card with the given land type, reveal it, put
  it into your hand, then shuffle (e.g. Mountaincycling, Swampcycling). -/
  | searchLandTypeToHand (landType : String)
  /-- Exile the top card of your library. You may play it until the end of
  your next turn (e.g. Snowslope Hunter). -/
  | exileTopPlayUntilEndOfNextTurn
  /-- This creature deals `amount` damage to target creature
  (e.g. Goblin Cratermaker). -/
  | dealDamageToTargetCreature (amount : Nat)
  /-- Destroy target colorless nonland permanent (e.g. Goblin Cratermaker). -/
  | destroyTargetColorlessNonland
  /-- Attach this Equipment to target creature you control (CR 702.6a). -/
  | attachToTargetCreatureYouControl
  /-- This enchantment becomes a Bear creature in addition to its other types
  and gains “This creature's power and toughness are each equal to the number
  of lands you control.” The effect does not end (e.g. Beorn's Hospitality). -/
  | becomeBearCreatureWithLandsPT
  /-- This creature gets +P/+T until end of turn (e.g. Goblin Fireleaper). -/
  | sourceGets (power toughness : Int)
  /-- Put `n` +1/+1 counters on this creature (e.g. Guardian of the Halls). -/
  | putPlusOnePlusOneOnSource (n : Nat)
  /-- Target creature can't be blocked this turn (e.g. Rogue's Passage). -/
  | targetCantBeBlockedThisTurn
  /-- Return this card from your graveyard to the battlefield tapped
  (e.g. Haunt of the Dead Marshes). -/
  | returnFromGraveyardTapped
  /-- Return this card from your graveyard to your hand
  (e.g. Gollum the Abandoned). -/
  | returnFromGraveyardToHand
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- Destroy target artifact or enchantment. -/
  | destroyTargetArtifactOrEnchantment
  /-- Target player mills `n` cards. -/
  | millPlayer (n : Nat)
  /-- Draw a card, then discard a card. -/
  | drawThenDiscard
deriving Repr, Inhabited, BEq

/-- How the demonstration agent classifies an activated-ability mode.
Adding a constructor is a compile error in `AbilityEffect.spec` rather than
silently skipping the new effect in `Game.defaultAbilityMode`. -/
inductive AbilityCastKind where
  /-- Damage to a creature. -/
  | creatureDamage
  /-- Destroy a colorless nonland permanent. -/
  | destroyColorless
  /-- Any other mode. -/
  | other
deriving Repr, Inhabited, BEq, DecidableEq

/-- How an activated ability resolves (CR 608). Grouped so
`Game.applyAbilityEffect` matches a handful of shapes instead of every
constructor. Permanent-target and source pumps, damage, destroy, and +1/+1
counters share `PermanentAction` with spells and triggers. -/
inductive AbilityResolution where
  /-- Search for a basic land, put it onto the battlefield tapped, then shuffle. -/
  | searchBasicLand
  /-- Search for a card with this land type, put it into your hand, then shuffle. -/
  | searchLandTypeToHand (landType : String)
  /-- Exile the top card and grant permission to play it. -/
  | exileTop
  /-- Attach this Equipment to the announced creature. -/
  | attach
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Affect the ability's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- Become a Bear creature with lands-you-control P/T. -/
  | becomeBear
  /-- Return the source from the graveyard to the battlefield tapped. -/
  | returnFromGraveyardTapped
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnFromGraveyardToHand
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
  /-- Target player mills `n` cards. -/
  | mill (n : Nat)
  /-- Draw a card, then discard a card. -/
  | drawThenDiscard
deriving Repr, Inhabited, BEq

/-- Targeting, demonstration-agent classification, and resolution of an
activated ability. Exhaustive so a new constructor is a compile error in
`AbilityEffect.spec`. -/
structure AbilityMeta where
  targeting : EffectTargeting := .of .none
  castKind : AbilityCastKind := .other
  resolution : AbilityResolution := .searchBasicLand
deriving Repr, Inhabited, BEq

namespace AbilityEffect

/-- Classification of this ability. Exhaustive so a new constructor is a
compile error here rather than silently matching no targets or doing nothing
on resolution. -/
def spec : AbilityEffect → AbilityMeta
  | .dealDamageToTargetCreature n =>
    { targeting := .of .creature, castKind := .creatureDamage,
      resolution := .onPermanent (.dealDamage n) }
  | .destroyTargetColorlessNonland =>
    { targeting := .of .colorlessNonland, castKind := .destroyColorless,
      resolution := .onPermanent .destroy }
  | .attachToTargetCreatureYouControl =>
    { targeting := .of .creatureYouControl, resolution := .attach }
  | .targetCantBeBlockedThisTurn =>
    { targeting := .of .creature .own, resolution := .onPermanent .cantBeBlocked }
  | .searchBasicLandTapped =>
    { resolution := .searchBasicLand }
  | .searchLandTypeToHand t =>
    { resolution := .searchLandTypeToHand t }
  | .exileTopPlayUntilEndOfNextTurn =>
    { resolution := .exileTop }
  | .becomeBearCreatureWithLandsPT =>
    { resolution := .becomeBear }
  | .sourceGets p t =>
    { resolution := .onSource (.pump p t) }
  | .putPlusOnePlusOneOnSource n =>
    { resolution := .onSource (.plusOne n) }
  | .returnFromGraveyardTapped =>
    { resolution := .returnFromGraveyardTapped }
  | .returnFromGraveyardToHand =>
    { resolution := .returnFromGraveyardToHand }
  | .creaturesYouControlGet p t =>
    { resolution := .creaturesYouControlPump p t }
  | .destroyTargetArtifactOrEnchantment =>
    { targeting := .of .artifactOrEnchantment, castKind := .destroyColorless,
      resolution := .onPermanent .destroy }
  | .millPlayer n =>
    { targeting := .of .player, resolution := .mill n }
  | .drawThenDiscard =>
    { resolution := .drawThenDiscard }

instance : HasTargeting AbilityEffect where
  targeting e := e.spec.targeting

/-- Classification of this ability effect's targeting (CR 115.1 / 601.2c). -/
def targeting (e : AbilityEffect) : EffectTargeting :=
  HasTargeting.targeting e

/-- Whom this effect may target when announced (CR 115.1 / 601.2c). -/
def targetKind (e : AbilityEffect) : EffectTargetKind :=
  HasTargeting.targetKind e

/-- How many targets must be announced for this effect (CR 601.2c). -/
def targetCount (e : AbilityEffect) : Nat :=
  HasTargeting.targetCount e

/-- True when announcing this effect requires choosing a target (CR 115.1 / 601.2c). -/
def requiresTarget (e : AbilityEffect) : Bool :=
  HasTargeting.requiresTarget e

/-- Demonstration-agent category for this ability mode. -/
def castKind (e : AbilityEffect) : AbilityCastKind :=
  e.spec.castKind

/-- How this effect resolves (CR 608). -/
def resolution (e : AbilityEffect) : AbilityResolution :=
  e.spec.resolution

/-- Oracle-style reminder from targeting and resolution, so a new constructor
only updates `spec`. Source-deals-damage uses the creature as the subject
(`This creature deals N…`) rather than the generic `PermanentAction` wording. -/
def toNotation (e : AbilityEffect) : String :=
  let noun := e.targetKind.noun
  match e.resolution with
  | .searchBasicLand =>
    "Search your library for a basic land card, put it onto the battlefield tapped, then shuffle"
  | .searchLandTypeToHand t =>
    s!"Search your library for a {t} card, reveal it, put it into your hand, then shuffle"
  | .exileTop =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .attach =>
    s!"Attach this Equipment to {noun}"
  | .onPermanent (.dealDamage n) =>
    s!"This creature deals {n} damage to {noun}"
  | .onPermanent action =>
    PermanentAction.toNotation action noun (sentence := true)
  | .onSource action =>
    PermanentAction.toNotation action "this creature" (sentence := true)
  | .becomeBear =>
    "This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .returnFromGraveyardTapped =>
    "Return this card from your graveyard to the battlefield tapped"
  | .returnFromGraveyardToHand =>
    "Return this card from your graveyard to your hand"
  | .creaturesYouControlPump p t =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .mill n =>
    s!"{noun} mills {n} cards"
  | .drawThenDiscard =>
    "Draw a card, then discard a card"

instance : ToString AbilityEffect where
  toString := toNotation

end AbilityEffect

/-- Costs of an activated ability besides announcements (CR 602.1). -/
structure ActivationCost where
  mana : ManaCost := ManaCost.empty
  tap : Bool := false
  sacrificeSource : Bool := false
  /-- Sacrifice another creature or artifact you control (CR 701.17). -/
  sacrificeAnotherCreatureOrArtifact : Bool := false
  /-- Pay this much life (CR 118.3b / 119.4). Payment of life is not damage. -/
  payLife : Nat := 0
  /-- Discard this card from your hand (CR 701.9 / 702.29, e.g. cycling). -/
  discardSource : Bool := false
deriving Repr, Inhabited, BEq

namespace ActivationCost

def toNotation (c : ActivationCost) : String :=
  let parts : List String :=
    (if c.mana.symbols.isEmpty then [] else [toString c.mana]) ++
    (if c.tap then ["{T}"] else []) ++
    (if c.payLife != 0 then [s!"Pay {c.payLife} life"] else []) ++
    (if c.discardSource then ["Discard this card"] else []) ++
    (if c.sacrificeSource then ["Sacrifice"] else []) ++
    (if c.sacrificeAnotherCreatureOrArtifact then
      ["Sacrifice another creature or artifact"]
     else [])
  String.intercalate ", " parts

instance : ToString ActivationCost where
  toString := toNotation

end ActivationCost

/-- An activated ability printed on a card (CR 602.1). Mana abilities that
are `{T}: Add` are stored separately on `CardDef.tapAddMana` /
`CardDef.tapAddManaForEach` / basic land types. -/
structure ActivatedAbility where
  cost : ActivationCost
  /-- First (or only) mode of this ability. -/
  effect : AbilityEffect
  /-- Additional modes of a modal ability (CR 700.2). Empty means the ability
  is not modal; the player otherwise chooses one mode at CR 601.2b. -/
  otherModes : Array AbilityEffect := #[]
  /-- Timing restriction “Activate only as a sorcery” (CR 117.1a). -/
  onlyAsSorcery : Bool := false
  /-- Timing restriction “Activate only during your turn”. -/
  onlyDuringYourTurn : Bool := false
  /-- Frequency restriction “Activate only once each turn”. -/
  onceEachTurn : Bool := false
  /-- This ability can be activated only while the source is in a graveyard
  (CR 112.6 / 404). -/
  activateFromGraveyard : Bool := false
  /-- This ability can be activated only while the source is in your hand
  (CR 112.6 / 702.29, e.g. cycling). -/
  activateFromHand : Bool := false
  /-- Timing restriction “Activate only if you control a legendary creature”. -/
  onlyIfYouControlLegendary : Bool := false
  /-- This ability costs this much generic mana less if you control a legendary
  creature (e.g. Esquire of the King). -/
  costReductionIfYouControlLegendary : Nat := 0
  /-- Equip restricted to a creature subtype (e.g. Equip Human). -/
  equipSubtype : Option String := none
deriving Repr, Inhabited, BEq

namespace ActivatedAbility

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array AbilityEffect :=
  #[ab.effect] ++ ab.otherModes

/-- True when the player must choose among two or more modes (CR 700.2). -/
def isModal (ab : ActivatedAbility) : Bool :=
  !ab.otherModes.isEmpty

def toNotation (ab : ActivatedAbility) : String :=
  let timing :=
    (if ab.onlyAsSorcery then " (activate only as a sorcery)" else "") ++
    (if ab.onlyDuringYourTurn then " (activate only during your turn)" else "") ++
    (if ab.onceEachTurn then " (activate only once each turn)" else "") ++
    (if ab.activateFromGraveyard then " (activate only from the graveyard)" else "") ++
    (if ab.activateFromHand then " (activate only from your hand)" else "") ++
    (if ab.onlyIfYouControlLegendary then
      " (activate only if you control a legendary creature)" else "")
  let body :=
    if ab.isModal then
      let modes := ab.allModes.toList.map AbilityEffect.toNotation
      s!"Choose one — {String.intercalate "; " modes}"
    else
      ab.effect.toNotation
  s!"{ab.cost.toNotation}: {body}{timing}"

instance : ToString ActivatedAbility where
  toString := toNotation

end ActivatedAbility

/-- A static ability the engine currently understands (CR 604). -/
inductive StaticAbility where
  /-- Other creatures you control that have any of these subtypes have trample
  (e.g. Orcish Siegemaster). -/
  | otherCreaturesHaveTrample (subtypes : Array String)
  /-- Other creatures you control that have any of these subtypes get +P/+T
  (e.g. Elvish Archdruid). -/
  | otherCreaturesGet (subtypes : Array String) (power toughness : Int)
  /-- Enchanted creature gets +P/+T (e.g. Gift of Strands). -/
  | enchantedCreatureGets (power toughness : Int)
  /-- Equipped creature gets +P/+T (e.g. Ragged Short Spear). -/
  | equippedCreatureGets (power toughness : Int)
  /-- This creature's power and toughness are each equal to the number of lands
  you control. A characteristic-defining ability that functions in all zones
  (CR 208.2a / 604.3), e.g. Mirkwood Pathmaker and animated Beorn's Hospitality. -/
  | powerToughnessEqualLandsYouControl
  /-- This creature can't block unless its controller controls a permanent with
  any of these subtypes (e.g. Olog-hai Crusher). An empty list means it can't
  block at all. The restriction is checked when declaring blockers (CR 509.1b). -/
  | cantBlockUnlessYouControl (subtypes : Array String)
  /-- This creature can't be blocked except by `n` or more creatures
  (e.g. Troll of Khazad-dûm with 3). Menace is the keyword for `n = 2`. -/
  | cantBeBlockedExceptBy (n : Nat)
  /-- Enchanted creature is only this subtype and can't attack or block
  (e.g. Fog on the Barrow-Downs). -/
  | enchantedIsOnlySubtypeCantAttackOrBlock (subtype : String)
  /-- This creature's power is equal to the number of cards in your hand
  (e.g. Minas Tirith Garrison). -/
  | powerEqualCardsInHand
deriving Repr, Inhabited, BEq

namespace StaticAbility

/-- English plural used in Oracle-style reminders (`Orc` → `Orcs`). -/
def pluralSubtype (s : String) : String :=
  if s.endsWith "s" then s else s ++ "s"

/-- Oracle-style “Enchanted/Equipped creature gets +P/+T.” -/
def hostGetsPhrase (host : String) (p t : Int) : String :=
  s!"{host} gets {signedStat p}/{signedStat t}."

/-- Join subtype names for Oracle-style lord reminders (`Orc` and `Goblin`). -/
def joinedSubtypes (subtypes : Array String) (each : String → String := fun s => s) : String :=
  String.intercalate " and " (subtypes.toList.map each)

/-- How a static ability applies (CR 604 / 613). Grouped so Game accessors and
`toNotation` match a handful of shapes instead of every constructor. Enchanted
and equipped host pumps share `hostGets`. -/
inductive StaticShape where
  /-- Other matching creatures you control have trample. -/
  | lordTrample (subtypes : Array String)
  /-- Other matching creatures you control get +P/+T. -/
  | lordPump (subtypes : Array String) (power toughness : Int)
  /-- The enchanted or equipped host gets +P/+T. -/
  | hostGets (host : String) (power toughness : Int)
  /-- Characteristic-defining P/T equal to lands you control. -/
  | landsYouControlPT
  /-- This creature can't block unless you control a listed subtype. -/
  | cantBlockUnless (subtypes : Array String)
  /-- This creature can't be blocked except by `n` or more creatures. -/
  | cantBeBlockedExcept (n : Nat)
  /-- Enchanted creature is only this subtype and can't attack or block. -/
  | enchantedOnlySubtypeCantAttackOrBlock (subtype : String)
  /-- Characteristic-defining power equal to cards in your hand. -/
  | cardsInHandPower
deriving Repr, Inhabited, BEq

/-- Projections Game reads from a static shape. Exhaustive so a new shape is a
compile error here rather than silently matching `none` / `(0, 0)` / `false`. -/
structure StaticMeta where
  lordPump : Option (Array String × Int × Int) := none
  trampleSubtypes : Option (Array String) := none
  hostBonus : Int × Int := (0, 0)
  landsYouControlPT : Bool := false
  cantBlockUnless : Option (Array String) := none
  cantBeBlockedExcept : Option Nat := none
  enchantedOnlySubtype : Option String := none
  cardsInHandPower : Bool := false
deriving Repr, Inhabited, BEq

/-- Classification of a static shape for Game accessors. -/
def StaticShape.spec : StaticShape → StaticMeta
  | .lordTrample subtypes => { trampleSubtypes := some subtypes }
  | .lordPump subtypes p t => { lordPump := some (subtypes, p, t) }
  | .hostGets _ p t => { hostBonus := (p, t) }
  | .landsYouControlPT => { landsYouControlPT := true }
  | .cantBlockUnless subtypes => { cantBlockUnless := some subtypes }
  | .cantBeBlockedExcept n => { cantBeBlockedExcept := some n }
  | .enchantedOnlySubtypeCantAttackOrBlock subtype =>
    { enchantedOnlySubtype := some subtype }
  | .cardsInHandPower => { cardsInHandPower := true }

/-- Classification of this static ability. Exhaustive so a new constructor is a
compile error here rather than silently matching `false` / `(0, 0)` in `Game`. -/
def shape : StaticAbility → StaticShape
  | .otherCreaturesHaveTrample subtypes => .lordTrample subtypes
  | .otherCreaturesGet subtypes p t => .lordPump subtypes p t
  | .enchantedCreatureGets p t => .hostGets "Enchanted creature" p t
  | .equippedCreatureGets p t => .hostGets "Equipped creature" p t
  | .powerToughnessEqualLandsYouControl => .landsYouControlPT
  | .cantBlockUnlessYouControl subtypes => .cantBlockUnless subtypes
  | .cantBeBlockedExceptBy n => .cantBeBlockedExcept n
  | .enchantedIsOnlySubtypeCantAttackOrBlock subtype =>
    .enchantedOnlySubtypeCantAttackOrBlock subtype
  | .powerEqualCardsInHand => .cardsInHandPower

/-- Oracle-style reminder from `shape`, so a new constructor only updates that
table. -/
def toNotation (ab : StaticAbility) : String :=
  match ab.shape with
  | .lordTrample subtypes =>
    s!"Other {joinedSubtypes subtypes pluralSubtype} you control have trample."
  | .lordPump subtypes p t =>
    s!"Other {joinedSubtypes subtypes} creatures you control get {signedStat p}/{signedStat t}."
  | .hostGets host p t => hostGetsPhrase host p t
  | .landsYouControlPT =>
    "This creature's power and toughness are each equal to the number of lands you control."
  | .cantBlockUnless subtypes =>
    match subtypes.toList with
    | [] => "This creature can't block."
    | xs =>
      s!"This creature can't block unless you control a {String.intercalate " or " xs}."
  | .cantBeBlockedExcept n =>
    let nWord := if n == 2 then "two" else if n == 3 then "three" else toString n
    s!"This creature can't be blocked except by {nWord} or more creatures."
  | .enchantedOnlySubtypeCantAttackOrBlock subtype =>
    s!"Enchanted creature is a {subtype} and can't attack or block."
  | .cardsInHandPower =>
    "This power is equal to the number of cards in your hand."

instance : ToString StaticAbility where
  toString := toNotation

/-- Lord +P/+T this ability grants other matching creatures, if any. -/
def lordPump? (ab : StaticAbility) : Option (Array String × Int × Int) :=
  ab.shape.spec.lordPump

/-- Subtypes this ability grants trample to, if any. -/
def trampleSubtypes? (ab : StaticAbility) : Option (Array String) :=
  ab.shape.spec.trampleSubtypes

/-- Continuous +P/+T this ability grants its enchanted or equipped host
(CR 613.3c). Other static abilities contribute `(0, 0)` here. -/
def hostStatBonus (ab : StaticAbility) : Int × Int :=
  ab.shape.spec.hostBonus

/-- True for the lands-you-control P/T characteristic-defining ability. -/
def isLandsYouControlPT (ab : StaticAbility) : Bool :=
  ab.shape.spec.landsYouControlPT

/-- Subtypes required to declare a blocker, if this ability restricts blocking. -/
def cantBlockUnless? (ab : StaticAbility) : Option (Array String) :=
  ab.shape.spec.cantBlockUnless

/-- Minimum number of blockers required, if this ability restricts blocking. -/
def cantBeBlockedExcept? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.cantBeBlockedExcept

/-- Enchanted-only subtype that also prevents attacking and blocking. -/
def enchantedOnlySubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.enchantedOnlySubtype

/-- True for the cards-in-hand power characteristic-defining ability. -/
def isCardsInHandPower (ab : StaticAbility) : Bool :=
  ab.shape.spec.cardsInHandPower

end StaticAbility

/-- A `{T}: Add {M} for each [subtype] you control` mana ability (CR 106.4 / 605). -/
structure TapAddForEach where
  mana : ManaType
  subtype : String
deriving Repr, Inhabited, BEq

namespace TapAddForEach

def toNotation (a : TapAddForEach) : String :=
  s!"\{T}: Add \{{a.mana.letter}} for each {a.subtype} you control"

instance : ToString TapAddForEach where
  toString := toNotation

end TapAddForEach

/-- A triggered ability the engine currently understands (CR 603). -/
inductive TriggeredAbility where
  /-- Whenever this creature attacks, it gets +X/+0 until end of turn, where X
  is the greatest power among creatures you control. -/
  | onAttackPumpByGreatestPower
  /-- Whenever this creature attacks, choose up to one other target creature you
  control. Its base power and toughness become equal to this creature's power
  and toughness until end of turn (e.g. Galion, Elvenking's Butler). -/
  | onAttackSetOtherBasePT
  /-- Whenever this creature attacks, another target creature you control gets
  +2/+0 and gains trample until end of turn (e.g. Oliphaunt). -/
  | onAttackOtherGets2AndTrample
  /-- Whenever this creature attacks, scry `n` (e.g. Lothlórien Lookout). -/
  | onAttackScry (n : Nat)
  /-- Ferocious — Whenever this creature attacks while you control a creature
  with power 4 or greater, you gain `n` life (e.g. Ravening Warg). The power
  check is an intervening condition (CR 603.2 / 603.4): it is checked when
  the creature attacks and not again on resolution. -/
  | onAttackFerociousGainLife (n : Nat)
  /-- Whenever this creature becomes blocked, it deals 1 damage to each creature
  blocking it (e.g. Battle-Scarred Goblin). -/
  | onBecomesBlockedDeal1ToBlockers
  /-- When this permanent enters, scry `n` (e.g. Gift of Strands). -/
  | onEnterScry (n : Nat)
  /-- When this permanent enters, draw `n` cards (e.g. Elvish Visionary). -/
  | onEnterDraw (n : Nat)
  /-- When this permanent enters, search your library for a Forest card, put
  that card onto the battlefield, then shuffle (e.g. Wood Elves). -/
  | onEnterSearchForest
  /-- When this permanent enters, you may discard a card. If you do, draw `n`
  cards (e.g. Ragged Short Spear). -/
  | onEnterMayDiscardDraw (n : Nat)
  /-- When this permanent enters, target opponent sacrifices a creature of
  their choice (e.g. Crude Bent Blade). -/
  | onEnterTargetOpponentSacrificesCreature
  /-- Landfall — Whenever a land you control enters, put a +1/+1 counter on
  target creature you control (e.g. Beorn's Hospitality). -/
  | onLandYouControlEntersPlusOnePlusOne
  /-- Landfall — Whenever a land you control enters, this creature gets +1/+1
  until end of turn (e.g. Attercop). -/
  | onLandYouControlEntersGets1
  /-- When this permanent enters, it deals `amount` damage divided as you
  choose among one to `maxTargets` targets (e.g. Gandalf, Spark Starter). -/
  | onEnterDealDividedDamage (amount maxTargets : Nat)
  /-- Whenever this creature enters or attacks, it deals `amount` damage divided
  as you choose among one to `maxTargets` targets (e.g. Inferno Titan). -/
  | onEnterOrAttackDealDividedDamage (amount maxTargets : Nat)
  /-- Whenever this creature enters or attacks, return target Elf card from
  your graveyard to your hand. You gain life equal to that card's power
  (e.g. Mirkwood Elk). -/
  | onEnterOrAttackReturnElfGainLife
  /-- When this creature dies, it deals damage equal to its power to target
  creature an opponent controls (e.g. Goblin Fireleaper). -/
  | onDiesDealDamageEqualToPowerToOppCreature
  /-- Whenever you cast an instant or sorcery spell, this creature deals
  `amount` damage to each opponent (e.g. Guttersnipe). -/
  | onCastInstantOrSorceryDealDamageToEachOpponent (amount : Nat)
  /-- Whenever you attack with one or more Elves, scry `n` (e.g. Celeborn the Wise). -/
  | onAttackWithElvesScry (n : Nat)
  /-- Whenever you scry, this creature gets +1/+1 until end of turn for each card
  looked at while scrying this way (e.g. Celeborn the Wise). -/
  | onScryPumpSelfForEachLookedAt
  /-- Whenever another Elf you control enters, this creature gets +1/+1 until
  end of turn (e.g. Woodland Weavemaster). -/
  | onAnotherElfYouControlEntersGets1
  /-- When this creature dies, target creature an opponent controls gets
  +P/+T until end of turn (e.g. Front Porch Sentries). -/
  | onDiesOppCreatureGets (power toughness : Int)
  /-- Whenever one or more other creatures die, scry `n`
  (e.g. Great Fierce Bee). -/
  | onOneOrMoreOtherCreaturesDieScry (n : Nat)
  /-- When this permanent enters, target opponent sacrifices a creature of
  their choice (e.g. Crude Bent Blade). -/
  | onEnterTargetOpponentSacrifices
  /-- When this permanent enters, each player sacrifices a creature of their
  choice (e.g. Merciless Executioner). -/
  | onEnterEachPlayerSacrificesCreature
  /-- When this permanent enters, each opponent discards a card
  (e.g. Stony-Voiced Goblins). -/
  | onEnterEachOpponentDiscards
  /-- When this permanent enters, exile up to one target card from an
  opponent's graveyard. Each opponent loses `life` life
  (e.g. Gollum the Abandoned). -/
  | onEnterExileOppGyCardOppsLoseLife (life : Nat)
  /-- When this permanent enters, target creature gets +P/+T until end of turn. -/
  | onEnterTargetGets (power toughness : Int)
  /-- When this permanent enters, creatures you control get +P/+0 and first strike. -/
  | onEnterCreaturesYouControlGetAndFirstStrike (power : Int)
  /-- When this creature dies, draw `n` cards. -/
  | onDiesDraw (n : Nat)
  /-- Whenever this creature attacks, it gets +1/+1 for each other creature you control. -/
  | onAttackPumpForEachOtherCreature
  /-- Whenever two or more creatures you control attack a player, target
  attacking creature without flying gains flying until end of turn. -/
  | onAttackWithTwoOrMoreGrantFlying
  /-- Whenever another creature you control with power `power` or less enters,
  you may pay `{generic}`. If you do, draw a card. -/
  | onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw (power : Int) (generic : Nat)
  /-- When this creature enters, draw a card. Then if you don't control a
  legendary creature, put a card from your hand on the bottom of your library. -/
  | onEnterDrawThenBottomIfNoLegendary
  /-- When this creature enters, you may exile another target creature. -/
  | onEnterMayExileAnotherCreature
  /-- When this creature leaves the battlefield, return the exiled card. -/
  | onLeaveReturnExiled
  /-- When this enchantment enters, exile target nonland an opponent controls
  until this leaves the battlefield. -/
  | onEnterExileOppNonlandUntilLeaves
  /-- At the beginning of your end step, remove a hope counter. If you do,
  draw a card. Then if this has no hope counters, sacrifice it and gain 4 life. -/
  | onYourEndStepRemoveHopeDrawSac
  /-- Whenever you draw your second card each turn, put a +1/+1 counter on this. -/
  | onDrawSecondPlusOne
  /-- Whenever you draw a card, put a +1/+1 counter on this. -/
  | onDrawPlusOne
  /-- Whenever you scry, this gets +1/+0 and can't be blocked this turn.
  Triggers only once each turn. -/
  | onScryPumpAndUnblockableOnce
  /-- Whenever this deals combat damage to a player, draw a card, then discard a card. -/
  | onCombatDamageToPlayerLoot
  /-- Whenever this attacks, you may exile target creature defending player
  controls until this leaves the battlefield. -/
  | onAttackMayExileDefenderUntilLeaves
  /-- Whenever this attacks, you may tap any number of untapped Humans you
  control. Draw a card for each Human tapped this way. -/
  | onAttackTapHumansDraw
deriving Repr, Inhabited, BEq

/-- When a triggered ability fires (CR 603). Several printed abilities share
an event (`scry` on attack, enter, or attack-with-Elves); “enters or attacks”
is two events. -/
inductive TriggerEvent where
  /-- This creature is declared as an attacker (CR 508.2). -/
  | attacking
  /-- This creature becomes blocked (CR 509.5c). -/
  | becomesBlocked
  /-- This permanent enters the battlefield (CR 603.6a). -/
  | entering
  /-- A land the controller controls enters (landfall). -/
  | landYouControlEnters
  /-- This creature dies (CR 700.4 / 603.6c). -/
  | dying
  /-- You cast an instant or sorcery (CR 601.2i). -/
  | youCastInstantOrSorcery
  /-- You attack with one or more Elves (CR 508.2 / 603.2a). -/
  | youAttackWithElves
  /-- You scry (CR 701.20 / 603.2). -/
  | youScry
  /-- Another Elf you control enters (CR 603.6a). -/
  | anotherElfYouControlEnters
  /-- One or more other creatures die (CR 700.4 / 603.2a). -/
  | oneOrMoreOtherCreaturesDie
  /-- This permanent leaves the battlefield (CR 603.6c). -/
  | leaving
  /-- You draw a card (CR 121 / 603.2). -/
  | youDraw
  /-- You draw your second card this turn. -/
  | youDrawSecondCard
  /-- Two or more creatures you control attack a player. -/
  | youAttackWithTwoOrMore
  /-- This creature deals combat damage to a player (CR 510.2 / 603.2). -/
  | dealsCombatDamageToPlayer
  /-- The beginning of your end step (CR 513.1 / 603.1). -/
  | yourEndStep
  /-- Another creature you control enters (CR 603.6a). -/
  | anotherCreatureYouControlEnters
deriving Repr, Inhabited, BEq, DecidableEq

namespace TriggerEvent

/-- Oracle wording plus how Game queues this event. Exhaustive so a new event
is a compile error here rather than silently matching `When this occurs` with
`Whenever`, or restating the stack label and CR 603.3d check at every queue
site. -/
structure Spec where
  clause : String
  isWhenever : Bool := true
  /-- Log label when this event is put on the stack. -/
  label : String
  /-- Remove the ability when it requires a target and has none (CR 603.3d). -/
  checkTargets : Bool := true
  /-- Trigger condition is another ability triggering (CR 603.3b part 2). -/
  isAnotherAbilityTriggering : Bool := false
deriving Repr, Inhabited, BEq

/-- Classification of this event. `clause`, `isWhenever`, `label`, and
`checkTargets` read this table. -/
def spec : TriggerEvent → Spec
  | .attacking =>
    { clause := "this creature attacks", label := "attack trigger" }
  | .becomesBlocked =>
    { clause := "this creature becomes blocked", label := "becomes-blocked trigger",
      checkTargets := false }
  | .entering =>
    { clause := "this permanent enters", isWhenever := false, label := "enters trigger" }
  | .landYouControlEnters =>
    { clause := "a land you control enters", label := "landfall trigger" }
  | .dying =>
    { clause := "this creature dies", isWhenever := false, label := "dies trigger" }
  | .youCastInstantOrSorcery =>
    { clause := "you cast an instant or sorcery spell", label := "cast trigger",
      checkTargets := false }
  | .youAttackWithElves =>
    { clause := "you attack with one or more Elves", label := "attack trigger",
      checkTargets := false }
  | .youScry =>
    { clause := "you scry", label := "scry trigger", checkTargets := false }
  | .anotherElfYouControlEnters =>
    { clause := "another Elf you control enters", label := "Elf-enters trigger",
      checkTargets := false }
  | .oneOrMoreOtherCreaturesDie =>
    { clause := "one or more other creatures die", label := "other-creatures-die trigger",
      checkTargets := false }
  | .leaving =>
    { clause := "this creature leaves the battlefield", isWhenever := false,
      label := "leaves trigger", checkTargets := false }
  | .youDraw =>
    { clause := "you draw a card", label := "draw trigger", checkTargets := false }
  | .youDrawSecondCard =>
    { clause := "you draw your second card each turn", label := "second-card trigger",
      checkTargets := false }
  | .youAttackWithTwoOrMore =>
    { clause := "two or more creatures you control attack a player",
      label := "attack trigger" }
  | .dealsCombatDamageToPlayer =>
    { clause := "this deals combat damage to a player", label := "combat-damage trigger",
      checkTargets := false }
  | .yourEndStep =>
    { clause := "the beginning of your end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .anotherCreatureYouControlEnters =>
    { clause := "another creature you control enters", label := "creature-enters trigger",
      checkTargets := false }

/-- Oracle “when/whenever” clause after the leading word. -/
def clause (e : TriggerEvent) : String :=
  e.spec.clause

/-- `Whenever` rather than one-shot `When` (enters / dies). -/
def isWhenever (e : TriggerEvent) : Bool :=
  e.spec.isWhenever

/-- Log label when this event is put on the stack. -/
def label (e : TriggerEvent) : String :=
  e.spec.label

/-- True when Game removes this trigger for lack of a legal target (CR 603.3d). -/
def checkTargets (e : TriggerEvent) : Bool :=
  e.spec.checkTargets

/-- True when this event is “another ability triggering” (CR 603.3b part 2). -/
def isAnotherAbilityTriggering (e : TriggerEvent) : Bool :=
  e.spec.isAnotherAbilityTriggering

end TriggerEvent

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

/-- How a triggered ability selects targets when it is put on the stack
(CR 603.3d / 601.2c). Spell and activated-ability targeting use the same
`EffectTargetKind` constructors. -/
abbrev TriggerTargetKind := EffectTargetKind

/-- What a triggered ability does when it resolves (CR 608). Grouped so
`Game.applyTriggeredAbility` matches resolution shapes instead of every
constructor: scry, +1/+1 on the source, and divided damage each cover
multiple printed abilities. Permanent-target counters and pumps, and source
pumps, share `PermanentAction` with spells and activated abilities. -/
inductive TriggerResolution where
  /-- Pump the source by the greatest power among creatures you control. -/
  | pumpGreatestPower
  /-- Set another creature's base P/T to this creature's. -/
  | setOtherBasePT
  /-- Deal `amount` damage to each creature blocking the source. -/
  | damageBlockers (amount : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search the library for a Forest card. -/
  | searchForest
  /-- You may discard a card. If you do, draw `n`. -/
  | mayDiscardDraw (n : Nat)
  /-- Target opponent sacrifices a creature of their choice. -/
  | opponentSacrificesCreature
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Deal previously divided damage to the announced targets. -/
  | dividedDamage
  /-- Deal last-known power as damage to the announced creature. -/
  | damageFromLastKnownPower
  /-- Return an Elf card from the graveyard and gain life equal to its power. -/
  | returnElfGainLife
  /-- Deal `amount` damage to each opponent. -/
  | damageEachOpponent (amount : Nat)
  /-- Pump the source +1/+1 per card looked at while scrying. -/
  | pumpByLookedAt
  /-- Affect the trigger's source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life (CR 118.2). -/
  | gainLife (n : Nat)
  /-- Target opponent sacrifices a creature of their choice. -/
  | targetOpponentSacrifices
  /-- Each player sacrifices a creature of their choice. -/
  | eachPlayerSacrificesCreature
  /-- Each opponent discards a card. -/
  | eachOpponentDiscards
  /-- Exile up to one targeted card from an opponent's graveyard, then each
  opponent loses `life` life. -/
  | exileOppGyCardOppsLoseLife (life : Nat)
  /-- Creatures you control get +P/+0 and first strike until end of turn. -/
  | creaturesYouControlPumpAndFirstStrike (power : Int)
  /-- Pump the source +1/+1 for each other creature you control. -/
  | pumpForEachOtherCreature
  /-- Grant flying until end of turn to the targeted creature. -/
  | grantFlying
  /-- You may pay `{generic}`. If you do, draw a card. -/
  | mayPayGenericDraw (generic : Nat)
  /-- Draw a card, then put a card on the bottom if you control no legendary. -/
  | drawThenBottomIfNoLegendary
  /-- Exile the targeted permanent until the source leaves the battlefield. -/
  | exileUntilLeaves
  /-- Return cards exiled by the source. -/
  | returnLinkedExile
  /-- Remove a hope counter, draw, then maybe sacrifice and gain life. -/
  | removeHopeDrawSac
  /-- Draw a card, then discard a card. -/
  | loot
  /-- Tap any number of Humans you control; draw that many cards. -/
  | tapHumansDraw
  /-- Pump the source +1/+0 and grant can't be blocked this turn. -/
  | pumpAndUnblockable
deriving Repr, Inhabited, BEq

/-- When a triggered ability fires, how it targets, optional divided-damage
parameters, and how it resolves (CR 603 / 601.2d / 608). Adding a constructor
only requires updating `timing` instead of parallel match trees. -/
structure TriggerTiming where
  events : Array TriggerEvent := #[]
  targeting : EffectTargeting := .of .none
  /-- Zero targets is a legal announcement (CR 115.1c / 601.2c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
  /-- Damage amount and maximum number of targets when this ability divides
  damage as the controller chooses (CR 601.2d). -/
  dividedDamage : Option (Nat × Nat) := none
  /-- What happens when this ability resolves. -/
  resolution : TriggerResolution := .pumpGreatestPower
  /-- Intervening “while you control a creature with power ≥ n” (e.g. Ferocious).
  Checked when the trigger event occurs (CR 603.2 / 603.4); not rechecked on
  resolution. -/
  youControlCreatureWithPower : Option Int := none
  /-- This trigger fires only once each turn. -/
  onceEachTurn : Bool := false
  /-- Intervening “another creature you control with power ≤ n”. -/
  anotherCreaturePowerAtMost : Option Int := none
deriving Repr, Inhabited, BEq

/-- Classification of this triggered ability. Exhaustive so a new constructor
is a compile error here rather than silently matching `false` elsewhere. -/
def timing : TriggeredAbility → TriggerTiming
  | .onAttackPumpByGreatestPower =>
    { events := #[.attacking], resolution := .pumpGreatestPower }
  | .onAttackSetOtherBasePT =>
    { events := #[.attacking], targeting := .of .anotherCreatureYouControl,
      allowsZeroTargets := true, resolution := .setOtherBasePT }
  | .onAttackOtherGets2AndTrample =>
    { events := #[.attacking], targeting := .of .anotherCreatureYouControl,
      resolution := .onPermanent (.pumpAndTrample 2 0) }
  | .onAttackScry n => { events := #[.attacking], resolution := .scry n }
  | .onAttackFerociousGainLife n =>
    { events := #[.attacking], resolution := .gainLife n,
      youControlCreatureWithPower := some 4 }
  | .onBecomesBlockedDeal1ToBlockers =>
    { events := #[.becomesBlocked], resolution := .damageBlockers 1 }
  | .onEnterScry n => { events := #[.entering], resolution := .scry n }
  | .onEnterDraw n => { events := #[.entering], resolution := .draw n }
  | .onEnterSearchForest => { events := #[.entering], resolution := .searchForest }
  | .onEnterMayDiscardDraw n =>
    { events := #[.entering], resolution := .mayDiscardDraw n }
  | .onEnterTargetOpponentSacrificesCreature =>
    { events := #[.entering], targeting := .of .opponent,
      resolution := .opponentSacrificesCreature }
  | .onLandYouControlEntersPlusOnePlusOne =>
    { events := #[.landYouControlEnters], targeting := .of .creatureYouControl,
      resolution := .onPermanent (.plusOne 1) }
  | .onLandYouControlEntersGets1 =>
    { events := #[.landYouControlEnters], resolution := .onSource (.pump 1 1) }
  | .onEnterDealDividedDamage amount maxTargets =>
    { events := #[.entering], targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .onEnterOrAttackDealDividedDamage amount maxTargets =>
    { events := #[.entering, .attacking], targeting := .of .playerOrCreature,
      dividedDamage := some (amount, maxTargets), resolution := .dividedDamage }
  | .onEnterOrAttackReturnElfGainLife =>
    { events := #[.entering, .attacking], targeting := .of .elfInYourGraveyard,
      resolution := .returnElfGainLife }
  | .onDiesDealDamageEqualToPowerToOppCreature =>
    { events := #[.dying], targeting := .of .oppCreature,
      resolution := .damageFromLastKnownPower }
  | .onCastInstantOrSorceryDealDamageToEachOpponent n =>
    { events := #[.youCastInstantOrSorcery], resolution := .damageEachOpponent n }
  | .onAttackWithElvesScry n =>
    { events := #[.youAttackWithElves], resolution := .scry n }
  | .onScryPumpSelfForEachLookedAt =>
    { events := #[.youScry], resolution := .pumpByLookedAt }
  | .onAnotherElfYouControlEntersGets1 =>
    { events := #[.anotherElfYouControlEnters], resolution := .onSource (.pump 1 1) }
  | .onDiesOppCreatureGets p t =>
    { events := #[.dying], targeting := .of .oppCreature,
      resolution := .onPermanent (.pump p t) }
  | .onOneOrMoreOtherCreaturesDieScry n =>
    { events := #[.oneOrMoreOtherCreaturesDie], resolution := .scry n }
  | .onEnterTargetOpponentSacrifices =>
    { events := #[.entering], targeting := .of .opponent,
      resolution := .targetOpponentSacrifices }
  | .onEnterEachPlayerSacrificesCreature =>
    { events := #[.entering], resolution := .eachPlayerSacrificesCreature }
  | .onEnterEachOpponentDiscards =>
    { events := #[.entering], resolution := .eachOpponentDiscards }
  | .onEnterExileOppGyCardOppsLoseLife n =>
    { events := #[.entering], targeting := .of .oppGraveyardCard,
      allowsZeroTargets := true, resolution := .exileOppGyCardOppsLoseLife n }
  | .onEnterTargetGets p t =>
    { events := #[.entering], targeting := .of .creature,
      resolution := .onPermanent (.pump p t) }
  | .onEnterCreaturesYouControlGetAndFirstStrike p =>
    { events := #[.entering], resolution := .creaturesYouControlPumpAndFirstStrike p }
  | .onDiesDraw n =>
    { events := #[.dying], resolution := .draw n }
  | .onAttackPumpForEachOtherCreature =>
    { events := #[.attacking], resolution := .pumpForEachOtherCreature }
  | .onAttackWithTwoOrMoreGrantFlying =>
    { events := #[.youAttackWithTwoOrMore], targeting := .of .attackingCreatureWithoutFlying,
      resolution := .grantFlying }
  | .onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw p generic =>
    { events := #[.anotherCreatureYouControlEnters],
      resolution := .mayPayGenericDraw generic,
      anotherCreaturePowerAtMost := some p }
  | .onEnterDrawThenBottomIfNoLegendary =>
    { events := #[.entering], resolution := .drawThenBottomIfNoLegendary }
  | .onEnterMayExileAnotherCreature =>
    { events := #[.entering], targeting := .of .anotherCreature,
      allowsZeroTargets := true, resolution := .exileUntilLeaves }
  | .onLeaveReturnExiled =>
    { events := #[.leaving], resolution := .returnLinkedExile }
  | .onEnterExileOppNonlandUntilLeaves =>
    { events := #[.entering], targeting := .of .oppNonland, resolution := .exileUntilLeaves }
  | .onYourEndStepRemoveHopeDrawSac =>
    { events := #[.yourEndStep], resolution := .removeHopeDrawSac }
  | .onDrawSecondPlusOne =>
    { events := #[.youDrawSecondCard], resolution := .onSource (.plusOne 1) }
  | .onDrawPlusOne =>
    { events := #[.youDraw], resolution := .onSource (.plusOne 1) }
  | .onScryPumpAndUnblockableOnce =>
    { events := #[.youScry], resolution := .pumpAndUnblockable, onceEachTurn := true }
  | .onCombatDamageToPlayerLoot =>
    { events := #[.dealsCombatDamageToPlayer], resolution := .loot }
  | .onAttackMayExileDefenderUntilLeaves =>
    { events := #[.attacking], targeting := .of .defendingPlayerCreature,
      allowsZeroTargets := true, resolution := .exileUntilLeaves }
  | .onAttackTapHumansDraw =>
    { events := #[.attacking], resolution := .tapHumansDraw }

/-- Damage amount and maximum number of targets when this ability divides
damage as the controller chooses (CR 601.2d). -/
def dividedDamage? (ab : TriggeredAbility) : Option (Nat × Nat) :=
  ab.timing.dividedDamage

/-- How this ability resolves (CR 608). -/
def resolution (ab : TriggeredAbility) : TriggerResolution :=
  ab.timing.resolution

instance : HasTargeting TriggeredAbility where
  targeting ab := ab.timing.targeting

/-- Targeting shape when this trigger is put on the stack (CR 603.3d). -/
def targeting (ab : TriggeredAbility) : EffectTargeting :=
  HasTargeting.targeting ab

/-- True when this ability fires on `e`. Game queues triggers by `TriggerEvent`. -/
def firesOn (ab : TriggeredAbility) (e : TriggerEvent) : Bool :=
  ab.timing.events.contains e

/-- Whom this trigger may target when announced (CR 603.3d / 601.2c). -/
def targetKind (ab : TriggeredAbility) : TriggerTargetKind :=
  HasTargeting.targetKind ab

/-- True when putting this trigger on the stack requires announcing a target
(CR 603.3d / 601.2c). “Up to one” still announces, including choosing zero. -/
def requiresTarget (ab : TriggeredAbility) : Bool :=
  HasTargeting.requiresTarget ab

/-- True when zero targets is a legal announcement (CR 115.1c / 601.2c), e.g.
“choose up to one”. Such a trigger is never removed for lack of targets. -/
def allowsZeroTargets (ab : TriggeredAbility) : Bool :=
  ab.timing.allowsZeroTargets

/-- Intervening power threshold, if this ability requires you to control a
creature with at least that power (e.g. Ferocious). -/
def youControlCreatureWithPower? (ab : TriggeredAbility) : Option Int :=
  ab.timing.youControlCreatureWithPower

/-- Leading “When/Whenever …” from the event list. -/
def eventPrefix (t : TriggerTiming) : String :=
  if t.events.contains .entering && t.events.contains .attacking then
    "Whenever this creature enters or attacks"
  else if t.events.contains .yourEndStep then
    "At the beginning of your end step"
  else if t.events.contains .anotherCreatureYouControlEnters then
    match t.anotherCreaturePowerAtMost with
    | some n =>
      s!"Whenever another creature you control with power {n} or less enters"
    | none => "Whenever another creature you control enters"
  else
    match t.events[0]? with
    | none => "When this occurs"
    | some e =>
      let word := if e.isWhenever then "Whenever" else "When"
      s!"{word} {e.clause}"

/-- Intervening “while you control a creature with power ≥ n”, or empty. -/
def interveningClause (t : TriggerTiming) : String :=
  match t.youControlCreatureWithPower with
  | some n => s!" while you control a creature with power {n} or greater"
  | none => ""

/-- Effect clause from resolution, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : TriggerTiming) : String :=
  let noun := t.targeting.kind.noun
  match t.resolution with
  | .pumpGreatestPower =>
    "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
  | .setOtherBasePT =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .onPermanent action => PermanentAction.toNotation action noun
  | .damageBlockers n =>
    s!"it deals {n} damage to each creature blocking it"
  | .scry n => s!"scry {n}"
  | .draw n => s!"draw {cardPhrase n}"
  | .searchForest =>
    "search your library for a Forest card, put that card onto the battlefield, then shuffle"
  | .mayDiscardDraw n =>
    s!"you may discard a card. If you do, draw {cardPhrase n}"
  | .opponentSacrificesCreature =>
    s!"{noun} sacrifices a creature of their choice"
  | .dividedDamage =>
    match t.dividedDamage with
    | some (amount, maxTargets) =>
      s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
    | none => "it deals damage divided as you choose"
  | .damageFromLastKnownPower =>
    s!"it deals damage equal to its power to {noun}"
  | .returnElfGainLife =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .damageEachOpponent n =>
    s!"this creature deals {n} damage to each opponent"
  | .pumpByLookedAt =>
    "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
  | .onSource action => PermanentAction.toNotation action "this creature"
  | .gainLife n => s!"you gain {n} life"
  | .targetOpponentSacrifices =>
    s!"{noun} sacrifices a creature of their choice"
  | .eachPlayerSacrificesCreature =>
    "each player sacrifices a creature of their choice"
  | .eachOpponentDiscards =>
    "each opponent discards a card"
  | .exileOppGyCardOppsLoseLife n =>
    s!"exile up to one {noun}. Each opponent loses {n} life"
  | .creaturesYouControlPumpAndFirstStrike p =>
    s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
  | .pumpForEachOtherCreature =>
    "it gets +1/+1 until end of turn for each other creature you control"
  | .grantFlying =>
    s!"{noun} gains flying until end of turn"
  | .mayPayGenericDraw generic =>
    s!"you may pay \{{generic}}. If you do, draw a card"
  | .drawThenBottomIfNoLegendary =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .exileUntilLeaves =>
    if t.allowsZeroTargets then
      if t.targeting.kind == .defendingPlayerCreature then
        s!"you may exile {noun} until this leaves the battlefield"
      else
        s!"you may exile {noun}"
    else
      s!"exile {noun} until this leaves the battlefield"
  | .returnLinkedExile =>
    "return the exiled card to the battlefield under its owner's control"
  | .removeHopeDrawSac =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .loot =>
    "draw a card, then discard a card"
  | .tapHumansDraw =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .pumpAndUnblockable =>
    "this gets +1/+0 until end of turn and can't be blocked this turn"

/-- True when this trigger fires only once each turn. -/
def onceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.timing.onceEachTurn

/-- Intervening power-at-most threshold for another creature entering. -/
def anotherCreaturePowerAtMost? (ab : TriggeredAbility) : Option Int :=
  ab.timing.anotherCreaturePowerAtMost

def toNotation (ab : TriggeredAbility) : String :=
  let t := ab.timing
  let once :=
    if t.onceEachTurn then " This ability triggers only once each turn." else ""
  s!"{eventPrefix t}{interveningClause t}, {resolutionPhrase t}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

end TriggeredAbility

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
structure AdventureFace where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[.sorcery]
  subtypes : Array Subtype := #["Adventure"]
  oracleText : String := ""
  spellEffect : Option SpellEffect := none
deriving Repr, Inhabited, BEq

/-- Printed (Oracle) characteristics of a card. -/
structure CardDef where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  oracleText : String := ""
  power : Option Int := none
  toughness : Option Int := none
  loyalty : Option Int := none
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  keywords : Keywords := Keywords.none
  spellEffect : Option SpellEffect := none
  /-- Additional cost: sacrifice an artifact or creature (CR 601.2b / 601.2h), e.g.
  Improvised Club. When `additionalCostOrPayGeneric` is set, that sacrifice
  may be replaced by paying that much generic mana (e.g. Stir Up Trouble).
  The choice is announced at CR 601.2b, before targets. -/
  additionalCostSacrificeArtifactOrCreature : Bool := false
  /-- Alternative additional cost: pay this much generic mana instead of
  sacrificing an artifact or creature (CR 601.2b). -/
  additionalCostOrPayGeneric : Option Nat := none
  /-- This spell costs this much generic mana less if a creature died this
  turn (e.g. Dreaded Bat-Cloud). -/
  costReductionIfCreatureDied : Nat := 0
  /-- This spell costs this much generic mana less if it targets a creature
  that was dealt damage this turn (e.g. Bitter Downfall). -/
  costReductionIfTargetDamaged : Nat := 0
  /-- This spell costs this much generic mana less if it targets a tapped
  creature (e.g. Magnificent End). -/
  costReductionIfTargetTapped : Nat := 0
  /-- This spell costs this much generic mana less if it targets an attacking
  nontoken creature (e.g. Uneasy Partings). -/
  costReductionIfTargetAttackingNontoken : Nat := 0
  /-- Modes of a “Choose one” spell (CR 700.2). Nonempty means the spell is modal. -/
  spellModes : Array SpellEffect := #[]
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
  /-- `{T}: Add {M} for each permanent you control with this subtype
  (e.g. Elvish Archdruid). -/
  tapAddManaForEach : Array TapAddForEach := #[]
  /-- `{T}: Add X mana of any one color, where X is this creature's power.
  That mana may be spent only to cast Elf spells and activate abilities of
  Elf sources (e.g. Woodland Weavemaster). -/
  tapAddAnyColorEqualToPower : Bool := false
  /-- `{T}: Add one mana of any color. Spend this mana only to cast an instant
  or sorcery spell (e.g. Pelargir Survivor). -/
  tapAddAnyColorForInstantOrSorcery : Bool := false
  /-- This enchantment enters with a hope counter for each creature you control
  (e.g. Dawn of a New Age). -/
  entersWithHopePerCreature : Bool := false
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / `tapAddManaForEach` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
deriving Repr, Inhabited

namespace CardDef

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

/-- True when `t` is among this card's types. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.any (· == t)

/-- True when `s` is among this card's subtypes. -/
def hasSubtype (c : CardDef) (s : Subtype) : Bool := c.subtypes.any (· == s)

/-- True when `s` is among this card's supertypes. -/
def hasSupertype (c : CardDef) (s : Supertype) : Bool := c.supertypes.any (· == s)

def isLand (c : CardDef) : Bool := c.hasType .land
def isCreature (c : CardDef) : Bool := c.hasType .creature
def isArtifact (c : CardDef) : Bool := c.hasType .artifact
def isInstant (c : CardDef) : Bool := c.hasType .instant
def isSorcery (c : CardDef) : Bool := c.hasType .sorcery
def isInstantOrSorcery (c : CardDef) : Bool := c.types.any CardType.isInstantOrSorcery
def isEnchantment (c : CardDef) : Bool := c.hasType .enchantment
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype "Aura"
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype "Equipment"

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !c.keywords.flash

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || c.keywords.flash

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  !c.spellModes.isEmpty

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array SpellEffect :=
  c.spellModes

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.isAura ||
  match c.spellEffect with
  | some e => e.requiresTarget
  | none => !c.spellModes.isEmpty && c.spellModes.all (·.requiresTarget)

/-- True when the printed effect or a mode is classified as `k`. -/
def hasCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellEffect.any (fun e => e.castKind == k)

/-- True when a modal mode is classified as `k`. -/
def hasModeCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellModes.any (fun e => e.castKind == k)

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- `{T}: Add {M}` abilities that produce one mana, from basic land types or
an explicit `tapAddMana` list. -/
def simpleTapAddMana (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.simpleTapAddMana ++ c.tapAddManaForEach.map (·.mana) ++
    (if c.tapAddAnyColorEqualToPower || c.tapAddAnyColorForInstantOrSorcery then
      (Color.all.map ManaType.colored).toArray
     else #[])

/-- Lowercase ASCII for comparing Oracle keyword lines to `Keywords.toList`. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- Drop a trailing Oracle reminder parenthetical, e.g. `Menace (This creature...)`. -/
def stripReminderParenthetical (s : String) : String :=
  match s.splitOn "(" with
  | [] => s
  | head :: _ => head.trimAscii.copy

/-- True when `line` restates modeled keywords, e.g. `Haste` or `Reach, deathtouch`.
A line that is only a parenthetical (e.g. basic-land `{T}: Add` reminder text)
is not a keyword restatement. -/
def isKeywordRestatement (k : Keywords) (line : String) : Bool :=
  let kw := k.toList
  let cleaned := stripReminderParenthetical ((line.replace "." "").trimAscii.copy)
  if cleaned.isEmpty then false
  else
    let parts := cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
    !parts.isEmpty && parts.all (fun p => kw.any (fun w => w == lowerAscii p))

/-- Gatherer delimiter between an adventurer card's primary and Adventure faces. -/
def isAdventureDelimiter (line : String) : Bool :=
  line == "//ADV//" || line.startsWith "//ADV//"

/-- Drop a leading `//ADV//` marker. The remainder (Adventure name and mana
cost) is kept so leftover Oracle text does not lose printed mana symbols. -/
def stripAdventureDelimiter (line : String) : Option String :=
  if line == "//ADV//" then none
  else if line.startsWith "//ADV//" then
    let rest := (line.drop "//ADV//".length).trimAscii.copy
    if rest.isEmpty then none else some rest
  else some line

/-- Oracle ability lines that are not just restating modeled keywords. The
Gatherer `//ADV//` marker is stored in `oracleText` but is not an ability. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.oracleText.splitOn "\n" |>.map (fun s => s.trimAscii.copy) |>.filterMap (fun line =>
    match stripAdventureDelimiter line with
    | none => none
    | some rest =>
      if rest.isEmpty || isKeywordRestatement c.keywords rest then none else some rest)

/-- `{T}: Add` mana abilities, additional costs, activated, static, triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.simpleTapAddMana.toList.map (fun t => s!"\{T}: Add \{{t.letter}}") ++
  c.tapAddManaForEach.toList.map TapAddForEach.toNotation ++
  (if c.tapAddAnyColorEqualToPower then
    ["{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."]
   else []) ++
  (if c.tapAddAnyColorForInstantOrSorcery then
    ["{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell."]
   else []) ++
  (if c.additionalCostSacrificeArtifactOrCreature then
    match c.additionalCostOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, sacrifice an artifact or creature or pay \{{n}}"]
    | none =>
      ["As an additional cost to cast this spell, sacrifice an artifact or creature"]
   else []) ++
  c.activatedAbilities.toList.map ActivatedAbility.toNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  match c.spellEffect with
  | some e => [SpellEffect.toNotation e]
  | none => []

/-- Abilities to print in the demo. Prefer leftover Oracle text so unmodeled
abilities (triggers, extra activations) are visible; fall back to structured
abilities when Oracle is empty or only restates keywords. -/
def abilitiesText (c : CardDef) : String :=
  let fromOracle := leftoverOracleLines c
  if !fromOracle.isEmpty then
    String.intercalate " / " fromOracle
  else
    String.intercalate "; " (structuredAbilityLines c)

/-- Keywords `k` plus leftover Oracle / structured abilities. -/
def keywordsAndAbilitiesOf (c : CardDef) (k : Keywords) : String :=
  String.intercalate " "
    ([toString k, c.abilitiesText].filter (fun s => !s.isEmpty))

/-- Keywords and abilities shown next to a card in the demo. -/
def keywordsAndAbilities (c : CardDef) : String :=
  c.keywordsAndAbilitiesOf c.keywords

def typeLine (c : CardDef) : String :=
  formatTypeLine c.supertypes c.types c.subtypes

def ptString (c : CardDef) : String :=
  match c.power, c.toughness with
  | some p, some t => s!"{p}/{t}"
  | some p, none => s!"{p}/*"
  | none, some t => s!"*/{t}"
  | none, none => if c.isCreature then "*/*" else ""

/-- Name, printed mana cost if any, type line, P/T, then keywords and abilities.
Cards with no mana cost (lands, and other objects whose cost cannot be paid)
omit the cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def summary (c : CardDef) : String :=
  String.intercalate " "
    ([c.name, toString c.manaCost, c.typeLine, c.ptString, c.keywordsAndAbilities].filter
      (fun s => !s.isEmpty))

instance : ToString CardDef where
  toString := summary

#guard toString Keyword.haste == "haste"
#guard toString Keyword.flash == "flash"
#guard toString Keyword.vigilance == "vigilance"
#guard toString Keyword.lifelink == "lifelink"
#guard toString Keyword.menace == "menace"
#guard CardDef.isKeywordRestatement Keyword.haste "Haste"
#guard !CardDef.isKeywordRestatement Keywords.none "({T}: Add {R}.)"
#guard CardDef.isKeywordRestatement Keyword.flash "Flash"
#guard CardDef.isKeywordRestatement Keyword.vigilance "Vigilance"
#guard CardDef.isKeywordRestatement (Keyword.reach.merge Keyword.deathtouch)
  "Reach, deathtouch"
#guard !CardDef.isKeywordRestatement Keyword.flying "Flash"
#guard toString Keyword.hexproof == "hexproof"
#guard CardDef.isKeywordRestatement Keyword.hexproof "Hexproof"
#guard toString Keyword.indestructible == "indestructible"
#guard CardDef.isKeywordRestatement Keyword.indestructible "Indestructible"
#guard CardDef.isAdventureDelimiter "//ADV//"
#guard CardDef.isAdventureDelimiter "//ADV// Spew Flame {4}{R}"
#guard !CardDef.isAdventureDelimiter "Spew Flame {4}{R}"
#guard CardDef.stripAdventureDelimiter "//ADV//" == none
#guard CardDef.stripAdventureDelimiter "//ADV// Spew Flame {4}{R}" ==
  some "Spew Flame {4}{R}"
#guard
  let c : CardDef := {
    name := "Silent Adventurer"
    types := #[.creature]
    oracleText :=
      "Flying\n//ADV//\nSpew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature."
    keywords := Keyword.flying
  }
  leftoverOracleLines c ==
    ["Spew Flame {4}{R}", "Sorcery — Adventure",
      "Spew Flame deals 5 damage to target creature."] &&
    (c.oracleText.splitOn "//ADV//").length > 1
#guard
  let c : CardDef := {
    name := "Silent Adventurer"
    types := #[.creature]
    oracleText :=
      "Flying\n//ADV// Spew Flame {4}{R}\nSorcery — Adventure\nSpew Flame deals 5 damage to target creature."
    keywords := Keyword.flying
  }
  leftoverOracleLines c ==
    ["Spew Flame {4}{R}", "Sorcery — Adventure",
      "Spew Flame deals 5 damage to target creature."]
#guard SpellEffect.toNotation (.dealDamage 3) == "deals 3 damage to any target"
#guard SpellEffect.toNotation (.pump 3 3) == "target creature gets +3/+3 until end of turn"
#guard SpellEffect.toNotation .destroyCreatureWithFlying ==
  "destroy target creature with flying"
#guard SpellEffect.toNotation .destroyCreature ==
  "destroy target creature"
#guard SpellEffect.toNotation .plusOnePlusOneTrampleHexproof ==
  "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"
#guard SpellEffect.toNotation (.dealDamageToCreature 5) ==
  "deals 5 damage to target creature"
#guard SpellEffect.toNotation (.dealDamageLoseIndestructibleExile 3) ==
  "deals 3 damage to target creature. That creature loses indestructible until end of turn. If that creature would die this turn, exile it instead"
#guard SpellEffect.toNotation .creatureYouControlDealsPowerToOppCreature ==
  "target creature you control deals damage equal to its power to target creature an opponent controls"
#guard SpellEffect.toNotation .playAdditionalLandThisTurn ==
  "you may play an additional land this turn"
#guard SpellEffect.toNotation .destroyArtifactOrLandNonflyersCantBlock ==
  "destroy target artifact or land. Creatures without flying can't block this turn"
#guard SpellEffect.toNotation (.destroyTargetCreatureControllerLosesLife 2) ==
  "destroy target creature. Its controller loses 2 life"
#guard SpellEffect.toNotation (.allCreaturesGet (-4) (-4)) ==
  "all creatures get -4/-4 until end of turn"
#guard SpellEffect.toNotation (.drawAndLoseLife 2 2) ==
  "you draw 2 cards and lose 2 life"
#guard SpellEffect.toNotation (.drawAndLoseLife 1 0) ==
  "you draw a card and lose 0 life"
#guard SpellEffect.toNotation (.targetPlayerDrawLoseLife 2 2) ==
  "target player draws 2 cards and loses 2 life"
#guard SpellEffect.toNotation (.creaturesTargetPlayerGet (-1) (-1)) ==
  "creatures target player controls get -1/-1 until end of turn"
#guard SpellEffect.toNotation (.pumpAndLifelink 2 2) ==
  "target creature gets +2/+2 and gains lifelink until end of turn"
#guard SpellEffect.toNotation (.pumpAndExileIfDies (-5) (-5)) ==
  "target creature gets -5/-5 until end of turn. If that creature would die this turn, exile it instead"
#guard (SpellEffect.toNotation .exileGraveyardCreaturesGrantCast).startsWith
  "exile all creature cards"
#guard EffectTargetKind.noun .playerOrCreature == "any target"
#guard EffectTargetKind.noun .creatureWithFlying == "target creature with flying"
#guard EffectTargetKind.noun .opponent == "target opponent"
#guard EffectTargetKind.noun .colorlessNonland ==
  "target colorless nonland permanent"
#guard EffectTargetKind.noun .player == "target player"
#guard EffectTargetKind.noun .opponent == "target opponent"
#guard EffectTargetKind.noun .oppGraveyardCard ==
  "target card from an opponent's graveyard"
#guard EffectTargetKind.spec .none == { count := 0, noun := "", prefer := .own }
#guard EffectTargetKind.spec .playerOrCreature ==
  { count := 1, noun := "any target", prefer := .opponentPlayer }
#guard EffectTargetKind.spec .opponent ==
  { count := 1, noun := "target opponent", prefer := .opponentPlayer }
#guard EffectTargetKind.spec .creatureYouControlThenOppCreature ==
  { count := 2
    noun := "target creature you control and a creature an opponent controls"
    prefer := .ownThenOpponent
    slots := #[.creatureYouControl, .oppCreature] }
#guard EffectTargetKind.slotKind .creatureYouControlThenOppCreature 0 ==
  .creatureYouControl
#guard EffectTargetKind.slotKind .creatureYouControlThenOppCreature 1 ==
  .oppCreature
#guard EffectTargetKind.slotKind .creature 0 == .creature
#guard TriggerEvent.spec .entering ==
  { clause := "this permanent enters", isWhenever := false, label := "enters trigger" }
#guard TriggerEvent.spec .attacking ==
  { clause := "this creature attacks", isWhenever := true, label := "attack trigger" }
#guard TriggerEvent.clause .youScry == "you scry"
#guard TriggerEvent.label .dying == "dies trigger"
#guard TriggerEvent.label .youScry == "scry trigger"
#guard TriggerEvent.label .landYouControlEnters == "landfall trigger"
#guard TriggerEvent.label .becomesBlocked == "becomes-blocked trigger"
#guard TriggerEvent.label .youCastInstantOrSorcery == "cast trigger"
#guard TriggerEvent.label .anotherElfYouControlEnters == "Elf-enters trigger"
#guard TriggerEvent.label .attacking == "attack trigger"
#guard TriggerEvent.label .youAttackWithElves == "attack trigger"
#guard !TriggerEvent.checkTargets .youCastInstantOrSorcery
#guard !TriggerEvent.checkTargets .youAttackWithElves
#guard !TriggerEvent.checkTargets .anotherElfYouControlEnters
#guard TriggerEvent.checkTargets .entering
#guard TriggerEvent.checkTargets .landYouControlEnters
#guard TriggerEvent.checkTargets .attacking
#guard !TriggerEvent.isWhenever .dying
#guard TriggerEvent.isWhenever .youAttackWithElves
#guard SpellEffect.targetCount (.dealDamage 3) == 1
#guard SpellEffect.targetCount .tapOneOrTwoCreatures == 1
#guard SpellEffect.maxTargetCount .tapOneOrTwoCreatures == 2
#guard SpellEffect.targetCount .creatureYouControlDealsPowerToOppCreature == 2
#guard SpellEffect.targetCount .playAdditionalLandThisTurn == 0
#guard SpellEffect.targetCount .destroyArtifactOrLandNonflyersCantBlock == 1
#guard SpellEffect.targetCount .destroyCreature == 1
#guard SpellEffect.targetCount (.drawAndLoseLife 2 2) == 0
#guard SpellEffect.targetKind (.dealDamage 3) == .playerOrCreature
#guard SpellEffect.targetKind (.pump 3 3) == .creature
#guard SpellEffect.targeting (.pump 3 3) == EffectTargeting.of .creature .own
#guard EffectTargetKind.defaultPreference .playerOrCreature == .opponentPlayer
#guard EffectTargetKind.defaultPreference .opponent == .opponentPlayer
#guard EffectTargetKind.defaultPreference .creatureYouControl == .own
#guard EffectTargetKind.defaultPreference .creature == .opponent
#guard SpellEffect.targetKind .destroyCreatureWithFlying == .creatureWithFlying
#guard SpellEffect.targetKind .destroyCreature == .creature
#guard SpellEffect.targetKind .plusOnePlusOneTrampleHexproof == .creatureYouControl
#guard SpellEffect.targetKind (.dealDamageToCreature 5) == .creature
#guard SpellEffect.targetKind (.dealDamageLoseIndestructibleExile 3) == .creature
#guard SpellEffect.targetKind .creatureYouControlDealsPowerToOppCreature ==
  .creatureYouControlThenOppCreature
#guard SpellEffect.targetKind .destroyArtifactOrLandNonflyersCantBlock == .artifactOrLand
#guard SpellEffect.targetKind .playAdditionalLandThisTurn == .none
#guard SpellEffect.targetKind (.destroyTargetCreatureControllerLosesLife 2) == .creature
#guard SpellEffect.targetKind (.allCreaturesGet (-4) (-4)) == .none
#guard SpellEffect.targetKind (.drawAndLoseLife 2 2) == .none
#guard SpellEffect.targetKind (.targetPlayerDrawLoseLife 2 2) == .player
#guard SpellEffect.targetKind (.creaturesTargetPlayerGet (-1) (-1)) == .player
#guard SpellEffect.targetKind .exileGraveyardCreaturesGrantCast == .player
#guard !SpellEffect.requiresTarget (.allCreaturesGet (-4) (-4))
#guard !SpellEffect.requiresTarget (.drawAndLoseLife 2 2)
#guard SpellEffect.requiresTarget (.destroyTargetCreatureControllerLosesLife 2)
#guard SpellEffect.requiresTarget (.targetPlayerDrawLoseLife 2 2)
#guard SpellEffect.castKind (.allCreaturesGet (-4) (-4)) == .massPump
#guard SpellEffect.castKind (.drawAndLoseLife 2 2) == .draw
#guard SpellEffect.castKind (.targetPlayerDrawLoseLife 2 2) == .draw
#guard SpellEffect.preferAsDefaultMode (.pumpAndExileIfDies (-5) (-5))
#guard SpellEffect.requiresTarget (.dealDamage 3)
#guard SpellEffect.requiresTarget (.dealDamageToCreature 5)
#guard SpellEffect.requiresTarget .destroyCreature
#guard SpellEffect.requiresTarget .destroyArtifactOrLandNonflyersCantBlock
#guard SpellEffect.requiresTarget (.dealDamageLoseIndestructibleExile 3)
#guard SpellEffect.targetCount (.dealDamageLoseIndestructibleExile 3) == 1
#guard SpellEffect.requiresTarget .creatureYouControlDealsPowerToOppCreature
#guard !SpellEffect.requiresTarget .playAdditionalLandThisTurn
#guard !SpellEffect.requiresTarget (.drawAndLoseLife 2 2)
#guard SpellEffect.castKind (.dealDamage 3) == .burn
#guard SpellEffect.castKind (.dealDamageToCreature 5) == .creatureDamage
#guard SpellEffect.castKind (.dealDamageLoseIndestructibleExile 3) == .creatureDamage
#guard SpellEffect.castKind .creatureYouControlDealsPowerToOppCreature == .fight
#guard SpellEffect.castKind .destroyCreatureWithFlying == .destroyFlying
#guard SpellEffect.castKind .destroyCreature == .destroyCreature
#guard SpellEffect.castKind .destroyArtifactOrLandNonflyersCantBlock ==
  .destroyArtifactOrLand
#guard SpellEffect.castKind (.pump 3 3) == .pump
#guard SpellEffect.castKind .plusOnePlusOneTrampleHexproof == .pump
#guard SpellEffect.castKind .playAdditionalLandThisTurn == .extraLand
#guard SpellEffect.castKind (.drawAndLoseLife 2 2) == .draw
#guard SpellEffect.preferAsDefaultMode .destroyCreatureWithFlying
#guard !SpellEffect.preferAsDefaultMode .destroyCreature
#guard !SpellEffect.preferAsDefaultMode (.pump 3 3)
#guard !SpellEffect.preferAsDefaultMode .plusOnePlusOneTrampleHexproof
#guard SpellEffect.resolution (.dealDamage 3) == .onPermanent (.dealDamage 3)
#guard SpellEffect.resolution (.pump 3 3) == .onPermanent (.pump 3 3)
#guard SpellEffect.resolution .destroyCreatureWithFlying == .onPermanent .destroy
#guard SpellEffect.resolution .destroyCreature == .onPermanent .destroy
#guard SpellEffect.resolution .playAdditionalLandThisTurn == .extraLand
#guard SpellEffect.resolution (.drawAndLoseLife 2 2) == .drawAndLoseLife 2 2
#guard SpellEffect.resolution .creatureYouControlDealsPowerToOppCreature == .fight
#guard SpellEffect.resolution (.dealDamageToCreature 5) ==
  .onPermanent (.dealDamage 5)
#guard SpellEffect.resolution .destroyArtifactOrLandNonflyersCantBlock ==
  .onPermanent .destroyThenNonflyersCantBlock
#guard
  let c : CardDef := {
    name := "Silent Club"
    types := #[.instant]
    spellEffect := some (.dealDamage 4)
    additionalCostSacrificeArtifactOrCreature := true
  }
  (c.abilitiesText.splitOn "sacrifice an artifact or creature").length > 1 &&
    (c.abilitiesText.splitOn "deals 4 damage").length > 1
#guard (AbilityEffect.toNotation .searchBasicLandTapped).startsWith "Search your library"
#guard AbilityEffect.toNotation (.searchLandTypeToHand "Mountain") ==
  "Search your library for a Mountain card, reveal it, put it into your hand, then shuffle"
#guard AbilityEffect.toNotation (.searchLandTypeToHand "Swamp") ==
  "Search your library for a Swamp card, reveal it, put it into your hand, then shuffle"
#guard !AbilityEffect.requiresTarget (.searchLandTypeToHand "Mountain")
#guard AbilityEffect.resolution (.searchLandTypeToHand "Swamp") ==
  .searchLandTypeToHand "Swamp"
#guard AbilityEffect.toNotation (.dealDamageToTargetCreature 2) ==
  "This creature deals 2 damage to target creature"
#guard AbilityEffect.toNotation .destroyTargetColorlessNonland ==
  "Destroy target colorless nonland permanent"
#guard AbilityEffect.toNotation .attachToTargetCreatureYouControl ==
  "Attach this Equipment to target creature you control"
#guard (AbilityEffect.toNotation .becomeBearCreatureWithLandsPT).startsWith
  "This enchantment becomes a Bear creature"
#guard AbilityEffect.toNotation (.sourceGets 1 0) ==
  "This creature gets +1/+0 until end of turn"
#guard AbilityEffect.toNotation (.putPlusOnePlusOneOnSource 3) ==
  "Put 3 +1/+1 counters on this creature"
#guard AbilityEffect.toNotation (.putPlusOnePlusOneOnSource 1) ==
  "Put a +1/+1 counter on this creature"
#guard AbilityEffect.toNotation .targetCantBeBlockedThisTurn ==
  "Target creature can't be blocked this turn"
#guard AbilityEffect.toNotation .returnFromGraveyardTapped ==
  "Return this card from your graveyard to the battlefield tapped"
#guard AbilityEffect.toNotation .returnFromGraveyardToHand ==
  "Return this card from your graveyard to your hand"
#guard !AbilityEffect.requiresTarget .returnFromGraveyardTapped
#guard !AbilityEffect.requiresTarget .returnFromGraveyardToHand
#guard AbilityEffect.resolution .returnFromGraveyardTapped ==
  .returnFromGraveyardTapped
#guard AbilityEffect.resolution .returnFromGraveyardToHand ==
  .returnFromGraveyardToHand
#guard AbilityEffect.requiresTarget (.dealDamageToTargetCreature 2)
#guard AbilityEffect.requiresTarget .destroyTargetColorlessNonland
#guard AbilityEffect.requiresTarget .attachToTargetCreatureYouControl
#guard AbilityEffect.requiresTarget .targetCantBeBlockedThisTurn
#guard AbilityEffect.targetKind (.dealDamageToTargetCreature 2) == .creature
#guard AbilityEffect.targetKind .destroyTargetColorlessNonland == .colorlessNonland
#guard AbilityEffect.targetKind .attachToTargetCreatureYouControl == .creatureYouControl
#guard AbilityEffect.targeting .targetCantBeBlockedThisTurn ==
  EffectTargeting.of .creature .own
#guard AbilityEffect.targetKind .searchBasicLandTapped == .none
#guard AbilityEffect.targetCount (.dealDamageToTargetCreature 2) == 1
#guard AbilityEffect.targetCount .searchBasicLandTapped == 0
#guard AbilityEffect.castKind (.dealDamageToTargetCreature 2) == .creatureDamage
#guard AbilityEffect.castKind .destroyTargetColorlessNonland == .destroyColorless
#guard AbilityEffect.castKind (.sourceGets 1 0) == .other
#guard AbilityEffect.resolution (.dealDamageToTargetCreature 2) ==
  .onPermanent (.dealDamage 2)
#guard AbilityEffect.resolution .destroyTargetColorlessNonland ==
  .onPermanent .destroy
#guard AbilityEffect.resolution .targetCantBeBlockedThisTurn ==
  .onPermanent .cantBeBlocked
#guard AbilityEffect.resolution (.sourceGets 1 0) == .onSource (.pump 1 0)
#guard AbilityEffect.resolution (.putPlusOnePlusOneOnSource 3) == .onSource (.plusOne 3)
#guard AbilityEffect.resolution .becomeBearCreatureWithLandsPT ==
  .becomeBear
#guard AbilityEffect.resolution .searchBasicLandTapped == .searchBasicLand
#guard !AbilityEffect.requiresTarget .searchBasicLandTapped
#guard !AbilityEffect.requiresTarget .becomeBearCreatureWithLandsPT
#guard !AbilityEffect.requiresTarget (.sourceGets 1 0)
#guard !AbilityEffect.requiresTarget (.putPlusOnePlusOneOnSource 3)
#guard toString Keyword.cantBeBlocked == "can't be blocked"
#guard toString Keyword.menace == "menace"
#guard CardDef.isKeywordRestatement Keyword.menace "Menace"
#guard CardDef.isKeywordRestatement Keyword.menace
  "Menace (This creature can't be blocked except by two or more creatures.)"
#guard !CardDef.isKeywordRestatement Keyword.menace "Flying"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 1, discardSource := true }
    effect := .searchLandTypeToHand "Mountain"
    activateFromHand := true
  }
  toString ab ==
    "{1}, Discard this card: Search your library for a Mountain card, reveal it, put it into your hand, then shuffle (activate only from your hand)"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := .searchBasicLandTapped
  }
  (toString ab).startsWith "{2}, {T}, Sacrifice:"
#guard
  let ab : ActivatedAbility := {
    cost := { payLife := 2 }
    effect := .sourceGets 2 2
    onceEachTurn := true
  }
  toString ab ==
    "Pay 2 life: This creature gets +2/+2 until end of turn (activate only once each turn)"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 1, sacrificeSource := true }
    effect := .dealDamageToTargetCreature 2
    otherModes := #[.destroyTargetColorlessNonland]
  }
  ab.isModal &&
    (toString ab).startsWith "{1}, Sacrifice: Choose one —" &&
    ((toString ab).splitOn "target creature").length > 1 &&
    ((toString ab).splitOn "colorless nonland").length > 1
#guard StaticAbility.toNotation (.otherCreaturesHaveTrample #["Orc", "Goblin"]) ==
  "Other Orcs and Goblins you control have trample."
#guard StaticAbility.toNotation (.otherCreaturesGet #["Elf"] 1 1) ==
  "Other Elf creatures you control get +1/+1."
#guard TapAddForEach.toNotation { mana := .colored .green, subtype := "Elf" } ==
  "{T}: Add {G} for each Elf you control"
#guard StaticAbility.toNotation (.enchantedCreatureGets 3 3) ==
  "Enchanted creature gets +3/+3."
#guard StaticAbility.toNotation (.equippedCreatureGets 2 0) ==
  "Equipped creature gets +2/+0."
#guard StaticAbility.toNotation .powerToughnessEqualLandsYouControl ==
  "This creature's power and toughness are each equal to the number of lands you control."
#guard
  let c : CardDef := { name := "Silent Path", types := #[.creature] }
  c.ptString == "*/*"
#guard
  let c : CardDef := { name := "Silent Aura", types := #[.enchantment] }
  c.ptString == ""
#guard
  let c : CardDef := { name := "Silent Star", types := #[.creature], power := some 2 }
  c.ptString == "2/*"
#guard
  let c : CardDef := { name := "Silent Star", types := #[.creature], toughness := some 3 }
  c.ptString == "*/3"
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #["Goblin", "Orc"]) ==
  "This creature can't block unless you control a Goblin or Orc."
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #[]) ==
  "This creature can't block."
#guard StaticAbility.toNotation (.cantBeBlockedExceptBy 3) ==
  "This creature can't be blocked except by three or more creatures."
#guard StaticAbility.toNotation (.cantBeBlockedExceptBy 2) ==
  "This creature can't be blocked except by two or more creatures."
#guard (StaticAbility.cantBeBlockedExcept? (.cantBeBlockedExceptBy 3)) == some 3
#guard TriggeredAbility.toNotation .onAttackPumpByGreatestPower ==
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
#guard TriggeredAbility.toNotation .onAttackSetOtherBasePT ==
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."
#guard TriggeredAbility.toNotation .onAttackOtherGets2AndTrample ==
  "Whenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn."
#guard TriggeredAbility.toNotation (.onAttackScry 1) ==
  "Whenever this creature attacks, scry 1."
#guard TriggeredAbility.toNotation (.onAttackFerociousGainLife 2) ==
  "Whenever this creature attacks while you control a creature with power 4 or greater, you gain 2 life."
#guard TriggeredAbility.toNotation .onBecomesBlockedDeal1ToBlockers ==
  "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
#guard TriggeredAbility.toNotation (.onEnterScry 2) ==
  "When this permanent enters, scry 2."
#guard TriggeredAbility.toNotation (.onEnterDraw 1) ==
  "When this permanent enters, draw a card."
#guard TriggeredAbility.toNotation (.onEnterDraw 2) ==
  "When this permanent enters, draw 2 cards."
#guard TriggeredAbility.toNotation .onEnterSearchForest ==
  "When this permanent enters, search your library for a Forest card, put that card onto the battlefield, then shuffle."
#guard TriggeredAbility.toNotation (.onEnterMayDiscardDraw 2) ==
  "When this permanent enters, you may discard a card. If you do, draw 2 cards."
#guard TriggeredAbility.toNotation .onEnterTargetOpponentSacrificesCreature ==
  "When this permanent enters, target opponent sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onLandYouControlEntersPlusOnePlusOne ==
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard TriggeredAbility.toNotation .onLandYouControlEntersGets1 ==
  "Whenever a land you control enters, this creature gets +1/+1 until end of turn."
#guard TriggeredAbility.toNotation (.onEnterDealDividedDamage 3 3) ==
  "When this permanent enters, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation (.onEnterOrAttackDealDividedDamage 3 3) ==
  "Whenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation .onEnterOrAttackReturnElfGainLife ==
  "Whenever this creature enters or attacks, return target Elf card from your graveyard to your hand. You gain life equal to that card's power."
#guard TriggeredAbility.toNotation .onDiesDealDamageEqualToPowerToOppCreature ==
  "When this creature dies, it deals damage equal to its power to target creature an opponent controls."
#guard TriggeredAbility.toNotation (.onCastInstantOrSorceryDealDamageToEachOpponent 2) ==
  "Whenever you cast an instant or sorcery spell, this creature deals 2 damage to each opponent."
#guard TriggeredAbility.toNotation (.onAttackWithElvesScry 1) ==
  "Whenever you attack with one or more Elves, scry 1."
#guard TriggeredAbility.toNotation .onScryPumpSelfForEachLookedAt ==
  "Whenever you scry, this creature gets +1/+1 until end of turn for each card looked at while scrying this way."
#guard TriggeredAbility.toNotation .onAnotherElfYouControlEntersGets1 ==
  "Whenever another Elf you control enters, this creature gets +1/+1 until end of turn."
#guard TriggeredAbility.toNotation (.onDiesOppCreatureGets (-1) (-1)) ==
  "When this creature dies, target creature an opponent controls gets -1/-1 until end of turn."
#guard TriggeredAbility.toNotation (.onOneOrMoreOtherCreaturesDieScry 1) ==
  "Whenever one or more other creatures die, scry 1."
#guard TriggeredAbility.toNotation .onEnterTargetOpponentSacrifices ==
  "When this permanent enters, target opponent sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onEnterEachPlayerSacrificesCreature ==
  "When this permanent enters, each player sacrifices a creature of their choice."
#guard TriggeredAbility.toNotation .onEnterEachOpponentDiscards ==
  "When this permanent enters, each opponent discards a card."
#guard TriggeredAbility.toNotation (.onEnterExileOppGyCardOppsLoseLife 2) ==
  "When this permanent enters, exile up to one target card from an opponent's graveyard. Each opponent loses 2 life."
#guard TriggeredAbility.firesOn (.onDiesOppCreatureGets (-1) (-1)) .dying
#guard TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .oneOrMoreOtherCreaturesDie
#guard !TriggeredAbility.firesOn (.onOneOrMoreOtherCreaturesDieScry 1) .dying
#guard TriggeredAbility.firesOn .onEnterEachPlayerSacrificesCreature .entering
#guard TriggeredAbility.requiresTarget (.onDiesOppCreatureGets (-1) (-1))
#guard TriggeredAbility.requiresTarget .onEnterTargetOpponentSacrifices
#guard TriggeredAbility.requiresTarget (.onEnterExileOppGyCardOppsLoseLife 2)
#guard TriggeredAbility.allowsZeroTargets (.onEnterExileOppGyCardOppsLoseLife 2)
#guard !TriggeredAbility.requiresTarget .onEnterEachPlayerSacrificesCreature
#guard !TriggeredAbility.requiresTarget .onEnterEachOpponentDiscards
#guard TriggeredAbility.targetKind (.onDiesOppCreatureGets (-1) (-1)) == .oppCreature
#guard TriggeredAbility.targetKind .onEnterTargetOpponentSacrifices == .opponent
#guard TriggeredAbility.targetKind (.onEnterExileOppGyCardOppsLoseLife 2) ==
  .oppGraveyardCard
#guard TriggerEvent.label .oneOrMoreOtherCreaturesDie == "other-creatures-die trigger"
#guard TriggerEvent.clause .oneOrMoreOtherCreaturesDie ==
  "one or more other creatures die"
#guard !TriggerEvent.checkTargets .oneOrMoreOtherCreaturesDie
#guard TriggeredAbility.dividedDamage? (.onEnterDealDividedDamage 3 3) == some (3, 3)
#guard (TriggeredAbility.dividedDamage? (.onEnterOrAttackDealDividedDamage 3 3)) == some (3, 3)
#guard (TriggeredAbility.dividedDamage? .onEnterOrAttackReturnElfGainLife).isNone
#guard (TriggeredAbility.dividedDamage? .onLandYouControlEntersPlusOnePlusOne).isNone
#guard (TriggeredAbility.dividedDamage? .onLandYouControlEntersGets1).isNone
#guard (TriggeredAbility.dividedDamage? (.onEnterDraw 1)).isNone
#guard (TriggeredAbility.dividedDamage? .onEnterSearchForest).isNone
#guard (TriggeredAbility.dividedDamage? .onEnterTargetOpponentSacrificesCreature).isNone
#guard (TriggeredAbility.dividedDamage? .onDiesDealDamageEqualToPowerToOppCreature).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackSetOtherBasePT).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackOtherGets2AndTrample).isNone
#guard (TriggeredAbility.dividedDamage? (.onAttackScry 1)).isNone
#guard (TriggeredAbility.dividedDamage? (.onAttackFerociousGainLife 2)).isNone
#guard (TriggeredAbility.dividedDamage? (.onCastInstantOrSorceryDealDamageToEachOpponent 2)).isNone
#guard TriggeredAbility.firesOn .onAttackPumpByGreatestPower .attacking
#guard TriggeredAbility.firesOn .onAttackSetOtherBasePT .attacking
#guard TriggeredAbility.firesOn .onAttackOtherGets2AndTrample .attacking
#guard TriggeredAbility.firesOn (.onAttackScry 1) .attacking
#guard TriggeredAbility.firesOn (.onAttackFerociousGainLife 2) .attacking
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .attacking
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .attacking
#guard !TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .attacking
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .attacking
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .attacking
#guard !TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .attacking
#guard TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .youAttackWithElves
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower .youAttackWithElves
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .youAttackWithElves
#guard TriggeredAbility.firesOn .onScryPumpSelfForEachLookedAt .youScry
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .youScry
#guard !TriggeredAbility.firesOn (.onAttackWithElvesScry 1) .youScry
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .youScry
#guard TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 .anotherElfYouControlEnters
#guard !TriggeredAbility.firesOn (.onEnterDraw 1) .anotherElfYouControlEnters
#guard !TriggeredAbility.firesOn .onAnotherElfYouControlEntersGets1 .entering
#guard !TriggeredAbility.requiresTarget .onAnotherElfYouControlEntersGets1
#guard (TriggeredAbility.dividedDamage? .onAnotherElfYouControlEntersGets1).isNone
#guard TriggeredAbility.firesOn .onBecomesBlockedDeal1ToBlockers .becomesBlocked
#guard TriggeredAbility.firesOn (.onEnterScry 2) .entering
#guard TriggeredAbility.firesOn (.onEnterDraw 1) .entering
#guard TriggeredAbility.firesOn .onEnterSearchForest .entering
#guard TriggeredAbility.firesOn (.onEnterMayDiscardDraw 2) .entering
#guard TriggeredAbility.firesOn .onEnterTargetOpponentSacrificesCreature .entering
#guard TriggeredAbility.firesOn (.onEnterDealDividedDamage 3 3) .entering
#guard TriggeredAbility.firesOn (.onEnterOrAttackDealDividedDamage 3 3) .entering
#guard TriggeredAbility.firesOn .onEnterOrAttackReturnElfGainLife .entering
#guard !TriggeredAbility.firesOn .onAttackPumpByGreatestPower .entering
#guard !TriggeredAbility.firesOn (.onAttackScry 1) .entering
#guard TriggeredAbility.firesOn
  (.onCastInstantOrSorceryDealDamageToEachOpponent 2) .youCastInstantOrSorcery
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .youCastInstantOrSorcery
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 3 }
    effect := .attachToTargetCreatureYouControl
    onlyAsSorcery := true
  }
  (toString ab).startsWith "{3}: Attach this Equipment" &&
    (toString ab).endsWith "(activate only as a sorcery)"
#guard TriggeredAbility.firesOn .onLandYouControlEntersPlusOnePlusOne .landYouControlEnters
#guard TriggeredAbility.firesOn .onLandYouControlEntersGets1 .landYouControlEnters
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .landYouControlEnters
#guard TriggeredAbility.requiresTarget .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.requiresTarget .onLandYouControlEntersGets1
#guard TriggeredAbility.targetKind .onLandYouControlEntersPlusOnePlusOne ==
  .creatureYouControl
#guard TriggeredAbility.targetKind .onAttackSetOtherBasePT ==
  .anotherCreatureYouControl
#guard TriggeredAbility.targetKind (.onEnterDealDividedDamage 3 3) ==
  .playerOrCreature
#guard TriggeredAbility.targetKind .onEnterOrAttackReturnElfGainLife ==
  .elfInYourGraveyard
#guard TriggeredAbility.targetKind .onDiesDealDamageEqualToPowerToOppCreature ==
  .oppCreature
#guard TriggeredAbility.targetKind .onEnterTargetOpponentSacrificesCreature ==
  .opponent
#guard TriggeredAbility.targetKind (.onEnterDraw 1) == .none
#guard StaticAbility.hostStatBonus (.enchantedCreatureGets 3 3) == (3, 3)
#guard StaticAbility.hostStatBonus (.equippedCreatureGets 2 0) == (2, 0)
#guard StaticAbility.shape (.enchantedCreatureGets 3 3) ==
  .hostGets "Enchanted creature" 3 3
#guard StaticAbility.shape (.equippedCreatureGets 2 0) ==
  .hostGets "Equipped creature" 2 0
#guard (StaticAbility.StaticShape.spec (.hostGets "Enchanted creature" 3 3)).hostBonus ==
  (3, 3)
#guard (StaticAbility.StaticShape.spec (.lordPump #["Elf"] 1 1)).lordPump ==
  some (#["Elf"], 1, 1)
#guard (StaticAbility.StaticShape.spec (.lordTrample #["Orc"])).trampleSubtypes ==
  some #["Orc"]
#guard (StaticAbility.StaticShape.spec .landsYouControlPT).landsYouControlPT
#guard (StaticAbility.StaticShape.spec (.cantBlockUnless #["Goblin"])).cantBlockUnless ==
  some #["Goblin"]
#guard (StaticAbility.lordPump? (.otherCreaturesGet #["Elf"] 1 1)) == some (#["Elf"], 1, 1)
#guard (StaticAbility.trampleSubtypes? (.otherCreaturesHaveTrample #["Orc"])) == some #["Orc"]
#guard StaticAbility.isLandsYouControlPT .powerToughnessEqualLandsYouControl
#guard !StaticAbility.isLandsYouControlPT (.enchantedCreatureGets 1 1)
#guard (StaticAbility.cantBlockUnless? (.cantBlockUnlessYouControl #["Goblin"])) ==
  some #["Goblin"]
#guard TriggeredAbility.requiresTarget (.onEnterDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget (.onEnterOrAttackDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget .onEnterOrAttackReturnElfGainLife
#guard TriggeredAbility.requiresTarget .onDiesDealDamageEqualToPowerToOppCreature
#guard TriggeredAbility.requiresTarget .onEnterTargetOpponentSacrificesCreature
#guard TriggeredAbility.requiresTarget .onAttackSetOtherBasePT
#guard TriggeredAbility.requiresTarget .onAttackOtherGets2AndTrample
#guard TriggeredAbility.allowsZeroTargets .onAttackSetOtherBasePT
#guard !TriggeredAbility.allowsZeroTargets .onAttackOtherGets2AndTrample
#guard !TriggeredAbility.allowsZeroTargets .onEnterOrAttackReturnElfGainLife
#guard !TriggeredAbility.allowsZeroTargets .onEnterTargetOpponentSacrificesCreature
#guard !TriggeredAbility.allowsZeroTargets .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.allowsZeroTargets .onLandYouControlEntersGets1
#guard TriggeredAbility.firesOn .onDiesDealDamageEqualToPowerToOppCreature .dying
#guard !TriggeredAbility.firesOn (.onEnterScry 2) .dying
#guard !TriggeredAbility.requiresTarget (.onEnterScry 2)
#guard !TriggeredAbility.requiresTarget (.onAttackScry 1)
#guard !TriggeredAbility.requiresTarget (.onAttackFerociousGainLife 2)
#guard !TriggeredAbility.requiresTarget (.onEnterDraw 1)
#guard !TriggeredAbility.requiresTarget .onEnterSearchForest
#guard !TriggeredAbility.requiresTarget .onAnotherElfYouControlEntersGets1
#guard !TriggeredAbility.requiresTarget (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard !TriggeredAbility.requiresTarget (.onAttackWithElvesScry 1)
#guard !TriggeredAbility.requiresTarget .onScryPumpSelfForEachLookedAt
#guard (TriggeredAbility.dividedDamage? (.onAttackWithElvesScry 1)).isNone
#guard (TriggeredAbility.dividedDamage? .onScryPumpSelfForEachLookedAt).isNone
#guard TriggeredAbility.resolution .onAttackPumpByGreatestPower == .pumpGreatestPower
#guard TriggeredAbility.resolution .onAttackSetOtherBasePT == .setOtherBasePT
#guard TriggeredAbility.resolution .onAttackOtherGets2AndTrample ==
  .onPermanent (.pumpAndTrample 2 0)
#guard TriggeredAbility.resolution (.onEnterScry 2) == .scry 2
#guard TriggeredAbility.resolution (.onAttackScry 1) == .scry 1
#guard TriggeredAbility.resolution (.onAttackFerociousGainLife 2) == .gainLife 2
#guard TriggeredAbility.youControlCreatureWithPower? (.onAttackFerociousGainLife 2) == some 4
#guard (TriggeredAbility.youControlCreatureWithPower? (.onAttackScry 1)).isNone
#guard TriggeredAbility.resolution (.onAttackWithElvesScry 1) == .scry 1
#guard TriggeredAbility.resolution (.onEnterDraw 1) == .draw 1
#guard TriggeredAbility.resolution .onEnterSearchForest == .searchForest
#guard TriggeredAbility.resolution .onEnterTargetOpponentSacrificesCreature ==
  .opponentSacrificesCreature
#guard TriggeredAbility.resolution .onLandYouControlEntersGets1 ==
  .onSource (.pump 1 1)
#guard TriggeredAbility.resolution .onLandYouControlEntersPlusOnePlusOne ==
  .onPermanent (.plusOne 1)
#guard TriggeredAbility.resolution .onAnotherElfYouControlEntersGets1 ==
  .onSource (.pump 1 1)
#guard TriggeredAbility.resolution (.onEnterDealDividedDamage 3 3) == .dividedDamage
#guard TriggeredAbility.resolution (.onEnterOrAttackDealDividedDamage 3 3) ==
  .dividedDamage
#guard TriggeredAbility.resolution .onDiesDealDamageEqualToPowerToOppCreature ==
  .damageFromLastKnownPower
#guard TriggeredAbility.resolution (.onCastInstantOrSorceryDealDamageToEachOpponent 2) ==
  .damageEachOpponent 2
#guard
  let instant : CardDef := { name := "Silent Bolt", types := #[.instant] }
  let sorcery : CardDef := { name := "Silent Flame", types := #[.sorcery] }
  let creature : CardDef := { name := "Silent Ogre", types := #[.creature] }
  instant.isInstantOrSorcery && sorcery.isInstantOrSorcery && !creature.isInstantOrSorcery

end CardDef

namespace AdventureFace

/-- Characteristics used while this card is on the stack as an Adventure (CR 715.3b). -/
def toCardDef (a : AdventureFace) : CardDef := {
  name := a.name
  manaCost := a.manaCost
  types := a.types
  subtypes := a.subtypes
  oracleText := a.oracleText
  spellEffect := a.spellEffect
}

/-- True when this Adventure's effect is classified as `k`. -/
def hasCastKind (a : AdventureFace) (k : SpellCastKind) : Bool :=
  a.spellEffect.any (fun e => e.castKind == k)

end AdventureFace

#guard
  let adv : AdventureFace := {
    name := "Spew Flame"
    manaCost := ManaCost.ofGenericAndColor 4 .red
    oracleText := "Spew Flame deals 5 damage to target creature."
    spellEffect := some (.dealDamageToCreature 5)
  }
  let c := adv.toCardDef
  c.name == "Spew Flame" && c.isSorcery && c.requiresTarget &&
    c.hasSubtype "Adventure"

#guard
  let adv : AdventureFace := {
    name := "Till and Tend"
    manaCost := ManaCost.ofGenericAndColor 1 .green
    oracleText := "You may play an additional land this turn."
    spellEffect := some .playAdditionalLandThisTurn
  }
  let c := adv.toCardDef
  c.name == "Till and Tend" && c.isSorcery && !c.requiresTarget &&
    c.hasSubtype "Adventure"

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.hasSupertype .basic

/-- A land card with the given land type (CR 205.3i / 305.7). -/
def isLandTypeCard (c : CardDef) (landType : String) : Bool :=
  c.isLand && c.hasSubtype landType

/-- A card with the Forest land type (CR 205.3i / 305.7). -/
def isForestCard (c : CardDef) : Bool :=
  isLandTypeCard c "Forest"

end Mtg.Engine
