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
  /-- Storied (HOB): if you control three or more artifacts, legendaries,
  and/or Sagas, you have an enduring story for the rest of the game. -/
  storied : Bool := false
  /-- This creature deals both first-strike and regular combat damage (CR 702.4). -/
  doubleStrike : Bool := false
  /-- Prowess (CR 702.108). -/
  prowess : Bool := false
  /-- Ascend (CR 702.131). -/
  ascend : Bool := false
  /-- Shadow (CR 702.27): can block or be blocked by only creatures with shadow. -/
  shadow : Bool := false
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
  ⟨(·.islandwalk), fun k b => { k with islandwalk := b }, "islandwalk"⟩,
  ⟨(·.storied), fun k b => { k with storied := b }, "storied"⟩,
  ⟨(·.doubleStrike), fun k b => { k with doubleStrike := b }, "double strike"⟩,
  ⟨(·.prowess), fun k b => { k with prowess := b }, "prowess"⟩,
  ⟨(·.ascend), fun k b => { k with ascend := b }, "ascend"⟩,
  ⟨(·.shadow), fun k b => { k with shadow := b }, "shadow"⟩
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
def storied : Keywords := { Keywords.none with storied := true }
def doubleStrike : Keywords := { Keywords.none with doubleStrike := true }
def prowess : Keywords := { Keywords.none with prowess := true }
def ascend : Keywords := { Keywords.none with ascend := true }
def shadow : Keywords := { Keywords.none with shadow := true }
end Keyword

/-- A token the engine can create (CR 111). Oracle nouns are fixed so catalog
cards reconstruct printed “create a …” lines. -/
inductive TokenKind where
  | treasure
  | food
  | humanSoldier
  | wolf
  | dwarf
  | bear
  | elf
  | spirit
  | birdSoldier
  | wall
deriving Repr, Inhabited, BEq

namespace TokenKind

def oracleNoun : TokenKind → String
  | .treasure => "Treasure token"
  | .food => "Food token"
  | .humanSoldier => "1/1 white Human Soldier creature token"
  | .wolf => "2/2 green Wolf creature token"
  | .dwarf => "2/2 red Dwarf creature token"
  | .bear => "2/2 green Bear creature token"
  | .elf => "1/1 green Elf creature token"
  | .spirit => "1/1 white Spirit creature token with flying"
  | .birdSoldier => "4/4 white Bird Soldier creature token with flying"
  | .wall => "3/1 colorless Wall artifact creature token with defender named Stone Boulder"

def pluralNoun : TokenKind → String
  | .treasure => "Treasure tokens"
  | .food => "Food tokens"
  | .humanSoldier => "1/1 white Human Soldier creature tokens"
  | .wolf => "2/2 green Wolf creature tokens"
  | .dwarf => "2/2 red Dwarf creature tokens"
  | .bear => "2/2 green Bear creature tokens"
  | .elf => "1/1 green Elf creature tokens"
  | .spirit => "1/1 white Spirit creature tokens with flying"
  | .birdSoldier => "4/4 white Bird Soldier creature tokens with flying"
  | .wall => "3/1 colorless Wall artifact creature tokens with defender named Stone Boulder"

/-- Oracle “create …” clause for `n` tokens of this kind. -/
def createPhrase (k : TokenKind) (n : Nat) (tapped := false) : String :=
  let tappedS := if tapped then "tapped " else ""
  if n == 1 then
    s!"create a {tappedS}{k.oracleNoun}"
  else
    let nWord := if n == 3 then "three" else toString n
    s!"create {nWord} {tappedS}{k.pluralNoun}"

end TokenKind

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
  /-- Target creature with power `n` or greater. -/
  | creaturePowerAtLeast (n : Int)
  /-- Target creature with power `n` or less. -/
  | creaturePowerAtMost (n : Int)
  /-- Target creature you control with any of these subtypes. -/
  | creatureYouControlAnySubtype (subtypes : Array String)
  /-- Target permanent. -/
  | permanent
  /-- Target creature card in your graveyard. -/
  | creatureCardInYourGraveyard
  /-- Target legendary creature you control. -/
  | legendaryCreatureYouControl
  /-- Target creature you control with power `n` or less. -/
  | creatureYouControlPowerAtMost (n : Int)
  /-- Target artifact. -/
  | artifact
  /-- Target artifact token. -/
  | artifactToken
  /-- Target attacking creature. -/
  | attackingCreature
  /-- Target Equipment you control. -/
  | equipmentYouControl
  /-- Target creature or land you control. -/
  | creatureOrLandYouControl
  /-- Two target creatures and/or lands you control. -/
  | twoCreaturesOrLandsYouControl
  /-- Target Equipment you control, then up to one target creature you control. -/
  | equipmentYouControlThenCreatureYouControl
  /-- Two target players (Gleaming Splendor). -/
  | twoPlayers
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
  | .creaturePowerAtLeast n =>
    { noun := s!"target creature with power {n} or greater" }
  | .creaturePowerAtMost n =>
    { noun := s!"target creature with power {n} or less", prefer := .own }
  | .creatureYouControlAnySubtype subtypes =>
    { noun :=
        match subtypes.toList with
        | [] => "target creature you control"
        | [a] => s!"target {a} you control"
        | [a, b] => s!"target {a} or {b} you control"
        | xs =>
          let last := xs.getLast!
          let init := String.intercalate ", " xs.dropLast
          s!"target {init}, or {last} you control"
      prefer := .own }
  | .permanent =>
    { noun := "target permanent", prefer := .ownThenOpponent }
  | .creatureCardInYourGraveyard =>
    { noun := "target creature card from your graveyard", prefer := .last }
  | .legendaryCreatureYouControl =>
    { noun := "target legendary creature you control", prefer := .own }
  | .creatureYouControlPowerAtMost n =>
    { noun := s!"target creature you control with power {n} or less", prefer := .own }
  | .artifact =>
    { noun := "target artifact" }
  | .artifactToken =>
    { noun := "target artifact token" }
  | .attackingCreature =>
    { noun := "target attacking creature", prefer := .own }
  | .equipmentYouControl =>
    { noun := "target Equipment you control", prefer := .own }
  | .creatureOrLandYouControl =>
    { noun := "target creature or land you control", prefer := .own }
  | .twoCreaturesOrLandsYouControl =>
    { count := 2
      noun := "two target creatures and/or lands you control"
      prefer := .own
      slots := #[.creatureOrLandYouControl, .creatureOrLandYouControl] }
  | .equipmentYouControlThenCreatureYouControl =>
    { count := 2
      noun := "target Equipment you control and up to one target creature you control"
      prefer := .own
      slots := #[.equipmentYouControl, .creatureYouControl] }
  | .twoPlayers =>
    { count := 2
      noun := "two target players"
      prefer := .ownThenOpponent
      slots := #[.player, .player] }

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
  /-- Return target spell to its owner's hand, then draw a card (e.g. Reprieve). -/
  | returnSpellDraw
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- Destroy target artifact or enchantment. You gain `life` life. -/
  | destroyArtifactOrEnchantmentGainLife (life : Nat)
  /-- Destroy target creature with power `n` or greater. -/
  | destroyCreaturePowerAtLeast (n : Int)
  /-- Until end of turn, target creature becomes an artifact in addition to
  its other types and gains indestructible. -/
  | becomeArtifactGainIndestructible
  /-- Target creature gets +P/+T and gains these keywords until end of turn. -/
  | pumpAndGrantKeywords (power toughness : Int) (k : Keywords)
  /-- Amass Goblins `n` (CR 701.43). -/
  | amassGoblins (n : Nat)
  /-- You draw a card and lose 1 life, then amass Goblins `n`. -/
  | drawLoseLifeThenAmass (n : Nat)
  /-- Return up to one target creature card from your graveyard to your hand,
  then amass Goblins `n`. -/
  | returnCreatureFromGyThenAmass (n : Nat)
  /-- Counter target spell. If its mana value was `n` or less, recruit. -/
  | counterThenRecruitIfMvAtMost (n : Nat)
  /-- Put `n` +1/+1 counters on target creature you control, then it fights. -/
  | plusOneThenFight (n : Nat)
  /-- Put a +1/+1 counter on target creature you control; if cast from a
  graveyard, also each other creature you control. -/
  | plusOneThenEachOtherIfFromGy
  /-- Draw `n` cards, or `fromGy` if this spell was cast from a graveyard. -/
  | drawIfFromGy (n fromGy : Nat)
  /-- Amass Goblins `n`, or `fromGy` if cast from a graveyard. -/
  | amassGoblinsOrFromGy (n fromGy : Nat)
  /-- Search your library for a legendary creature card, reveal it, put it
  into your hand, then shuffle. -/
  | searchLegendaryCreatureToHand
  /-- Deal `n` damage to each creature opponents control. -/
  | dealDamageToEachOppCreature (n : Nat)
  /-- Destroy target artifact. -/
  | destroyTargetArtifact
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Deal `n` damage to target creature. If it would die this turn, exile it. -/
  | dealDamageToCreatureExileIfDies (n : Nat)
  /-- Destroy target artifact token. -/
  | destroyArtifactToken
  /-- Add {R} for each artifact opponents control. -/
  | addRedPerOppArtifacts
  /-- Deal `n` damage to each non-Dragon creature. -/
  | dealDamageToEachNonDragon (n : Nat)
  /-- Choose a creature type. Return all creatures that aren't of that type. -/
  | chooseTypeReturnOthers
  /-- Draw cards equal to the greatest toughness among creatures you control,
  then put any number of creature cards from your hand onto the battlefield. -/
  | drawEqualToughnessThenPutCreatures
  /-- Mill `n`, then put an instant or sorcery from among them into your hand. -/
  | millThenPutInstantOrSorcery (n : Nat)
  /-- Mill `n`, then put up to `max` land cards from among them into your hand. -/
  | millThenPutLands (n max : Nat)
  /-- Exile the targeted permanents you control, then return them. -/
  | exileThenReturnYouControl
  /-- Deal `n` damage to each non-Dragon, then add four mana that can be
  spent only on Dragon spells. -/
  | dealDamageToEachNonDragonThenAddDragonMana (n : Nat)
  /-- Mill `n`, then put all instant and sorcery cards from among them
  into your hand. -/
  | millThenPutAllInstantsOrSorceries (n : Nat)
  /-- Exile all attacking creatures target player controls. That player
  may search for that many basic lands. -/
  | exileAttackersSearchBasics
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Exile the top `n` cards face down; play them if you control this subtype. -/
  | exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String)
  /-- Return target spell to its owner's hand. If a gift was promised,
  players can't cast spells this turn. -/
  | returnSpellCantCastIfGift
  /-- Exile the top X of target opponent's library; play them this turn,
  paying life equal to mana value. -/
  | exileTopXOppPlayForLife
  /-- Look at the top four; an opponent chooses a pile. -/
  | riddlesInTheDark
  /-- Return this-turn dies-from-battlefield creature cards as Food artifacts. -/
  | supperForSpiders
  /-- Return owned creatures to hand; delayed Bird Soldiers next upkeep. -/
  | eaglesAreComing
  /-- Look at the top `n` cards, put any number of lands onto the battlefield
  tapped, then gain `life` life. -/
  | lookAtTopLandsGainLife (n life : Nat)
  /-- For each opponent, gain control of up to one target artifact they control. -/
  | gainControlOppArtifacts
  /-- Deal damage to each opposing creature equal to other spells' mana value. -/
  | damageOppCreaturesEqualOtherSpellsMv
  /-- Phase out the target, or each of a player's creatures if kicked. -/
  | phaseOutKicker
  /-- Unique printed spell wording. -/
  | printed (text : String)
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
  /-- Until end of turn, this becomes an artifact in addition to its other
  types and gains indestructible. -/
  | becomeArtifactIndestructible
  /-- Until-end-of-turn +P/+T and these keywords. -/
  | pumpAndGrant (power toughness : Int) (k : Keywords)
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
    | .becomeArtifactIndestructible =>
      s!"until end of turn, {noun} becomes an artifact in addition to its other types and gains indestructible"
    | .pumpAndGrant p t k =>
      let joined :=
        match k.toList with
        | [a, b] => s!"{a} and {b}"
        | ks => String.intercalate ", " ks
      s!"{noun} gets {signedStat p}/{signedStat t} and gains {joined} until end of turn"
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
  /-- Return the targeted spell to its owner's hand, then draw a card. -/
  | returnSpellDraw
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
  /-- Destroy the targeted artifact or enchantment; you gain life. -/
  | destroyArtifactOrEnchantmentGainLife (life : Nat)
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Draw a card, lose 1 life, then amass Goblins `n`. -/
  | drawLoseLifeThenAmass (n : Nat)
  /-- Return an optional graveyard creature card, then amass Goblins `n`. -/
  | returnCreatureFromGyThenAmass (n : Nat)
  /-- Counter the targeted spell; recruit if its mana value was `n` or less. -/
  | counterThenRecruitIfMvAtMost (n : Nat)
  /-- +1/+1 counters on the first target, then it fights the second. -/
  | plusOneThenFight (n : Nat)
  /-- +1/+1 on the target; if from the graveyard, also each other. -/
  | plusOneThenEachOtherIfFromGy
  /-- Draw `n`, or `fromGy` if cast from a graveyard. -/
  | drawIfFromGy (n fromGy : Nat)
  /-- Amass Goblins `n`, or `fromGy` if cast from a graveyard. -/
  | amassGoblinsOrFromGy (n fromGy : Nat)
  /-- Search the library for a legendary creature and put it into hand. -/
  | searchLegendaryCreatureToHand
  /-- Deal `n` damage to each creature opponents control. -/
  | dealDamageToEachOppCreature (n : Nat)
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Deal `n` damage; if the creature would die this turn, exile it. -/
  | dealDamageToCreatureExileIfDies (n : Nat)
  /-- Unique printed spell wording. -/
  | printed (text : String)
  /-- Add {R} for each artifact opponents control. -/
  | addRedPerOppArtifacts
  /-- Deal `n` damage to each non-Dragon creature. -/
  | dealDamageToEachNonDragon (n : Nat)
  /-- Choose a creature type and bounce the rest. -/
  | chooseTypeReturnOthers
  /-- Draw equal to greatest toughness, then put creatures onto the battlefield. -/
  | drawEqualToughnessThenPutCreatures
  /-- Mill `n`, then put an instant or sorcery into hand. -/
  | millThenPutInstantOrSorcery (n : Nat)
  /-- Mill `n`, then put up to `max` lands into hand. -/
  | millThenPutLands (n max : Nat)
  /-- Exile targeted permanents you control, then return them. -/
  | exileThenReturnYouControl
  /-- Deal `n` to each non-Dragon, then add Dragon-restricted mana. -/
  | dealDamageToEachNonDragonThenAddDragonMana (n : Nat)
  /-- Mill `n`, then put all instants and sorceries into hand. -/
  | millThenPutAllInstantsOrSorceries (n : Nat)
  /-- Exile attacking creatures; that player may search basics. -/
  | exileAttackersSearchBasics
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Exile the top `n`; play them if you control this subtype. -/
  | exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String)
  /-- Return the targeted spell; if a gift was promised, lock casts. -/
  | returnSpellCantCastIfGift
  /-- Exile the top X of the targeted opponent; play them for life. -/
  | exileTopXOppPlayForLife
  /-- Riddles in the Dark piles. -/
  | riddlesInTheDark
  /-- Return this-turn battlefield-to-gy creatures as Food. -/
  | supperForSpiders
  /-- Bounce owned creatures; delayed Bird Soldiers. -/
  | eaglesAreComing
  /-- Look at the top `n`; put lands onto the battlefield tapped; gain life. -/
  | lookAtTopLandsGainLife (n life : Nat)
  /-- Gain control of targeted opposing artifacts. -/
  | gainControlOppArtifacts
  /-- Damage opposing creatures equal to other spells cast this turn. -/
  | damageOppCreaturesEqualOtherSpellsMv
  /-- Phase out the target, or each of a player's creatures if kicked. -/
  | phaseOutKicker
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
  /-- Zero targets is a legal announcement (CR 115.1c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
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
  | .returnSpellDraw =>
    { targeting := .of .spell, castKind := .counter, resolution := .returnSpellDraw }
  | .creaturesYouControlGet p t =>
    { targeting := .of .none, castKind := .massPump,
      resolution := .creaturesYouControlPump p t }
  | .destroyArtifactOrEnchantmentGainLife n =>
    { targeting := .of .artifactOrEnchantment, castKind := .destroyArtifactOrLand,
      resolution := .destroyArtifactOrEnchantmentGainLife n }
  | .destroyCreaturePowerAtLeast n =>
    { targeting := .of (.creaturePowerAtLeast n), castKind := .destroyCreature,
      preferAsDefaultMode := true, resolution := .onPermanent .destroy }
  | .becomeArtifactGainIndestructible =>
    { targeting := .of .creature, castKind := .pump,
      resolution := .onPermanent .becomeArtifactIndestructible }
  | .pumpAndGrantKeywords p t k =>
    { targeting := .of .creature .own, castKind := .pump,
      resolution := .onPermanent (.pumpAndGrant p t k) }
  | .amassGoblins n =>
    { targeting := .of .none, castKind := .pump, resolution := .amassGoblins n }
  | .drawLoseLifeThenAmass n =>
    { targeting := .of .none, castKind := .draw, resolution := .drawLoseLifeThenAmass n }
  | .returnCreatureFromGyThenAmass n =>
    { targeting := .of .creatureCardInYourGraveyard, castKind := .draw,
      allowsZeroTargets := true, resolution := .returnCreatureFromGyThenAmass n }
  | .counterThenRecruitIfMvAtMost n =>
    { targeting := .of .spell, castKind := .counter,
      resolution := .counterThenRecruitIfMvAtMost n }
  | .plusOneThenFight n =>
    { targeting := .of .creatureYouControlThenOppCreature, castKind := .fight,
      resolution := .plusOneThenFight n }
  | .plusOneThenEachOtherIfFromGy =>
    { targeting := .of .creatureYouControl, castKind := .pump,
      resolution := .plusOneThenEachOtherIfFromGy }
  | .drawIfFromGy n fromGy =>
    { targeting := .of .none, castKind := .draw, resolution := .drawIfFromGy n fromGy }
  | .amassGoblinsOrFromGy n fromGy =>
    { targeting := .of .none, castKind := .pump, resolution := .amassGoblinsOrFromGy n fromGy }
  | .searchLegendaryCreatureToHand =>
    { targeting := .of .none, castKind := .draw, resolution := .searchLegendaryCreatureToHand }
  | .dealDamageToEachOppCreature n =>
    { targeting := .of .none, castKind := .creatureDamage,
      resolution := .dealDamageToEachOppCreature n }
  | .destroyTargetArtifact =>
    { targeting := .of .artifact, castKind := .destroyArtifactOrLand,
      resolution := .onPermanent .destroy }
  | .targetPlayerDraw n =>
    { targeting := .of .player .selfPlayer, castKind := .draw,
      resolution := .targetPlayerDraw n }
  | .dealDamageToCreatureExileIfDies n =>
    { targeting := .of .creature, castKind := .creatureDamage,
      resolution := .dealDamageToCreatureExileIfDies n }
  | .destroyArtifactToken =>
    { targeting := .of .artifactToken, castKind := .destroyArtifactOrLand,
      resolution := .onPermanent .destroy }
  | .addRedPerOppArtifacts =>
    { targeting := .of .none, castKind := .draw, resolution := .addRedPerOppArtifacts }
  | .dealDamageToEachNonDragon n =>
    { targeting := .of .none, castKind := .creatureDamage,
      resolution := .dealDamageToEachNonDragon n }
  | .chooseTypeReturnOthers =>
    { targeting := .of .none, castKind := .counter, resolution := .chooseTypeReturnOthers }
  | .drawEqualToughnessThenPutCreatures =>
    { targeting := .of .none, castKind := .draw,
      resolution := .drawEqualToughnessThenPutCreatures }
  | .millThenPutInstantOrSorcery n =>
    { targeting := .of .none, castKind := .draw, resolution := .millThenPutInstantOrSorcery n }
  | .millThenPutLands n max =>
    { targeting := .of .none, castKind := .draw, resolution := .millThenPutLands n max }
  | .exileThenReturnYouControl =>
    { targeting := .of .twoCreaturesOrLandsYouControl, castKind := .counter,
      resolution := .exileThenReturnYouControl }
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    { targeting := .of .none, castKind := .creatureDamage,
      resolution := .dealDamageToEachNonDragonThenAddDragonMana n }
  | .millThenPutAllInstantsOrSorceries n =>
    { targeting := .of .none, castKind := .draw,
      resolution := .millThenPutAllInstantsOrSorceries n }
  | .exileAttackersSearchBasics =>
    { targeting := .of .player, castKind := .destroyCreature,
      resolution := .exileAttackersSearchBasics }
  | .createTokensX kind =>
    { targeting := .of .none, castKind := .extraLand, resolution := .createTokensX kind }
  | .exileTopPlayIfYouControlSubtype n subtype =>
    { targeting := .of .none, castKind := .draw,
      resolution := .exileTopPlayIfYouControlSubtype n subtype }
  | .returnSpellCantCastIfGift =>
    { targeting := .of .spell, castKind := .counter,
      resolution := .returnSpellCantCastIfGift }
  | .exileTopXOppPlayForLife =>
    { targeting := .of .opponent, castKind := .draw,
      resolution := .exileTopXOppPlayForLife }
  | .riddlesInTheDark =>
    { targeting := .of .none, castKind := .draw, resolution := .riddlesInTheDark }
  | .supperForSpiders =>
    { targeting := .of .none, castKind := .draw, resolution := .supperForSpiders }
  | .eaglesAreComing =>
    { targeting := .of .creatureYouControl, castKind := .draw,
      resolution := .eaglesAreComing }
  | .lookAtTopLandsGainLife n life =>
    { targeting := .of .none, castKind := .draw,
      resolution := .lookAtTopLandsGainLife n life }
  | .gainControlOppArtifacts =>
    { targeting := .of .artifact, castKind := .counter,
      allowsZeroTargets := true, resolution := .gainControlOppArtifacts }
  | .damageOppCreaturesEqualOtherSpellsMv =>
    { targeting := .of .none, castKind := .creatureDamage,
      resolution := .damageOppCreaturesEqualOtherSpellsMv }
  | .phaseOutKicker =>
    { targeting := .of .creature, castKind := .counter, resolution := .phaseOutKicker }
  | .printed text =>
    { targeting := .of .none, castKind := .extraLand, resolution := .printed text }

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

/-- True when zero targets is a legal announcement (CR 115.1c). -/
def allowsZeroTargets (e : SpellEffect) : Bool :=
  e.spec.allowsZeroTargets

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
  | .returnSpellDraw =>
    s!"return {noun} to its owner's hand. Draw a card"
  | .creaturesYouControlPump p t =>
    s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .destroyArtifactOrEnchantmentGainLife n =>
    s!"destroy {noun}. You gain {n} life"
  | .amassGoblins n =>
    s!"amass Goblins {n}"
  | .drawLoseLifeThenAmass n =>
    s!"you draw a card and lose 1 life. Amass Goblins {n}"
  | .returnCreatureFromGyThenAmass n =>
    s!"return up to one {noun} to your hand. Amass Goblins {n}"
  | .counterThenRecruitIfMvAtMost n =>
    s!"counter {noun}. If that spell's mana value was {n} or less, recruit"
  | .plusOneThenFight n =>
    s!"put {plusOnePlusOneCountersPhrase n} on target creature you control. Then it fights target creature an opponent controls"
  | .plusOneThenEachOtherIfFromGy =>
    "put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control"
  | .drawIfFromGy n fromGy =>
    s!"draw {cardPhrase n}. If this spell was cast from a graveyard, draw {cardPhrase fromGy} instead"
  | .amassGoblinsOrFromGy n fromGy =>
    s!"amass Goblins {n}. If this spell was cast from a graveyard, amass Goblins {fromGy} instead"
  | .searchLegendaryCreatureToHand =>
    "search your library for a legendary creature card, reveal it, put it into your hand, then shuffle"
  | .dealDamageToEachOppCreature n =>
    s!"deals {n} damage to each creature your opponents control"
  | .targetPlayerDraw n =>
    s!"{noun} draws {cardPhrase n}"
  | .dealDamageToCreatureExileIfDies n =>
    s!"deals {n} damage to {noun}. If that creature would die this turn, exile it instead"
  | .addRedPerOppArtifacts =>
    "add {R} for each artifact your opponents control"
  | .dealDamageToEachNonDragon n =>
    s!"deals {n} damage to each non-Dragon creature"
  | .chooseTypeReturnOthers =>
    "choose a creature type. Return all creatures that aren't of the chosen type to their owners' hands"
  | .drawEqualToughnessThenPutCreatures =>
    "draw cards equal to the greatest toughness among creatures you control, then put any number of creature cards from your hand onto the battlefield"
  | .millThenPutInstantOrSorcery n =>
    s!"mill {n} cards, then put an instant or sorcery card from among them into your hand"
  | .millThenPutLands n max =>
    let maxWord := if max == 2 then "two" else toString max
    s!"mill {n} cards, then put up to {maxWord} land cards from among them into your hand"
  | .exileThenReturnYouControl =>
    "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control"
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    s!"deals {n} damage to each non-Dragon creature. Add four mana in any combination of colors. Spend this mana only to cast Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    s!"mill {n} cards, then put all instant and sorcery cards from among them into your hand"
  | .exileAttackersSearchBasics =>
    s!"exile all attacking creatures {noun} controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle"
  | .createTokensX kind =>
    s!"create X {kind.pluralNoun}"
  | .exileTopPlayIfYouControlSubtype n subtype =>
    s!"look at the top {n} cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a {subtype}"
  | .returnSpellCantCastIfGift =>
    "return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn"
  | .exileTopXOppPlayForLife =>
    "exile the top X cards of target opponent's library. You may play those cards this turn. If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost"
  | .riddlesInTheDark =>
    "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. An opponent chooses one of the piles. Put that pile into your hand and the other into your graveyard"
  | .supperForSpiders =>
    "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. They are Food artifacts with \"{2}, {T}, Sacrifice this artifact: You gain 3 life.\""
  | .eaglesAreComing =>
    "choose target creature you own. If this spell was kicked, instead choose any number of target creatures you own. Return each chosen creature to your hand. At the beginning of the next upkeep, create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .lookAtTopLandsGainLife n life =>
    s!"look at the top {n} cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle. You gain {life} life"
  | .gainControlOppArtifacts =>
    "for each opponent, gain control of up to one target artifact that player controls"
  | .damageOppCreaturesEqualOtherSpellsMv =>
    "deals damage to each creature your opponents control equal to the total mana value of other spells you've cast this turn"
  | .phaseOutKicker =>
    "target creature phases out. If this spell was kicked, each creature target player controls phases out instead"
  | .printed text => text

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
  /-- Add one mana of any color (e.g. Treasure). -/
  | addAnyColor
  /-- Destroy target permanent. -/
  | destroyTargetPermanent
  /-- Put `n` +1/+1 counters on target creature you control. -/
  | plusOneOnTarget (n : Nat)
  /-- Put `n` +1/+1 counters on target creature you control of this subtype. -/
  | plusOneOnTargetSubtype (n : Nat) (subtype : String)
  /-- Put `n` +1/+1 counters on target creature you control of any listed subtype. -/
  | plusOneOnTargetAnySubtype (n : Nat) (subtypes : Array String)
  /-- Target creature with power `n` or less can't be blocked this turn. -/
  | targetCantBeBlockedPowerAtMost (n : Int)
  /-- Draw `n` cards, then discard a card. -/
  | drawThenDiscardN (n : Nat)
  /-- Create `n` Treasure tokens. -/
  | createTreasure (n : Nat)
  /-- Recruit (draw, discard; if nonland, create a Human Soldier). -/
  | recruit
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat)
  /-- The source's owner shuffles it into their library and draws `n` cards. -/
  | ownerShuffleSourceDraw (n : Nat)
  /-- Return this from the graveyard attached to a creature you control with
  power `n` or less. -/
  | returnFromGyAttachPowerAtMost (n : Int)
  /-- Add these mana types (e.g. `{B}{R}`). -/
  | addMana (types : Array ManaType)
  /-- Search your library for a basic land card, reveal it, put it into your
  hand, then shuffle. -/
  | searchBasicLandToHand
  /-- Create `n` tokens of this kind. `none` means X (as much as was paid). -/
  | createTokensX (kind : TokenKind)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search for up to two basic lands; one enters tapped, one to hand. -/
  | searchTwoBasicsSplit
  /-- Creatures you control get +P/+T. Each opponent loses `life` life. -/
  | creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat)
  /-- Goblins and Orcs you control gain menace until end of turn. -/
  | goblinsAndOrcsGainMenace
  /-- Exile up to two other nonlands you control; return them next end step. -/
  | exileThenReturnNextEnd
  /-- Search a basic land onto the battlefield tapped, then maybe behold an Elf. -/
  | searchBasicBeholdElfUntap
  /-- Two target players each draw a card. -/
  | twoPlayersDraw
  /-- Discard a legendary card with the same name as a legendary you control;
  draw two cards. -/
  | discardLegendarySameNameDraw
  /-- This deals `n` damage to any target. -/
  | dealDamageToAny (n : Nat)
  /-- Draw cards equal to a sacrificed creature's power, then discard a card. -/
  | drawEqualSacrificedPowerThenDiscard
  /-- Arwen: another creature gains indestructible; share +1/+1 and lifelink. -/
  | arwenShare
  /-- Target creature gains a combat-damage-creates-Treasure trigger. -/
  | grantCombatDamageCreateTreasure
  /-- Put a shadow counter on target creature. -/
  | putShadowCounter
  /-- Deal `n` damage to each opponent. -/
  | damageEachOpponent (n : Nat)
  /-- Choose up to two creatures, then destroy the rest. -/
  | chooseTwoDestroyRest
  /-- Target creature can't be blocked by the most-life player's creatures. -/
  | blackGateUnblockable
  /-- Put a burden counter on the source, then draw that many. -/
  | burdenThenDraw
  /-- Creatures you control gain double strike until end of turn. -/
  | teamGainDoubleStrike
  /-- The source gains indestructible until end of turn and becomes tapped. -/
  | sourceGainsIndestructibleTap
  /-- Unique printed activated wording. -/
  | printed (text : String)
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
  /-- Add one mana of any color. -/
  | addAnyColor
  /-- Draw `n` cards, then discard a card. -/
  | drawThenDiscardN (n : Nat)
  /-- Create `n` Treasure tokens. -/
  | createTreasure (n : Nat)
  /-- Recruit. -/
  | recruit
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat)
  /-- Owner shuffles the source into their library and draws `n`. -/
  | ownerShuffleSourceDraw (n : Nat)
  /-- Return from the graveyard attached to the targeted creature. -/
  | returnFromGyAttach
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Search for a basic land and put it into hand. -/
  | searchBasicLandToHand
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Search two basics; one tapped, one to hand. -/
  | searchTwoBasicsSplit
  /-- Team pump and opponents lose life. -/
  | creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat)
  /-- Goblins and Orcs you control gain menace. -/
  | goblinsAndOrcsGainMenace
  /-- Exile then return at the next end step. -/
  | exileThenReturnNextEnd
  /-- Search a basic tapped, then behold an Elf to untap it. -/
  | searchBasicBeholdElfUntap
  /-- Two players each draw. -/
  | twoPlayersDraw
  /-- Discard a same-name legendary; draw two. -/
  | discardLegendarySameNameDraw
  /-- Deal `n` to any target. -/
  | dealDamageToAny (n : Nat)
  /-- Draw equal to sacrificed power, then discard. -/
  | drawEqualSacrificedPowerThenDiscard
  /-- Arwen share. -/
  | arwenShare
  /-- Grant a combat-damage Treasure trigger. -/
  | grantCombatDamageCreateTreasure
  /-- Put a shadow counter. -/
  | putShadowCounter
  /-- Damage each opponent. -/
  | damageEachOpponent (n : Nat)
  /-- Choose two, destroy the rest. -/
  | chooseTwoDestroyRest
  /-- Black Gate unblockable. -/
  | blackGateUnblockable
  /-- Burden then draw. -/
  | burdenThenDraw
  /-- Team double strike. -/
  | teamGainDoubleStrike
  /-- Source gains indestructible and taps. -/
  | sourceGainsIndestructibleTap
  /-- Unique printed activated wording. -/
  | printed (text : String)
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
  | .addAnyColor =>
    { resolution := .addAnyColor }
  | .destroyTargetPermanent =>
    { targeting := .of .permanent, castKind := .destroyColorless,
      resolution := .onPermanent .destroy }
  | .plusOneOnTarget n =>
    { targeting := .of .creatureYouControl, resolution := .onPermanent (.plusOne n) }
  | .plusOneOnTargetSubtype n subtype =>
    { targeting := .of (.creatureYouControlSubtype subtype),
      resolution := .onPermanent (.plusOne n) }
  | .plusOneOnTargetAnySubtype n subtypes =>
    { targeting := .of (.creatureYouControlAnySubtype subtypes),
      resolution := .onPermanent (.plusOne n) }
  | .targetCantBeBlockedPowerAtMost n =>
    { targeting := .of (.creaturePowerAtMost n),
      resolution := .onPermanent .cantBeBlocked }
  | .drawThenDiscardN n =>
    { resolution := .drawThenDiscardN n }
  | .createTreasure n =>
    { resolution := .createTreasure n }
  | .recruit =>
    { resolution := .recruit }
  | .scry n =>
    { resolution := .scry n }
  | .gainLife n =>
    { resolution := .gainLife n }
  | .createTokens kind n =>
    { resolution := .createTokens kind n }
  | .ownerShuffleSourceDraw n =>
    { resolution := .ownerShuffleSourceDraw n }
  | .returnFromGyAttachPowerAtMost n =>
    { targeting := .of (.creatureYouControlPowerAtMost n),
      resolution := .returnFromGyAttach }
  | .addMana types =>
    { resolution := .addMana types }
  | .searchBasicLandToHand =>
    { resolution := .searchBasicLandToHand }
  | .createTokensX kind =>
    { resolution := .createTokensX kind }
  | .draw n =>
    { resolution := .draw n }
  | .searchTwoBasicsSplit =>
    { resolution := .searchTwoBasicsSplit }
  | .creaturesYouControlGetOppsLoseLife p t life =>
    { resolution := .creaturesYouControlGetOppsLoseLife p t life }
  | .goblinsAndOrcsGainMenace =>
    { resolution := .goblinsAndOrcsGainMenace }
  | .exileThenReturnNextEnd =>
    { targeting := .of .twoCreaturesOrLandsYouControl,
      resolution := .exileThenReturnNextEnd }
  | .searchBasicBeholdElfUntap =>
    { resolution := .searchBasicBeholdElfUntap }
  | .twoPlayersDraw =>
    { targeting := .of .twoPlayers, resolution := .twoPlayersDraw }
  | .discardLegendarySameNameDraw =>
    { resolution := .discardLegendarySameNameDraw }
  | .dealDamageToAny n =>
    { targeting := .of .playerOrCreature, castKind := .creatureDamage,
      resolution := .dealDamageToAny n }
  | .drawEqualSacrificedPowerThenDiscard =>
    { resolution := .drawEqualSacrificedPowerThenDiscard }
  | .arwenShare =>
    { targeting := .of .anotherCreature, resolution := .arwenShare }
  | .grantCombatDamageCreateTreasure =>
    { targeting := .of .creature, resolution := .grantCombatDamageCreateTreasure }
  | .putShadowCounter =>
    { targeting := .of .creature, resolution := .putShadowCounter }
  | .damageEachOpponent n =>
    { resolution := .damageEachOpponent n }
  | .chooseTwoDestroyRest =>
    { targeting := .of .creature, resolution := .chooseTwoDestroyRest }
  | .blackGateUnblockable =>
    { targeting := .of .creature, resolution := .blackGateUnblockable }
  | .burdenThenDraw =>
    { resolution := .burdenThenDraw }
  | .teamGainDoubleStrike =>
    { resolution := .teamGainDoubleStrike }
  | .sourceGainsIndestructibleTap =>
    { resolution := .sourceGainsIndestructibleTap }
  | .printed text =>
    { resolution := .printed text }

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
  | .addAnyColor =>
    "Add one mana of any color"
  | .drawThenDiscardN n =>
    s!"Draw {cardPhrase n}, then discard a card"
  | .createTreasure n =>
    if n == 1 then "Create a Treasure token"
    else s!"Create {n} Treasure tokens"
  | .recruit =>
    "Recruit"
  | .scry n =>
    s!"Scry {n}"
  | .gainLife n =>
    s!"You gain {n} life"
  | .createTokens kind n =>
    capitalizeAscii (TokenKind.createPhrase kind n)
  | .ownerShuffleSourceDraw n =>
    s!"This owner shuffles him into their library and draws {cardPhrase n}"
  | .returnFromGyAttach =>
    s!"Return this card from your graveyard to the battlefield attached to {noun}"
  | .addMana types =>
    let parts := types.toList.map (fun t => s!"\{{t.letter}}")
    s!"Add {String.intercalate "" parts}"
  | .searchBasicLandToHand =>
    "Search your library for a basic land card, reveal it, put it into your hand, then shuffle"
  | .createTokensX kind =>
    s!"Create X {kind.pluralNoun}"
  | .draw n =>
    s!"Draw {cardPhrase n}"
  | .searchTwoBasicsSplit =>
    "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"
  | .creaturesYouControlGetOppsLoseLife p t life =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn. Each opponent loses {life} life"
  | .goblinsAndOrcsGainMenace =>
    "Goblins and Orcs you control gain menace until end of turn"
  | .exileThenReturnNextEnd =>
    "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"
  | .searchBasicBeholdElfUntap =>
    "Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land"
  | .twoPlayersDraw =>
    "Two target players each draw a card"
  | .discardLegendarySameNameDraw =>
    "Draw two cards"
  | .dealDamageToAny n =>
    s!"This creature deals {n} damage to any target"
  | .drawEqualSacrificedPowerThenDiscard =>
    "Draw cards equal to the sacrificed creature's power, then discard a card"
  | .arwenShare =>
    "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"
  | .grantCombatDamageCreateTreasure =>
    "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
  | .putShadowCounter =>
    "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"
  | .damageEachOpponent n =>
    s!"This deals {n} damage to each opponent"
  | .chooseTwoDestroyRest =>
    "Choose up to two creatures, then destroy the rest"
  | .blackGateUnblockable =>
    "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"
  | .burdenThenDraw =>
    "Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring"
  | .teamGainDoubleStrike =>
    "Creatures you control gain double strike until end of turn"
  | .sourceGainsIndestructibleTap =>
    "Witch-king of Angmar gains indestructible until end of turn. Tap him"
  | .printed text => text

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
  /-- Sacrifice another permanent you control of this subtype. -/
  sacrificeAnotherSubtype : Option String := none
  /-- Discard a card (not necessarily this card). -/
  discardACard : Bool := false
  /-- Tap an untapped creature you control. -/
  tapAnUntappedCreatureYouControl : Bool := false
  /-- Remove an indestructible counter from the source (Arwen). -/
  removeIndestructibleCounter : Bool := false
  /-- Sacrifice a legendary artifact you control (Mount Doom). -/
  sacrificeLegendaryArtifact : Bool := false
  /-- Discard a legendary card with the same name as a legendary you control. -/
  discardLegendarySameName : Bool := false
  /-- Sacrifice an artifact you control (Stone-Giant). -/
  sacrificeArtifact : Bool := false
deriving Repr, Inhabited, BEq

namespace ActivationCost

def toNotation (c : ActivationCost) : String :=
  let parts : List String :=
    (if c.mana.symbols.isEmpty then [] else [toString c.mana]) ++
    (if c.tap then ["{T}"] else []) ++
    (if c.payLife != 0 then [s!"Pay {c.payLife} life"] else []) ++
    (if c.discardSource then ["Discard this card"] else []) ++
    (if c.sacrificeSource && c.sacrificeLegendaryArtifact then
      ["Sacrifice Mount Doom and a legendary artifact"]
     else if c.sacrificeSource then ["Sacrifice"]
     else []) ++
    (if c.sacrificeAnotherCreatureOrArtifact then
      ["Sacrifice another creature or artifact"]
     else []) ++
    (if c.sacrificeArtifact && !(c.sacrificeSource && c.sacrificeLegendaryArtifact) then
      ["Sacrifice an artifact"]
     else []) ++
    (match c.sacrificeAnotherSubtype with
     | some t => [s!"Sacrifice another {t}"]
     | none => []) ++
    (if c.discardACard then ["Discard a card"] else []) ++
    (if c.tapAnUntappedCreatureYouControl then
      ["Tap an untapped creature you control"] else []) ++
    (if c.removeIndestructibleCounter then
      ["Remove an indestructible counter from Arwen"] else []) ++
    (if c.sacrificeLegendaryArtifact && !c.sacrificeSource then
      ["Sacrifice a legendary artifact"] else []) ++
    (if c.discardLegendarySameName then
      ["Discard a legendary card with the same name as a legendary permanent you control"]
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
  /-- This ability costs this much generic mana less for each Equipment you
  control. -/
  costReductionPerEquipment : Nat := 0
  /-- “Activate only if you attacked with two or more creatures this turn.” -/
  onlyIfYouAttackedWithTwoOrMore : Bool := false
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
      " (activate only if you control a legendary creature)" else "") ++
    (if ab.onlyIfYouAttackedWithTwoOrMore then
      " (activate only if you attacked with two or more creatures this turn)" else "")
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
  /-- Equipped creature has these keywords. -/
  | equippedCreatureHasKeywords (k : Keywords)
  /-- Enchanted creature gets +P/+T and has these keywords. -/
  | enchantedCreatureGetsAndHas (power toughness : Int) (k : Keywords)
  /-- This creature can't be blocked by tokens. -/
  | cantBeBlockedByTokens
  /-- This creature's power is equal to the number of creatures you control. -/
  | powerEqualCreaturesYouControl
  /-- Armies you control have trample. -/
  | armiesYouControlHaveTrample
  /-- Creatures you control (including this) get +P/+T. -/
  | creaturesYouControlGet (power toughness : Int)
  /-- This has haste as long as you control another permanent of this subtype. -/
  | hasteIfYouControlOtherSubtype (subtype : String)
  /-- This can't attack unless you control `n` or more other permanents of
  this subtype. -/
  | cantAttackUnlessYouControlNOther (n : Nat) (subtype : String)
  /-- Legendary creatures you control get +P/+T and have ward `{w}`. -/
  | legendaryCreaturesGetAndWard (power toughness : Int) (ward : Nat)
  /-- Nonlegendary creatures you control get +P/+T. -/
  | nonlegendaryCreaturesGet (power toughness : Int)
  /-- Equipped creature gets +P/+T and has these keywords. -/
  | equippedCreatureGetsAndHas (power toughness : Int) (k : Keywords)
  /-- Equipped creature gets +P/+T and has ward `{w}`. -/
  | equippedCreatureGetsAndWard (power toughness : Int) (ward : Nat)
  /-- Each creature you control with a +1/+1 counter has menace. -/
  | creaturesYouControlWithPlusOneHaveMenace
  /-- This has lifelink as long as you control another of this subtype. -/
  | lifelinkIfYouControlOtherSubtype (subtype : String)
  /-- Threshold — this gets +P/+T if there are seven or more cards in your
  graveyard. -/
  | thresholdGets (power toughness : Int)
  /-- This can't be blocked by creatures with power `n` or less. -/
  | cantBeBlockedByPowerAtMost (n : Int)
  /-- During your turn, equipped creatures you control have these keywords. -/
  | equippedCreaturesHaveKeywordsDuringYourTurn (k : Keywords)
  /-- As long as you have an enduring story, this gets +P/+T and has these
  keywords. -/
  | getsAndHasIfEnduringStory (power toughness : Int) (k : Keywords)
  /-- As long as you have an enduring story, creatures you control get +P/+T. -/
  | creaturesYouControlGetIfEnduringStory (power toughness : Int)
  /-- This doesn't untap during your untap step unless you have an enduring
  story. -/
  | doesntUntapUnlessEnduringStory
  /-- As long as you have an enduring story, artifacts and creatures you
  control have ward `{w}`. -/
  | artifactsAndCreaturesHaveWardIfEnduringStory (ward : Nat)
  /-- As long as you have an enduring story, creatures can't attack you unless
  their controller pays `{n}` for each. -/
  | creaturesCantAttackYouUnlessPayIfEnduringStory (n : Nat)
  /-- Other permanents of these subtypes have `{T}: Add one of these types`. -/
  | otherSubtypeHaveTapAddOneOf (subtypes : Array String) (mana : Array ManaType)
  /-- This can't be blocked by creatures with power `n` or greater. -/
  | cantBeBlockedByPowerAtLeast (n : Int)
  /-- Equipped creature has these keywords and can't be blocked. -/
  | equippedCreatureHasKeywordsAndCantBeBlocked (k : Keywords)
  /-- Equip abilities that target this cost `{n}` less. -/
  | equipAbilitiesTargetingThisCostLess (n : Nat)
  /-- As long as you have an enduring story, the first equip each turn is `{0}`. -/
  | firstEquipFreeIfEnduringStory
  /-- Creatures you control of the chosen type get +P/+T. -/
  | chosenTypeCreaturesGet (power toughness : Int)
  /-- Instant and sorcery spells cost {X} less, X = equipped creature's power. -/
  | instantSorceryCostReductionEqualEquippedPower
  /-- Other permanents of this subtype get +P/+0 for each artifact token. -/
  | otherSubtypeGetPowerPerArtifactToken (subtype : String)
  /-- As long as you have an enduring story, Dwarf triggers go twice. -/
  | extraTriggerIfEnduringStorySubtype (subtype : String)
  /-- If a triggered ability of another matching permanent you control
  triggers, it triggers an additional time (e.g. Chief of the Wilds). -/
  | extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool)
  /-- Enchanted creature loses all abilities and doesn't untap. -/
  | enchantedLosesAbilitiesDoesntUntap
  /-- During your turn, equipped creature has hexproof and can't be blocked. -/
  | equippedHexproofUnblockableDuringYourTurn
  /-- If a triggered ability of equipped creature triggers, it triggers again. -/
  | equippedTriggersAgain
  /-- Equipped creature has first strike and gets +1/+0 per instant/sorcery
  in your graveyard. -/
  | equippedFirstStrikePlusPerInstantSorcery
  /-- This gets +P/+0 for each graveyard with seven or more cards. -/
  | powerPerFatGraveyard (power : Int)
  /-- If an opposing creature would die, exile it and create a Wolf. -/
  | exileOppDeathCreateWolf
  /-- This has all activated abilities of cards of this subtype in your
  graveyard. -/
  | copyActivatedFromGySubtype (subtype : String)
  /-- Equipped creature gets +P/+T and has trample and a combat Treasure
  trigger. -/
  | equippedGetsTrampleAndCombatTreasures (power toughness : Int)
  /-- Ward — discard an enchantment, instant, or sorcery card. -/
  | wardDiscardEnchantmentInstantOrSorcery
  /-- Ward — sacrifice a legendary artifact or legendary creature. -/
  | wardSacrificeLegendary
  /-- Unique printed static wording. -/
  | printed (text : String)
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
  /-- Equipped or enchanted host has these keywords, and optionally +P/+T. -/
  | hostKeywords (host : String) (k : Keywords) (power toughness : Int)
  /-- This creature can't be blocked by tokens. -/
  | cantBeBlockedByTokens
  /-- Characteristic-defining power equal to creatures you control. -/
  | creaturesYouControlPower
  /-- Creatures you control of this subtype have trample. -/
  | youControlSubtypeTrample (subtype : String)
  /-- Creatures you control get +P/+T (includes the source). -/
  | teamPump (power toughness : Int) (legendaryOnly nonlegendaryOnly : Bool)
  /-- This has haste while you control another of this subtype. -/
  | hasteIfOtherSubtype (subtype : String)
  /-- This can't attack unless you control `n` other permanents of this subtype. -/
  | cantAttackUnlessNOther (n : Nat) (subtype : String)
  /-- Legendary creatures you control get +P/+T and have ward `{w}`. -/
  | legendaryTeamPumpWard (power toughness : Int) (ward : Nat)
  /-- Equipped/enchanted host gets +P/+T and has ward `{w}`. -/
  | hostGetsAndWard (host : String) (power toughness : Int) (ward : Nat)
  /-- Creatures you control with a +1/+1 counter have menace. -/
  | creaturesWithPlusOneHaveMenace
  /-- This has lifelink while you control another of this subtype. -/
  | lifelinkIfOtherSubtype (subtype : String)
  /-- Threshold +P/+T. -/
  | thresholdGets (power toughness : Int)
  /-- Can't be blocked by creatures with power `n` or less. -/
  | cantBeBlockedByPowerAtMost (n : Int)
  /-- During your turn, equipped creatures you control have these keywords. -/
  | equippedTeamKeywordsDuringYourTurn (k : Keywords)
  /-- Enduring-story self pump and keywords. -/
  | selfIfEnduringStory (power toughness : Int) (k : Keywords)
  /-- Enduring-story team pump. -/
  | teamIfEnduringStory (power toughness : Int)
  /-- Doesn't untap unless enduring story. -/
  | doesntUntapUnlessEnduringStory
  /-- Artifacts and creatures you control have ward if enduring story. -/
  | teamWardIfEnduringStory (ward : Nat)
  /-- Attack tax if enduring story. -/
  | attackTaxIfEnduringStory (n : Nat)
  /-- Other matching permanents have a tap-add-one-of mana ability. -/
  | otherSubtypeTapAddOneOf (subtypes : Array String) (mana : Array ManaType)
  /-- Can't be blocked by creatures with power `n` or greater. -/
  | cantBeBlockedByPowerAtLeast (n : Int)
  /-- Equipped creature has keywords and can't be blocked. -/
  | equippedKeywordsAndUnblockable (k : Keywords)
  /-- Equip abilities targeting this cost less. -/
  | equipTargetingThisCostLess (n : Nat)
  /-- First equip each turn is free if enduring story. -/
  | firstEquipFreeIfEnduringStory
  /-- Chosen-type team pump. -/
  | chosenTypePump (power toughness : Int)
  /-- Instant/sorcery cost reduction equal to equipped power. -/
  | instantSorceryCostReductionEqualEquippedPower
  /-- Other matching creatures get +P/+0 per artifact token. -/
  | otherSubtypePowerPerArtifactToken (subtype : String)
  | extraTriggerIfEnduringStorySubtype (subtype : String)
  | extraTriggerAnotherYouControl (subtypes : Array String) (includeBattles : Bool)
  | enchantedLosesAbilitiesDoesntUntap
  | equippedHexproofUnblockableDuringYourTurn
  | equippedTriggersAgain
  | equippedFirstStrikePlusPerInstantSorcery
  | powerPerFatGraveyard (power : Int)
  | exileOppDeathCreateWolf
  | copyActivatedFromGySubtype (subtype : String)
  | equippedGetsTrampleAndCombatTreasures (power toughness : Int)
  | wardDiscardEnchantmentInstantOrSorcery
  | wardSacrificeLegendary
  | printed (text : String)
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
  hostKeywords : Keywords := Keywords.none
  cantBeBlockedByTokens : Bool := false
  creaturesYouControlPower : Bool := false
  /-- Lord pump includes the source (not only other creatures). -/
  lordIncludesSelf : Bool := false
  /-- Lord pump applies only to legendary creatures. -/
  lordLegendaryOnly : Bool := false
  /-- Lord pump applies only to nonlegendary creatures. -/
  lordNonlegendaryOnly : Bool := false
  /-- Ward cost this ability grants matching creatures. -/
  grantedWard : Option Nat := none
  /-- This has haste while you control another of this subtype. -/
  hasteIfOtherSubtype : Option String := none
  /-- Can't attack unless you control this many other permanents of the subtype. -/
  cantAttackUnlessNOther : Option (Nat × String) := none
  /-- Creatures you control with a +1/+1 counter have menace. -/
  creaturesWithPlusOneHaveMenace : Bool := false
  /-- This has lifelink while you control another of this subtype. -/
  lifelinkIfOtherSubtype : Option String := none
  /-- Threshold +P/+T if seven or more cards in graveyard. -/
  thresholdGets : Option (Int × Int) := none
  /-- Can't be blocked by creatures with power at most this. -/
  cantBeBlockedByPowerAtMost : Option Int := none
  /-- During your turn, equipped creatures you control have these keywords. -/
  equippedTeamKeywordsDuringYourTurn : Keywords := Keywords.none
  /-- Enduring-story self pump. -/
  selfIfEnduringStory : Option (Int × Int × Keywords) := none
  /-- Enduring-story team pump. -/
  teamIfEnduringStory : Option (Int × Int) := none
  /-- Doesn't untap unless enduring story. -/
  doesntUntapUnlessEnduringStory : Bool := false
  /-- Team ward if enduring story. -/
  teamWardIfEnduringStory : Option Nat := none
  /-- Attack tax `{n}` if enduring story. -/
  attackTaxIfEnduringStory : Option Nat := none
  /-- Can't be blocked by creatures with power at least this. -/
  cantBeBlockedByPowerAtLeast : Option Int := none
  /-- Equipped creature also can't be blocked. -/
  equippedCantBeBlocked : Bool := false
  /-- Equip abilities targeting this cost this much less. -/
  equipTargetingThisCostLess : Option Nat := none
  /-- First equip is free if enduring story. -/
  firstEquipFreeIfEnduringStory : Bool := false
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
  | .hostKeywords _ k p t => { hostKeywords := k, hostBonus := (p, t) }
  | .cantBeBlockedByTokens => { cantBeBlockedByTokens := true }
  | .creaturesYouControlPower => { creaturesYouControlPower := true }
  | .youControlSubtypeTrample subtype => { trampleSubtypes := some #[subtype] }
  | .teamPump p t legendaryOnly nonlegendaryOnly =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true,
      lordLegendaryOnly := legendaryOnly, lordNonlegendaryOnly := nonlegendaryOnly }
  | .hasteIfOtherSubtype subtype => { hasteIfOtherSubtype := some subtype }
  | .cantAttackUnlessNOther n subtype => { cantAttackUnlessNOther := some (n, subtype) }
  | .legendaryTeamPumpWard p t w =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true, lordLegendaryOnly := true,
      grantedWard := some w }
  | .hostGetsAndWard _ p t w =>
    { hostBonus := (p, t), grantedWard := some w }
  | .creaturesWithPlusOneHaveMenace =>
    { creaturesWithPlusOneHaveMenace := true }
  | .lifelinkIfOtherSubtype subtype =>
    { lifelinkIfOtherSubtype := some subtype }
  | .thresholdGets p t =>
    { thresholdGets := some (p, t) }
  | .cantBeBlockedByPowerAtMost n =>
    { cantBeBlockedByPowerAtMost := some n }
  | .equippedTeamKeywordsDuringYourTurn k =>
    { equippedTeamKeywordsDuringYourTurn := k }
  | .selfIfEnduringStory p t k =>
    { selfIfEnduringStory := some (p, t, k) }
  | .teamIfEnduringStory p t =>
    { teamIfEnduringStory := some (p, t) }
  | .doesntUntapUnlessEnduringStory =>
    { doesntUntapUnlessEnduringStory := true }
  | .teamWardIfEnduringStory w =>
    { teamWardIfEnduringStory := some w }
  | .attackTaxIfEnduringStory n =>
    { attackTaxIfEnduringStory := some n }
  | .otherSubtypeTapAddOneOf _ _ => {}
  | .cantBeBlockedByPowerAtLeast n =>
    { cantBeBlockedByPowerAtLeast := some n }
  | .equippedKeywordsAndUnblockable k =>
    { hostKeywords := k, equippedCantBeBlocked := true }
  | .equipTargetingThisCostLess n =>
    { equipTargetingThisCostLess := some n }
  | .firstEquipFreeIfEnduringStory =>
    { firstEquipFreeIfEnduringStory := true }
  | .chosenTypePump p t =>
    { lordPump := some (#[], p, t), lordIncludesSelf := true }
  | .instantSorceryCostReductionEqualEquippedPower => {}
  | .otherSubtypePowerPerArtifactToken _ => {}
  | .extraTriggerIfEnduringStorySubtype _ => {}
  | .extraTriggerAnotherYouControl _ _ => {}
  | .enchantedLosesAbilitiesDoesntUntap => {}
  | .equippedHexproofUnblockableDuringYourTurn => {}
  | .equippedTriggersAgain => {}
  | .equippedFirstStrikePlusPerInstantSorcery => {}
  | .powerPerFatGraveyard _ => {}
  | .exileOppDeathCreateWolf => {}
  | .copyActivatedFromGySubtype _ => {}
  | .equippedGetsTrampleAndCombatTreasures p t =>
    { hostBonus := (p, t) }
  | .wardDiscardEnchantmentInstantOrSorcery => {}
  | .wardSacrificeLegendary => {}
  | .printed _ => {}

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
  | .equippedCreatureHasKeywords k => .hostKeywords "Equipped creature" k 0 0
  | .enchantedCreatureGetsAndHas p t k => .hostKeywords "Enchanted creature" k p t
  | .cantBeBlockedByTokens => .cantBeBlockedByTokens
  | .powerEqualCreaturesYouControl => .creaturesYouControlPower
  | .armiesYouControlHaveTrample => .youControlSubtypeTrample "Army"
  | .creaturesYouControlGet p t => .teamPump p t false false
  | .hasteIfYouControlOtherSubtype subtype => .hasteIfOtherSubtype subtype
  | .cantAttackUnlessYouControlNOther n subtype => .cantAttackUnlessNOther n subtype
  | .legendaryCreaturesGetAndWard p t w => .legendaryTeamPumpWard p t w
  | .nonlegendaryCreaturesGet p t => .teamPump p t false true
  | .equippedCreatureGetsAndHas p t k => .hostKeywords "Equipped creature" k p t
  | .equippedCreatureGetsAndWard p t w => .hostGetsAndWard "Equipped creature" p t w
  | .creaturesYouControlWithPlusOneHaveMenace => .creaturesWithPlusOneHaveMenace
  | .lifelinkIfYouControlOtherSubtype subtype => .lifelinkIfOtherSubtype subtype
  | .thresholdGets p t => .thresholdGets p t
  | .cantBeBlockedByPowerAtMost n => .cantBeBlockedByPowerAtMost n
  | .equippedCreaturesHaveKeywordsDuringYourTurn k =>
    .equippedTeamKeywordsDuringYourTurn k
  | .getsAndHasIfEnduringStory p t k => .selfIfEnduringStory p t k
  | .creaturesYouControlGetIfEnduringStory p t => .teamIfEnduringStory p t
  | .doesntUntapUnlessEnduringStory => .doesntUntapUnlessEnduringStory
  | .artifactsAndCreaturesHaveWardIfEnduringStory w => .teamWardIfEnduringStory w
  | .creaturesCantAttackYouUnlessPayIfEnduringStory n => .attackTaxIfEnduringStory n
  | .otherSubtypeHaveTapAddOneOf subtypes mana =>
    .otherSubtypeTapAddOneOf subtypes mana
  | .cantBeBlockedByPowerAtLeast n => .cantBeBlockedByPowerAtLeast n
  | .equippedCreatureHasKeywordsAndCantBeBlocked k =>
    .equippedKeywordsAndUnblockable k
  | .equipAbilitiesTargetingThisCostLess n => .equipTargetingThisCostLess n
  | .firstEquipFreeIfEnduringStory => .firstEquipFreeIfEnduringStory
  | .chosenTypeCreaturesGet p t => .chosenTypePump p t
  | .instantSorceryCostReductionEqualEquippedPower =>
    .instantSorceryCostReductionEqualEquippedPower
  | .otherSubtypeGetPowerPerArtifactToken subtype =>
    .otherSubtypePowerPerArtifactToken subtype
  | .extraTriggerIfEnduringStorySubtype subtype =>
    .extraTriggerIfEnduringStorySubtype subtype
  | .extraTriggerAnotherYouControl subtypes includeBattles =>
    .extraTriggerAnotherYouControl subtypes includeBattles
  | .enchantedLosesAbilitiesDoesntUntap => .enchantedLosesAbilitiesDoesntUntap
  | .equippedHexproofUnblockableDuringYourTurn =>
    .equippedHexproofUnblockableDuringYourTurn
  | .equippedTriggersAgain => .equippedTriggersAgain
  | .equippedFirstStrikePlusPerInstantSorcery =>
    .equippedFirstStrikePlusPerInstantSorcery
  | .powerPerFatGraveyard n => .powerPerFatGraveyard n
  | .exileOppDeathCreateWolf => .exileOppDeathCreateWolf
  | .copyActivatedFromGySubtype subtype => .copyActivatedFromGySubtype subtype
  | .equippedGetsTrampleAndCombatTreasures p t =>
    .equippedGetsTrampleAndCombatTreasures p t
  | .wardDiscardEnchantmentInstantOrSorcery =>
    .wardDiscardEnchantmentInstantOrSorcery
  | .wardSacrificeLegendary => .wardSacrificeLegendary
  | .printed text => .printed text

/-- Oracle-style reminder from `shape`, so a new constructor only updates that
table. -/
def toNotation (ab : StaticAbility) : String :=
  match ab.shape with
  | .lordTrample subtypes =>
    s!"Other {joinedSubtypes subtypes pluralSubtype} you control have trample."
  | .lordPump subtypes p t =>
    if subtypes.isEmpty then
      s!"Other creatures you control get {signedStat p}/{signedStat t}."
    else
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
  | .hostKeywords host k p t =>
    let kw :=
      match k.toList with
      | [a, b] => s!"{a} and {b}"
      | ks => String.intercalate ", " ks
    if p == 0 && t == 0 then
      s!"{host} has {kw}."
    else
      s!"{host} gets {signedStat p}/{signedStat t} and has {kw}."
  | .cantBeBlockedByTokens =>
    "This creature can't be blocked by tokens."
  | .creaturesYouControlPower =>
    "This power is equal to the number of creatures you control."
  | .youControlSubtypeTrample subtype =>
    let plural := if subtype == "Army" then "Armies" else pluralSubtype subtype
    s!"{plural} you control have trample."
  | .teamPump p t legendaryOnly nonlegendaryOnly =>
    let who :=
      if legendaryOnly then "Legendary creatures you control"
      else if nonlegendaryOnly then "Nonlegendary creatures you control"
      else "Creatures you control"
    s!"{who} get {signedStat p}/{signedStat t}."
  | .hasteIfOtherSubtype subtype =>
    s!"This creature has haste as long as you control another {subtype}."
  | .cantAttackUnlessNOther n subtype =>
    let nWord := if n == 2 then "two" else toString n
    let plural := if subtype == "Wolf" then "Wolves" else pluralSubtype subtype
    s!"This creature can't attack unless you control {nWord} or more other {plural}."
  | .legendaryTeamPumpWard p t w =>
    s!"Legendary creatures you control get {signedStat p}/{signedStat t} and have ward \{{w}}."
  | .hostGetsAndWard host p t w =>
    s!"{host} gets {signedStat p}/{signedStat t} and has ward \{{w}}."
  | .creaturesWithPlusOneHaveMenace =>
    "Each creature you control with a +1/+1 counter on it has menace."
  | .lifelinkIfOtherSubtype subtype =>
    s!"This creature has lifelink as long as you control another {subtype}."
  | .thresholdGets p t =>
    s!"This creature gets {signedStat p}/{signedStat t} as long as there are seven or more cards in your graveyard."
  | .cantBeBlockedByPowerAtMost n =>
    s!"This creature can't be blocked by creatures with power {n} or less."
  | .equippedTeamKeywordsDuringYourTurn k =>
    let kw :=
      if k.firstStrike && k.vigilance then "first strike and vigilance"
      else
        match k.toList with
        | [a, b] => s!"{a} and {b}"
        | ks => String.intercalate ", " ks
    s!"During your turn, creatures you control that are equipped have {kw}."
  | .selfIfEnduringStory p t k =>
    let kw :=
      match k.toList with
      | [a] => a
      | [a, b] => s!"{a} and {b}"
      | ks => String.intercalate ", " ks
    if p == 0 && t == 0 then
      s!"As long as you have an enduring story, this has {kw}."
    else if k.toList.isEmpty then
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t}."
    else
      s!"As long as you have an enduring story, this gets {signedStat p}/{signedStat t} and has {kw}."
  | .teamIfEnduringStory p t =>
    s!"As long as you have an enduring story, creatures you control get {signedStat p}/{signedStat t}."
  | .doesntUntapUnlessEnduringStory =>
    "This doesn't untap during your untap step unless you have an enduring story."
  | .teamWardIfEnduringStory w =>
    s!"As long as you have an enduring story, artifacts and creatures you control have ward \{{w}}."
  | .attackTaxIfEnduringStory n =>
    s!"As long as you have an enduring story, creatures can't attack you unless their controller pays \{{n}} for each of those creatures."
  | .otherSubtypeTapAddOneOf subtypes mana =>
    let who :=
      if subtypes == #["Elf"] then "Other Elves you control"
      else s!"Other {joinedSubtypes subtypes} you control"
    let add :=
      String.intercalate " or " (mana.toList.map (fun t => s!"\{{t.letter}}"))
    s!"{who} have \"\{T}: Add {add}.\""
  | .cantBeBlockedByPowerAtLeast n =>
    s!"This creature can't be blocked by creatures with power {n} or greater."
  | .equippedKeywordsAndUnblockable k =>
    let kw :=
      match k.toList with
      | [a] => a
      | [a, b] => s!"{a} and {b}"
      | ks => String.intercalate ", " ks
    s!"Equipped creature has {kw} and can't be blocked."
  | .equipTargetingThisCostLess n =>
    s!"Equip abilities you activate that target this creature cost \{{n}} less to activate."
  | .firstEquipFreeIfEnduringStory =>
    "As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn."
  | .chosenTypePump p t =>
    s!"Creatures you control of the chosen type get {signedStat p}/{signedStat t}."
  | .instantSorceryCostReductionEqualEquippedPower =>
    "Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power."
  | .otherSubtypePowerPerArtifactToken subtype =>
    let plural := if subtype == "Dwarf" then "Dwarves" else pluralSubtype subtype
    s!"Other {plural} you control get +1/+0 for each artifact token you control."
  | .extraTriggerIfEnduringStorySubtype subtype =>
    s!"As long as you have an enduring story, if a triggered ability of a {subtype} you control triggers, that ability triggers an additional time."
  | .extraTriggerAnotherYouControl subtypes includeBattles =>
    let parts :=
      subtypes.toList ++ (if includeBattles then ["battle"] else [])
    let joined :=
      match parts with
      | [a] => a
      | [a, b] => s!"{a} or {b}"
      | xs => String.intercalate ", " xs
    s!"If a triggered ability of another {joined} you control triggers, that ability triggers an additional time."
  | .enchantedLosesAbilitiesDoesntUntap =>
    "Enchanted creature loses all abilities and doesn't untap during its controller's untap step."
  | .equippedHexproofUnblockableDuringYourTurn =>
    "During your turn, equipped creature has hexproof and can't be blocked."
  | .equippedTriggersAgain =>
    "If a triggered ability of equipped creature triggers, that ability triggers an additional time."
  | .equippedFirstStrikePlusPerInstantSorcery =>
    "Equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard."
  | .powerPerFatGraveyard n =>
    s!"This creature gets {signedStat n}/+0 for each graveyard with seven or more cards in it."
  | .exileOppDeathCreateWolf =>
    "If a creature an opponent controls would die, exile it instead. When you do, create a 2/2 green Wolf creature token."
  | .copyActivatedFromGySubtype subtype =>
    s!"This has all activated abilities of all {subtype} cards in your graveyard."
  | .equippedGetsTrampleAndCombatTreasures p t =>
    s!"Equipped creature gets {signedStat p}/{signedStat t} and has trample and \"Whenever this creature deals combat damage to a player or planeswalker, create that many Treasure tokens.\""
  | .wardDiscardEnchantmentInstantOrSorcery =>
    "Ward—Discard an enchantment, instant, or sorcery card."
  | .wardSacrificeLegendary =>
    "Ward—Sacrifice a legendary artifact or legendary creature."
  | .printed text => text

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

/-- Keywords this ability grants its enchanted or equipped host. -/
def hostKeywords (ab : StaticAbility) : Keywords :=
  ab.shape.spec.hostKeywords

/-- True when this creature can't be blocked by tokens. -/
def blocksTokens (ab : StaticAbility) : Bool :=
  ab.shape.spec.cantBeBlockedByTokens

/-- True for the creatures-you-control power characteristic-defining ability. -/
def isCreaturesYouControlPower (ab : StaticAbility) : Bool :=
  ab.shape.spec.creaturesYouControlPower

/-- True when this lord pump also applies to the source. -/
def lordIncludesSelf (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordIncludesSelf

/-- True when this lord pump applies only to legendary creatures. -/
def lordLegendaryOnly (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordLegendaryOnly

/-- True when this lord pump applies only to nonlegendary creatures. -/
def lordNonlegendaryOnly (ab : StaticAbility) : Bool :=
  ab.shape.spec.lordNonlegendaryOnly

/-- Ward cost this ability grants matching creatures, if any. -/
def grantedWard? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.grantedWard

/-- Subtype that grants this creature haste while another is controlled. -/
def hasteIfOtherSubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.hasteIfOtherSubtype

/-- Attack restriction: need `n` other permanents of this subtype. -/
def cantAttackUnlessNOther? (ab : StaticAbility) : Option (Nat × String) :=
  ab.shape.spec.cantAttackUnlessNOther

def creaturesWithPlusOneHaveMenace (ab : StaticAbility) : Bool :=
  ab.shape.spec.creaturesWithPlusOneHaveMenace

def lifelinkIfOtherSubtype? (ab : StaticAbility) : Option String :=
  ab.shape.spec.lifelinkIfOtherSubtype

def thresholdGets? (ab : StaticAbility) : Option (Int × Int) :=
  ab.shape.spec.thresholdGets

def cantBeBlockedByPowerAtMost? (ab : StaticAbility) : Option Int :=
  ab.shape.spec.cantBeBlockedByPowerAtMost

def equippedTeamKeywordsDuringYourTurn (ab : StaticAbility) : Keywords :=
  ab.shape.spec.equippedTeamKeywordsDuringYourTurn

def selfIfEnduringStory? (ab : StaticAbility) : Option (Int × Int × Keywords) :=
  ab.shape.spec.selfIfEnduringStory

def teamIfEnduringStory? (ab : StaticAbility) : Option (Int × Int) :=
  ab.shape.spec.teamIfEnduringStory

def doesntUntapUnlessEnduringStory? (ab : StaticAbility) : Bool :=
  ab.shape.spec.doesntUntapUnlessEnduringStory

def teamWardIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.teamWardIfEnduringStory

def attackTaxIfEnduringStory? (ab : StaticAbility) : Option Nat :=
  ab.shape.spec.attackTaxIfEnduringStory

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
  /-- Whenever equipped creature attacks alone, you draw a card and lose 1 life. -/
  | onEquippedAttacksAloneDrawLoseLife
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
  /-- When this permanent enters, you gain `n` life. -/
  | onEnterGainLife (n : Nat)
  /-- When this permanent enters, untap another target creature you control.
  If it has this subtype, put a +1/+1 counter on it. -/
  | onEnterUntapOtherPlusOneIfSubtype (subtype : String)
  /-- When this permanent enters, put a +1/+1 counter on target creature. -/
  | onEnterPlusOneOnCreature
  /-- When this permanent enters, create a tapped Treasure token. -/
  | onEnterCreateTreasureTapped
  /-- When this permanent enters, create a Treasure token. -/
  | onEnterCreateTreasure
  /-- When this permanent enters, exile the top card; you may play it. -/
  | onEnterExileTop
  /-- When this permanent enters, recruit. -/
  | onEnterRecruit
  /-- When this creature dies, recruit. -/
  | onDiesRecruit
  /-- Ferocious — Whenever this creature attacks, it gets +P/+T. -/
  | onAttackFerociousSourceGets (power toughness : Int)
  /-- Ferocious — Whenever this creature attacks, put a +1/+1 counter on each
  creature you control. -/
  | onAttackFerociousPlusOneEach
  /-- Ferocious — Whenever this creature attacks, it gets +P/+0 and creatures
  you control gain trample. -/
  | onAttackFerociousSourceGetsAndTeamTrample (power : Int)
  /-- Ferocious — Whenever you attack, you draw a card and lose 1 life. -/
  | onYouAttackFerociousDrawLoseLife
  /-- Ferocious — At the beginning of combat on your turn, put a +1/+1
  counter on this creature. -/
  | onYourBeginCombatFerociousPlusOne
  /-- Whenever you attack, draw a card. -/
  | onYouAttackDraw
  /-- Landfall — this creature gets +P/+T until end of turn. -/
  | onLandYouControlEntersGets (power toughness : Int)
  /-- When this permanent enters, amass Goblins `n`. -/
  | onEnterAmassGoblins (n : Nat)
  /-- When this creature dies, amass Goblins `n`. -/
  | onDiesAmassGoblins (n : Nat)
  /-- Whenever you attack, amass Goblins `n`. -/
  | onYouAttackAmassGoblins (n : Nat)
  /-- Whenever you cast a noncreature spell, amass Goblins `n`. -/
  | onCastNoncreatureAmassGoblins (n : Nat)
  /-- Whenever this creature enters or attacks, amass Goblins `n`. -/
  | onEnterOrAttackAmassGoblins (n : Nat)
  /-- Whenever this creature enters or attacks, recruit. -/
  | onEnterOrAttackRecruit
  /-- At the beginning of your upkeep, create `n` tokens. -/
  | onYourUpkeepCreateTokens (kind : TokenKind) (n : Nat)
  /-- When this permanent enters, create `n` tokens. -/
  | onEnterCreateTokens (kind : TokenKind) (n : Nat)
  /-- Landfall — create `n` tokens. -/
  | onLandYouControlEntersCreateTokens (kind : TokenKind) (n : Nat)
  /-- Whenever you attack, recruit. -/
  | onYouAttackRecruit
  /-- At the beginning of your end step, draw a card. -/
  | onYourEndStepDraw
  /-- Whenever an artifact you control enters, draw a card. -/
  | onArtifactYouControlEntersDraw
  /-- When this Equipment enters, create a token then attach this to it. -/
  | onEnterCreateThenAttach (kind : TokenKind)
  /-- When this Equipment enters, amass Goblins `n` then attach to the Army. -/
  | onEnterAmassThenAttach (n : Nat)
  /-- When this Equipment enters, attach it to target creature you control of
  this subtype. -/
  | onEnterAttachToSubtype (subtype : String)
  /-- When this Equipment enters, attach it to target legendary creature. -/
  | onEnterAttachToLegendary
  /-- Whenever this creature enters or attacks, put a +1/+1 counter on target
  creature. -/
  | onEnterOrAttackPlusOneOnCreature
  /-- Whenever this attacks, target attacking creature gains these keywords. -/
  | onAttackTargetGainsKeywords (k : Keywords)
  /-- Whenever this or another nontoken permanent of this subtype you control
  enters, create `n` tokens. -/
  | onThisOrNontokenSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind) (n : Nat)
  /-- When this enters, search for a basic land and put it into your hand. -/
  | onEnterSearchBasicToHand
  /-- When this enters, you gain `n` life. You may search for a basic land,
  reveal it, then shuffle and put that card on top. -/
  | onEnterGainLifeSearchBasicOnTop (n : Nat)
  /-- Whenever this enters or attacks, put a +1/+1 counter on each other
  creature you control. You gain 1 life for each other creature you control. -/
  | onEnterOrAttackPlusOneEachOtherGainLife
  /-- When this enters, destroy all artifacts and enchantments opponents
  control. You gain 1 life for each permanent destroyed this way. -/
  | onEnterDestroyOppArtifactsEnchantmentsGainLife
  /-- Whenever this attacks, it deals damage equal to the number of permanents
  of this subtype you control to each opponent. -/
  | onAttackDamageEqualSubtypeToEachOpponent (subtype : String)
  /-- Whenever this attacks, it deals damage equal to the number of Treasures
  you control to any target. -/
  | onAttackDamageEqualTreasures
  /-- Whenever an opponent casts their first noncreature spell each turn,
  recruit. -/
  | onOpponentCastsFirstNoncreatureRecruit
  /-- Whenever a player casts their second spell each turn, you lose 1 life
  and create a Treasure. -/
  | onPlayerCastsSecondSpellLoseLifeCreateTreasure
  /-- When this enters, it deals `n` damage to any target. If a permanent of
  this subtype is dealt damage this way, destroy it. -/
  | onEnterDealDamageDestroyIfSubtype (n : Nat) (subtype : String)
  /-- When this enters, attach target Equipment you control to up to one
  target creature you control. -/
  | onEnterAttachTargetEquipment
  /-- At the beginning of your first main phase, add these mana types. -/
  | onYourFirstMainAddMana (types : Array ManaType)
  /-- Whenever this becomes the target of a spell or ability an opponent
  controls, draw a card. -/
  | onBecomesTargetDraw
  /-- At the beginning of each end step, if you gained `n` or more life
  this turn, draw a card. -/
  | onEachEndStepDrawIfGainedLife (n : Nat)
  /-- Whenever this attacks, defending player sacrifices a creature with
  the least power. -/
  | onAttackDefenderSacsLeastPower
  /-- When this enters, create an Axe Equipment token. -/
  | onEnterCreateAxe
  /-- Landfall — choose tap an opposing creature or untap yours. -/
  | onLandYouControlEntersTapOrUntap
  /-- Landfall — this creature's base P/T becomes these values. -/
  | onLandYouControlEntersBecomePT (power toughness : Int)
  /-- When this enters, return up to one other permanent you control.
  If you do, put a +1/+1 counter on this. -/
  | onEnterReturnOtherPlusOne
  /-- Whenever you cast a green spell and whenever a Forest you control enters,
  +1/+1 on target creature you control. -/
  | onCastGreenOrForestEntersPlusOne
  /-- Whenever another permanent of this subtype or an Equipment you control
  enters, draw a card. Once each turn. -/
  | onAnotherSubtypeOrEquipmentEntersDrawOnce (subtype : String)
  /-- When this enters, look at the top `n` cards. You may reveal a card
  of one of these types and put it into your hand. -/
  | onEnterLookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Whenever you cast a noncreature spell, this gets +1/+1 and deals
  `n` damage to each opponent. -/
  | onCastNoncreaturePumpAndDamageOpponents (n : Nat)
  /-- When this enters, create X tapped Treasures, where X is artifacts
  opponents control. -/
  | onEnterCreateTappedTreasuresEqualOppArtifacts
  /-- Whenever you cast a spell, if Treasure mana was spent, draw and lose 1. -/
  | onCastWithTreasureDrawLoseLife
  /-- When this enters, gain control of target opposing creature until
  end of turn. Untap it. It gains haste. -/
  | onEnterGainControlOppUntilEot
  /-- At the beginning of each combat, other matching creatures get +P/+T
  and opposing creatures get +oppP/+oppT. -/
  | onEachCombatOthersGetAndOppsGet (subtypes : Array String)
      (power toughness oppP oppT : Int)
  /-- Whenever this or another permanent of this subtype you control enters,
  create `n` tokens. -/
  | onThisOrAnotherSubtypeEntersCreateTokens (subtype : String) (kind : TokenKind)
      (n : Nat)
  /-- Whenever this deals combat damage to a player or battle, put a nonland
  permanent card with mana value `mv` or less from a graveyard onto the
  battlefield. -/
  | onCombatDamagePutNonlandMvAtMost (mv : Nat)
  /-- Whenever this enters or attacks, put a hone counter on each Equipment
  you control (e.g. Dwalin, Weaponmaster). -/
  | onEnterOrAttackHoneEachEquipment
  /-- Cascade on the spell that is being cast (CR 702.85). -/
  | onCastCascade
  /-- Whenever the Ring tempts you, draw `n` cards. -/
  | onTheRingTemptsYouDraw (n : Nat)
  /-- Whenever you choose a creature as your Ring-bearer, draw a card. -/
  | onChooseRingBearerDraw
  /-- Whenever a token you control enters, reward by how many times this has
  resolved this turn (e.g. Belladonna Took). -/
  | onTokenYouControlEntersBelladonna
  /-- Whenever you activate an ability of a creature, draw a card. Triggers
  only once each turn (e.g. Elrond, Moon-Reader). -/
  | onActivateCreatureAbilityDrawOnce
  /-- When this enters, you may sacrifice another creature. If you do, a
  reflexive trigger deals that creature's power as damage (e.g. Bolg of the
  North). -/
  | onEnterBolgMaySacrifice
  /-- Reflexive trigger after Bolg's sacrifice instruction. -/
  | onBolgDealSacrificedPower
  /-- Whenever equipped creature attacks, create two tapped Spirits; they
  enter attacking if that creature is legendary and you control it
  (e.g. Andúril, Flame of the West). -/
  | onEquippedAttacksCreateSpirits
  /-- Whenever this deals combat damage to a player, create a Treasure for
  each artifact that player controls (e.g. Cavern-Hoard Dragon). -/
  | onCombatDamageCreateTreasuresEqualPlayerArtifacts
  /-- When this enters and whenever an opponent draws a card except the first
  one they draw in each of their draw steps, deal 1 then amass Orcs 1
  (e.g. Orcish Bowmasters). -/
  | onEnterOrOpponentDrawsDeal1AmassOrcs
  /-- Whenever an opponent draws their second card each turn, create a
  Treasure (e.g. Gleaming Splendor). -/
  | onOpponentDrawsSecondCreateTreasure
  /-- Whenever you attack with creatures with total power `n` or greater
  for the first time each turn, untap attackers and take an extra combat
  (e.g. Desert Were-Worm). -/
  | onAttackWithTotalPowerUntapExtraCombat (n : Int)
  /-- Delayed: create `n` Bird Soldier tokens (The Eagles Are Coming!). -/
  | onDelayedEaglesCreateBirds
  /-- Alliance — whenever another creature you control enters, choose one
  that hasn't been chosen this turn (e.g. Galadriel, Light of Valinor). -/
  | onAnotherCreatureYouControlEntersAlliance
  /-- When this enters, destroy up to one other target creature. Its
  controller amasses Goblins X equal to that creature's last-known power
  (e.g. Azog, Moria's Ruin). -/
  | onEnterDestroyOtherAmassControllerPower
  /-- Whenever a permanent you control of this subtype deals combat damage
  to a player or battle, create `n` tokens (e.g. Thorin, Company's Leader). -/
  | onSubtypeYouControlCombatDamageCreateTokens (subtype : String) (kind : TokenKind)
      (n : Nat)
  /-- Alliance-style modes that last for the object's lifetime
  (e.g. Gollum, Riddle Master). -/
  | onOpponentCastsChosenParityModes
  /-- Whenever you cast a spell of this color, create tokens. -/
  | onCastColorCreateTokens (color : Color) (kind : TokenKind) (n : Nat)
  /-- Whenever you cast a spell of this color, scry. -/
  | onCastColorScry (color : Color) (n : Nat)
  /-- Whenever you cast a spell of this color, deal damage to target opponent. -/
  | onCastColorDamageOpponent (color : Color) (n : Nat)
  /-- Whenever you cast a spell of this color, target creature gets +P/+T. -/
  | onCastColorPump (color : Color) (power toughness : Int)
  /-- When this enters, return a creature card from your graveyard to hand. -/
  | onEnterReturnCreatureFromGyToHand
  /-- Whenever a creature card leaves your graveyard, amass Goblins `n`. -/
  | onCreatureCardLeavesYourGyAmassGoblins (n : Nat)
  /-- Whenever this or another of this subtype enters, you may discard your
  hand and draw that many; if enduring story, damage opponents. -/
  | onThisOrAnotherSubtypeEntersDiscardHand (subtype : String)
  /-- Whenever you draw your second card, +1/+1 and lifelink on a creature. -/
  | onDrawSecondPlusOneLifelink
  /-- Combat damage: +1/+1 on a Wolf or create a Treasure. -/
  | onCombatDamageWolfPlusOneOrTreasure
  /-- Begin combat: trample counter, become a Bear, maybe draw. -/
  | onYourBeginCombatTrampleCounterBecomeBear
  /-- Whenever this attacks, you may cast from the graveyard. -/
  | onAttackCastFromGyArtifactInstantSorcery
  /-- When this enters, mill `n` then put matching cards into hand. -/
  | onEnterMillThenSubtypeToHand (n : Nat) (subtype : String)
  /-- When this enters, exile up to one opposing nonland per opponent. -/
  | onEnterExileOppNonlandEachUntilLeaves
  /-- Whenever you cast a creature, +X/+X counters equal to its mana value. -/
  | onCastCreaturePlusOneEqualMv
  /-- When this enters, create an Axe and attach it. -/
  | onEnterCreateAxeAttach
  /-- Whenever this attacks, equipped attackers gain double strike. -/
  | onAttackEquippedGainDoubleStrike
  /-- When this Aura enters, tap the enchanted creature and remove counters. -/
  | onEnterTapEnchantedRemoveCounters
  /-- When this dies, reveal the top `n` and put a random creature in. -/
  | onDiesRevealTopPutRandomCreature (n : Nat)
  /-- Begin combat: if you drew two or more, pump and first strike. -/
  | onYourBeginCombatIfDrawnTwoPumpFirstStrike
  /-- Whenever a Mountain you control enters, quest then maybe find a Dragon. -/
  | onMountainEntersQuestThenDragon
  /-- Whenever you draw your second card, target player mills `n`. -/
  | onDrawSecondMillPlayer (n : Nat)
  /-- Equipped combat damage: Treasures per chosen creature type. -/
  | onEquippedCombatDamageTreasuresPerChosenType
  /-- Whenever a nontoken you control dies, reveal until a creature. -/
  | onNontokenYouControlDiesRevealCreature
  /-- Whenever this attacks, you may sacrifice another for +1/+1s. -/
  | onAttackMaySacAnotherPlusOneEqualPower
  /-- When this dies, amass Goblins equal to its power. -/
  | onDiesAmassGoblinsEqualPower
  /-- Landfall from the graveyard: pay to return this to hand. -/
  | onLandYouControlEntersPayReturnFromGy
  /-- When this enters, loot; a discarded land enters tapped. -/
  | onEnterLootLandEntersTapped
  /-- When this enters, hone per opposing creatures and attach. -/
  | onEnterHonePerOppCreaturesAttach
  /-- Whenever this enters or attacks, create a Wall token. -/
  | onEnterOrAttackCreateWall
  /-- Whenever you put counters on a Goblin, Orc, or Army, damage an opponent. -/
  | onPutCountersOnGoblinOrcArmyDamageOpp
  /-- Whenever another Goblin, Orc, or Army you control dies, exile the top. -/
  | onAnotherGoblinOrcArmyDiesExileTop
  /-- Whenever a player loses life, that player mills that many. -/
  | onPlayerLosesLifeMillThatMany
  /-- When this dies, draw per fat graveyard. -/
  | onDiesDrawPerFatGraveyard
  /-- When this enters, if not a token, create two nonlegendary copies. -/
  | onEnterIfNotTokenCopySelf
  /-- When this enters, you may sacrifice another for a card and a Treasure. -/
  | onEnterMaySacDrawTreasure
  /-- Whenever you sacrifice a token, an opponent loses 1 life. -/
  | onYouSacrificeTokenOppLosesLife
  /-- When this enters, attach Equipment then the host fights. -/
  | onEnterAttachEquipmentThenFight
  /-- Landfall: two +1/+1s and vigilance. -/
  | onLandYouControlEntersPlusOneVigilance
  /-- Whenever another legendary of this subtype enters, loot two. -/
  | onAnotherLegendarySubtypeEntersLoot (subtype : String)
  /-- When this dies as a creature, return it as an artifact. -/
  | onDiesReturnAsArtifact
  /-- Whenever you cast a noncreature, you may draw X then discard two. -/
  | onCastNoncreatureMayDrawXDiscard2
  /-- Equipped attacks: +1/+1 each, or two with the city's blessing. -/
  | onEquippedAttacksPlusOneEachIfCityBlessing
  /-- Whenever another of this subtype enters, +n/+n counters on the source. -/
  | onAnotherSubtypeEntersPlusOneOnSource (subtype : String) (n : Nat)
  /-- Begin combat: you may cast an instant or sorcery from hand. -/
  | onYourBeginCombatCastInstantSorceryFromHand
  /-- Landfall: draw and +1/+1 on the source. -/
  | onLandYouControlEntersDrawPlusOneSource
  /-- When this enters, exile up to three lands you control, then return tapped. -/
  | onEnterExileLandsThenReturnTapped
  /-- Equipped combat damage: you may cast an instant or sorcery. -/
  | onEquippedCombatDamageCastInstantSorcery
  /-- Combat damage: impulse until an instant or sorcery. -/
  | onCombatDamageImpulseInstantSorcery
  /-- End step: Palantír influence, scry, then optional draw or mill. -/
  | onYourEndStepPalantir
  /-- Whenever you cast your second spell, mill then maybe copy. -/
  | onCastSecondSpellMillThenCopy
  /-- Whenever an opponent casts a spell, amass Orcs `n`. -/
  | onOpponentCastsAmassOrcs (n : Nat)
  /-- Whenever an Army you control deals combat damage, the Ring tempts you. -/
  | onArmyCombatDamageRingTempts
  /-- Whenever the Ring tempts you, you may discard and draw `n`. -/
  | onRingTemptsMayDiscardDraw (n : Nat)
  /-- Whenever this is dealt noncombat damage, create that many Treasures. -/
  | onDealtNoncombatDamageCreateTreasures
  /-- When this enters, if you cast it, protection from everything. -/
  | onEnterIfCastProtectionEverything
  /-- Upkeep: lose 1 life per burden counter. -/
  | onYourUpkeepLoseLifePerBurden
  /-- Whenever a final Saga chapter you control resolves, find a Saga. -/
  | onFinalSagaChapterRevealSaga
  /-- Whenever creatures deal combat damage to you, sac and the Ring tempts. -/
  | onCombatDamageToYouSacRingTempts
  /-- Unique printed trigger wording. -/
  | printed (text : String)
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
  /-- The beginning of combat on your turn (CR 507.1 / 603.1). -/
  | yourBeginCombat
  /-- You attack with one or more creatures (CR 508.2). -/
  | youAttack
  /-- You cast a noncreature spell (CR 601.2i / 603.3). -/
  | youCastNoncreature
  /-- The beginning of your upkeep (CR 503.1 / 603.1). -/
  | yourUpkeep
  /-- An artifact you control enters (CR 603.6a). -/
  | artifactYouControlEnters
  /-- An opponent casts their first noncreature spell this turn. -/
  | opponentCastsFirstNoncreature
  /-- A player casts their second spell this turn. -/
  | anyPlayerCastsSecondSpell
  /-- The beginning of your first main phase. -/
  | yourFirstMain
  /-- This or another nontoken permanent of a listed subtype you control
  enters. The subtype is stored on the triggered ability. -/
  | thisOrNontokenSubtypeYouControlEnters
  /-- This becomes the target of a spell or ability an opponent controls. -/
  | becomesTarget
  /-- The beginning of each end step. -/
  | eachEndStep
  /-- The beginning of each combat. -/
  | eachBeginCombat
  /-- You cast a green spell. -/
  | youCastGreen
  /-- A Forest you control enters. -/
  | forestYouControlEnters
  /-- Another permanent of a listed subtype or an Equipment you control enters. -/
  | anotherSubtypeOrEquipmentYouControlEnters
  /-- You cast a spell that had Treasure mana spent. -/
  | youCastWithTreasure
  /-- This or another permanent of a listed subtype you control enters. -/
  | thisOrAnotherSubtypeYouControlEnters
  /-- This deals combat damage to a player or battle. -/
  | dealsCombatDamageToPlayerOrBattle
  /-- The Ring tempts you. -/
  | theRingTemptsYou
  /-- You choose a creature as your Ring-bearer. -/
  | youChooseRingBearer
  /-- Equipped creature is the only attacker declared this combat. -/
  | equippedAttacksAlone
  /-- A token you control enters (CR 603.6a). -/
  | tokenYouControlEnters
  /-- You activate an ability of a creature, including a mana ability
  (CR 605.3b / 603.2). -/
  | youActivateCreatureAbility
  /-- Equipped creature attacks (CR 508.2). -/
  | equippedAttacks
  /-- An opponent draws a card that is not the first card of their draw step. -/
  | opponentDrawsExceptFirstDrawStep
  /-- An opponent draws their second card this turn. -/
  | opponentDrawsSecondCard
  /-- You attack with creatures whose total power meets a threshold. -/
  | youAttackWithTotalPower
  /-- Delayed trigger: create Bird Soldiers at the next upkeep. -/
  | eaglesCreateBirds
  /-- You sacrificed a creature to Bolg's enters instruction. -/
  | bolgSacrificedForReflexive
  /-- You cast a spell of this color. -/
  | youCastColor (color : Color)
  /-- An opponent casts a spell whose mana value matches a chosen odd/even. -/
  | opponentCastsMatchingParity
  /-- A creature card leaves your graveyard. -/
  | creatureCardLeavesYourGy
  /-- You cast a creature spell. -/
  | youCastCreature
  /-- A Mountain you control enters. -/
  | mountainYouControlEnters
  /-- This was dealt noncombat damage. -/
  | sourceDealtNoncombatDamage
  /-- An opponent casts a spell. -/
  | opponentCastsSpell
  /-- An Army you control deals combat damage to a player. -/
  | armyYouControlCombatDamage
  /-- The final chapter of a Saga you control resolves. -/
  | finalSagaChapterResolves
  /-- One or more creatures deal combat damage to you. -/
  | combatDamageToYou
  /-- You cast your second spell this turn. -/
  | youCastSecondSpell
  /-- You sacrifice a token. -/
  | youSacrificeToken
  /-- A player loses life. -/
  | playerLosesLife
  /-- You put one or more counters on a Goblin, Orc, or Army you control. -/
  | youPutCountersOnGoblinOrcArmy
  /-- Another Goblin, Orc, or Army you control dies. -/
  | anotherGoblinOrcArmyDies
  /-- A nontoken creature you control dies. -/
  | nontokenYouControlDies
  /-- Equipped creature deals combat damage to a player. -/
  | equippedDealsCombatDamageToPlayer
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
  | .yourBeginCombat =>
    { clause := "the beginning of combat on your turn", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youAttack =>
    { clause := "you attack", label := "attack trigger", checkTargets := false }
  | .youCastNoncreature =>
    { clause := "you cast a noncreature spell", label := "cast trigger",
      checkTargets := false }
  | .yourUpkeep =>
    { clause := "the beginning of your upkeep", isWhenever := false,
      label := "upkeep trigger", checkTargets := false }
  | .artifactYouControlEnters =>
    { clause := "an artifact you control enters", label := "artifact-enters trigger",
      checkTargets := false }
  | .opponentCastsFirstNoncreature =>
    { clause := "an opponent casts their first noncreature spell each turn",
      label := "opponent-cast trigger", checkTargets := false }
  | .anyPlayerCastsSecondSpell =>
    { clause := "a player casts their second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .yourFirstMain =>
    { clause := "the beginning of your first main phase", isWhenever := false,
      label := "main-phase trigger", checkTargets := false }
  | .thisOrNontokenSubtypeYouControlEnters =>
    { clause := "this or another nontoken creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .becomesTarget =>
    { clause := "this creature becomes the target of a spell or ability an opponent controls",
      label := "becomes-target trigger", checkTargets := false }
  | .eachEndStep =>
    { clause := "the beginning of each end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .eachBeginCombat =>
    { clause := "the beginning of each combat", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youCastGreen =>
    { clause := "you cast a green spell", label := "cast trigger" }
  | .forestYouControlEnters =>
    { clause := "a Forest you control enters", label := "forest-enters trigger" }
  | .anotherSubtypeOrEquipmentYouControlEnters =>
    { clause := "another Dwarf or Equipment you control enters",
      label := "dwarf-or-equipment trigger", checkTargets := false }
  | .youCastWithTreasure =>
    { clause := "you cast a spell, if mana from a Treasure was spent to cast it",
      label := "treasure-cast trigger", checkTargets := false }
  | .thisOrAnotherSubtypeYouControlEnters =>
    { clause := "this or another creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .dealsCombatDamageToPlayerOrBattle =>
    { clause := "this deals combat damage to a player or battle",
      label := "combat-damage trigger" }
  | .theRingTemptsYou =>
    { clause := "the Ring tempts you", label := "Ring-tempts trigger",
      checkTargets := false }
  | .youChooseRingBearer =>
    { clause := "you choose a creature as your Ring-bearer",
      label := "Ring-bearer trigger", checkTargets := false }
  | .equippedAttacksAlone =>
    { clause := "equipped creature attacks alone",
      label := "attacks-alone trigger", checkTargets := false }
  | .tokenYouControlEnters =>
    { clause := "a token you control enters", label := "token-enters trigger",
      checkTargets := false }
  | .youActivateCreatureAbility =>
    { clause := "you activate an ability of a creature",
      label := "activate-creature trigger", checkTargets := false }
  | .equippedAttacks =>
    { clause := "equipped creature attacks",
      label := "equipped-attacks trigger", checkTargets := false }
  | .opponentDrawsExceptFirstDrawStep =>
    { clause := "an opponent draws a card except the first one they draw in each of their draw steps",
      label := "opponent-draw trigger" }
  | .opponentDrawsSecondCard =>
    { clause := "an opponent draws their second card each turn",
      label := "opponent-second-card trigger", checkTargets := false }
  | .youAttackWithTotalPower =>
    { clause := "you attack with creatures with total power 12 or greater",
      label := "total-power-attack trigger", checkTargets := false }
  | .eaglesCreateBirds =>
    { clause := "the beginning of the next upkeep", isWhenever := false,
      label := "delayed Bird Soldier trigger", checkTargets := false }
  | .bolgSacrificedForReflexive =>
    { clause := "you sacrifice a creature this way", isWhenever := false,
      label := "reflexive trigger" }
  | .youCastColor c =>
    { clause := s!"you cast a {c} spell", label := "cast-color trigger",
      checkTargets := false }
  | .opponentCastsMatchingParity =>
    { clause := "an opponent casts a spell with mana value of the chosen quality",
      label := "parity-cast trigger", checkTargets := false }
  | .creatureCardLeavesYourGy =>
    { clause := "a creature card leaves your graveyard",
      label := "leaves-graveyard trigger", checkTargets := false }
  | .youCastCreature =>
    { clause := "you cast a creature spell", label := "cast-creature trigger" }
  | .mountainYouControlEnters =>
    { clause := "a Mountain you control enters", label := "mountain-enters trigger" }
  | .sourceDealtNoncombatDamage =>
    { clause := "this is dealt noncombat damage",
      label := "noncombat-damage trigger", checkTargets := false }
  | .opponentCastsSpell =>
    { clause := "an opponent casts a spell", label := "opponent-cast trigger",
      checkTargets := false }
  | .armyYouControlCombatDamage =>
    { clause := "an Army you control deals combat damage to a player",
      label := "army-combat-damage trigger", checkTargets := false }
  | .finalSagaChapterResolves =>
    { clause := "the final chapter ability of a Saga you control resolves",
      label := "saga-chapter trigger", checkTargets := false }
  | .combatDamageToYou =>
    { clause := "one or more creatures deal combat damage to you",
      label := "combat-damage-to-you trigger", checkTargets := false }
  | .youCastSecondSpell =>
    { clause := "you cast your second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .youSacrificeToken =>
    { clause := "you sacrifice a token", label := "sacrifice-token trigger" }
  | .playerLosesLife =>
    { clause := "a player loses life", label := "lose-life trigger",
      checkTargets := false }
  | .youPutCountersOnGoblinOrcArmy =>
    { clause := "you put one or more counters on a Goblin, Orc, or Army you control",
      label := "put-counters trigger" }
  | .anotherGoblinOrcArmyDies =>
    { clause := "another Goblin, Orc, or Army you control dies",
      label := "army-dies trigger", checkTargets := false }
  | .nontokenYouControlDies =>
    { clause := "a nontoken creature you control dies",
      label := "nontoken-dies trigger", checkTargets := false }
  | .equippedDealsCombatDamageToPlayer =>
    { clause := "equipped creature deals combat damage to a player",
      label := "equipped-combat-damage trigger", checkTargets := false }

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
  /-- Exile the targeted permanent. Link it if the source is still in play. -/
  | exileTarget
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
  /-- Recruit. -/
  | recruit
  /-- You recruit. -/
  | youRecruit
  /-- Create a tapped Treasure token. -/
  | createTreasureTapped
  /-- Create a Treasure token. -/
  | createTreasure
  /-- Exile the top card; you may play it until the end of your next turn. -/
  | exileTop
  /-- Untap the target; if it has this subtype, put a +1/+1 counter on it. -/
  | untapPlusOneIfSubtype (subtype : String)
  /-- Put a +1/+1 counter on each creature you control. -/
  | plusOneEachYouControl
  /-- Pump the source +P/+0 and grant trample to creatures you control. -/
  | sourceGetsAndTeamTrample (power : Int)
  /-- Draw a card and lose 1 life. -/
  | drawAndLoseLife
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool)
  /-- Create a token, then attach the source to it. -/
  | createThenAttach (kind : TokenKind)
  /-- Amass Goblins `n`, then attach the source to the Army. -/
  | amassThenAttach (n : Nat)
  /-- Attach the source to the targeted permanent. -/
  | attachSourceToTarget
  /-- Search for a basic land and put it into hand. -/
  | searchBasicToHand
  /-- Gain `n` life, then search a basic land to the top. -/
  | gainLifeSearchBasicOnTop (n : Nat)
  /-- +1/+1 on each other creature you control; gain that much life. -/
  | plusOneEachOtherGainLife
  /-- Destroy opponents' artifacts and enchantments; gain 1 per destroyed. -/
  | destroyOppArtifactsEnchantmentsGainLife
  /-- Deal damage equal to the count of this subtype you control to each
  opponent. -/
  | damageEqualSubtypeToEachOpponent (subtype : String)
  /-- Deal damage equal to Treasures you control to the target. -/
  | damageEqualTreasures
  /-- Lose 1 life and create a Treasure. -/
  | loseLifeCreateTreasure
  /-- Deal `n` damage to the target; destroy it if it has this subtype. -/
  | dealDamageDestroyIfSubtype (n : Nat) (subtype : String)
  /-- Attach the first target (Equipment) to the second (creature). -/
  | attachEquipmentToCreature
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Defending player sacrifices a least-power creature. -/
  | defenderSacsLeastPower
  /-- Create an Axe Equipment token. -/
  | createAxe
  /-- Tap an opposing creature or untap yours. -/
  | tapOppOrUntapYours
  /-- Set the source's base P/T. -/
  | becomePT (power toughness : Int)
  /-- Return another permanent you control; if you do, +1 on the source. -/
  | returnOtherPlusOne
  /-- Look at the top `n` and reveal a listed type. -/
  | lookAtTopRevealTypes (n : Nat) (types : Array String)
  /-- Pump the source +1/+1 and deal `n` to each opponent. -/
  | pumpAndDamageOpponents (n : Nat)
  /-- Create tapped Treasures equal to opposing artifacts. -/
  | createTappedTreasuresEqualOppArtifacts
  /-- Gain control of the target until end of turn; untap; haste. -/
  | gainControlOppUntilEot
  /-- Other matching creatures get +P/+T; opposing creatures get +oppP/+oppT. -/
  | othersGetAndOppsGet (subtypes : Array String) (power toughness oppP oppT : Int)
  /-- Put a nonland permanent card with mana value at most `mv` from a
  graveyard onto the battlefield. -/
  | putNonlandMvAtMostFromGy (mv : Nat)
  /-- Put a hone counter on each Equipment you control. -/
  | honeEachEquipment
  /-- Cascade: exile until a cheaper nonland, then you may cast it. -/
  | cascade
  /-- First resolve: gain 1 life. Second: draw. Third: +1/+1 each creature.
  Later resolves this turn do nothing (Belladonna Took). -/
  | belladonnaTokenReward
  /-- You may sacrifice another creature you control (Bolg). -/
  | bolgMaySacrifice
  /-- Deal last-known sacrificed power to the target; amass Goblins equal to
  excess damage. -/
  | bolgDealSacrificedPower
  /-- Create two tapped Spirits; they enter attacking if the equipped
  creature is legendary and you control it. -/
  | createSpiritsForEquipped
  /-- Create a Treasure for each artifact the damaged player controls. -/
  | createTreasuresEqualDamagedPlayerArtifacts
  /-- Deal 1 damage to any target, then amass Orcs 1. -/
  | deal1ThenAmassOrcs
  /-- Untap attacking creatures; an additional combat phase follows. -/
  | untapAttackersExtraCombat
  /-- Create Bird Soldier tokens equal to last-known count. -/
  | eaglesCreateBirds
  /-- Apply an unused Alliance mode, or do nothing if all were chosen. -/
  | allianceMode
  /-- Destroy the targeted creature if any; that controller amasses equal
  to last-known power. No target means no player amasses. -/
  | destroyOtherAmassControllerPower
  /-- Apply an unused Gollum mode, or do nothing if all were chosen. -/
  | gollumMode
  /-- Return a creature card from your graveyard to your hand. -/
  | returnCreatureFromGyToHand
  /-- Discard your hand, draw that many, and maybe damage opponents. -/
  | discardHandDrawDamageIfStory
  /-- +1/+1 and lifelink on the targeted creature. -/
  | plusOneAndLifelink
  /-- +1/+1 on a Wolf you control, or create a Treasure. -/
  | wolfPlusOneOrTreasure
  /-- Trample counter, become a Bear, maybe draw two. -/
  | trampleCounterBecomeBear
  /-- You may cast an artifact, instant, or sorcery from your graveyard. -/
  | castFromGyArtifactInstantSorcery
  /-- Mill `n`, then put cards of this subtype into hand. -/
  | millThenSubtypeToHand (n : Nat) (subtype : String)
  /-- Exile up to one opposing nonland per opponent until this leaves. -/
  | exileOppNonlandEachUntilLeaves
  /-- +1/+1 counters equal to the last-known mana value. -/
  | plusOneEqualLastKnownMv
  /-- Create an Axe and attach it to a creature you control. -/
  | createAxeAttach
  /-- Equipped attacking creatures gain double strike. -/
  | equippedAttackersGainDoubleStrike
  /-- Tap the enchanted creature and remove its counters. -/
  | tapEnchantedRemoveCounters
  /-- Reveal the top `n`; put a random creature onto the battlefield. -/
  | revealTopPutRandomCreature (n : Nat)
  /-- If you drew two or more, pump and first strike. -/
  | beginCombatIfDrawnTwoPump
  /-- Quest counter; at six, sacrifice and find a Dragon. -/
  | mountainQuestDragon
  /-- Target player mills `n`. -/
  | millPlayer (n : Nat)
  /-- Treasures equal to permanents of a chosen type. -/
  | treasuresPerChosenType
  /-- Reveal until a creature; put it onto the battlefield or into hand. -/
  | revealUntilCreature
  /-- You may sacrifice another creature for +1/+1s equal to its power. -/
  | attackSacPlusOneEqualPower
  /-- Amass Goblins equal to last-known power. -/
  | amassGoblinsEqualPower
  /-- You may pay to return this from the graveyard to your hand. -/
  | payReturnFromGy
  /-- Draw, discard; a discarded land enters tapped. -/
  | lootLandEntersTapped
  /-- Hone per opposing creatures, then attach. -/
  | honePerOppAttach
  /-- Deal 2 to target opponent. -/
  | damageTargetOpponent (n : Nat)
  /-- Each player who lost life mills that much. -/
  | millThatManyLost
  /-- Draw per graveyard with seven or more cards. -/
  | drawPerFatGraveyard
  /-- Create two nonlegendary token copies of the source. -/
  | copySelfNonlegendary
  /-- You may sacrifice another for a card and a Treasure. -/
  | maySacDrawTreasure
  /-- Target opponent loses 1 life. -/
  | targetOpponentLosesLife (n : Nat)
  /-- Attach any number of Equipment, then the host fights. -/
  | attachEquipmentThenFight
  /-- Two +1/+1 counters and vigilance. -/
  | plusOneVigilance (n : Nat)
  /-- Draw two, then discard a card. -/
  | drawThenDiscardN (n : Nat)
  /-- Return the source as an artifact. -/
  | returnAsArtifact
  /-- You may draw X (mana spent), then discard two. -/
  | mayDrawXDiscard2
  /-- +1/+1 each, or two with the city's blessing. -/
  | plusOneEachIfCityBlessing
  /-- You may cast an instant or sorcery from hand without paying. -/
  | castInstantSorceryFromHand
  /-- Draw a card and put a +1/+1 counter on the source. -/
  | drawPlusOneSource
  /-- Exile up to three lands you control, then return them tapped. -/
  | exileLandsThenReturnTapped
  /-- You may cast an instant or sorcery of MV at most last-known power. -/
  | castInstantSorceryMvAtMost
  /-- Exile until an instant or sorcery; you may cast it. -/
  | grimaImpulse
  /-- Palantír of Orthanc. -/
  | palantir
  /-- Each opponent mills two; then maybe copy a card. -/
  | millThenCopy
  /-- Amass Orcs `n`. -/
  | amassOrcs (n : Nat)
  /-- The Ring tempts you. -/
  | ringTempts
  /-- You may discard your hand and draw `n`. -/
  | mayDiscardHandDraw (n : Nat)
  /-- Create Treasures equal to last-known damage. -/
  | treasuresEqualLastKnown
  /-- You gain protection from everything until your next turn. -/
  | protectionEverything
  /-- Lose 1 life per burden counter. -/
  | loseLifePerBurden
  /-- Reveal until a Saga and put it onto the battlefield. -/
  | revealSaga
  /-- Each opponent sacrifices a creature that damaged you; the Ring tempts you. -/
  | sacDamagersRingTempts
  /-- Unique printed trigger wording. -/
  | printed (text : String)
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
  /-- “This or another nontoken {subtype} you control enters”. -/
  thisOrNontokenSubtype : Option String := none
  /-- Intervening “if you gained `n` or more life this turn”. -/
  gainedLifeAtLeast : Option Nat := none
  /-- “Another {subtype} or Equipment you control enters”. -/
  anotherSubtypeOrEquipment : Option String := none
  /-- “This or another {subtype} you control enters”. -/
  thisOrAnotherSubtype : Option String := none
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
      allowsZeroTargets := true, resolution := .exileTarget }
  | .onEquippedAttacksAloneDrawLoseLife =>
    { events := #[.equippedAttacksAlone], resolution := .drawAndLoseLife }
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
  | .onEnterGainLife n =>
    { events := #[.entering], resolution := .gainLife n }
  | .onEnterUntapOtherPlusOneIfSubtype subtype =>
    { events := #[.entering], targeting := .of .anotherCreatureYouControl,
      resolution := .untapPlusOneIfSubtype subtype }
  | .onEnterPlusOneOnCreature =>
    { events := #[.entering], targeting := .of .creature,
      resolution := .onPermanent (.plusOne 1) }
  | .onEnterCreateTreasureTapped =>
    { events := #[.entering], resolution := .createTreasureTapped }
  | .onEnterCreateTreasure =>
    { events := #[.entering], resolution := .createTreasure }
  | .onEnterExileTop =>
    { events := #[.entering], resolution := .exileTop }
  | .onEnterRecruit =>
    { events := #[.entering], resolution := .recruit }
  | .onDiesRecruit =>
    { events := #[.dying], resolution := .recruit }
  | .onAttackFerociousSourceGets p t =>
    { events := #[.attacking], resolution := .onSource (.pump p t),
      youControlCreatureWithPower := some 4 }
  | .onAttackFerociousPlusOneEach =>
    { events := #[.attacking], resolution := .plusOneEachYouControl,
      youControlCreatureWithPower := some 4 }
  | .onAttackFerociousSourceGetsAndTeamTrample p =>
    { events := #[.attacking], resolution := .sourceGetsAndTeamTrample p,
      youControlCreatureWithPower := some 4 }
  | .onYouAttackFerociousDrawLoseLife =>
    { events := #[.youAttack], resolution := .drawAndLoseLife,
      youControlCreatureWithPower := some 4 }
  | .onYourBeginCombatFerociousPlusOne =>
    { events := #[.yourBeginCombat], resolution := .onSource (.plusOne 1),
      youControlCreatureWithPower := some 4 }
  | .onYouAttackDraw =>
    { events := #[.youAttack], resolution := .draw 1 }
  | .onLandYouControlEntersGets p t =>
    { events := #[.landYouControlEnters], resolution := .onSource (.pump p t) }
  | .onEnterAmassGoblins n =>
    { events := #[.entering], resolution := .amassGoblins n }
  | .onDiesAmassGoblins n =>
    { events := #[.dying], resolution := .amassGoblins n }
  | .onYouAttackAmassGoblins n =>
    { events := #[.youAttack], resolution := .amassGoblins n }
  | .onCastNoncreatureAmassGoblins n =>
    { events := #[.youCastNoncreature], resolution := .amassGoblins n }
  | .onEnterOrAttackAmassGoblins n =>
    { events := #[.entering, .attacking], resolution := .amassGoblins n }
  | .onEnterOrAttackRecruit =>
    { events := #[.entering, .attacking], resolution := .recruit }
  | .onYourUpkeepCreateTokens kind n =>
    { events := #[.yourUpkeep], resolution := .createTokens kind n false }
  | .onEnterCreateTokens kind n =>
    { events := #[.entering], resolution := .createTokens kind n false }
  | .onLandYouControlEntersCreateTokens kind n =>
    { events := #[.landYouControlEnters], resolution := .createTokens kind n false }
  | .onYouAttackRecruit =>
    { events := #[.youAttack], resolution := .recruit }
  | .onYourEndStepDraw =>
    { events := #[.yourEndStep], resolution := .draw 1 }
  | .onArtifactYouControlEntersDraw =>
    { events := #[.artifactYouControlEnters], resolution := .draw 1 }
  | .onEnterCreateThenAttach kind =>
    { events := #[.entering], resolution := .createThenAttach kind }
  | .onEnterAmassThenAttach n =>
    { events := #[.entering], resolution := .amassThenAttach n }
  | .onEnterAttachToSubtype subtype =>
    { events := #[.entering], targeting := .of (.creatureYouControlSubtype subtype),
      resolution := .attachSourceToTarget }
  | .onEnterAttachToLegendary =>
    { events := #[.entering], targeting := .of .legendaryCreatureYouControl,
      resolution := .attachSourceToTarget }
  | .onEnterOrAttackPlusOneOnCreature =>
    { events := #[.entering, .attacking], targeting := .of .creature,
      resolution := .onPermanent (.plusOne 1) }
  | .onAttackTargetGainsKeywords k =>
    { events := #[.attacking], targeting := .of .attackingCreature,
      resolution := .onPermanent (.grantKeywords k) }
  | .onThisOrNontokenSubtypeEntersCreateTokens subtype kind n =>
    { events := #[.thisOrNontokenSubtypeYouControlEnters],
      resolution := .createTokens kind n false, thisOrNontokenSubtype := some subtype }
  | .onEnterSearchBasicToHand =>
    { events := #[.entering], resolution := .searchBasicToHand }
  | .onEnterGainLifeSearchBasicOnTop n =>
    { events := #[.entering], resolution := .gainLifeSearchBasicOnTop n }
  | .onEnterOrAttackPlusOneEachOtherGainLife =>
    { events := #[.entering, .attacking], resolution := .plusOneEachOtherGainLife }
  | .onEnterDestroyOppArtifactsEnchantmentsGainLife =>
    { events := #[.entering], resolution := .destroyOppArtifactsEnchantmentsGainLife }
  | .onAttackDamageEqualSubtypeToEachOpponent subtype =>
    { events := #[.attacking], resolution := .damageEqualSubtypeToEachOpponent subtype }
  | .onAttackDamageEqualTreasures =>
    { events := #[.attacking], targeting := .of .playerOrCreature,
      resolution := .damageEqualTreasures }
  | .onOpponentCastsFirstNoncreatureRecruit =>
    { events := #[.opponentCastsFirstNoncreature], resolution := .youRecruit }
  | .onPlayerCastsSecondSpellLoseLifeCreateTreasure =>
    { events := #[.anyPlayerCastsSecondSpell], resolution := .loseLifeCreateTreasure }
  | .onEnterDealDamageDestroyIfSubtype n subtype =>
    { events := #[.entering], targeting := .of .playerOrCreature,
      resolution := .dealDamageDestroyIfSubtype n subtype }
  | .onEnterAttachTargetEquipment =>
    { events := #[.entering],
      targeting := .of .equipmentYouControlThenCreatureYouControl,
      allowsZeroTargets := true, resolution := .attachEquipmentToCreature }
  | .onYourFirstMainAddMana types =>
    { events := #[.yourFirstMain], resolution := .addMana types }
  | .onBecomesTargetDraw =>
    { events := #[.becomesTarget], resolution := .draw 1 }
  | .onEachEndStepDrawIfGainedLife n =>
    { events := #[.eachEndStep], resolution := .draw 1, gainedLifeAtLeast := some n }
  | .onAttackDefenderSacsLeastPower =>
    { events := #[.attacking], resolution := .defenderSacsLeastPower }
  | .onEnterCreateAxe =>
    { events := #[.entering], resolution := .createAxe }
  | .onLandYouControlEntersTapOrUntap =>
    { events := #[.landYouControlEnters], resolution := .tapOppOrUntapYours }
  | .onLandYouControlEntersBecomePT p t =>
    { events := #[.landYouControlEnters], resolution := .becomePT p t }
  | .onEnterReturnOtherPlusOne =>
    { events := #[.entering], targeting := .of .anotherCreatureYouControl,
      allowsZeroTargets := true, resolution := .returnOtherPlusOne }
  | .onCastGreenOrForestEntersPlusOne =>
    { events := #[.youCastGreen, .forestYouControlEnters],
      targeting := .of .creatureYouControl, resolution := .onPermanent (.plusOne 1) }
  | .onAnotherSubtypeOrEquipmentEntersDrawOnce subtype =>
    { events := #[.anotherSubtypeOrEquipmentYouControlEnters],
      resolution := .draw 1, onceEachTurn := true,
      anotherSubtypeOrEquipment := some subtype }
  | .onEnterLookAtTopRevealTypes n types =>
    { events := #[.entering], resolution := .lookAtTopRevealTypes n types }
  | .onCastNoncreaturePumpAndDamageOpponents n =>
    { events := #[.youCastNoncreature], resolution := .pumpAndDamageOpponents n }
  | .onEnterCreateTappedTreasuresEqualOppArtifacts =>
    { events := #[.entering], resolution := .createTappedTreasuresEqualOppArtifacts }
  | .onCastWithTreasureDrawLoseLife =>
    { events := #[.youCastWithTreasure], resolution := .drawAndLoseLife }
  | .onEnterGainControlOppUntilEot =>
    { events := #[.entering], targeting := .of .oppCreature,
      resolution := .gainControlOppUntilEot }
  | .onEachCombatOthersGetAndOppsGet subtypes p t oppP oppT =>
    { events := #[.eachBeginCombat],
      resolution := .othersGetAndOppsGet subtypes p t oppP oppT }
  | .onThisOrAnotherSubtypeEntersCreateTokens subtype kind n =>
    { events := #[.thisOrAnotherSubtypeYouControlEnters],
      resolution := .createTokens kind n false, thisOrAnotherSubtype := some subtype }
  | .onCombatDamagePutNonlandMvAtMost mv =>
    { events := #[.dealsCombatDamageToPlayerOrBattle],
      targeting := .of .nonland, allowsZeroTargets := true,
      resolution := .putNonlandMvAtMostFromGy mv }
  | .onEnterOrAttackHoneEachEquipment =>
    { events := #[.entering, .attacking], resolution := .honeEachEquipment }
  | .onCastCascade =>
    { events := #[], resolution := .cascade }
  | .onTheRingTemptsYouDraw n =>
    { events := #[.theRingTemptsYou], resolution := .draw n }
  | .onChooseRingBearerDraw =>
    { events := #[.youChooseRingBearer], resolution := .draw 1 }
  | .onTokenYouControlEntersBelladonna =>
    { events := #[.tokenYouControlEnters], resolution := .belladonnaTokenReward }
  | .onActivateCreatureAbilityDrawOnce =>
    { events := #[.youActivateCreatureAbility], resolution := .draw 1,
      onceEachTurn := true }
  | .onEnterBolgMaySacrifice =>
    { events := #[.entering], resolution := .bolgMaySacrifice }
  | .onBolgDealSacrificedPower =>
    { events := #[.bolgSacrificedForReflexive], targeting := .of .anotherCreature,
      resolution := .bolgDealSacrificedPower }
  | .onEquippedAttacksCreateSpirits =>
    { events := #[.equippedAttacks], resolution := .createSpiritsForEquipped }
  | .onCombatDamageCreateTreasuresEqualPlayerArtifacts =>
    { events := #[.dealsCombatDamageToPlayer],
      resolution := .createTreasuresEqualDamagedPlayerArtifacts }
  | .onEnterOrOpponentDrawsDeal1AmassOrcs =>
    { events := #[.entering, .opponentDrawsExceptFirstDrawStep],
      targeting := .of .playerOrCreature, resolution := .deal1ThenAmassOrcs }
  | .onOpponentDrawsSecondCreateTreasure =>
    { events := #[.opponentDrawsSecondCard], resolution := .createTreasure }
  | .onAttackWithTotalPowerUntapExtraCombat _n =>
    { events := #[.youAttackWithTotalPower],
      resolution := .untapAttackersExtraCombat, onceEachTurn := true }
  | .onDelayedEaglesCreateBirds =>
    { events := #[.eaglesCreateBirds], resolution := .eaglesCreateBirds }
  | .onAnotherCreatureYouControlEntersAlliance =>
    { events := #[.anotherCreatureYouControlEnters], resolution := .allianceMode }
  | .onEnterDestroyOtherAmassControllerPower =>
    { events := #[.entering], targeting := .of .anotherCreature,
      allowsZeroTargets := true, resolution := .destroyOtherAmassControllerPower }
  | .onSubtypeYouControlCombatDamageCreateTokens _subtype kind n =>
    { events := #[.dealsCombatDamageToPlayerOrBattle],
      resolution := .createTokens kind n false }
  | .onOpponentCastsChosenParityModes =>
    { events := #[.opponentCastsMatchingParity], resolution := .gollumMode }
  | .onCastColorCreateTokens c kind n =>
    { events := #[.youCastColor c], resolution := .createTokens kind n false }
  | .onCastColorScry c n =>
    { events := #[.youCastColor c], resolution := .scry n }
  | .onCastColorDamageOpponent c n =>
    { events := #[.youCastColor c], targeting := .of .opponent,
      resolution := .damageEachOpponent n }
  | .onCastColorPump c p t =>
    { events := #[.youCastColor c], targeting := .of .creature,
      resolution := .onPermanent (.pump p t) }
  | .onEnterReturnCreatureFromGyToHand =>
    { events := #[.entering], targeting := .of .creatureCardInYourGraveyard,
      resolution := .returnCreatureFromGyToHand }
  | .onCreatureCardLeavesYourGyAmassGoblins n =>
    { events := #[.creatureCardLeavesYourGy], resolution := .amassGoblins n }
  | .onThisOrAnotherSubtypeEntersDiscardHand subtype =>
    { events := #[.thisOrAnotherSubtypeYouControlEnters],
      resolution := .discardHandDrawDamageIfStory, thisOrAnotherSubtype := some subtype }
  | .onDrawSecondPlusOneLifelink =>
    { events := #[.youDrawSecondCard], targeting := .of .creature,
      resolution := .plusOneAndLifelink }
  | .onCombatDamageWolfPlusOneOrTreasure =>
    { events := #[.dealsCombatDamageToPlayer], resolution := .wolfPlusOneOrTreasure }
  | .onYourBeginCombatTrampleCounterBecomeBear =>
    { events := #[.yourBeginCombat], targeting := .of .creatureYouControl,
      allowsZeroTargets := true, resolution := .trampleCounterBecomeBear }
  | .onAttackCastFromGyArtifactInstantSorcery =>
    { events := #[.attacking], resolution := .castFromGyArtifactInstantSorcery }
  | .onEnterMillThenSubtypeToHand n subtype =>
    { events := #[.entering], resolution := .millThenSubtypeToHand n subtype }
  | .onEnterExileOppNonlandEachUntilLeaves =>
    { events := #[.entering], targeting := .of .oppNonland, allowsZeroTargets := true,
      resolution := .exileOppNonlandEachUntilLeaves }
  | .onCastCreaturePlusOneEqualMv =>
    { events := #[.youCastCreature], targeting := .of .creatureYouControl,
      resolution := .plusOneEqualLastKnownMv }
  | .onEnterCreateAxeAttach =>
    { events := #[.entering], targeting := .of .creatureYouControl,
      resolution := .createAxeAttach }
  | .onAttackEquippedGainDoubleStrike =>
    { events := #[.attacking], resolution := .equippedAttackersGainDoubleStrike }
  | .onEnterTapEnchantedRemoveCounters =>
    { events := #[.entering], resolution := .tapEnchantedRemoveCounters }
  | .onDiesRevealTopPutRandomCreature n =>
    { events := #[.dying], resolution := .revealTopPutRandomCreature n }
  | .onYourBeginCombatIfDrawnTwoPumpFirstStrike =>
    { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
      resolution := .beginCombatIfDrawnTwoPump }
  | .onMountainEntersQuestThenDragon =>
    { events := #[.mountainYouControlEnters], resolution := .mountainQuestDragon }
  | .onDrawSecondMillPlayer n =>
    { events := #[.youDrawSecondCard], targeting := .of .player,
      resolution := .millPlayer n }
  | .onEquippedCombatDamageTreasuresPerChosenType =>
    { events := #[.equippedDealsCombatDamageToPlayer],
      resolution := .treasuresPerChosenType }
  | .onNontokenYouControlDiesRevealCreature =>
    { events := #[.nontokenYouControlDies], resolution := .revealUntilCreature,
      onceEachTurn := true }
  | .onAttackMaySacAnotherPlusOneEqualPower =>
    { events := #[.attacking], resolution := .attackSacPlusOneEqualPower }
  | .onDiesAmassGoblinsEqualPower =>
    { events := #[.dying], resolution := .amassGoblinsEqualPower }
  | .onLandYouControlEntersPayReturnFromGy =>
    { events := #[.landYouControlEnters], resolution := .payReturnFromGy }
  | .onEnterLootLandEntersTapped =>
    { events := #[.entering], resolution := .lootLandEntersTapped }
  | .onEnterHonePerOppCreaturesAttach =>
    { events := #[.entering], targeting := .of .creatureYouControl,
      allowsZeroTargets := true, resolution := .honePerOppAttach }
  | .onEnterOrAttackCreateWall =>
    { events := #[.entering, .attacking], resolution := .createTokens .wall 1 false }
  | .onPutCountersOnGoblinOrcArmyDamageOpp =>
    { events := #[.youPutCountersOnGoblinOrcArmy], targeting := .of .opponent,
      resolution := .damageTargetOpponent 2 }
  | .onAnotherGoblinOrcArmyDiesExileTop =>
    { events := #[.anotherGoblinOrcArmyDies], resolution := .exileTop }
  | .onPlayerLosesLifeMillThatMany =>
    { events := #[.playerLosesLife], resolution := .millThatManyLost }
  | .onDiesDrawPerFatGraveyard =>
    { events := #[.dying], resolution := .drawPerFatGraveyard }
  | .onEnterIfNotTokenCopySelf =>
    { events := #[.entering], resolution := .copySelfNonlegendary }
  | .onEnterMaySacDrawTreasure =>
    { events := #[.entering], resolution := .maySacDrawTreasure }
  | .onYouSacrificeTokenOppLosesLife =>
    { events := #[.youSacrificeToken], targeting := .of .opponent,
      resolution := .targetOpponentLosesLife 1 }
  | .onEnterAttachEquipmentThenFight =>
    { events := #[.entering], targeting := .of .creatureYouControl,
      resolution := .attachEquipmentThenFight }
  | .onLandYouControlEntersPlusOneVigilance =>
    { events := #[.landYouControlEnters], targeting := .of .creatureYouControl,
      resolution := .plusOneVigilance 2 }
  | .onAnotherLegendarySubtypeEntersLoot subtype =>
    { events := #[.anotherCreatureYouControlEnters],
      resolution := .drawThenDiscardN 2, thisOrAnotherSubtype := some subtype }
  | .onDiesReturnAsArtifact =>
    { events := #[.dying], resolution := .returnAsArtifact }
  | .onCastNoncreatureMayDrawXDiscard2 =>
    { events := #[.youCastNoncreature], resolution := .mayDrawXDiscard2 }
  | .onEquippedAttacksPlusOneEachIfCityBlessing =>
    { events := #[.equippedAttacks], resolution := .plusOneEachIfCityBlessing }
  | .onAnotherSubtypeEntersPlusOneOnSource subtype n =>
    { events := #[.anotherCreatureYouControlEnters],
      resolution := .onSource (.plusOne n), thisOrAnotherSubtype := some subtype }
  | .onYourBeginCombatCastInstantSorceryFromHand =>
    { events := #[.yourBeginCombat], resolution := .castInstantSorceryFromHand }
  | .onLandYouControlEntersDrawPlusOneSource =>
    { events := #[.landYouControlEnters], resolution := .drawPlusOneSource }
  | .onEnterExileLandsThenReturnTapped =>
    { events := #[.entering], targeting := .of .creatureOrLandYouControl,
      allowsZeroTargets := true, resolution := .exileLandsThenReturnTapped }
  | .onEquippedCombatDamageCastInstantSorcery =>
    { events := #[.equippedDealsCombatDamageToPlayer],
      resolution := .castInstantSorceryMvAtMost }
  | .onCombatDamageImpulseInstantSorcery =>
    { events := #[.dealsCombatDamageToPlayer], resolution := .grimaImpulse }
  | .onYourEndStepPalantir =>
    { events := #[.yourEndStep], targeting := .of .opponent, resolution := .palantir }
  | .onCastSecondSpellMillThenCopy =>
    { events := #[.youCastSecondSpell], resolution := .millThenCopy }
  | .onOpponentCastsAmassOrcs n =>
    { events := #[.opponentCastsSpell], resolution := .amassOrcs n }
  | .onArmyCombatDamageRingTempts =>
    { events := #[.armyYouControlCombatDamage], resolution := .ringTempts }
  | .onRingTemptsMayDiscardDraw n =>
    { events := #[.theRingTemptsYou], resolution := .mayDiscardHandDraw n }
  | .onDealtNoncombatDamageCreateTreasures =>
    { events := #[.sourceDealtNoncombatDamage], resolution := .treasuresEqualLastKnown }
  | .onEnterIfCastProtectionEverything =>
    { events := #[.entering], resolution := .protectionEverything }
  | .onYourUpkeepLoseLifePerBurden =>
    { events := #[.yourUpkeep], resolution := .loseLifePerBurden }
  | .onFinalSagaChapterRevealSaga =>
    { events := #[.finalSagaChapterResolves], resolution := .revealSaga,
      onceEachTurn := true }
  | .onCombatDamageToYouSacRingTempts =>
    { events := #[.combatDamageToYou], resolution := .sacDamagersRingTempts }
  | .printed text =>
    { resolution := .printed text }

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
  else if t.events.contains .yourBeginCombat then
    "At the beginning of combat on your turn"
  else if t.events.contains .yourUpkeep then
    "At the beginning of your upkeep"
  else if t.events.contains .yourFirstMain then
    "At the beginning of your first main phase"
  else if t.events.contains .eachEndStep then
    "At the beginning of each end step"
  else if t.events.contains .eachBeginCombat then
    "At the beginning of each combat"
  else if t.events.contains .youCastGreen && t.events.contains .forestYouControlEnters then
    "Whenever you cast a green spell and whenever a Forest you control enters"
  else if t.events.contains .thisOrAnotherSubtypeYouControlEnters then
    match t.thisOrAnotherSubtype with
    | some s => s!"Whenever this or another {s} you control enters"
    | none => "Whenever this or another creature you control enters"
  else if t.events.contains .anotherSubtypeOrEquipmentYouControlEnters then
    match t.anotherSubtypeOrEquipment with
    | some s => s!"Whenever another {s} or Equipment you control enters"
    | none => "Whenever another creature or Equipment you control enters"
  else if t.events.contains .thisOrNontokenSubtypeYouControlEnters then
    match t.thisOrNontokenSubtype with
    | some s => s!"Whenever this or another nontoken {s} you control enters"
    | none => "Whenever this or another nontoken creature you control enters"
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
  match t.youControlCreatureWithPower, t.gainedLifeAtLeast with
  | some n, _ => s!" while you control a creature with power {n} or greater"
  | none, some n => s!", if you gained {n} or more life this turn"
  | none, none => ""

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
  | .exileTarget =>
    if t.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
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
  | .recruit =>
    "recruit"
  | .youRecruit =>
    "you recruit"
  | .createTreasureTapped =>
    "create a tapped Treasure token"
  | .createTreasure =>
    "create a Treasure token"
  | .exileTop =>
    "exile the top card of your library. Until the end of your next turn, you may play that card"
  | .sourceGetsAndTeamTrample p =>
    s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
  | .untapPlusOneIfSubtype subtype =>
    s!"untap {noun}. If that creature is a {subtype}, put a +1/+1 counter on it"
  | .plusOneEachYouControl =>
    "put a +1/+1 counter on each creature you control"
  | .drawAndLoseLife =>
    "you draw a card and lose 1 life"
  | .amassGoblins n =>
    s!"amass Goblins {n}"
  | .createTokens kind n tapped =>
    TokenKind.createPhrase kind n (tapped := tapped)
  | .createThenAttach kind =>
    s!"{TokenKind.createPhrase kind 1}, then attach this Equipment to it"
  | .amassThenAttach n =>
    s!"amass Goblins {n}, then attach this Equipment to the amassed Army"
  | .attachSourceToTarget =>
    s!"attach it to {noun}"
  | .searchBasicToHand =>
    "search your library for a basic land card, reveal it, put it into your hand, then shuffle"
  | .gainLifeSearchBasicOnTop n =>
    s!"you gain {n} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .plusOneEachOtherGainLife =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .destroyOppArtifactsEnchantmentsGainLife =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .damageEqualSubtypeToEachOpponent subtype =>
    let plural :=
      if subtype == "Dwarf" then "Dwarves"
      else if subtype.endsWith "s" then subtype
      else subtype ++ "s"
    s!"it deals damage equal to the number of {plural} you control to each opponent"
  | .damageEqualTreasures =>
    s!"it deals damage equal to the number of Treasures you control to {noun}"
  | .loseLifeCreateTreasure =>
    "you lose 1 life and create a Treasure token"
  | .dealDamageDestroyIfSubtype n subtype =>
    s!"it deals {n} damage to {noun}. If a {subtype} is dealt damage this way, destroy it"
  | .attachEquipmentToCreature =>
    "attach target Equipment you control to up to one target creature you control"
  | .addMana types =>
    let parts := types.toList.map (fun t => s!"\{{t.letter}}")
    s!"add {String.intercalate "" parts}"
  | .defenderSacsLeastPower =>
    "defending player sacrifices a creature with the least power among creatures they control"
  | .createAxe =>
    "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
  | .tapOppOrUntapYours =>
    "choose one — tap target creature an opponent controls; untap target creature you control"
  | .becomePT p t =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .returnOtherPlusOne =>
    "return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .lookAtTopRevealTypes n types =>
    let joined :=
      match types.toList with
      | [a, b] => s!"a {a} or {b} card"
      | xs => s!"a {String.intercalate " or " xs} card"
    s!"look at the top {n} cards of your library. You may reveal {joined} from among them and put it into your hand. Put the rest on the bottom of your library in a random order"
  | .pumpAndDamageOpponents n =>
    s!"this gets +1/+1 until end of turn and deals {n} damage to each opponent"
  | .createTappedTreasuresEqualOppArtifacts =>
    "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
  | .gainControlOppUntilEot =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .othersGetAndOppsGet subtypes p t oppP oppT =>
    let who :=
      if subtypes == #["Goblin", "Orc"] then "other Goblins and Orcs you control"
      else s!"other {StaticAbility.joinedSubtypes subtypes} you control"
    s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
  | .putNonlandMvAtMostFromGy mv =>
    s!"put up to one target nonland permanent card with mana value {mv} or less from a graveyard onto the battlefield under its owner's control"
  | .honeEachEquipment =>
    "put a hone counter on each Equipment you control"
  | .cascade =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .belladonnaTokenReward =>
    "you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control"
  | .bolgMaySacrifice =>
    "you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .bolgDealSacrificedPower =>
    s!"Bolg deals damage equal to the sacrificed creature's power to {noun}. If excess damage was dealt this way, amass Goblins X, where X is that excess damage"
  | .createSpiritsForEquipped =>
    "create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking"
  | .createTreasuresEqualDamagedPlayerArtifacts =>
    "you create a Treasure token for each artifact that player controls"
  | .deal1ThenAmassOrcs =>
    s!"this creature deals 1 damage to {noun}. Then amass Orcs 1"
  | .untapAttackersExtraCombat =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .eaglesCreateBirds =>
    "create a 4/4 white Bird Soldier creature token with flying for each creature returned to your hand this way"
  | .allianceMode =>
    "choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card"
  | .destroyOtherAmassControllerPower =>
    s!"destroy {noun}. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card"
  | .gollumMode =>
    "choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card"
  | .returnCreatureFromGyToHand =>
    s!"return {noun} to your hand"
  | .discardHandDrawDamageIfStory =>
    "you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, this deals X damage to each opponent"
  | .plusOneAndLifelink =>
    s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
  | .wolfPlusOneOrTreasure =>
    "choose one — • Put a +1/+1 counter on target Wolf you control. • Create a Treasure token"
  | .trampleCounterBecomeBear =>
    s!"put a trample counter on up to one {noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .castFromGyArtifactInstantSorcery =>
    "you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead"
  | .millThenSubtypeToHand n subtype =>
    s!"mill {n} cards, then put all {subtype} cards from among them into your hand"
  | .exileOppNonlandEachUntilLeaves =>
    "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
  | .plusOneEqualLastKnownMv =>
    s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
  | .createAxeAttach =>
    "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control"
  | .equippedAttackersGainDoubleStrike =>
    "each equipped attacking creature gains double strike until end of turn"
  | .tapEnchantedRemoveCounters =>
    "tap enchanted creature and remove all counters from it"
  | .revealTopPutRandomCreature n =>
    s!"reveal the top {n} cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order"
  | .beginCombatIfDrawnTwoPump =>
    s!"if you've drawn two or more cards this turn, {noun} gets +3/+0 and gains first strike until end of turn"
  | .mountainQuestDragon =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .millPlayer n =>
    s!"{noun} mills {n} cards"
  | .treasuresPerChosenType =>
    "choose a creature type. Create a Treasure token for each creature you control of that type"
  | .revealUntilCreature =>
    "reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. Put the rest on the bottom of your library in a random order"
  | .attackSacPlusOneEqualPower =>
    "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .amassGoblinsEqualPower =>
    "amass Goblins X, where X is this creature's power"
  | .payReturnFromGy =>
    "you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand"
  | .lootLandEntersTapped =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .honePerOppAttach =>
    "put a hone counter on this for each creature target opponent controls. Attach this to up to one target creature you control"
  | .damageTargetOpponent n =>
    s!"this deals {n} damage to {noun}"
  | .millThatManyLost =>
    "that player mills that many cards"
  | .drawPerFatGraveyard =>
    "draw a card for each graveyard with seven or more cards in it"
  | .copySelfNonlegendary =>
    "if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary"
  | .maySacDrawTreasure =>
    "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
  | .targetOpponentLosesLife n =>
    s!"{noun} loses {n} life"
  | .attachEquipmentThenFight =>
    "attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature"
  | .plusOneVigilance n =>
    s!"put {plusOnePlusOneCountersPhrase n} on {noun}. It gains vigilance until end of turn"
  | .drawThenDiscardN n =>
    s!"draw {cardPhrase n}, then discard a card"
  | .returnAsArtifact =>
    "if they were a creature, return them to the battlefield. They're an artifact"
  | .mayDrawXDiscard2 =>
    "you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard two cards"
  | .plusOneEachIfCityBlessing =>
    "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
  | .castInstantSorceryFromHand =>
    "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
  | .drawPlusOneSource =>
    "draw a card and put a +1/+1 counter on this"
  | .exileLandsThenReturnTapped =>
    "exile up to three target lands you control, then return them to the battlefield tapped under their owner's control"
  | .castInstantSorceryMvAtMost =>
    "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
  | .grimaImpulse =>
    "that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order"
  | .palantir =>
    "put an influence counter on this and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on this, and that player loses life equal to the total mana value of those cards"
  | .millThenCopy =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .amassOrcs n =>
    s!"amass Orcs {n}"
  | .ringTempts =>
    "the Ring tempts you"
  | .mayDiscardHandDraw n =>
    s!"you may discard your hand. If you do, draw {cardPhrase n}"
  | .treasuresEqualLastKnown =>
    "create that many Treasure tokens"
  | .protectionEverything =>
    "if you cast it, you gain protection from everything until your next turn"
  | .loseLifePerBurden =>
    "you lose 1 life for each burden counter on this"
  | .revealSaga =>
    "reveal cards from the top of your library until you reveal a Saga card. Put that card onto the battlefield and the rest on the bottom of your library in a random order"
  | .sacDamagersRingTempts =>
    "each opponent sacrifices a creature of their choice that dealt combat damage to you this turn. The Ring tempts you"
  | .printed text => text

/-- True when this trigger fires only once each turn. -/
def onceEachTurn (ab : TriggeredAbility) : Bool :=
  ab.timing.onceEachTurn

/-- Intervening power-at-most threshold for another creature entering. -/
def anotherCreaturePowerAtMost? (ab : TriggeredAbility) : Option Int :=
  ab.timing.anotherCreaturePowerAtMost

def toNotation (ab : TriggeredAbility) : String :=
  match ab with
  | .onEnterBolgMaySacrifice =>
    "When Bolg enters, you may sacrifice another creature. When you do, Bolg deals damage equal to that creature's power to another target creature. If excess damage was dealt this way, amass Goblins X, where X is that excess damage."
  | .onEquippedAttacksCreateSpirits =>
    "Whenever equipped creature attacks, create two tapped 1/1 white Spirit creature tokens with flying. If that creature is legendary, instead create two of those tokens that are tapped and attacking."
  | .onCombatDamageCreateTreasuresEqualPlayerArtifacts =>
    "Whenever this creature deals combat damage to a player, you create a Treasure token for each artifact that player controls."
  | .onEnterOrOpponentDrawsDeal1AmassOrcs =>
    "When this creature enters and whenever an opponent draws a card except the first one they draw in each of their draw steps, this creature deals 1 damage to any target. Then amass Orcs 1."
  | .onOpponentDrawsSecondCreateTreasure =>
    "Whenever an opponent draws their second card each turn, you create a Treasure token."
  | .onAttackWithTotalPowerUntapExtraCombat n =>
    s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn, untap all attacking creatures. After this phase, there is an additional combat phase."
  | .onAnotherCreatureYouControlEntersAlliance =>
    "Alliance — Whenever another creature you control enters, choose one that hasn't been chosen this turn — • Add {G}{G}{G}. • Put a +1/+1 counter on each creature you control. • Scry 2, then draw a card."
  | .onEnterDestroyOtherAmassControllerPower =>
    "When Azog enters, destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card."
  | .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2 =>
    "Whenever a Dwarf you control deals combat damage to a player or battle, create two Treasure tokens."
  | .onOpponentCastsChosenParityModes =>
    "Whenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen — • Put a +1/+1 counter on Gollum. • Each opponent loses 2 life and you gain 2 life. • Draw a card."
  | .onCastColorCreateTokens .white .humanSoldier 1 =>
    "Whenever you cast a white spell, create a 1/1 white Human Soldier creature token."
  | .onCastColorScry .blue 2 =>
    "Whenever you cast a blue spell, scry 2."
  | .onCastColorDamageOpponent .red 3 =>
    "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
  | .onCastColorPump .green 4 4 =>
    "Whenever you cast a green spell, target creature gets +4/+4 until end of turn."
  | .onEnterReturnCreatureFromGyToHand =>
    "When this enchantment enters, return target creature card from your graveyard to your hand."
  | .onThisOrAnotherSubtypeEntersDiscardHand "Dwarf" =>
    "Whenever Balin or another Dwarf you control enters, you may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, Balin deals X damage to each opponent."
  | .onAttackCastFromGyArtifactInstantSorcery =>
    "Whenever Bilbo attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead."
  | .onEnterCreateAxeAttach =>
    "When Dáin enters, create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}. When you do, attach it to target creature you control."
  | .onAttackEquippedGainDoubleStrike =>
    "Whenever Dáin attacks, each equipped attacking creature gains double strike until end of turn."
  | .onEnterTapEnchantedRemoveCounters =>
    "When this Aura enters, tap enchanted creature and remove all counters from it."
  | .onDiesRevealTopPutRandomCreature n =>
    s!"When this artifact is put into a graveyard from the battlefield, reveal the top {n} cards of your library. Put a random creature card from among them onto the battlefield. Put the rest on the bottom of your library in a random order."
  | .onYourBeginCombatIfDrawnTwoPumpFirstStrike =>
    "At the beginning of combat on your turn, if you've drawn two or more cards this turn, another target creature you control gets +3/+0 and gains first strike until end of turn."
  | .onEnterHonePerOppCreaturesAttach =>
    "When Sting enters, put a hone counter on Sting for each creature target opponent controls. Attach Sting to up to one target creature you control."
  | .onEnterIfNotTokenCopySelf =>
    "When The Notary Hobbits enter, if they're not a token, create two tokens that are copies of them, except the tokens aren't legendary."
  | .onEnterAttachEquipmentThenFight =>
    "When Thorin enters, attach any number of target Equipment you control to target creature you control. When one or more Equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature."
  | .onAnotherLegendarySubtypeEntersLoot "Elf" =>
    "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
  | .onDiesReturnAsArtifact =>
    "When Tom, Bert, and William die, if they were a creature, return them to the battlefield. They're an artifact."
  | .onAnotherSubtypeEntersPlusOneOnSource "Wolf" 2 =>
    "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
  | .onLandYouControlEntersDrawPlusOneSource =>
    "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
  | .onEnterExileLandsThenReturnTapped =>
    "When Gandalf enters, exile up to three target lands you control, then return them to the battlefield tapped under their owner's control."
  | .onCombatDamageImpulseInstantSorcery =>
    "Whenever Gríma deals combat damage to a player, that player exiles cards from the top of their library until they exile an instant or sorcery card. You may cast that card without paying its mana cost. Then that player puts the exiled cards that weren't cast this way on the bottom of their library in a random order."
  | .onYourEndStepPalantir =>
    "At the beginning of your end step, put an influence counter on Palantír of Orthanc and scry 2. Then target opponent may have you draw a card. If that player doesn't, you mill X cards, where X is the number of influence counters on Palantír of Orthanc, and that player loses life equal to the total mana value of those cards."
  | .onDealtNoncombatDamageCreateTreasures =>
    "Whenever Smaug is dealt noncombat damage, create that many Treasure tokens."
  | .onEnterIfCastProtectionEverything =>
    "When The One Ring enters, if you cast it, you gain protection from everything until your next turn."
  | .onYourUpkeepLoseLifePerBurden =>
    "At the beginning of your upkeep, you lose 1 life for each burden counter on The One Ring."
  | .onLandYouControlEntersPayReturnFromGy =>
    "Landfall — Whenever a land you control enters, you may pay {1}{G}{U}. If you do, return this card from your graveyard to your hand."
  | .onPutCountersOnGoblinOrcArmyDamageOpp =>
    "Whenever you put one or more counters on a Goblin, Orc, or Army you control, The Great Goblin deals 2 damage to target opponent."
  | .printed text => text
  | _ =>
    match ab.resolution with
    | .printed text => text
    | _ =>
      let t := ab.timing
      if t.events.contains .equippedAttacksAlone then
        "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
      else
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
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
deriving Repr, Inhabited, BEq

/-- One printed Saga chapter line (`I — …`, `III, IV — …`). -/
structure SagaChapter where
  roman : String
  effect : String
deriving Repr, Inhabited, BEq

/-- Printed Saga (CR 714): reminder plus chapter abilities. -/
structure SagaDef where
  /-- Roman numeral in “Sacrifice after …”. -/
  sacrificeAfter : String
  chapters : Array SagaChapter
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
  /-- This permanent enters tapped (CR 110.5b exception). -/
  entersTapped : Bool := false
  /-- `{T}: Add one of these mana types` as a single choice ability
  (e.g. `{T}: Add {G} or {U}`). -/
  tapAddOneOf : Array ManaType := #[]
  /-- `{T}: Add one mana of any color` with no spending restriction. -/
  tapAddAnyColor : Bool := false
  /-- `{T}, Sacrifice this permanent: Add one mana of any color` (Treasure). -/
  tapSacrificeAddAnyColor : Bool := false
  /-- This object is a token (CR 111). -/
  isToken : Bool := false
  /-- This spell can't be countered. -/
  cantBeCountered : Bool := false
  /-- You may cast this as though it had flash if you control this subtype. -/
  flashIfYouControlSubtype : Option String := none
  /-- Printed ward cost (CR 702.21), e.g. `Ward {3}`. -/
  ward : Option Nat := none
  /-- Flashback cost (CR 702.34). -/
  flashback : Option ManaCost := none
  /-- This permanent enters tapped unless you control a legendary creature. -/
  entersTappedUnlessLegendary : Bool := false
  /-- This permanent enters tapped unless you control an Equipment. -/
  entersTappedUnlessEquipment : Bool := false
  /-- `{T}: Add one mana of any color. Spend this mana only to cast a
  legendary spell, and that spell can't be countered.` -/
  tapAddAnyColorForLegendary : Bool := false
  /-- This spell costs {X} less to cast, where X is the total power of
  creatures you control with flying. -/
  costReductionEqualFlyingPower : Bool := false
  /-- Crew `n` (CR 702.122). -/
  crew : Option Nat := none
  /-- `{T}: Add two mana in any combination of these types`. -/
  tapAddTwoAmong : Array ManaType := #[]
  /-- Modal spell is “Choose one or both” rather than “Choose one”. -/
  chooseOneOrBoth : Bool := false
  /-- “Choose one. If you control a {subtype}, you may choose two instead.” -/
  chooseTwoIfYouControlSubtype : Option String := none
  /-- `{T}: Add one mana of any color among legendary creatures and
  planeswalkers you control`. -/
  tapAddAnyColorAmongLegendaries : Bool := false
  /-- `{T}: Add these mana types. Spend this mana only to cast …`. -/
  tapAddRestricted : Option (Array ManaType × String) := none
  /-- `{T}, Pay n life: Add one of these types`. -/
  tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none
  /-- As this land enters, you may pay `n` life. If you don't, it enters tapped. -/
  entersTappedUnlessPayLife : Option Nat := none
  /-- `{T}: Add one mana of any color in your commander's color identity`. -/
  tapAddCommanderIdentity : Bool := false
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
  /-- As this enchantment enters, choose a creature type. -/
  asEntersChooseCreatureType : Bool := false
  /-- Printed Saga chapters (CR 714). -/
  saga : Option SagaDef := none
  /-- Affinity for this subtype (CR 702.40). -/
  affinityForSubtype : Option String := none
  /-- This spell costs {X} less, where X is the greatest number of artifacts
  an opponent controls. -/
  costReductionEqualOppArtifacts : Bool := false
  /-- Gift a Treasure (you may promise an opponent a Treasure). -/
  giftTreasure : Bool := false
  /-- If you would create a Food token, also create a Treasure. -/
  foodAlsoCreatesTreasure : Bool := false
  /-- Other creatures enter with +1/+1 counters equal to this creature's toughness. -/
  othersEnterWithPlusOneEqualToughness : Bool := false
  /-- This gets +N/+0 for each Mountain you control. -/
  powerPerMountain : Nat := 0
  /-- You may play an additional land if you control another of this subtype. -/
  extraLandIfOtherSubtype : Option String := none
  /-- `{T}: Add {C} for each permanent you control of this subtype`. -/
  tapAddColorlessPerSubtype : Option String := none
  /-- Cascade printed `n` times (`Cascade, cascade` when `n = 2`). -/
  cascade : Nat := 0
  /-- Optional kicker cost (CR 702.32). Paid at most once as an additional cost. -/
  kicker : Option ManaCost := none
  /-- If one or more tokens would be created under your control, twice that
  many of those tokens are created instead (e.g. Bard, King of Dale). -/
  tokenDoubling : Bool := false
  /-- If you would draw a card except the first one you draw in each of your
  draw steps, draw two cards instead. -/
  drawTwoExceptFirstDrawStep : Bool := false
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / `tapAddManaForEach` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- If a creature an opponent controls would die, exile it instead
  (e.g. Head of the Hunt). -/
  exileOppCreaturesInstead : Bool := false
  /-- You may look at the top card of your library any time
  (e.g. Elven Chorus). -/
  mayLookAtTopAnytime : Bool := false
  /-- You may cast creature spells from the top of your library
  (e.g. Elven Chorus). Does not grant flash or change timing. -/
  mayCastCreaturesFromTop : Bool := false
  /-- Creatures you control have `{T}: Add one mana of any color`
  (e.g. Elven Chorus). -/
  grantCreaturesTapAddAnyColor : Bool := false
  /-- The first creature spell you cast each turn costs this much generic
  less (e.g. Radagast of Rhosgobel). -/
  firstCreatureCostsLess : Nat := 0
  /-- The first creature spell you cast each turn can be cast as though it
  had flash (e.g. Radagast of Rhosgobel). -/
  firstCreatureHasFlash : Bool := false
  /-- Hexproof and indestructible while you control this many lore counters
  among Sagas (e.g. Tom Bombadil). -/
  hexproofIndestructibleIfLore : Option Nat := none
  /-- This creature enters with an indestructible counter. -/
  entersWithIndestructibleCounter : Bool := false
  /-- As this permanent enters, choose odd or even (Gollum, Riddle Master). -/
  asEntersChooseOddEven : Bool := false
  /-- Spells you cast from anywhere other than your hand cost this much
  generic mana less (e.g. Bilbo, Thief in the Night). -/
  costReductionNotFromHand : Nat := 0
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
def isPlaneswalker (c : CardDef) : Bool := c.hasType .planeswalker
def isBattle (c : CardDef) : Bool := c.hasType .battle
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype "Aura"
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype "Equipment"

/-- Names a player may choose for “choose a card name”, including an
Adventure face (Gatherer ruling on adventurer cards). -/
def choosableNames (c : CardDef) : Array String :=
  match c.adventure with
  | some adv => #[c.name, adv.name]
  | none => #[c.name]

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

/-- True when the printed spell may be announced with zero targets. -/
def allowsZeroTargets (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.allowsZeroTargets
  | none => false

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
  c.simpleTapAddMana ++ c.tapAddOneOf ++ c.tapAddManaForEach.map (·.mana) ++
    (if c.tapAddAnyColorEqualToPower || c.tapAddAnyColorForInstantOrSorcery ||
        c.tapAddAnyColor || c.tapSacrificeAddAnyColor ||
        c.tapAddAnyColorForLegendary || c.tapAddTwoAmong.size >= 2 ||
        c.tapAddAnyColorAmongLegendaries || c.tapAddCommanderIdentity then
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
#guard StaticAbility.toNotation (.extraTriggerAnotherYouControl #["Wolf"] true) ==
  "If a triggered ability of another Wolf or battle you control triggers, that ability triggers an additional time."
#guard StaticAbility.toNotation (.extraTriggerIfEnduringStorySubtype "Dwarf") ==
  "As long as you have an enduring story, if a triggered ability of a Dwarf you control triggers, that ability triggers an additional time."
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

#guard TriggeredAbility.toNotation .onTokenYouControlEntersBelladonna ==
  "Whenever a token you control enters, you gain 1 life if this is the first time this ability has resolved this turn. If it's the second time, draw a card. If it's the third time, put a +1/+1 counter on each creature you control."
#guard TriggeredAbility.toNotation .onActivateCreatureAbilityDrawOnce ==
  "Whenever you activate an ability of a creature, draw a card. This ability triggers only once each turn."
#guard TriggeredAbility.firesOn .onTokenYouControlEntersBelladonna .tokenYouControlEnters
#guard TriggeredAbility.firesOn .onActivateCreatureAbilityDrawOnce .youActivateCreatureAbility
#guard TriggeredAbility.onceEachTurn .onActivateCreatureAbilityDrawOnce
#guard
  let c : CardDef := {
    name := "Smaug, the Great Calamity"
    types := #[.creature]
    adventure := some {
      name := "Spew Flame"
      manaCost := ManaCost.ofGenericAndColor 4 .red
      oracleText := ""
      spellEffect := some (.dealDamageToCreature 5)
    }
  }
  c.choosableNames == #["Smaug, the Great Calamity", "Spew Flame"]

end Mtg.Engine
