import Mtg.Engine.Card.Text

/-!
# Targeting (CR 115.1 / 601.2c / 603.3d)

Targeting shapes shared by spells, activated abilities, and triggered
abilities, plus the `HasTargeting` interface.
-/

namespace Mtg.Engine

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
  /-- Target tapped creature an opponent controls. -/
  | oppTappedCreature
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
  /-- Target creature card with mana value `n` or less in your graveyard. -/
  | creatureCardInYourGraveyardMvAtMost (n : Nat)
  /-- Target legendary creature you control. -/
  | legendaryCreatureYouControl
  /-- Target creature you control with power `n` or less. -/
  | creatureYouControlPowerAtMost (n : Int)
  /-- Target artifact. -/
  | artifact
  /-- Target artifact an opponent controls. -/
  | oppArtifact
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
  /-- Up to one target creature, then target player (e.g. Meager Meal). -/
  | upToOneCreatureThenPlayer
  /-- Target attacking or blocking creature. -/
  | attackingOrBlockingCreature
  /-- Target creature with mana value `n` or less. -/
  | creatureMvAtMost (n : Nat)
  /-- Target creature with toughness `n` or greater. -/
  | creatureToughnessAtLeast (n : Int)
  /-- Target enchantment with mana value `n` or greater. -/
  | enchantmentMvAtLeast (n : Nat)
  /-- Target noncreature artifact. -/
  | noncreatureArtifact
  /-- An activated or triggered ability you control from a creature source
  (Echo; MSH 74). -/
  | stackAbilityFromCreatureSource
  /-- An activated or triggered ability you control from an artifact source
  (Scientist Supreme of A.I.M.; MSH 87). -/
  | stackAbilityFromArtifactSource
  /-- Target creature an opponent controls with power `n` or less. -/
  | oppCreaturePowerAtMost (n : Int)
  /-- Target creature an opponent controls that dealt damage this turn. -/
  | oppCreatureDealtDamageThisTurn
  /-- Target nonland, nontoken permanent. -/
  | nonlandNontoken
  /-- Target permanent card in your graveyard. -/
  | permanentCardInYourGraveyard
  /-- Target Equipment, instant, or sorcery card in your graveyard. -/
  | equipmentInstantOrSorceryInYourGraveyard
  /-- Target artifact or enchantment card in your graveyard. -/
  | artEnchCardInYourGraveyard
  /-- Target artifact you control. -/
  | artifactYouControl
  /-- Two target artifacts you control. -/
  | twoArtifactsYouControl
  /-- Target creature you control that's attacking alone. -/
  | attackingAloneCreatureYouControl
  /-- Target noncreature artifact or noncreature enchantment. -/
  | noncreatureArtifactOrEnchantment
  /-- Target permanent or player. -/
  | permanentOrPlayer
  /-- Up to two target creatures whose total mana value is `n` or less. -/
  | upToTwoCreaturesTotalMvAtMost (n : Nat)
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
  /-- 0-based slot indices that are optional (“up to one”). Announcing no
  target for such a slot advances to the next instance (CR 115.1c / 601.2c). -/
  optionalSlots : Array Nat := #[]
  /-- True when this shape targets a spell on the stack. -/
  stackSpell : Bool := false
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
  | .oppTappedCreature =>
    { noun := "target tapped creature an opponent controls" }
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
    { noun := "target spell", stackSpell := true }
  | .creatureSpell =>
    { noun := "target creature spell", stackSpell := true }
  | .creatureSpellPTAtMost n =>
    { noun := s!"target creature spell with power or toughness {n} or less",
      stackSpell := true }
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
        if subtypes.isEmpty then "target creature you control"
        else s!"target {orJoin subtypes.toList} you control"
      prefer := .own }
  | .permanent =>
    { noun := "target permanent", prefer := .ownThenOpponent }
  | .creatureCardInYourGraveyard =>
    { noun := "target creature card from your graveyard", prefer := .last }
  | .creatureCardInYourGraveyardMvAtMost n =>
    { noun := s!"target creature card with mana value {n} or less from your graveyard",
      prefer := .last }
  | .legendaryCreatureYouControl =>
    { noun := "target legendary creature you control", prefer := .own }
  | .creatureYouControlPowerAtMost n =>
    { noun := s!"target creature you control with power {n} or less", prefer := .own }
  | .artifact =>
    { noun := "target artifact" }
  | .oppArtifact =>
    { noun := "target artifact an opponent controls" }
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
  | .upToOneCreatureThenPlayer =>
    { count := 2
      noun := "up to one target creature and target player"
      prefer := .own
      slots := #[.creature, .player]
      optionalSlots := #[0] }
  | .attackingOrBlockingCreature =>
    { noun := "target attacking or blocking creature" }
  | .creatureMvAtMost n =>
    { noun := s!"target creature with mana value {n} or less" }
  | .creatureToughnessAtLeast n =>
    { noun := s!"target creature with toughness {n} or greater" }
  | .enchantmentMvAtLeast n =>
    { noun := s!"target enchantment with mana value {n} or greater" }
  | .noncreatureArtifact =>
    { noun := "target noncreature artifact" }
  | .stackAbilityFromCreatureSource =>
    { noun := "target activated or triggered ability you control from a creature source",
      stackSpell := true }
  | .stackAbilityFromArtifactSource =>
    { noun := "target activated or triggered ability you control from an artifact source",
      stackSpell := true }
  | .oppCreaturePowerAtMost n =>
    { noun := s!"target creature an opponent controls with power {n} or less" }
  | .oppCreatureDealtDamageThisTurn =>
    { noun := "target creature an opponent controls that dealt damage this turn" }
  | .nonlandNontoken =>
    { noun := "target nonland, nontoken permanent", prefer := .ownThenOpponent }
  | .permanentCardInYourGraveyard =>
    { noun := "target permanent card in your graveyard", prefer := .last }
  | .equipmentInstantOrSorceryInYourGraveyard =>
    { noun := "target Equipment, instant, or sorcery card from your graveyard",
      prefer := .last }
  | .artEnchCardInYourGraveyard =>
    { noun := "target artifact or enchantment card from your graveyard",
      prefer := .last }
  | .artifactYouControl =>
    { noun := "target artifact you control", prefer := .own }
  | .twoArtifactsYouControl =>
    { count := 2
      noun := "target artifact you control and a second target artifact you control"
      prefer := .own
      slots := #[.artifactYouControl, .artifactYouControl] }
  | .attackingAloneCreatureYouControl =>
    { noun := "target creature you control that's attacking alone", prefer := .own }
  | .noncreatureArtifactOrEnchantment =>
    { noun := "target noncreature artifact or noncreature enchantment" }
  | .permanentOrPlayer =>
    { noun := "target permanent or player", prefer := .ownThenOpponent }
  | .upToTwoCreaturesTotalMvAtMost n =>
    { count := 2
      noun := s!"up to two target creatures with total mana value {n} or less" }

/-- How many targets must be announced for this shape (CR 601.2c). -/
def targetCount (k : EffectTargetKind) : Nat :=
  k.spec.count

/-- Oracle-style noun phrase for this targeting shape. -/
def noun (k : EffectTargetKind) : String :=
  k.spec.noun

/-- Default demonstration-agent preference for this targeting shape. -/
def defaultPreference (k : EffectTargetKind) : TargetPreference :=
  k.spec.prefer

/-- True when this shape targets a spell on the stack. -/
def targetsStackSpell (k : EffectTargetKind) : Bool :=
  k.spec.stackSpell

/-- Kind of the `i`th instance of the word “target” (0-based). Atomic shapes
return themselves for every slot. -/
def slotKind (k : EffectTargetKind) (i : Nat) : EffectTargetKind :=
  k.spec.slots[i]?.getD k

/-- True when the `i`th instance of the word “target” is optional (“up to one”). -/
def isOptionalSlot (k : EffectTargetKind) (i : Nat) : Bool :=
  k.spec.optionalSlots.contains i

/-- Oracle-style noun for the `i`th instance, with “up to one” when optional. -/
def announcedNoun (k : EffectTargetKind) (i : Nat) : String :=
  let n := (k.slotKind i).noun
  if k.isOptionalSlot i && !n.startsWith "up to " then
    s!"up to one {n}"
  else n

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

end Mtg.Engine
