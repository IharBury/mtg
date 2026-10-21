import Mtg.Engine.Card.Text
import Mtg.Engine.TypeLine

/-!
# Targeting (CR 115.1 / 601.2c / 603.3d)

Targeting shapes shared by spells, activated abilities, and triggered
abilities, plus the `HasTargeting` interface.
-/

namespace Mtg.Engine

/-- Where a filtered target is found (CR 115.1). -/
inductive TargetZone where
  /-- Target zone kind: battlefield (`false, false, false`), your graveyard (`true, false, false`), any graveyard (`false, true, false`), stack (`true, true, false`), player (`false, false, true`), spell or creature (`true, false, true`), or any target (`false, true, true`, CR 115.4). -/
  | targetZoneKind (alt1 : Bool := false) (alt2 : Bool := false) (crossOrPlayer : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace TargetZone
@[match_pattern] abbrev battlefield : TargetZone := .targetZoneKind false false false
@[match_pattern] abbrev yourGraveyard : TargetZone := .targetZoneKind true false false
@[match_pattern] abbrev anyGraveyard : TargetZone := .targetZoneKind false true false
@[match_pattern] abbrev stack : TargetZone := .targetZoneKind true true false
@[match_pattern] abbrev player : TargetZone := .targetZoneKind false false true
@[match_pattern] abbrev spellOrCreature : TargetZone := .targetZoneKind true false true
@[match_pattern] abbrev anyTarget : TargetZone := .targetZoneKind false true true
end TargetZone

/-- Multiple-target, sequential-slot, controller, graveyard, stack, or player targeting shapes (CR 115.1 / 601.2c). -/
inductive MultiTarget where
  | multiTargetKind (n : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false)
      (alt3 : Bool := false) (alt4 : Bool := false)
      (ownAndOpp : Bool := false) (mvAtMost : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who controls (or, for a card in a graveyard, owns) a filtered target, unified with `MultiTarget`. -/
abbrev TargetController := MultiTarget

namespace TargetController
@[match_pattern] abbrev targetControllerKind (idx : Nat := 0) (you : Bool := false) (opponent : Bool := false)
    (eachOpponent : Bool := false) (specificSeat : Bool := false) : TargetController :=
  .multiTargetKind idx you opponent eachOpponent specificSeat false false
@[match_pattern] abbrev controllerKind (you : Bool := false) (opponent : Bool := false) (eachOpponent : Bool := false) : TargetController :=
  .targetControllerKind 0 you opponent eachOpponent false
@[match_pattern] abbrev specific (idx : Nat) : TargetController := .targetControllerKind idx false false false true
@[match_pattern] abbrev any : TargetController := .controllerKind false false false
@[match_pattern] abbrev you : TargetController := .controllerKind true false false
@[match_pattern] abbrev opponent : TargetController := .controllerKind false true false
@[match_pattern] abbrev eachOpponent : TargetController := .controllerKind false true true
end TargetController

/-- Type-line restrictions on a `TargetFilter` (CR 205). -/
structure TargetTypeFilter where
  /-- The target has at least one of these card types. Empty means any
  permanent, card, or spell. -/
  types : Array CardType := #[]
  /-- The target has at least one of these subtypes. Empty means any subtype. -/
  subtypes : Array String := #[]
  /-- A legendary object also qualifies (“creature or legendary spell”). -/
  orLegendary : Bool := false
  nonland : Bool := false
  noncreature : Bool := false
  /-- Not an Aura (“non-Aura enchantment”). -/
  nonAura : Bool := false
  /-- A permanent card (CR 110.4b). -/
  permanentCard : Bool := false
  nontoken : Bool := false
  legendary : Bool := false
  nonlegendary : Bool := false
deriving Repr, Inhabited, BEq, DecidableEq

/-- Color, mana-value, toughness, keyword, and counter restrictions on a `TargetFilter` (CR 202 / 208 / 702 / 122). -/
structure TargetStatFilter where
  /-- The target is at least one of these colors. Empty means any color. -/
  colors : Array Color := #[]
  mvAtLeast : Option Nat := none
  mvAtMost : Option Nat := none
  toughnessAtLeast : Option Int := none
  withFlying : Bool := false
  withPlusOneCounter : Bool := false
  withHaste : Bool := false
deriving Repr, Inhabited, BEq, DecidableEq

/-- Permanent status, combat state, and turn-history restrictions on a `TargetFilter` (CR 110.5 / 508 / 509). -/
structure TargetCombatStateFilter where
  /-- Not the source of the spell or ability. -/
  another : Bool := false
  attacking : Bool := false
  attackingOrBlocking : Bool := false
  attackedThisTurn : Bool := false
  enteredThisTurn : Bool := false
  /-- Only a creature that is still untapped (“tap target untapped creature”). -/
  untapped : Bool := false
  nonattacking : Bool := false
  /-- Owned (not necessarily controlled) by the caster. -/
  ownedByYou : Bool := false
deriving Repr, Inhabited, BEq, DecidableEq

/-- A target described by characteristics, with the Oracle noun phrase that
names it. Every listed restriction must hold. -/
structure TargetFilter extends TargetTypeFilter, TargetStatFilter, TargetCombatStateFilter where
  noun : String
  zone : TargetZone := .battlefield
  controller : TargetController := .any
deriving Repr, Inhabited, BEq, DecidableEq

/-- A permanent target on the battlefield (CR 115.1 / 110.1). -/
inductive BattlefieldTarget where
  | battlefieldTargetKind (n : Int := 0) (mv : Nat := 0) (controller : TargetController := .any)
      (subtype : String := "") (subtypes : Array String := #[])
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (alt4 : Bool := false) (g1 : Bool := false) (g2 : Bool := false)
      (controlledKind : Bool := false) (boundKind : Bool := false) (subtypeKind : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

namespace BattlefieldTarget
@[match_pattern] abbrev booleanBattlefieldTarget (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (alt4 : Bool := false) (g1 : Bool := false) (g2 : Bool := false) : BattlefieldTarget :=
  .battlefieldTargetKind 0 0 .any "" #[] alt1 alt2 alt3 alt4 g1 g2 false false false
@[match_pattern] abbrev controlledPermanentTarget (controller : TargetController := .any) (alt1 : Bool := false)
    (alt2 : Bool := false) (artifactTarget : Bool := false) : BattlefieldTarget :=
  .battlefieldTargetKind 0 0 controller "" #[] alt1 alt2 artifactTarget false false false true false false
@[match_pattern] abbrev boundPermanentTarget (n : Int := 0) (mv : Nat := 0) (controller : TargetController := .any)
    (alt1 : Bool := false) (alt2 : Bool := false) (mvBound : Bool := false) : BattlefieldTarget :=
  .battlefieldTargetKind n mv controller "" #[] alt1 alt2 mvBound false false false false true false
/-- Target creature you control with `subtype` (`multi = false`) or any of `subtypes` (`multi = true`). -/
@[match_pattern] abbrev creatureYouControlSubtypes (subtype : String := "") (subtypes : Array String := #[]) (multi : Bool := false) : BattlefieldTarget :=
  .battlefieldTargetKind 0 0 .any subtype subtypes multi false false false false false false false true
@[match_pattern] abbrev creatureTarget (youControl : Bool := false) (another : Bool := false) (legendaryOrFlying : Bool := false) : BattlefieldTarget :=
  .booleanBattlefieldTarget youControl another legendaryOrFlying false false false
@[match_pattern] abbrev oppOrEquipmentTarget (alt1 : Bool := false) (alt2 : Bool := false) (defendingOrEquip : Bool := false) : BattlefieldTarget :=
  .booleanBattlefieldTarget alt1 alt2 defendingOrEquip false true false
@[match_pattern] abbrev twoTypes (includeCreature : Bool := false) (includeArtifact : Bool := true) (youControl : Bool := false) (orEnchantment : Bool := false) : BattlefieldTarget :=
  .booleanBattlefieldTarget includeCreature includeArtifact youControl orEnchantment false true
@[match_pattern] abbrev nonlandOrAttacking (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (attacking : Bool := false) : BattlefieldTarget :=
  .booleanBattlefieldTarget alt1 alt2 alt3 attacking true true
@[match_pattern] abbrev permanentOrPlaneswalker (controller : TargetController := .any) (creatureOrPw : Bool := false) (planeswalkerOnly : Bool := false) : BattlefieldTarget :=
  .controlledPermanentTarget controller creatureOrPw planeswalkerOnly false
@[match_pattern] abbrev artifact (controller : TargetController := .any) (tokenOnly : Bool := false) (noncreature : Bool := false) : BattlefieldTarget :=
  .controlledPermanentTarget controller tokenOnly noncreature true
@[match_pattern] abbrev creatureStatBound (n : Int) (controller : TargetController := .any) (anotherOrToughness : Bool := false) (atLeast : Bool := false) : BattlefieldTarget :=
  .boundPermanentTarget n 0 controller anotherOrToughness atLeast false
@[match_pattern] abbrev permanentMvBound (n : Nat) (enchantmentAtLeast : Bool := false) : BattlefieldTarget :=
  .boundPermanentTarget 0 n .any enchantmentAtLeast false true
@[match_pattern] abbrev creatureYouControl (another : Bool := false) (legendary : Bool := false) : BattlefieldTarget :=
  .creatureTarget true another legendary
@[match_pattern] abbrev creature (another : Bool := false) (withFlying : Bool := false) : BattlefieldTarget :=
  .creatureTarget false another withFlying
@[match_pattern] abbrev creatureWithFlying : BattlefieldTarget := .creatureTarget false false true
@[match_pattern] abbrev oppCreature (tapped : Bool := false) (dealtDamageThisTurn : Bool := false) : BattlefieldTarget :=
  .oppOrEquipmentTarget tapped dealtDamageThisTurn false
@[match_pattern] abbrev defendingOrEquipment (equipment : Bool := false) : BattlefieldTarget :=
  .oppOrEquipmentTarget equipment false true
@[match_pattern] abbrev defendingPlayerCreature : BattlefieldTarget := .oppOrEquipmentTarget false false true
@[match_pattern] abbrev equipmentYouControl : BattlefieldTarget := .oppOrEquipmentTarget true false true
@[match_pattern] abbrev artifactOrEnchantment (noncreature : Bool := false) : BattlefieldTarget :=
  .twoTypes noncreature true false true
@[match_pattern] abbrev nonland (opp : Bool := false) (nontoken : Bool := false) (colorless : Bool := false) : BattlefieldTarget :=
  .nonlandOrAttacking opp nontoken colorless false
@[match_pattern] abbrev attackingCreature (withoutFlying : Bool := false) (orBlocking : Bool := false) (aloneYouControl : Bool := false) : BattlefieldTarget :=
  .nonlandOrAttacking withoutFlying orBlocking aloneYouControl true
@[match_pattern] abbrev creatureYouControlSubtype (subtype : String) : BattlefieldTarget :=
  .creatureYouControlSubtypes subtype #[] false
@[match_pattern] abbrev creatureYouControlAnySubtype (subtypes : Array String) : BattlefieldTarget :=
  .creatureYouControlSubtypes "" subtypes true
@[match_pattern] abbrev creatureStatAtLeast (n : Int) (toughness : Bool := false) : BattlefieldTarget :=
  .creatureStatBound n .any toughness true
@[match_pattern] abbrev creaturePowerAtMost (n : Int) (controller : TargetController := .any) (another : Bool := false) : BattlefieldTarget :=
  .creatureStatBound n controller another false
@[match_pattern] abbrev permanent (controller : TargetController := .any) : BattlefieldTarget :=
  .permanentOrPlaneswalker controller false false
@[match_pattern] abbrev creatureOrPlaneswalker (controller : TargetController := .any) (planeswalkerOnly : Bool := false) : BattlefieldTarget :=
  .permanentOrPlaneswalker controller true planeswalkerOnly
@[match_pattern] abbrev creatureMvAtMost (n : Nat) : BattlefieldTarget := .permanentMvBound n false
@[match_pattern] abbrev enchantmentMvAtLeast (n : Nat) : BattlefieldTarget := .permanentMvBound n true
end BattlefieldTarget

/-- A card target in a graveyard (CR 115.1 / 404.1), unified with `MultiTarget`. -/
abbrev GraveyardTarget := MultiTarget

namespace GraveyardTarget
@[match_pattern] abbrev graveyardTargetKind (n : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false)
    (multiType : Bool := false) (mvAtMost : Bool := false) : GraveyardTarget :=
  .multiTargetKind n alt1 alt2 multiType mvAtMost false false
@[match_pattern] abbrev graveyardCardKind (alt1 : Bool := false) (alt2 : Bool := false) (multiType : Bool := false) : GraveyardTarget :=
  .graveyardTargetKind 0 alt1 alt2 multiType false
@[match_pattern] abbrev creatureCardInYourGraveyardMvAtMost (n : Nat) : GraveyardTarget :=
  .graveyardTargetKind n false false false true
@[match_pattern] abbrev elfOrOppGraveyardCard (opp : Bool := false) : GraveyardTarget := .graveyardCardKind opp false false
@[match_pattern] abbrev elfInYourGraveyard : GraveyardTarget := .graveyardCardKind false false false
@[match_pattern] abbrev oppGraveyardCard : GraveyardTarget := .graveyardCardKind true false false
@[match_pattern] abbrev cardInYourGraveyard (permanentAny : Bool := false) : GraveyardTarget := .graveyardCardKind permanentAny true false
@[match_pattern] abbrev multiTypeInYourGraveyard (equipInstSorc : Bool := false) : GraveyardTarget := .graveyardCardKind equipInstSorc false true
end GraveyardTarget

/-- A spell or ability target on the stack (CR 115.1 / 405.1), unified with `MultiTarget`. -/
abbrev StackTarget := MultiTarget

namespace StackTarget
@[match_pattern] abbrev stackTargetKind (n : Nat := 0) (alt : Bool := false) (ability : Bool := false) (ptAtMost : Bool := false) : StackTarget :=
  .multiTargetKind n alt ability ptAtMost false false false
@[match_pattern] abbrev spellOrAbility (alt : Bool := false) (ability : Bool := false) : StackTarget :=
  .stackTargetKind 0 alt ability false
@[match_pattern] abbrev creatureSpellPTAtMost (n : Nat) : StackTarget :=
  .stackTargetKind n false false true
@[match_pattern] abbrev spell (creatureOnly : Bool := false) : StackTarget := .spellOrAbility creatureOnly false
@[match_pattern] abbrev stackAbilityFromSource (fromCreature : Bool := true) : StackTarget := .spellOrAbility fromCreature true
end StackTarget

/-- A player target, or a cross-category target involving a player or graveyard
(CR 115.1 / 115.4), unified with `MultiTarget`. -/
abbrev PlayerTarget := MultiTarget

namespace PlayerTarget
/-- Target player/opponent (`crossZone = false`, `opponentOnly = alt1`) or cross-category target (`crossZone = true`: “any target”, permanent or player if `alt1`, or creature/graveyard creature card if `alt2`). -/
@[match_pattern] abbrev playerOrCrossZoneTarget (alt1 : Bool := false) (alt2 : Bool := false) (crossZone : Bool := false) : PlayerTarget :=
  .multiTargetKind 0 alt1 alt2 crossZone false false false
@[match_pattern] abbrev player (opponentOnly : Bool := false) : PlayerTarget := .playerOrCrossZoneTarget opponentOnly false false
@[match_pattern] abbrev crossZoneTarget (anyPermanent : Bool := false) (creatureOrGy : Bool := false) : PlayerTarget :=
  .playerOrCrossZoneTarget anyPermanent creatureOrGy true
@[match_pattern] abbrev playerOrPermanent (anyPermanent : Bool := false) : PlayerTarget := .playerOrCrossZoneTarget anyPermanent false true
@[match_pattern] abbrev creatureOrGyCreatureCard : PlayerTarget := .playerOrCrossZoneTarget false true true
end PlayerTarget

namespace MultiTarget
export TargetController (targetControllerKind controllerKind specific any you opponent eachOpponent)
export GraveyardTarget (
  graveyardTargetKind graveyardCardKind creatureCardInYourGraveyardMvAtMost
  elfOrOppGraveyardCard elfInYourGraveyard oppGraveyardCard
  cardInYourGraveyard multiTypeInYourGraveyard
)
export StackTarget (stackTargetKind spellOrAbility creatureSpellPTAtMost spell stackAbilityFromSource)
export PlayerTarget (playerOrCrossZoneTarget player crossZoneTarget playerOrPermanent creatureOrGyCreatureCard)
@[match_pattern] abbrev twoStepOrSameTarget (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (twoTargets : Bool := false) : MultiTarget :=
  .multiTargetKind 0 alt1 alt2 alt3 twoTargets false false
@[match_pattern] abbrev ownAndOppPermanent (oppFirst : Bool := false) (orPlaneswalker : Bool := false) (planeswalkerFirst : Bool := false) : MultiTarget :=
  .multiTargetKind 0 oppFirst orPlaneswalker planeswalkerFirst false true false
@[match_pattern] abbrev upToTwoCreaturesTotalMvAtMost (n : Nat) : MultiTarget :=
  .multiTargetKind n false false false false false true
@[match_pattern] abbrev playerAndCreature (creatureFirstUpToOne : Bool := false) : MultiTarget :=
  .twoStepOrSameTarget creatureFirstUpToOne false false false
@[match_pattern] abbrev equipmentThenCreatureYouControl (optionalEquipment : Bool := false) : MultiTarget :=
  .twoStepOrSameTarget optionalEquipment true false false
@[match_pattern] abbrev twoTargets (artifacts : Bool := false) (players : Bool := false) (sharingType : Bool := false) : MultiTarget :=
  .twoStepOrSameTarget artifacts players sharingType true
@[match_pattern] abbrev twoSameKind (artifacts : Bool := false) (players : Bool := false) : MultiTarget :=
  .twoStepOrSameTarget artifacts players false true
@[match_pattern] abbrev twoNonlandsSharingType : MultiTarget := .twoStepOrSameTarget false false true true
end MultiTarget

/-- Whom a spell, activated ability, or triggered ability may target
(CR 115.1 / 601.2c / 603.3d). Adding a targeting shape here is a compile error
in `EffectTargetKind.spec` and `Game.legalTargetsForAtomicKind` rather than
silently offering no targets. Multiple instances of the word “target” list
each slot in `spec` and are announced sequentially. Multiple targets of one
instance are chosen together. -/
inductive EffectTargetKind where
  /-- Atomic, filtered, or multi-target/sequential-slot targeting shape (CR 115.1 / 601.2c): `none` (all `none`), battlefield (`battlefieldOpt = some t`), graveyard (`graveyardOpt = some t`), stack (`stackOpt = some t`), player (`playerOpt = some t`), filtered (`filteredOpt = some f`), multi-filtered (`multiOpt = some (fs, optional)`), or sequence (`seqOpt = some t`). -/
  | atomicTargetKind (battlefieldOpt : Option BattlefieldTarget := Option.none)
      (graveyardOpt : Option GraveyardTarget := Option.none)
      (stackOpt : Option StackTarget := Option.none)
      (playerOpt : Option PlayerTarget := Option.none)
      (filteredOpt : Option TargetFilter := Option.none)
      (multiOpt : Option (Array TargetFilter × Array Nat) := Option.none)
      (seqOpt : Option MultiTarget := Option.none)
  /-- The instances of “target” of `a`, then those of `b`: two modes of one
  modal spell chosen together (CR 700.2). -/
  | pair (a b : EffectTargetKind)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Default demonstration-agent choice among legal targets (CR 601.2c), unified with `TargetZone`. -/
abbrev TargetPreference := TargetZone

namespace TargetPreference
/-- Preference kind: own (`false, false, false`), opponent (`true, false, false`), last (`false, true, false`), own then opponent (`true, true, false`), opponent player (`false, false, true`), or self player (`true, false, true`). -/
@[match_pattern] abbrev preferenceKind (alt1 : Bool := false) (alt2 : Bool := false) (playerPref : Bool := false) : TargetPreference :=
  .targetZoneKind alt1 alt2 playerPref
@[match_pattern] abbrev own : TargetPreference := .preferenceKind false false false
@[match_pattern] abbrev opponent : TargetPreference := .preferenceKind true false false
@[match_pattern] abbrev last : TargetPreference := .preferenceKind false true false
@[match_pattern] abbrev ownThenOpponent : TargetPreference := .preferenceKind true true false
@[match_pattern] abbrev opponentPlayer : TargetPreference := .preferenceKind false false true
@[match_pattern] abbrev selfPlayer : TargetPreference := .preferenceKind true false true
end TargetPreference

namespace TargetZone
export TargetPreference (preferenceKind own opponent last ownThenOpponent opponentPlayer selfPlayer)
end TargetZone

namespace EffectTargetKind

@[match_pattern] abbrev none : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none Option.none Option.none Option.none Option.none Option.none
@[match_pattern] abbrev battlefield (t : BattlefieldTarget) : EffectTargetKind :=
  .atomicTargetKind (some t) Option.none Option.none Option.none Option.none Option.none Option.none
@[match_pattern] abbrev graveyard (t : GraveyardTarget) : EffectTargetKind :=
  .atomicTargetKind Option.none (some t) Option.none Option.none Option.none Option.none Option.none
@[match_pattern] abbrev stack (t : StackTarget) : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none (some t) Option.none Option.none Option.none Option.none
@[match_pattern] abbrev playerTarget (t : PlayerTarget) : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none Option.none (some t) Option.none Option.none Option.none
@[match_pattern] abbrev filtered (f : TargetFilter) : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none Option.none Option.none (some f) Option.none Option.none
@[match_pattern] abbrev multi (fs : Array TargetFilter) (optional : Array Nat) : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none Option.none Option.none Option.none (some (fs, optional)) Option.none
@[match_pattern] abbrev sequence (t : MultiTarget) : EffectTargetKind :=
  .atomicTargetKind Option.none Option.none Option.none Option.none Option.none Option.none (some t)

-- Battlefield permanent target aliases (CR 115.1 / 110.1)
@[match_pattern] abbrev creatureYouControl : EffectTargetKind := .battlefield (.creatureYouControl false false)
@[match_pattern] abbrev anotherCreatureYouControl : EffectTargetKind := .battlefield (.creatureYouControl true false)
@[match_pattern] abbrev anotherCreature : EffectTargetKind := .battlefield (.creature true)
@[match_pattern] abbrev oppCreature : EffectTargetKind := .battlefield (.oppCreature false false)
@[match_pattern] abbrev oppTappedCreature : EffectTargetKind := .battlefield (.oppCreature true false)
@[match_pattern] abbrev creature : EffectTargetKind := .battlefield (.creature false)
@[match_pattern] abbrev creatureWithFlying : EffectTargetKind := .battlefield .creatureWithFlying
@[match_pattern] abbrev artifactOrLand : EffectTargetKind := .battlefield (.twoTypes false true false false)
@[match_pattern] abbrev colorlessNonland : EffectTargetKind := .battlefield (.nonland false false true)
@[match_pattern] abbrev artifactOrEnchantment : EffectTargetKind := .battlefield (.artifactOrEnchantment false)
@[match_pattern] abbrev artifactOrCreatureYouControl : EffectTargetKind := .battlefield (.twoTypes true true true false)
@[match_pattern] abbrev nonland : EffectTargetKind := .battlefield (.nonland false false false)
@[match_pattern] abbrev oppNonland : EffectTargetKind := .battlefield (.nonland true false false)
@[match_pattern] abbrev attackingCreatureWithoutFlying : EffectTargetKind := .battlefield (.attackingCreature true false false)
@[match_pattern] abbrev creatureYouControlSubtype (subtype : String) : EffectTargetKind :=
  .battlefield (.creatureYouControlSubtype subtype)
@[match_pattern] abbrev defendingPlayerCreature : EffectTargetKind := .battlefield .defendingPlayerCreature
@[match_pattern] abbrev creaturePowerAtLeast (n : Int) : EffectTargetKind := .battlefield (.creatureStatAtLeast n false)
@[match_pattern] abbrev creaturePowerAtMost (n : Int) : EffectTargetKind := .battlefield (.creaturePowerAtMost n .any false)
@[match_pattern] abbrev creatureYouControlAnySubtype (subtypes : Array String) : EffectTargetKind :=
  .battlefield (.creatureYouControlAnySubtype subtypes)
@[match_pattern] abbrev permanent : EffectTargetKind := .battlefield (.permanent .any)
@[match_pattern] abbrev legendaryCreatureYouControl : EffectTargetKind := .battlefield (.creatureYouControl false true)
@[match_pattern] abbrev creatureYouControlPowerAtMost (n : Int) : EffectTargetKind :=
  .battlefield (.creaturePowerAtMost n .you false)
@[match_pattern] abbrev artifact : EffectTargetKind := .battlefield (.artifact .any false false)
@[match_pattern] abbrev oppArtifact : EffectTargetKind := .battlefield (.artifact .opponent false false)
@[match_pattern] abbrev artifactToken : EffectTargetKind := .battlefield (.artifact .any true false)
@[match_pattern] abbrev attackingCreature : EffectTargetKind := .battlefield (.attackingCreature false false false)
@[match_pattern] abbrev equipmentYouControl : EffectTargetKind := .battlefield .equipmentYouControl
@[match_pattern] abbrev creatureOrLandYouControl : EffectTargetKind := .battlefield (.twoTypes true false true false)
@[match_pattern] abbrev attackingOrBlockingCreature : EffectTargetKind := .battlefield (.attackingCreature false true false)
@[match_pattern] abbrev creatureMvAtMost (n : Nat) : EffectTargetKind := .battlefield (.creatureMvAtMost n)
@[match_pattern] abbrev creatureToughnessAtLeast (n : Int) : EffectTargetKind :=
  .battlefield (.creatureStatAtLeast n true)
@[match_pattern] abbrev enchantmentMvAtLeast (n : Nat) : EffectTargetKind := .battlefield (.enchantmentMvAtLeast n)
@[match_pattern] abbrev noncreatureArtifact : EffectTargetKind := .battlefield (.artifact .any false true)
@[match_pattern] abbrev oppCreaturePowerAtMost (n : Int) : EffectTargetKind :=
  .battlefield (.creaturePowerAtMost n .opponent false)
@[match_pattern] abbrev oppCreatureDealtDamageThisTurn : EffectTargetKind := .battlefield (.oppCreature false true)
@[match_pattern] abbrev nonlandNontoken : EffectTargetKind := .battlefield (.nonland false true false)
@[match_pattern] abbrev artifactYouControl : EffectTargetKind := .battlefield (.artifact .you false false)
@[match_pattern] abbrev creatureOrPlaneswalker : EffectTargetKind := .battlefield (.creatureOrPlaneswalker .any false)
@[match_pattern] abbrev permanentYouControl : EffectTargetKind := .battlefield (.permanent .you)
@[match_pattern] abbrev oppPermanent : EffectTargetKind := .battlefield (.permanent .opponent)
@[match_pattern] abbrev anotherCreatureYouControlPowerAtMost (n : Int) : EffectTargetKind :=
  .battlefield (.creaturePowerAtMost n .you true)
@[match_pattern] abbrev planeswalkerYouControl : EffectTargetKind := .battlefield (.creatureOrPlaneswalker .you true)
@[match_pattern] abbrev oppCreatureOrPlaneswalker : EffectTargetKind := .battlefield (.creatureOrPlaneswalker .opponent false)
@[match_pattern] abbrev attackingAloneCreatureYouControl : EffectTargetKind :=
  .battlefield (.attackingCreature false false true)
@[match_pattern] abbrev noncreatureArtifactOrEnchantment : EffectTargetKind :=
  .battlefield (.artifactOrEnchantment true)

-- Graveyard card target aliases (CR 115.1 / 404.1)
@[match_pattern] abbrev elfInYourGraveyard : EffectTargetKind := .graveyard .elfInYourGraveyard
@[match_pattern] abbrev oppGraveyardCard : EffectTargetKind := .graveyard .oppGraveyardCard
@[match_pattern] abbrev creatureCardInYourGraveyard : EffectTargetKind := .graveyard (.cardInYourGraveyard false)
@[match_pattern] abbrev creatureCardInYourGraveyardMvAtMost (n : Nat) : EffectTargetKind :=
  .graveyard (.creatureCardInYourGraveyardMvAtMost n)
@[match_pattern] abbrev permanentCardInYourGraveyard : EffectTargetKind := .graveyard (.cardInYourGraveyard true)
@[match_pattern] abbrev equipmentInstantOrSorceryInYourGraveyard : EffectTargetKind :=
  .graveyard (.multiTypeInYourGraveyard true)
@[match_pattern] abbrev artEnchCardInYourGraveyard : EffectTargetKind := .graveyard (.multiTypeInYourGraveyard false)

-- Stack spell / ability target aliases (CR 115.1 / 405.1)
@[match_pattern] abbrev spell : EffectTargetKind := .stack (.spell false)
@[match_pattern] abbrev creatureSpell : EffectTargetKind := .stack (.spell true)
@[match_pattern] abbrev creatureSpellPTAtMost (n : Nat) : EffectTargetKind := .stack (.creatureSpellPTAtMost n)
@[match_pattern] abbrev stackAbilityFromCreatureSource : EffectTargetKind := .stack (.stackAbilityFromSource true)
@[match_pattern] abbrev stackAbilityFromArtifactSource : EffectTargetKind := .stack (.stackAbilityFromSource false)

-- Player and cross-category target aliases (CR 115.1 / 115.4)
@[match_pattern] abbrev player : EffectTargetKind := .playerTarget (.player false)
@[match_pattern] abbrev opponent : EffectTargetKind := .playerTarget (.player true)
@[match_pattern] abbrev playerOrCreature : EffectTargetKind := .playerTarget (.playerOrPermanent false)
@[match_pattern] abbrev permanentOrPlayer : EffectTargetKind := .playerTarget (.playerOrPermanent true)
@[match_pattern] abbrev creatureOrGyCreatureCard : EffectTargetKind := .playerTarget .creatureOrGyCreatureCard

-- Multi-target and sequential-slot target aliases (CR 115.1 / 601.2c)
@[match_pattern] abbrev playerThenCreature : EffectTargetKind := .sequence (.playerAndCreature false)
@[match_pattern] abbrev oppCreatureThenUpToOneCreatureYouControl : EffectTargetKind :=
  .sequence (.ownAndOppPermanent true false false)
@[match_pattern] abbrev creatureYouControlThenOppCreature : EffectTargetKind :=
  .sequence (.ownAndOppPermanent false false false)
@[match_pattern] abbrev twoNonlandsSharingType : EffectTargetKind := .sequence .twoNonlandsSharingType
@[match_pattern] abbrev twoCreaturesOrLandsYouControl : EffectTargetKind := .sequence (.twoSameKind false false)
@[match_pattern] abbrev equipmentYouControlThenCreatureYouControl : EffectTargetKind :=
  .sequence (.equipmentThenCreatureYouControl false)
@[match_pattern] abbrev upToOneEquipmentThenCreatureYouControl : EffectTargetKind :=
  .sequence (.equipmentThenCreatureYouControl true)
@[match_pattern] abbrev twoPlayers : EffectTargetKind := .sequence (.twoSameKind false true)
@[match_pattern] abbrev upToOneCreatureThenPlayer : EffectTargetKind := .sequence (.playerAndCreature true)
@[match_pattern] abbrev twoArtifactsYouControl : EffectTargetKind := .sequence (.twoSameKind true false)
@[match_pattern] abbrev creatureYouControlThenOppCreatureOrPlaneswalker : EffectTargetKind :=
  .sequence (.ownAndOppPermanent false true false)
@[match_pattern] abbrev planeswalkerYouControlThenOppCreatureOrPlaneswalker : EffectTargetKind :=
  .sequence (.ownAndOppPermanent false true true)
@[match_pattern] abbrev upToTwoCreaturesTotalMvAtMost (n : Nat) : EffectTargetKind :=
  .sequence (.upToTwoCreaturesTotalMvAtMost n)

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

/-- Classification of a battlefield permanent targeting shape (CR 115.1 / 110.1). -/
def specBattlefield : BattlefieldTarget → Spec
  | .creatureYouControl another legendary =>
    let noun :=
      if another then "another target creature you control"
      else if legendary then "target legendary creature you control"
      else "target creature you control"
    { noun, prefer := .own }
  | .creature another withFlying =>
    if withFlying then
      { noun := "target creature with flying" }
    else
      { noun := if another then "another target creature" else "target creature" }
  | .oppCreature tapped dealtDamageThisTurn =>
    let noun :=
      if tapped then "target tapped creature an opponent controls"
      else if dealtDamageThisTurn then "target creature an opponent controls that dealt damage this turn"
      else "target creature an opponent controls"
    { noun }
  | .twoTypes includeCreature includeArtifact youControl false =>
    let noun :=
      if !includeCreature then "target artifact or land"
      else if includeArtifact then "target artifact or creature you control"
      else "target creature or land you control"
    { noun, prefer := if youControl then .own else .opponent }
  | .twoTypes noncreature _ _ true =>
    { noun :=
        if noncreature then "target noncreature artifact or noncreature enchantment"
        else "target artifact or enchantment" }
  | .nonland opp nontoken colorless =>
    if colorless then
      { noun := "target colorless nonland permanent" }
    else if opp then
      { noun := "target nonland permanent an opponent controls" }
    else if nontoken then
      { noun := "target nonland, nontoken permanent", prefer := .ownThenOpponent }
    else
      { noun := "target nonland permanent", prefer := .ownThenOpponent }
  | .attackingCreature withoutFlying orBlocking aloneYouControl =>
    if withoutFlying then
      { noun := "target attacking creature without flying", prefer := .own }
    else if orBlocking then
      { noun := "target attacking or blocking creature" }
    else if aloneYouControl then
      { noun := "target creature you control that's attacking alone", prefer := .own }
    else
      { noun := "target attacking creature", prefer := .own }
  | .creatureYouControlSubtypes subtype _ false =>
    { noun := s!"target {subtype} you control", prefer := .own }
  | .oppOrEquipmentTarget false _ true =>
    { noun := "target creature defending player controls" }
  | .creatureStatBound n _ toughness true =>
    let stat := if toughness then "toughness" else "power"
    { noun := s!"target creature with {stat} {n} or greater" }
  | .creaturePowerAtMost n controller another =>
    match controller with
    | .you =>
      let lead := if another then "another target" else "target"
      { noun := s!"{lead} creature you control with power {n} or less", prefer := .own }
    | .opponent =>
      { noun := s!"target creature an opponent controls with power {n} or less" }
    | _ =>
      { noun := s!"target creature with power {n} or less", prefer := .own }
  | .creatureYouControlSubtypes _ subtypes true =>
    { noun :=
        if subtypes.isEmpty then "target creature you control"
        else s!"target {orJoin subtypes.toList} you control"
      prefer := .own }
  | .permanentOrPlaneswalker controller false _ =>
    match controller with
    | .you => { noun := "target permanent you control", prefer := .own }
    | .opponent => { noun := "target permanent an opponent controls", prefer := .opponent }
    | _ => { noun := "target permanent", prefer := .ownThenOpponent }
  | .artifact controller tokenOnly noncreature =>
    if tokenOnly then
      { noun := "target artifact token" }
    else if noncreature then
      { noun := "target noncreature artifact" }
    else
      match controller with
      | .you => { noun := "target artifact you control", prefer := .own }
      | .opponent => { noun := "target artifact an opponent controls" }
      | _ => { noun := "target artifact" }
  | .oppOrEquipmentTarget true _ true =>
    { noun := "target Equipment you control", prefer := .own }
  | .creatureMvAtMost n =>
    { noun := s!"target creature with mana value {n} or less" }
  | .enchantmentMvAtLeast n =>
    { noun := s!"target enchantment with mana value {n} or greater" }
  | .creatureOrPlaneswalker controller planeswalkerOnly =>
    if planeswalkerOnly then
      { noun := "target planeswalker you control", prefer := .own }
    else
      match controller with
      | .opponent =>
        { noun := "target creature or planeswalker an opponent controls", prefer := .opponent }
      | _ =>
        { noun := "target creature or planeswalker" }
  | _ => {}

/-- Classification of a graveyard card targeting shape (CR 115.1 / 404.1). -/
def specGraveyard (t : GraveyardTarget) : Spec :=
  let noun :=
    match t with
    | .elfInYourGraveyard => "target Elf card from your graveyard"
    | .oppGraveyardCard => "target card from an opponent's graveyard"
    | .cardInYourGraveyard false => "target creature card from your graveyard"
    | .cardInYourGraveyard true => "target permanent card in your graveyard"
    | .creatureCardInYourGraveyardMvAtMost n =>
      s!"target creature card with mana value {n} or less from your graveyard"
    | .graveyardCardKind true _ true =>
      "target Equipment, instant, or sorcery card from your graveyard"
    | .graveyardCardKind false _ true =>
      "target artifact or enchantment card from your graveyard"
    | _ => ""
  { noun, prefer := .last }

/-- Classification of a stack spell or ability targeting shape (CR 115.1 / 405.1). -/
def specStack (t : StackTarget) : Spec :=
  let noun :=
    match t with
    | .spell false => "target spell"
    | .spell true => "target creature spell"
    | .creatureSpellPTAtMost n =>
      s!"target creature spell with power or toughness {n} or less"
    | .stackAbilityFromSource true =>
      "target activated or triggered ability you control from a creature source"
    | .stackAbilityFromSource false =>
      "target activated or triggered ability you control from an artifact source"
    | _ => ""
  { noun, stackSpell := true }

/-- Classification of a player or cross-category targeting shape (CR 115.1 / 115.4). -/
def specPlayer : PlayerTarget → Spec
  | .player opponentOnly =>
    { noun := if opponentOnly then "target opponent" else "target player", prefer := .opponentPlayer }
  | .playerOrPermanent false =>
    { noun := "any target", prefer := .opponentPlayer }
  | .playerOrPermanent true =>
    { noun := "target permanent or player", prefer := .ownThenOpponent }
  | .creatureOrGyCreatureCard =>
    { noun := "up to one target creature or creature card in a graveyard",
      prefer := .last }
  | _ => {}

/-- Classification of a multi-target or sequential-slot targeting shape (CR 115.1 / 601.2c). -/
def specMulti : MultiTarget → Spec
  | .playerAndCreature false =>
    { count := 2
      noun := "target player and target creature"
      prefer := .opponentPlayer
      slots := #[.player, .creature] }
  | .playerAndCreature true =>
    { count := 2
      noun := "up to one target creature and target player"
      prefer := .own
      slots := #[.creature, .player]
      optionalSlots := #[0] }
  | .ownAndOppPermanent true _ _ =>
    { count := 2
      noun := "target creature an opponent controls and up to one target creature you control"
      prefer := .opponent
      slots := #[.oppCreature, .creatureYouControl]
      optionalSlots := #[1] }
  | .ownAndOppPermanent false false _ =>
    { count := 2
      noun := "target creature you control and a creature an opponent controls"
      prefer := .ownThenOpponent
      slots := #[.creatureYouControl, .oppCreature] }
  | .ownAndOppPermanent false true false =>
    { count := 2
      noun := "target creature you control"
      prefer := .ownThenOpponent
      slots := #[.creatureYouControl, .oppCreatureOrPlaneswalker] }
  | .ownAndOppPermanent false true true =>
    { count := 2
      noun := "target planeswalker you control"
      prefer := .ownThenOpponent
      slots := #[.planeswalkerYouControl, .oppCreatureOrPlaneswalker] }
  | .twoNonlandsSharingType =>
    { count := 2
      noun := "two target nonland permanents that share a card type"
      prefer := .ownThenOpponent
      slots := #[.nonland, .nonland] }
  | .twoSameKind false false =>
    { count := 2
      noun := "two target creatures and/or lands you control"
      prefer := .own
      slots := #[.creatureOrLandYouControl, .creatureOrLandYouControl] }
  | .twoSameKind true false =>
    { count := 2
      noun := "target artifact you control and a second target artifact you control"
      prefer := .own
      slots := #[.artifactYouControl, .artifactYouControl] }
  | .twoSameKind _ true =>
    { count := 2
      noun := "two target players"
      prefer := .ownThenOpponent
      slots := #[.player, .player] }
  | .equipmentThenCreatureYouControl false =>
    { count := 2
      noun := "target Equipment you control and up to one target creature you control"
      prefer := .own
      slots := #[.equipmentYouControl, .creatureYouControl] }
  | .equipmentThenCreatureYouControl true =>
    { count := 2
      noun := "up to one target Equipment you control and target creature you control"
      prefer := .own
      slots := #[.equipmentYouControl, .creatureYouControl]
      optionalSlots := #[0] }
  | .upToTwoCreaturesTotalMvAtMost n =>
    { count := 2
      noun := s!"up to two target creatures with total mana value {n} or less" }
  | _ => {}

/-- Classification of this targeting shape. `targetCount`, `noun`, and
`defaultPreference` read this table. -/
def spec : EffectTargetKind → Spec
  | .none => { count := 0, prefer := .own }
  | .battlefield t => specBattlefield t
  | .graveyard t => specGraveyard t
  | .stack t => specStack t
  | .playerTarget t => specPlayer t
  | .sequence t => specMulti t
  | .filtered f =>
    { noun := f.noun
      prefer :=
        match f.zone, f.controller with
        | .yourGraveyard, _ | .anyGraveyard, _ => .last
        | .player, .you => .selfPlayer
        | _, .specific _ => .opponent
        | _, .eachOpponent => .opponent
        | .player, _ => .opponentPlayer
        | _, .you => .own
        | _, .opponent => .opponent
        | _, _ => .opponent
      stackSpell := f.zone == .stack || f.zone == .spellOrCreature }
  | .multi fs optional =>
    { count := fs.size
      noun := (fs[0]?.map (·.noun)).getD ""
      prefer := .ownThenOpponent
      slots := fs.map EffectTargetKind.filtered
      optionalSlots := optional }
  | .pair a b =>
    let sa := spec a
    let sb := spec b
    let la := if sa.slots.isEmpty then Array.replicate sa.count a else sa.slots
    let lb := if sb.slots.isEmpty then Array.replicate sb.count b else sb.slots
    { count := sa.count + sb.count
      noun := if sa.noun.isEmpty then sb.noun else sa.noun
      prefer := sa.prefer
      slots := la ++ lb
      optionalSlots := sa.optionalSlots ++ sb.optionalSlots.map (· + la.size)
      stackSpell := sa.stackSpell || sb.stackSpell }
  | _ => { count := 0, prefer := .own }

/-- How many targets must be announced for this shape (CR 601.2c). -/
def targetCount (k : EffectTargetKind) : Nat :=
  k.spec.count

/-- Oracle-style noun phrase for this targeting shape. -/
def noun (k : EffectTargetKind) : String :=
  k.spec.noun

/-- Parameter-free targeting shapes, so a noun can be parsed back to a kind.
A new parameter-free constructor belongs in this list; parameterized
constructors are parsed from their noun template instead. -/
def closedKinds : List EffectTargetKind := [
  .none,
  .creatureYouControl,
  .anotherCreatureYouControl,
  .anotherCreature,
  .playerOrCreature,
  .playerThenCreature,
  .elfInYourGraveyard,
  .oppCreature,
  .oppCreatureThenUpToOneCreatureYouControl,
  .oppTappedCreature,
  .creature,
  .creatureOrGyCreatureCard,
  .creatureWithFlying,
  .artifactOrLand,
  .colorlessNonland,
  .creatureYouControlThenOppCreature,
  .player,
  .opponent,
  .oppGraveyardCard,
  .artifactOrEnchantment,
  .artifactOrCreatureYouControl,
  .nonland,
  .oppNonland,
  .attackingCreatureWithoutFlying,
  .spell,
  .creatureSpell,
  .defendingPlayerCreature,
  .twoNonlandsSharingType,
  .permanent,
  .creatureCardInYourGraveyard,
  .legendaryCreatureYouControl,
  .artifact,
  .oppArtifact,
  .artifactToken,
  .attackingCreature,
  .equipmentYouControl,
  .creatureOrLandYouControl,
  .twoCreaturesOrLandsYouControl,
  .equipmentYouControlThenCreatureYouControl,
  .upToOneEquipmentThenCreatureYouControl,
  .twoPlayers,
  .upToOneCreatureThenPlayer,
  .attackingOrBlockingCreature,
  .noncreatureArtifact,
  .stackAbilityFromCreatureSource,
  .stackAbilityFromArtifactSource,
  .oppCreatureDealtDamageThisTurn,
  .nonlandNontoken,
  .permanentCardInYourGraveyard,
  .equipmentInstantOrSorceryInYourGraveyard,
  .artEnchCardInYourGraveyard,
  .artifactYouControl,
  .twoArtifactsYouControl,
  .creatureOrPlaneswalker,
  .permanentYouControl,
  .oppPermanent,
  .planeswalkerYouControl,
  .oppCreatureOrPlaneswalker,
  .creatureYouControlThenOppCreatureOrPlaneswalker,
  .planeswalkerYouControlThenOppCreatureOrPlaneswalker,
  .attackingAloneCreatureYouControl,
  .noncreatureArtifactOrEnchantment,
  .permanentOrPlayer,
]

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

namespace TargetFilter

def creatureOrPlaneswalker : TargetFilter :=
  { noun := "target creature or planeswalker", types := #[.creature, .planeswalker] }

def creature : TargetFilter :=
  { noun := "target creature", types := #[.creature] }

def creatureYouControl : TargetFilter :=
  { noun := "target creature you control", types := #[.creature], controller := .you }

def oppCreatureOrPlaneswalker : TargetFilter :=
  { noun := "target creature or planeswalker an opponent controls", types := #[.creature, .planeswalker], controller := .opponent }

def spell : TargetFilter :=
  { noun := "target spell", zone := .stack }

end TargetFilter

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
