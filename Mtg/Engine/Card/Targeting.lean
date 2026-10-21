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
  | battlefield
  | yourGraveyard
  | anyGraveyard
  | stack
  /-- A player rather than an object. `controller` narrows it to you or an
  opponent. -/
  | player
  /-- A spell on the stack or a creature on the battlefield. -/
  | spellOrCreature
  /-- “Any target”: a player, or a creature, planeswalker, or battle
  (CR 115.4). -/
  | anyTarget
deriving Repr, Inhabited, BEq, DecidableEq

/-- Who controls (or, for a card in a graveyard, owns) a filtered target. -/
inductive TargetController where
  | any
  | you
  | opponent
  /-- One particular player, by seat index. -/
  | specific (idx : Nat)
  /-- “For each opponent, up to one target … that player controls”: one
  optional instance per opponent, expanded as the ability is put on the
  stack. -/
  | eachOpponent
deriving Repr, Inhabited, BEq, DecidableEq

/-- A target described by characteristics, with the Oracle noun phrase that
names it. Every listed restriction must hold. -/
structure TargetFilter where
  noun : String
  zone : TargetZone := .battlefield
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
  controller : TargetController := .any
  /-- The target is at least one of these colors. Empty means any color. -/
  colors : Array Color := #[]
  mvAtLeast : Option Nat := none
  mvAtMost : Option Nat := none
  toughnessAtLeast : Option Int := none
  /-- Not the source of the spell or ability. -/
  another : Bool := false
  withFlying : Bool := false
  withPlusOneCounter : Bool := false
  attacking : Bool := false
  attackingOrBlocking : Bool := false
  attackedThisTurn : Bool := false
  enteredThisTurn : Bool := false
  /-- Only a creature that is still untapped (“tap target untapped creature”). -/
  untapped : Bool := false
  nonattacking : Bool := false
  withHaste : Bool := false
  /-- Owned (not necessarily controlled) by the caster. -/
  ownedByYou : Bool := false
deriving Repr, Inhabited, BEq, DecidableEq

/-- A permanent target on the battlefield (CR 115.1 / 110.1). -/
inductive BattlefieldTarget where
  /-- Target creature you control (optionally `another` or `legendary`). -/
  | creatureYouControl (another : Bool := false) (legendary : Bool := false)
  /-- Target creature (any controller; optionally `another`). -/
  | creature (another : Bool := false)
  /-- Target creature an opponent controls (optionally `tapped` or `dealtDamageThisTurn`). -/
  | oppCreature (tapped : Bool := false) (dealtDamageThisTurn : Bool := false)
  /-- Target creature with flying. -/
  | creatureWithFlying
  /-- Target two-type permanent (`artifactOrLand`, `artifactOrCreatureYouControl`, `creatureOrLandYouControl`). -/
  | twoTypes (includeCreature : Bool := false) (includeArtifact : Bool := true) (youControl : Bool := false)
  /-- Target artifact or enchantment (optionally `noncreature`). -/
  | artifactOrEnchantment (noncreature : Bool := false)
  /-- Target nonland permanent (optionally `opp`, `nontoken`, or `colorless`). -/
  | nonland (opp : Bool := false) (nontoken : Bool := false) (colorless : Bool := false)
  /-- Target attacking creature (optionally `withoutFlying`, `orBlocking`, or `aloneYouControl`). -/
  | attackingCreature (withoutFlying : Bool := false) (orBlocking : Bool := false) (aloneYouControl : Bool := false)
  /-- Target creature you control with this subtype (e.g. Equip Human). -/
  | creatureYouControlSubtype (subtype : String)
  /-- Target creature defending player controls. -/
  | defendingPlayerCreature
  /-- Target creature with power (or toughness) `n` or greater. -/
  | creatureStatAtLeast (n : Int) (toughness : Bool := false)
  /-- Target creature with power `n` or less (filtered by `controller` and `another`). -/
  | creaturePowerAtMost (n : Int) (controller : TargetController := .any) (another : Bool := false)
  /-- Target creature you control with any of these subtypes. -/
  | creatureYouControlAnySubtype (subtypes : Array String)
  /-- Target permanent (filtered by `controller`). -/
  | permanent (controller : TargetController := .any)
  /-- Target artifact (filtered by `controller`, `tokenOnly`, and `noncreature`). -/
  | artifact (controller : TargetController := .any) (tokenOnly : Bool := false) (noncreature : Bool := false)
  /-- Target Equipment you control. -/
  | equipmentYouControl
  /-- Target creature with mana value `n` or less. -/
  | creatureMvAtMost (n : Nat)
  /-- Target enchantment with mana value `n` or greater. -/
  | enchantmentMvAtLeast (n : Nat)
  /-- Target creature or planeswalker (filtered by `controller` and `planeswalkerOnly`). -/
  | creatureOrPlaneswalker (controller : TargetController := .any) (planeswalkerOnly : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- A card target in a graveyard (CR 115.1 / 404.1). -/
inductive GraveyardTarget where
  /-- Target Elf card in your graveyard. -/
  | elfInYourGraveyard
  /-- Target card in an opponent's graveyard. -/
  | oppGraveyardCard
  /-- Target creature or permanent card in your graveyard. -/
  | cardInYourGraveyard (permanentAny : Bool := false)
  /-- Target creature card with mana value `n` or less in your graveyard. -/
  | creatureCardInYourGraveyardMvAtMost (n : Nat)
  /-- Target artifact/enchantment or Equipment/instant/sorcery card in your graveyard. -/
  | multiTypeInYourGraveyard (equipInstSorc : Bool := false)
deriving Repr, Inhabited, BEq, DecidableEq

/-- A spell or ability target on the stack (CR 115.1 / 405.1). -/
inductive StackTarget where
  /-- A spell (or creature spell) on the stack. -/
  | spell (creatureOnly : Bool := false)
  /-- A creature spell with power or toughness at most `n`. -/
  | creatureSpellPTAtMost (n : Nat)
  /-- An activated or triggered ability you control from a creature or artifact source. -/
  | stackAbilityFromSource (fromCreature : Bool := true)
deriving Repr, Inhabited, BEq, DecidableEq

/-- A player target, or a cross-category target involving a player or graveyard
(CR 115.1 / 115.4). -/
inductive PlayerTarget where
  /-- Target player or target opponent. -/
  | player (opponentOnly : Bool := false)
  /-- “Any target” (CR 115.4) or target permanent or player. -/
  | playerOrPermanent (anyPermanent : Bool := false)
  /-- A creature on the battlefield, or a creature card in a graveyard. -/
  | creatureOrGyCreatureCard
deriving Repr, Inhabited, BEq, DecidableEq

/-- Multiple-target or sequential-slot targeting shapes (CR 115.1 / 601.2c). -/
inductive MultiTarget where
  /-- Target player and target creature (or up to one creature then player). -/
  | playerAndCreature (creatureFirstUpToOne : Bool := false)
  /-- Sequential own and opponent creature/planeswalker targets. -/
  | ownAndOppPermanent (oppFirst : Bool := false) (orPlaneswalker : Bool := false) (planeswalkerFirst : Bool := false)
  /-- Two target nonland permanents that share a card type. -/
  | twoNonlandsSharingType
  /-- Two targets of the same kind (`twoCreaturesOrLandsYouControl`, `twoArtifactsYouControl`, `twoPlayers`). -/
  | twoSameKind (artifacts : Bool := false) (players : Bool := false)
  /-- Target Equipment you control and target creature you control. -/
  | equipmentThenCreatureYouControl (optionalEquipment : Bool := false)
  /-- Up to two target creatures whose total mana value is `n` or less. -/
  | upToTwoCreaturesTotalMvAtMost (n : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- Whom a spell, activated ability, or triggered ability may target
(CR 115.1 / 601.2c / 603.3d). Adding a targeting shape here is a compile error
in `EffectTargetKind.spec` and `Game.legalTargetsForAtomicKind` rather than
silently offering no targets. Multiple instances of the word “target” list
each slot in `spec` and are announced sequentially. Multiple targets of one
instance are chosen together. -/
inductive EffectTargetKind where
  /-- No target (CR 115.1). -/
  | none
  /-- A permanent target on the battlefield (CR 115.1 / 110.1). -/
  | battlefield (t : BattlefieldTarget)
  /-- A card target in a graveyard (CR 115.1 / 404.1). -/
  | graveyard (t : GraveyardTarget)
  /-- A spell or ability target on the stack (CR 115.1 / 405.1). -/
  | stack (t : StackTarget)
  /-- A player target, or a cross-category target involving a player or
  graveyard (CR 115.1 / 115.4). -/
  | playerTarget (t : PlayerTarget)
  /-- Multiple-target or sequential-slot targeting shapes (CR 115.1 / 601.2c). -/
  | sequence (t : MultiTarget)
  /-- One instance of the word “target” described by a `TargetFilter`. -/
  | filtered (f : TargetFilter)
  /-- One instance of “target” per filter, announced in order. Indices in
  `optional` are “up to one” instances. -/
  | multi (fs : Array TargetFilter) (optional : Array Nat)
  /-- The instances of “target” of `a`, then those of `b`: two modes of one
  modal spell chosen together (CR 700.2). -/
  | pair (a b : EffectTargetKind)
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

-- Battlefield permanent target aliases (CR 115.1 / 110.1)
@[match_pattern] abbrev creatureYouControl : EffectTargetKind := .battlefield (.creatureYouControl false false)
@[match_pattern] abbrev anotherCreatureYouControl : EffectTargetKind := .battlefield (.creatureYouControl true false)
@[match_pattern] abbrev anotherCreature : EffectTargetKind := .battlefield (.creature true)
@[match_pattern] abbrev oppCreature : EffectTargetKind := .battlefield (.oppCreature false false)
@[match_pattern] abbrev oppTappedCreature : EffectTargetKind := .battlefield (.oppCreature true false)
@[match_pattern] abbrev creature : EffectTargetKind := .battlefield (.creature false)
@[match_pattern] abbrev creatureWithFlying : EffectTargetKind := .battlefield .creatureWithFlying
@[match_pattern] abbrev artifactOrLand : EffectTargetKind := .battlefield (.twoTypes false true false)
@[match_pattern] abbrev colorlessNonland : EffectTargetKind := .battlefield (.nonland false false true)
@[match_pattern] abbrev artifactOrEnchantment : EffectTargetKind := .battlefield (.artifactOrEnchantment false)
@[match_pattern] abbrev artifactOrCreatureYouControl : EffectTargetKind := .battlefield (.twoTypes true true true)
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
@[match_pattern] abbrev creatureOrLandYouControl : EffectTargetKind := .battlefield (.twoTypes true false true)
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
  | .creature another =>
    { noun := if another then "another target creature" else "target creature" }
  | .oppCreature tapped dealtDamageThisTurn =>
    let noun :=
      if tapped then "target tapped creature an opponent controls"
      else if dealtDamageThisTurn then "target creature an opponent controls that dealt damage this turn"
      else "target creature an opponent controls"
    { noun }
  | .creatureWithFlying =>
    { noun := "target creature with flying" }
  | .twoTypes includeCreature includeArtifact youControl =>
    let noun :=
      if !includeCreature then "target artifact or land"
      else if includeArtifact then "target artifact or creature you control"
      else "target creature or land you control"
    { noun, prefer := if youControl then .own else .opponent }
  | .artifactOrEnchantment noncreature =>
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
  | .creatureYouControlSubtype subtype =>
    { noun := s!"target {subtype} you control", prefer := .own }
  | .defendingPlayerCreature =>
    { noun := "target creature defending player controls" }
  | .creatureStatAtLeast n toughness =>
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
  | .creatureYouControlAnySubtype subtypes =>
    { noun :=
        if subtypes.isEmpty then "target creature you control"
        else s!"target {orJoin subtypes.toList} you control"
      prefer := .own }
  | .permanent controller =>
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
  | .equipmentYouControl =>
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
    | .multiTypeInYourGraveyard true =>
      "target Equipment, instant, or sorcery card from your graveyard"
    | .multiTypeInYourGraveyard false =>
      "target artifact or enchantment card from your graveyard"
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
        | _, .any => .opponent
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
