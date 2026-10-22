import Mtg.Engine.Card.Effect

/-!
# Activated abilities (CR 602)

Activation costs and the printed activated abilities built from unified
effects.
-/

namespace Mtg.Engine

/-- Part of an activation cost that needs the player to choose what to pay
with, additional activation cost, or equip target restriction (CR 601.2h / 602.1 / 602.2b / 702.6). -/
abbrev CostPick := SpellCastKind

namespace CostPick

/-- Chosen-object activation cost, additional activation cost, or equip restriction kind. -/
@[match_pattern] abbrev costPickKind (subtypeOpt : Option String := Option.none) (powerOpt : Option Nat := Option.none)
    (kindOpt : Option CounterKind := Option.none)
    (alt1 : Bool := false) (alt2 : Bool := false)
    (twoKind : Bool := false) (discardFlag : Bool := false)
    (exileOrTap : Bool := false) (tapFlag : Bool := false) (subtypeSac : Bool := false) : CostPick :=
  SpellCastKind.spellCastKind powerOpt Option.none subtypeOpt alt1 alt2 twoKind discardFlag exileOrTap tapFlag (some subtypeSac) kindOpt

end CostPick

/-- A loyalty symbol in an activation cost (CR 107.7 / 209.2).

`[+N]` puts N loyalty counters on the source, `[-N]` removes N, and `[0]`
puts zero. `[+X]` and `[-X]` use X in place of a fixed number (CR 107.3a). -/
abbrev LoyaltySymbol := CostPick

namespace LoyaltySymbol

@[match_pattern] abbrev loyaltySymbolKind (n : Nat := 0) (minus : Bool := false)
    (variableXFlag : Bool := false) (zeroFlag : Bool := false) : LoyaltySymbol :=
  CostPick.costPickKind Option.none (some n) Option.none minus variableXFlag zeroFlag false false false false
@[match_pattern] abbrev fixed (n : Nat) (minus : Bool := false) : LoyaltySymbol := .loyaltySymbolKind n minus false false
@[match_pattern] abbrev zero : LoyaltySymbol := .loyaltySymbolKind 0 false false true
@[match_pattern] abbrev variableX (minus : Bool := false) : LoyaltySymbol := .loyaltySymbolKind 0 minus true false
@[match_pattern] abbrev plus (n : Nat) : LoyaltySymbol := .fixed n false
@[match_pattern] abbrev minus (n : Nat) : LoyaltySymbol := .fixed n true
@[match_pattern] abbrev plusX : LoyaltySymbol := .variableX false
@[match_pattern] abbrev minusX : LoyaltySymbol := .variableX true

/-- Rules notation: `[+N]`, `[-N]`, `[0]`, `[+X]`, or `[-X]`. -/
def toNotation : LoyaltySymbol → String
  | .fixed n false => s!"[+{n}]"
  | .fixed n true => s!"[-{n}]"
  | .zero => "[0]"
  | .variableX false => "[+X]"
  | .variableX true => "[-X]"
  | _ => "[0]"

/-- Counters this symbol adds, or removes when negative.
`[+X]` and `[-X]` are not a fixed number. -/
def counters : LoyaltySymbol → Option Int
  | .fixed n false => some (Int.ofNat n)
  | .fixed n true => some (-Int.ofNat n)
  | .zero => some 0
  | _ => none

end LoyaltySymbol

namespace CostPick
export LoyaltySymbol (loyaltySymbolKind fixed zero variableX plus minus plusX minusX)

/-- Sacrifice another permanent of this subtype, or another creature when
the subtype is `Creature`. -/
@[match_pattern] abbrev sacrificeAnotherSubtype (subtype : String) : CostPick :=
  costPickKind (some subtype) Option.none Option.none false false false false false false true
@[match_pattern] abbrev sacrificeArtifactChoice (legendary : Bool := false) (anotherOrEquip : Bool := false) : CostPick :=
  costPickKind Option.none Option.none Option.none legendary anotherOrEquip false false false false false
@[match_pattern] abbrev sacrificeTwoKindChoice (anotherCreatureOrPw : Bool := false) (landOrDiscard : Bool := false) : CostPick :=
  costPickKind Option.none Option.none Option.none anotherCreatureOrPw landOrDiscard true false false false false
@[match_pattern] abbrev discardChoice (nonland : Bool := false) (legendary : Bool := false) : CostPick :=
  costPickKind Option.none Option.none Option.none nonland legendary false true false false false
@[match_pattern] abbrev exileAnotherCreatureCardFromGraveyard : CostPick :=
  costPickKind Option.none Option.none Option.none false false false false true false false
@[match_pattern] abbrev tapChoice (twoArtifacts : Bool := false) : CostPick :=
  costPickKind Option.none Option.none Option.none twoArtifacts false false false false true false
@[match_pattern] abbrev sacrificeArtifact : CostPick := .sacrificeArtifactChoice false false
@[match_pattern] abbrev sacrificeLegendaryArtifact : CostPick := .sacrificeArtifactChoice true false
@[match_pattern] abbrev sacrificeAnotherArtifact : CostPick := .sacrificeArtifactChoice false true
@[match_pattern] abbrev sacrificeEquipmentAttachedToSource : CostPick := .sacrificeArtifactChoice true true
@[match_pattern] abbrev sacrificeArtifactOrCreature : CostPick := .sacrificeTwoKindChoice false false
@[match_pattern] abbrev sacrificeAnotherCreatureOrPlaneswalker : CostPick := .sacrificeTwoKindChoice true false
@[match_pattern] abbrev sacrificeArtifactOrLand : CostPick := .sacrificeTwoKindChoice false true
@[match_pattern] abbrev sacrificeArtifactOrDiscardNonland : CostPick := .sacrificeTwoKindChoice true true
@[match_pattern] abbrev discardACard : CostPick := .discardChoice false false
@[match_pattern] abbrev discardNonland : CostPick := .discardChoice true false
@[match_pattern] abbrev discardLegendaryCard : CostPick := .discardChoice false true
@[match_pattern] abbrev discardLegendarySameName : CostPick := .discardChoice true true
@[match_pattern] abbrev tapUntappedCreature : CostPick := .tapChoice false
@[match_pattern] abbrev tapTwoUntappedArtifacts : CostPick := .tapChoice true

end CostPick

/-- How many objects `pick` takes. -/
def CostPick.count : CostPick → Nat
  | .tapTwoUntappedArtifacts => 2
  | _ => 1

/-- The cost phrase of `pick`, for prompts and logs. -/
def CostPick.phrase : CostPick → String
  | .sacrificeAnotherSubtype t => s!"sacrifice another {t.toLower}"
  | .sacrificeArtifact => "sacrifice an artifact"
  | .sacrificeLegendaryArtifact => "sacrifice a legendary artifact"
  | .sacrificeArtifactOrCreature => "sacrifice an artifact or creature"
  | .sacrificeAnotherArtifact => "sacrifice another artifact"
  | .sacrificeAnotherCreatureOrPlaneswalker => "sacrifice another creature or planeswalker"
  | .sacrificeArtifactOrLand => "sacrifice an artifact or land"
  | .sacrificeEquipmentAttachedToSource => "sacrifice an Equipment attached to the source"
  | .sacrificeArtifactOrDiscardNonland => "sacrifice an artifact or discard a nonland card"
  | .discardACard => "discard a card"
  | .discardNonland => "discard a nonland card"
  | .discardLegendaryCard => "discard a legendary card"
  | .discardLegendarySameName =>
    "discard a legendary card with the same name as a legendary permanent you control"
  | .exileAnotherCreatureCardFromGraveyard => "exile another creature card from your graveyard"
  | .tapUntappedCreature => "tap an untapped creature you control"
  | .tapTwoUntappedArtifacts => "tap two untapped artifacts you control"
  | _ => ""

/-- Additional non-mana activation costs (CR 602.1 / 118). -/
abbrev ExtraActivationCost := CostPick

namespace ExtraActivationCost

@[match_pattern] abbrev extraCostKind (powerOpt : Option Nat := Option.none) (kindOpt : Option CounterKind := Option.none)
    (alt1 : Bool := false) (alt2 : Bool := false)
    (exileOrSac : Bool := false) (counterMod : Bool := false) (zemo : Bool := false)
    (removeKind : Bool := false) (crewFlag : Bool := false) : ExtraActivationCost :=
  CostPick.costPickKind Option.none powerOpt kindOpt alt1 alt2 exileOrSac counterMod zemo removeKind crewFlag

/-- Remove a counter of `kind` from the source. -/
@[match_pattern] abbrev removeCounter (kind : CounterKind) : ExtraActivationCost :=
  .extraCostKind Option.none (some kind) false false false false false true false
/-- Crew N: tap any number of untapped creatures you control with total
power N or more (CR 702.122). -/
@[match_pattern] abbrev crew (power : Nat) : ExtraActivationCost :=
  .extraCostKind (some power) Option.none false false false false false false true
@[match_pattern] abbrev none : ExtraActivationCost := .extraCostKind Option.none Option.none false false false false false false false
@[match_pattern] abbrev exileOrSacrificeCost (fromHand : Bool := false) (battlefield : Bool := false) : ExtraActivationCost :=
  .extraCostKind Option.none Option.none fromHand battlefield true false false false false
@[match_pattern] abbrev counterModCost (putStun : Bool := false) : ExtraActivationCost :=
  .extraCostKind Option.none Option.none putStun false false true false false false
@[match_pattern] abbrev zemoBoast : ExtraActivationCost := .extraCostKind Option.none Option.none false false false false true false false
@[match_pattern] abbrev exileSourceFromGraveyard : ExtraActivationCost := .exileOrSacrificeCost false false
@[match_pattern] abbrev exileSourceFromHand : ExtraActivationCost := .exileOrSacrificeCost true false
@[match_pattern] abbrev exileSource : ExtraActivationCost := .exileOrSacrificeCost false true
@[match_pattern] abbrev sacrificeAnotherCreatureOrArtifact : ExtraActivationCost := .exileOrSacrificeCost true true
@[match_pattern] abbrev removeAnyNumberPlusOne : ExtraActivationCost := .counterModCost false
@[match_pattern] abbrev putStunCounterOnSource : ExtraActivationCost := .counterModCost true

end ExtraActivationCost

abbrev FraCost := ExtraActivationCost

/-- An “Activate only if …” restriction on an activated ability (CR 602.5b),
represented by the unified `ConditionSelector`. -/
abbrev ActivationCondition := ConditionSelector

abbrev FraActivationCondition := ConditionSelector

/-- Cost reduction on an activated ability (CR 602.2b / 601.2f), represented by
the unified `CostReduction`. -/
abbrev ActivationCostReduction := CostReduction

/-- Target quality restriction on an equip ability (CR 702.6). -/
abbrev EquipRestriction := CostPick

namespace EquipRestriction
@[match_pattern] abbrev equipRestrictionKind (sOpt : Option String := Option.none) (subtypeFlag : Bool := false) (worthyFlag : Bool := false) : EquipRestriction :=
  CostPick.costPickKind sOpt Option.none Option.none subtypeFlag worthyFlag false false false false false
@[match_pattern] abbrev none : EquipRestriction := .equipRestrictionKind Option.none false false
@[match_pattern] abbrev subtype (s : String) : EquipRestriction := .equipRestrictionKind (some s) true false
@[match_pattern] abbrev worthy : EquipRestriction := .equipRestrictionKind Option.none false true
end EquipRestriction

/-- Costs of an activated ability besides announcements (CR 602.1). -/
structure ActivationCost where
  mana : ManaCost := ManaCost.empty
  tap : Bool := false
  /-- Loyalty symbol in this cost (CR 209.2). The ability is a loyalty
  ability exactly when this is set. -/
  loyalty : Option LoyaltySymbol := none
  sacrificeSource : Bool := false
  /-- Pay this much life (CR 118.3b / 119.4). Payment of life is not damage. -/
  payLife : Nat := 0
  /-- Discard this card from your hand (CR 701.9 / 702.29, e.g. cycling). -/
  discardSource : Bool := false
  /-- Chosen-object costs (sacrificing, discarding, tapping, or exiling chosen objects). -/
  picks : Array CostPick := #[]
  /-- Additional activation cost (CR 602.1). -/
  extra : ExtraActivationCost := .none
deriving Repr, Inhabited, BEq

namespace ActivationCost

def fra (c : ActivationCost) : ExtraActivationCost :=
  c.extra

def exileSourceFromGraveyard (c : ActivationCost) : Bool :=
  c.extra == .exileSourceFromGraveyard

def sacrificeAnotherCreatureOrArtifact (c : ActivationCost) : Bool :=
  c.extra == .sacrificeAnotherCreatureOrArtifact

def removeIndestructibleCounter (c : ActivationCost) : Bool :=
  c.extra == .removeCounter .indestructible

def removeAnyNumberPlusOne (c : ActivationCost) : Bool :=
  c.extra == .removeAnyNumberPlusOne

def putStunCounterOnSource (c : ActivationCost) : Bool :=
  c.extra == .putStunCounterOnSource

def removeStoryCounter (c : ActivationCost) : Bool :=
  c.extra == .removeCounter .story

/-- True when this cost contains a loyalty symbol (CR 209.2). -/
def isLoyalty (c : ActivationCost) : Bool :=
  c.loyalty.isSome

def discardACard (c : ActivationCost) : Bool :=
  c.picks.contains .discardACard

def discardLegendarySameName (c : ActivationCost) : Bool :=
  c.picks.contains .discardLegendarySameName

def sacrificeLegendaryArtifact (c : ActivationCost) : Bool :=
  c.picks.contains .sacrificeLegendaryArtifact

def sacrificeArtifact (c : ActivationCost) : Bool :=
  c.picks.contains .sacrificeArtifact

def sacrificeArtifactOrCreature (c : ActivationCost) : Bool :=
  c.picks.contains .sacrificeArtifactOrCreature

def sacrificeArtifactOrDiscardNonland (c : ActivationCost) : Bool :=
  c.picks.contains .sacrificeArtifactOrDiscardNonland

def sacrificeEquipmentAttachedToSource (c : ActivationCost) : Bool :=
  c.picks.contains .sacrificeEquipmentAttachedToSource

def tapAnUntappedCreatureYouControl (c : ActivationCost) : Bool :=
  c.picks.contains .tapUntappedCreature

def sacrificeAnotherSubtype (c : ActivationCost) : Option String :=
  c.picks.findSome? fun
    | .sacrificeAnotherSubtype t => some t
    | _ => none

def toNotation (c : ActivationCost) : String :=
  let parts : List String :=
    (match c.loyalty with
     | some sym => [sym.toNotation]
     | none => []) ++
    (if c.mana.symbols.isEmpty then [] else [toString c.mana]) ++
    (if c.tap then ["{T}"] else []) ++
    (if c.payLife != 0 then [s!"Pay {c.payLife} life"] else []) ++
    (if c.discardSource then ["Discard this card"] else []) ++
    (if c.exileSourceFromGraveyard then ["Exile this card from your graveyard"] else []) ++
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
    (if c.sacrificeArtifactOrCreature then
      ["Sacrifice an artifact or creature"] else []) ++
    (if c.sacrificeArtifactOrDiscardNonland then
      ["Sacrifice an artifact or discard a nonland card"] else []) ++
    (if c.removeAnyNumberPlusOne then
      ["Remove any number of +1/+1 counters from this"] else []) ++
    (if c.putStunCounterOnSource then
      ["Put a stun counter on this"] else []) ++
    (if c.sacrificeEquipmentAttachedToSource then
      ["Sacrifice an Equipment attached to this"] else []) ++
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

/-- Timing, zone, condition, and frequency restrictions on an activated ability (CR 602.5 / 117.1a / 112.6 / 702.6 / 702.177 / 702.193). -/
structure ActivationRestrictions where
  /-- Exhaust: activate this ability only once (CR 702.177). -/
  exhaust : Bool := false
  /-- An “Activate only if …” restriction (CR 602.5b). -/
  condition : ActivationCondition := .none
  /-- Cost reduction on this activated ability (CR 602.2b / 601.2f). -/
  costReduction : ActivationCostReduction := .none
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
  /-- Target quality restriction on an equip ability (CR 702.6). -/
  equipRestriction : EquipRestriction := .none
  /-- Power-up (CR 702.193): activate only once; if the source entered this
  turn, the cost is reduced by the permanent's mana cost. -/
  powerUp : Bool := false
deriving Repr, Inhabited, BEq

/-- An activated ability printed on a card (CR 602.1). Mana abilities that
are `{T}: Add` are stored separately on `CardDef.tapAddMana` /
`CardDef.tapAddManaForEach` / basic land types. -/
structure ActivatedAbility extends ActivationRestrictions where
  cost : ActivationCost
  /-- The ability's printed line, when its wording isn't built from the cost
  and effect (Reality Fracture). -/
  printed : String := ""
  /-- First (or only) mode of this ability. -/
  effect : Effect
  /-- Additional modes of a modal ability (CR 700.2). Empty means the ability
  is not modal; the player otherwise chooses one mode at CR 601.2b. -/
  otherModes : Array Effect := #[]
deriving Repr, Inhabited, BEq

/-- Parts of `ab`'s cost the player chooses what to pay with (CR 601.2h). -/
def costPicksOf (ab : ActivatedAbility) : Array CostPick :=
  ab.cost.picks

namespace ActivatedAbility

def fraCondition (ab : ActivatedAbility) : ActivationCondition :=
  ab.condition

def onlyIfYouControlLegendary (ab : ActivatedAbility) : Bool :=
  ab.condition == .youControlLegendary

def onlyIfYouAttackedWithTwoOrMore (ab : ActivatedAbility) : Bool :=
  ab.condition == .youAttackedWithTwoOrMore

def onlyIfOpponentDealtNoncombatDamage (ab : ActivatedAbility) : Bool :=
  ab.condition == .opponentDealtNoncombatDamage

def onlyIfYouControlCreatureToughnessAtLeast (ab : ActivatedAbility) : Nat :=
  match ab.condition with
  | .youControlCreatureToughnessAtLeast n => n
  | _ => 0

def onlyIfGyCreaturesAtLeast (ab : ActivatedAbility) : Nat :=
  match ab.condition with
  | .gyCreaturesAtLeast n => n
  | _ => 0

def costLessPerPlusOneOnTarget (ab : ActivatedAbility) : Bool :=
  ab.costReduction == .perPlusOneOnTarget

def costReductionIfYouControlLegendary (ab : ActivatedAbility) : Nat :=
  match ab.costReduction with
  | .ifYouControlLegendary n => n
  | _ => 0

def costReductionPerEquipment (ab : ActivatedAbility) : Nat :=
  match ab.costReduction with
  | .perEquipment n => n
  | _ => 0

def costReductionIfTargetPowerAtMost (ab : ActivatedAbility) : Option (Nat × Int) :=
  match ab.costReduction with
  | .ifTargetPowerAtMost n p => some (n, p)
  | _ => none

def equipSubtype (ab : ActivatedAbility) : Option String :=
  match ab.equipRestriction with
  | .subtype s => some s
  | _ => none

def equipWorthy (ab : ActivatedAbility) : Bool :=
  ab.equipRestriction == .worthy

/-- The crew ability of a Vehicle with Crew `n` (CR 702.122). -/
def crewAbility (n : Nat) : ActivatedAbility :=
  { cost := { extra := .crew n }, printed := s!"Crew {n}"
    effect := { resolution := .grant .artifactCreatureVehicle .source
                phrase := "This Vehicle becomes an artifact creature until end of turn" } }

/-- An equip ability (CR 702.6): attach to target creature you control,
only as a sorcery. -/
def isEquip (ab : ActivatedAbility) : Bool :=
  ab.effect.resolution == .attach .source .target && ab.onlyAsSorcery && ab.otherModes.isEmpty

/-- Baron Helmut Zemo's boast ability (activate only if it attacked this turn
and only once each turn). -/
def zemoBoastAbility : ActivatedAbility :=
  { cost := { extra := .zemoBoast }
    printed := "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
    effect := { resolution := .mayCast .boastExiled .unlimited .withoutPaying
                phrase := "Copy those exiled cards. You may cast up to three of the copies without paying their mana costs" } }

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array Effect :=
  #[ab.effect] ++ ab.otherModes

/-- An activated ability with a loyalty symbol in its cost (CR 209.2). -/
def isLoyaltyAbility (ab : ActivatedAbility) : Bool :=
  ab.cost.isLoyalty

/-- True when zero targets is a legal announcement (CR 115.1c). -/
def allowsZeroTargets (ab : ActivatedAbility) : Bool :=
  ab.effect.allowsZeroTargets

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
      " (activate only if you attacked with two or more creatures this turn)" else "") ++
    (if ab.onlyIfOpponentDealtNoncombatDamage then
      " (activate only if an opponent has been dealt noncombat damage this turn)" else "")
  let body :=
    if ab.isModal then
      let modes := ab.allModes.toList.map Effect.toNotation
      s!"Choose one — {String.intercalate "; " modes}"
    else
      ab.effect.toNotation
  s!"{ab.cost.toNotation}: {body}{timing}"

instance : ToString ActivatedAbility where
  toString := toNotation

end ActivatedAbility

end Mtg.Engine
