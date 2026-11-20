import Mtg.Engine.Card.Effect

/-!
# Activated abilities (CR 602)

Activation costs and the printed activated abilities built from unified
effects.
-/

namespace Mtg.Engine

/-- A Reality Fracture “Activate only if …” condition. -/
inductive FraActivationCondition where
  | none
  /-- “Activate only if you've scried or surveilled this turn.” -/
  | scriedOrSurveilledThisTurn
  /-- “Activate only if there are `n` or more cards in your graveyard.” -/
  | graveyardAtLeast (n : Nat)
  /-- “Activate only if there are `n` or more loyalty counters among Jaces you
  control.” -/
  | jaceLoyaltyAtLeast (n : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- An activated ability printed on a card (CR 602.1). Mana abilities that
are `{T}: Add` are stored separately on `CardDef.tapAddMana` /
`CardDef.tapAddManaForEach` / basic land types. -/
structure ActivatedAbility where
  cost : CostSpec := {}
  /-- The ability's printed line, when its wording isn't built from the cost
  and effect (Reality Fracture). -/
  printed : String := ""
  /-- Exhaust: activate this ability only once (CR 702.177). -/
  exhaust : Bool := false
  /-- A Reality Fracture “Activate only if …” condition. -/
  fraCondition : FraActivationCondition := .none
  /-- Equip that costs {1} less for each +1/+1 counter on the target creature. -/
  costLessPerPlusOneOnTarget : Bool := false
  /-- First (or only) mode of this ability. -/
  effect : Effect
  /-- Additional modes of a modal ability (CR 700.2). Empty means the ability
  is not modal; the player otherwise chooses one mode at CR 601.2b. -/
  otherModes : Array Effect := #[]
  /-- Timing restriction “Activate only as a sorcery” (CR 117.1a). -/
  onlyAsSorcery : Bool := false
  /-- Timing restriction “Activate only during your turn”. -/
  onlyDuringYourTurn : Bool := false
  /-- Frequency restriction “Activate only once each turn”. -/
  onceEachTurn : Bool := false
  /-- This ability can be activated only while the source is in a graveyard
  (CR 113.6 / 404). -/
  activateFromGraveyard : Bool := false
  /-- This ability can be activated only while the source is in your hand
  (CR 113.6 / 702.29, e.g. cycling). -/
  activateFromHand : Bool := false
  /-- Timing restriction “Activate only if you control a legendary creature”. -/
  onlyIfYouControlLegendary : Bool := false
  /-- This ability costs this much generic mana less if you control a legendary
  creature (e.g. Esquire of the King). -/
  costReductionIfYouControlLegendary : Nat := 0
  /-- Equip restricted to a creature subtype (e.g. Equip Human). -/
  equipSubtype : Option CardSubtype := none
  /-- This ability costs this much generic mana less for each Equipment you
  control. -/
  costReductionPerEquipment : Nat := 0
  /-- “Activate only if you attacked with two or more creatures this turn.” -/
  onlyIfYouAttackedWithTwoOrMore : Bool := false
  /-- “Activate only if an opponent has been dealt noncombat damage this turn.” -/
  onlyIfOpponentDealtNoncombatDamage : Bool := false
  /-- Power-up (CR 702.193): activate only once; if the source entered this
  turn, the cost is reduced by the permanent's mana cost. -/
  powerUp : Bool := false
  /-- Equip worthy: attach only to a legendary non-Villain red or white
  creature (MSH 118 / 119). Other attach effects ignore this. -/
  equipWorthy : Bool := false
  /-- “Activate only if you control a creature with toughness `n` or greater.” -/
  onlyIfYouControlCreatureToughnessAtLeast : Nat := 0
  /-- “Activate only if there are `n` or more creature cards in your graveyard.” -/
  onlyIfGyCreaturesAtLeast : Nat := 0
  /-- This ability costs this much generic mana less if it targets a creature
  with power at most this value. -/
  costReductionIfTargetPowerAtMost : Option (Nat × Int) := none
deriving Repr, Inhabited, BEq

namespace ActivatedAbility

/-- The crew ability of a Vehicle with Crew `n` (CR 702.122). -/
def crewAbility (n : Nat) : ActivatedAbility :=
  { cost := CostSpec.crewCost n, printed := s!"Crew {n}"
    effect := { resolution := .becomeArtifactCreatureUntilEot
                phrase := "This Vehicle becomes an artifact creature until end of turn" } }

/-- An equip ability (CR 702.6): attach to target creature you control,
only as a sorcery. -/
def isEquip (ab : ActivatedAbility) : Bool :=
  ab.effect.resolution == .attach .source .target && ab.onlyAsSorcery && ab.otherModes.isEmpty

/-- A cycling or typecycling ability (CR 702.29). -/
def isCycling (ab : ActivatedAbility) : Bool :=
  ab.activateFromHand && ab.cost.discardSource &&
    ((ab.printed.toLower).startsWith "cycling " ||
     match ab.effect.resolution with
     | .draw 1 => ab.printed.isEmpty
     | .searchLandTypeToHand t => t != "Plan"
     | _ => false)

/-- Baron Helmut Zemo's boast ability (activate only if it attacked this turn
and only once each turn). -/
def zemoBoastAbility : ActivatedAbility :=
  { cost := CostSpec.exileBlackManaSymbols 15
    printed := "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
    effect := { resolution := .zemoBoastCopies
                phrase := "Copy those exiled cards. You may cast up to three of the copies without paying their mana costs" } }

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array Effect :=
  #[ab.effect] ++ ab.otherModes

/-- An activated ability with a loyalty symbol in its cost (CR 606.2). -/
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

instance : HasTextChange ActivatedAbility where
  applyTextChanges tcs ab :=
    if tcs.isEmpty then ab
    else
      { ab with
        cost := HasTextChange.applyTextChanges tcs ab.cost
        effect := HasTextChange.applyTextChanges tcs ab.effect
        otherModes := HasTextChange.applyTextChanges tcs ab.otherModes
        equipSubtype := HasTextChange.applyTextChanges tcs ab.equipSubtype }

end Mtg.Engine
