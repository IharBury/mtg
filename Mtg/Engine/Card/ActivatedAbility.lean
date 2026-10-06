import Mtg.Engine.Card.Effect

/-!
# Activated abilities (CR 602)

Activation costs and the printed activated abilities built from unified
effects.
-/

namespace Mtg.Engine

/-- A loyalty symbol in an activation cost (CR 107.7 / 209.2).

`[+N]` puts N loyalty counters on the source, `[-N]` removes N, and `[0]`
puts zero. `[+X]` and `[-X]` use X in place of a fixed number (CR 107.3a). -/
inductive LoyaltySymbol where
  | plus (n : Nat)
  | minus (n : Nat)
  | zero
  | plusX
  | minusX
deriving Repr, Inhabited, BEq

namespace LoyaltySymbol

/-- Rules notation: `[+N]`, `[-N]`, `[0]`, `[+X]`, or `[-X]`. -/
def toNotation : LoyaltySymbol → String
  | .plus n => s!"[+{n}]"
  | .minus n => s!"[-{n}]"
  | .zero => "[0]"
  | .plusX => "[+X]"
  | .minusX => "[-X]"

/-- Counters this symbol adds, or removes when negative.
`[+X]` and `[-X]` are not a fixed number. -/
def counters : LoyaltySymbol → Option Int
  | .plus n => some (Int.ofNat n)
  | .minus n => some (-Int.ofNat n)
  | .zero => some 0
  | .plusX | .minusX => none

end LoyaltySymbol

/-- Reality Fracture activation costs (CR 602.1 / 118). -/
inductive FraCost where
  | none
  /-- Exile another creature card from your graveyard. -/
  | exileAnotherCreatureCardFromGraveyard
  /-- Sacrifice another artifact. -/
  | sacrificeAnotherArtifact
  /-- Sacrifice another creature or planeswalker. -/
  | sacrificeAnotherCreatureOrPlaneswalker
  /-- Sacrifice an artifact or land. -/
  | sacrificeArtifactOrLand
  /-- Discard a legendary card. -/
  | discardLegendaryCard
  /-- Tap two untapped artifacts you control. -/
  | tapTwoUntappedArtifacts
  /-- Exile this card from your hand. -/
  | exileSourceFromHand
  /-- Exile this permanent. -/
  | exileSource
  /-- Crew N: tap any number of untapped creatures you control with total
  power N or more (CR 702.122). -/
  | crew (power : Nat)
  /-- Boast cost of Baron Helmut Zemo: exile any number of black cards from
  your graveyard with fifteen or more black mana symbols among their mana
  costs. -/
  | zemoBoast
deriving Repr, Inhabited, BEq, DecidableEq

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

/-- Costs of an activated ability besides announcements (CR 602.1). -/
structure ActivationCost where
  mana : ManaCost := ManaCost.empty
  tap : Bool := false
  /-- Loyalty symbol in this cost (CR 209.2). The ability is a loyalty
  ability exactly when this is set. -/
  loyalty : Option LoyaltySymbol := none
  sacrificeSource : Bool := false
  /-- Sacrifice another creature or artifact you control (CR 701.17). -/
  sacrificeAnotherCreatureOrArtifact : Bool := false
  /-- Pay this much life (CR 118.3b / 119.4). Payment of life is not damage. -/
  payLife : Nat := 0
  /-- Discard this card from your hand (CR 701.9 / 702.29, e.g. cycling). -/
  discardSource : Bool := false
  /-- Exile this card from your graveyard. -/
  exileSourceFromGraveyard : Bool := false
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
  /-- Sacrifice an artifact or creature you control. -/
  sacrificeArtifactOrCreature : Bool := false
  /-- Sacrifice an artifact or discard a nonland card. -/
  sacrificeArtifactOrDiscardNonland : Bool := false
  /-- Remove any number of +1/+1 counters from the source. -/
  removeAnyNumberPlusOne : Bool := false
  /-- Put a stun counter on the source. -/
  putStunCounterOnSource : Bool := false
  /-- Sacrifice an Equipment attached to the source. -/
  sacrificeEquipmentAttachedToSource : Bool := false
  /-- A Reality Fracture cost. -/
  fra : FraCost := .none
deriving Repr, Inhabited, BEq

namespace ActivationCost

/-- True when this cost contains a loyalty symbol (CR 209.2). -/
def isLoyalty (c : ActivationCost) : Bool :=
  c.loyalty.isSome

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

/-- An activated ability printed on a card (CR 602.1). Mana abilities that
are `{T}: Add` are stored separately on `CardDef.tapAddMana` /
`CardDef.tapAddManaForEach` / basic land types. -/
structure ActivatedAbility where
  cost : ActivationCost
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
  { cost := { fra := .crew n }, printed := s!"Crew {n}"
    effect := { resolution := .fra .becomeArtifactCreatureUntilEot
                phrase := "This Vehicle becomes an artifact creature until end of turn" } }

/-- An equip ability (CR 702.6): attach to target creature you control,
only as a sorcery. -/
def isEquip (ab : ActivatedAbility) : Bool :=
  ab.effect.resolution == .attach && ab.onlyAsSorcery && ab.otherModes.isEmpty

/-- Baron Helmut Zemo's boast ability (activate only if it attacked this turn
and only once each turn). -/
def zemoBoastAbility : ActivatedAbility :=
  { cost := { fra := .zemoBoast }
    printed := "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
    effect := { resolution := .fra .zemoBoastCopies
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
