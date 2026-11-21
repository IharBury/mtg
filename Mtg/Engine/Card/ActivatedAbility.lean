import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.ManaSpec

/-!
# Activated abilities (CR 602, 605, 606, 305.6)

Unified representation of every activated ability — including mana abilities
(CR 605.1a), loyalty abilities (CR 606.2), intrinsic basic-land mana abilities
(CR 305.6), equip/cycling/boast/exhaust/power-up/crew keyword abilities
(CR 702), zone-scoped abilities (CR 113.6), activation conditions (CR 602.5b),
and declarative cost reductions (CR 602.2b / 601.2f) — anchored to the
25 September 2026 Comprehensive Rules.
-/

namespace Mtg.Engine

/-- Activation timing class of an activated ability (CR 117.1b / 307.5 / 606.3). -/
inductive ActivationTiming where
  /-- Any time the player has priority (default). -/
  | instant
  /-- "Activate only as a sorcery" (CR 307.5). -/
  | sorcery
  /-- Loyalty ability timing (CR 606.3): main phase, empty stack, once per
  permanent per turn (subject to static exceptions such as Jace instant-speed). -/
  | loyalty
deriving DecidableEq, Repr, Inhabited, BEq

/-- Keyword / mechanic tag carried by an `ActivatedAbility` so keyword-sensitive
rules (e.g. Equip discounts, Cycling triggers, Boast CR 702.142a, Exhaust
CR 702.177a, Power-up CR 702.193a–b, Crew CR 702.122a) identify it directly. -/
inductive ActivationMechanicTag where
  /-- Equip (CR 702.6), with an optional extra creature filter (e.g. Human,
  worthy). -/
  | equip (filter? : Option ObjectPred := none)
  /-- Cycling / typecycling (CR 702.29). -/
  | cycling (subtype? : Option String := none)
  /-- Boast (CR 702.142a): activate only if this creature attacked this turn and
  only once each turn. -/
  | boast
  /-- Power-up (CR 702.193a–b): activate only once; if the source entered this
  turn, reduced by the permanent's mana cost. -/
  | powerUp
  /-- Exhaust (CR 702.177a): activate this ability only once. -/
  | exhaust
  /-- Crew N (CR 702.122a). -/
  | crew (minPower : Nat)
deriving Repr, Inhabited, BEq

instance : HasTextChange ActivationMechanicTag where
  applyTextChanges tcs tag :=
    if tcs.isEmpty then tag
    else
      match tag with
      | .equip (some pred) => .equip (some (HasTextChange.applyTextChanges tcs pred))
      | other => other

/-- Declarative generic-mana cost reduction on an activated ability
(CR 602.2b / 601.2f). `amount` evaluates to generic mana subtracted from the
ability's mana cost whenever `condition?` holds (unconditionally when `none`). -/
structure ActivationCostReduction where
  amount : ValueExpr
  condition? : Option Condition := none
deriving Repr, Inhabited, BEq

namespace ActivationCostReduction

/-- Whether evaluating this reduction depends on a chosen target (`target 0`),
so cost computation locks it in after CR 601.2c target selection. -/
def mentionsTarget (r : ActivationCostReduction) : Bool :=
  r.amount.mentionsTarget || (r.condition?.map Condition.mentionsTarget |>.getD false)

/-- "This ability costs `{n}` less to activate if you control a legendary creature." -/
def ifControlLegendary (n : Nat) : ActivationCostReduction :=
  { amount := .const (Int.ofNat n)
    condition? := some (.exists (.inZones .battlefield (.all #[
      .hasSupertype .legendary, .hasType .creature, .controlledBy .you]))) }

/-- "This ability costs `{n}` less to activate for each Equipment you control." -/
def perEquipment (n : Nat := 1) : ActivationCostReduction :=
  let eqCount := ValueExpr.count (.inZones .battlefield (.all #[
    .hasSubtype (.literal .equipment), .controlledBy .you]))
  { amount := if n == 1 then eqCount else .binary .mul (.const (Int.ofNat n)) eqCount }

/-- "This ability costs `{n}` less to activate if it targets a creature with
power `maxPower` or less." -/
def ifTargetPowerAtMost (n : Nat) (maxPower : Int) : ActivationCostReduction :=
  { amount := .const (Int.ofNat n)
    condition? := some (.all #[
      .exists (.target 0),
      .forAll (.target 0) (.all #[.hasType .creature, .stat .power .le (.const maxPower)])]) }

/-- "This ability costs `{1}` less to activate for each +1/+1 counter on that
creature." -/
def perPlusOneOnTarget : ActivationCostReduction :=
  { amount := .counterCount (some .plusOnePlusOne) (.target 0) }

end ActivationCostReduction

instance : HasTextChange ActivationCostReduction where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      { amount := HasTextChange.applyTextChanges tcs r.amount
        condition? := r.condition?.map (HasTextChange.applyTextChanges tcs) }

/-- An activated ability (CR 602.1), unifying stack activated abilities, mana
abilities (CR 605.1a), loyalty abilities (CR 606.2), and CR 305.6 intrinsic
basic-land mana abilities. -/
structure ActivatedAbility where
  cost : CostSpec := {}
  /-- The ability's printed line, when its wording isn't built from the cost
  and effect. -/
  printed : String := ""
  /-- First (or only) mode of this ability. Pure declarative mana abilities
  leave this at `{}` and carry their production in `mana?`. -/
  effect : Effect := {}
  /-- Additional modes of a modal ability (CR 700.2). Empty means the ability
  is not modal; the player otherwise chooses one mode at CR 601.2b. -/
  otherModes : Array Effect := #[]
  /-- Declarative mana production when this ability produces mana
  (CR 106.1 / 106.6 / 605.1a). -/
  mana? : Option ManaProductionSpec := none
  /-- Activation timing class: `.instant` (default), `.sorcery` (CR 307.5), or
  `.loyalty` (CR 606.3). -/
  timing : ActivationTiming := .instant
  /-- Zones from which this ability may be activated (CR 113.6). Defaults to
  the battlefield. -/
  activeZones : Array ZoneKind := #[.battlefield]
  /-- Maximum activations of this specific ability per turn (e.g. `some 1` for
  "Activate only once each turn" or Boast CR 702.142a). -/
  turnLimit? : Option Nat := none
  /-- Maximum activations of this specific ability across this permanent's
  lifetime on the battlefield (e.g. `some 1` for Exhaust CR 702.177a and
  Power-up CR 702.193a). -/
  lifetimeLimit? : Option Nat := none
  /-- Additional activation condition ("Activate only if ..." / "Activate only
  during your turn", CR 602.5b). -/
  condition? : Option Condition := none
  /-- Declarative generic-mana cost reductions (CR 602.2b / 601.2f). -/
  costReductions : Array ActivationCostReduction := #[]
  /-- Optional keyword / mechanic tag (`equip`, `cycling`, `boast`, `powerUp`,
  `exhaust`, `crew`). -/
  tag? : Option ActivationMechanicTag := none
deriving Repr, Inhabited, BEq

namespace ActivatedAbility

/-! ### Canonical Activation Conditions (CR 602.5b) -/

/-- "Activate only if you control a legendary creature." -/
def condControlsLegendaryCreature : Condition :=
  .exists (.inZones .battlefield (.all #[
    .hasSupertype .legendary, .hasType .creature, .controlledBy .you]))

/-- "Activate only if you attacked with `n` or more creatures this turn." -/
def condAttackedWithCreaturesAtLeast (n : Nat := 2) : Condition :=
  .turnHistory (.eventOccurredThisTurn .you (.attackedWith (.hasType .creature) n))

/-- "Activate only if an opponent has been dealt noncombat damage this turn." -/
def condOpponentDealtNoncombatDamageThisTurn : Condition :=
  .turnHistory (.eventOccurredThisTurn .opponent (.dealtDamage false true))

/-- "Activate only if you control a creature with toughness `n` or greater." -/
def condControlsCreatureToughnessAtLeast (n : Nat) : Condition :=
  .exists (.inZones .battlefield (.all #[
    .hasType .creature, .controlledBy .you, .stat .toughness .ge (.const (Int.ofNat n))]))

/-- "Activate only if there are `n` or more creature cards in your graveyard." -/
def condGraveyardCreatureCardsAtLeast (n : Nat) : Condition :=
  .cmp .ge (ValueExpr.count (.inZones .yourGraveyard (.all #[.isCard, .hasType .creature])))
    (.const (Int.ofNat n))

/-- "Activate only if you've scried or surveilled this turn." -/
def condScriedOrSurveilledThisTurn : Condition :=
  .any #[.turnHistory (.scriedThisTurn .you), .turnHistory (.surveilledThisTurn .you)]

/-- "Activate only if there are `n` or more cards in your graveyard." -/
def condGraveyardCardsAtLeast (n : Nat) : Condition :=
  .cmp .ge (.playerMetric .graveyardSize .you) (.const (Int.ofNat n))

/-- "Activate only if there are `n` or more loyalty counters among Jaces you control." -/
def condJaceLoyaltyAtLeast (n : Nat) : Condition :=
  .cmp .ge
    (.aggregate .sum (.counterCount (some .loyalty))
      (.inZones .battlefield (.all #[.hasSubtype (.literal .jace), .controlledBy .you])))
    (.const (Int.ofNat n))

/-- "Activate only if this land entered this turn or if you control a basic land." -/
def condEnteredThisTurnOrControlBasicLand : Condition :=
  .any #[
    .all #[.exists .this, .forAll .this .enteredThisTurn],
    .exists (.inZones .battlefield (.all #[
      .hasSupertype .basic, .hasType .land, .controlledBy .you]))]

/-- Boast prerequisite: this creature attacked this turn (CR 702.142a). -/
def condSourceAttackedThisTurn : Condition :=
  .all #[.exists .this, .forAll .this .attackedThisTurn]

/-! ### Zone / Timing / Mechanic Predicates -/

def isFromBattlefield (ab : ActivatedAbility) : Bool :=
  ab.activeZones.contains .battlefield

def isFromGraveyard (ab : ActivatedAbility) : Bool :=
  ab.activeZones.contains .graveyard || ab.cost.exileSourceFromGraveyard

def isFromHand (ab : ActivatedAbility) : Bool :=
  ab.activeZones.contains .hand || ab.cost.discardSource || ab.cost.exileSourceFromHand

def isSorcerySpeed (ab : ActivatedAbility) : Bool :=
  ab.timing == .sorcery

/-- An activated ability with a loyalty symbol in its cost (CR 606.2). -/
def isLoyaltyAbility (ab : ActivatedAbility) : Bool :=
  ab.timing == .loyalty || ab.cost.isLoyalty

/-- An equip ability (CR 702.6): attach to target creature you control,
only as a sorcery. -/
def isEquip (ab : ActivatedAbility) : Bool :=
  match ab.tag? with
  | some (.equip _) => true
  | _ => ab.effect.resolution == .attach .source .target && ab.timing == .sorcery && ab.otherModes.isEmpty

/-- Creature subtype restriction on an Equip `<Subtype>` ability, if any (CR 702.6c). -/
def equipSubtype? (ab : ActivatedAbility) : Option CardSubtype :=
  match ab.tag? with
  | some (.equip (some (.hasSubtype (.literal sub)))) => some sub
  | _ => none

/-- True when this ability is Equip worthy (legendary non-Villain red or white
creature, CR 702.6c). -/
def isEquipWorthy (ab : ActivatedAbility) : Bool :=
  match ab.tag? with
  | some (.equip (some pred)) => pred == ObjectPred.worthy
  | _ => false

/-- Extra target filter on an Equip ability, if any (CR 702.6c). -/
def equipTargetPred? (ab : ActivatedAbility) : Option ObjectPred :=
  match ab.tag? with
  | some (.equip pred?) => pred?
  | _ => none

/-- A cycling or typecycling ability (CR 702.29). -/
def isCycling (ab : ActivatedAbility) : Bool :=
  match ab.tag? with
  | some (.cycling _) => true
  | _ =>
    ab.isFromHand && ab.cost.discardSource &&
      ((ab.printed.toLower).startsWith "cycling " ||
       match ab.effect.resolution with
       | .draw 1 => ab.printed.isEmpty
       | .searchLandTypeToHand t => t != "Plan"
       | _ => false)

def isBoast (ab : ActivatedAbility) : Bool :=
  ab.tag? == some .boast

def isPowerUp (ab : ActivatedAbility) : Bool :=
  ab.tag? == some .powerUp

def isExhaust (ab : ActivatedAbility) : Bool :=
  ab.tag? == some .exhaust

def isCrew (ab : ActivatedAbility) : Bool :=
  match ab.tag? with
  | some (.crew _) => true
  | _ => ab.cost.crewPower?.isSome

/-- True when any cost reduction on this ability depends on a chosen target. -/
def hasTargetCostReduction (ab : ActivatedAbility) : Bool :=
  ab.costReductions.any ActivationCostReduction.mentionsTarget

/-- True when this ability has a once-per-turn cap (`turnLimit? = some 1`). -/
def isOnceEachTurn (ab : ActivatedAbility) : Bool :=
  ab.turnLimit? == some 1

/-! ### CR 605.1a Mana Ability Classification (25 September 2026) -/

/-- True when resolving any mode of this ability could add mana to a player's
mana pool (CR 605.1a). -/
def couldAddMana (ab : ActivatedAbility) : Bool :=
  ab.mana?.isSome || (#[ab.effect] ++ ab.otherModes).any (fun m => m.resolution.couldAddMana)

/-- CR 605.1a (25 September 2026): an activated ability is a mana ability iff:
1. it does not require a target;
2. it could add mana to a player's mana pool when it resolves;
3. it is not a loyalty ability; AND
4. its instructions do not include moving a card to or from a library.
All modes of a modal ability are inspected uniformly. -/
def isManaAbility (ab : ActivatedAbility) : Bool :=
  let modes := #[ab.effect] ++ ab.otherModes
  !ab.isLoyaltyAbility &&
    !modes.any (fun m => !m.targetSpec.isEmpty) &&
    ab.couldAddMana &&
    !ab.cost.movesToOrFromLibrary &&
    !modes.any (fun m => m.resolution.movesToOrFromLibrary)

/-! ### Canonical Ability Constructors -/

/-- Intrinsic `{T}: Add {M}` mana ability granted by a basic land type (CR 305.6). -/
def intrinsicBasicLandMana (c : Color) : ActivatedAbility :=
  { cost := CostSpec.tapOnly
    mana? := some { spec := .fixedOne (.colored c) } }

/-- Declarative mana ability builder with configurable cost, `ManaSpec`,
spending restriction, spell riders, self-damage, and activation condition. -/
def manaAbility (spec : ManaSpec) (cost : CostSpec := CostSpec.tapOnly)
    (restriction : Option ManaSpendRestriction := none)
    (riders : Array SpellRiderSpec := #[]) (damageYou : Nat := 0)
    (condition? : Option Condition := none) (turnLimit? : Option Nat := none)
    (lifetimeLimit? : Option Nat := none) (timing : ActivationTiming := .instant)
    (chooseColorPrefix : Bool := false) (filterPairFormat : Bool := false)
    (printed : String := "") : ActivatedAbility :=
  { cost
    printed
    mana? := some { spec, restriction, riders, damageYou, chooseColorPrefix, filterPairFormat }
    timing
    turnLimit?
    lifetimeLimit?
    condition? }

/-- Simple `{T}: Add {M}` mana ability (with optional spending restriction). -/
def manaSimple (t : ManaType) (restriction : Option ManaSpendRestriction := none) :
    ActivatedAbility :=
  manaAbility (.fixedOne t) CostSpec.tapOnly restriction

/-- `{T}, Sacrifice this permanent: Add one mana of any color.` (Treasure / Heartwood). -/
def manaTapSacrificeAnyColor : ActivatedAbility :=
  manaAbility (.oneOf .anyColor (.const 1))
    (CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self])

/-- `{T}, Sacrifice this permanent: Add three mana of any one color.` (Lotus). -/
def manaTapSacrificeThreeOfOneColor : ActivatedAbility :=
  manaAbility (.oneOf .anyColor (.const 3))
    (CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self])

/-- `{T}: Add one mana of the chosen color.` -/
def manaTapChosenColor : ActivatedAbility :=
  manaAbility (.oneOf .chosenColorOnSource (.const 1))

/-- The crew ability of a Vehicle with Crew `n` (CR 702.122). -/
def crewAbility (n : Nat) : ActivatedAbility :=
  { cost := CostSpec.crewCost n
    printed := s!"Crew {n}"
    effect := { resolution := .becomeArtifactCreatureUntilEot
                phrase := "This Vehicle becomes an artifact creature until end of turn" }
    tag? := some (.crew n) }

/-- Baron Helmut Zemo's boast ability (CR 702.142a: activate only if this
creature attacked this turn and only once each turn). -/
def zemoBoastAbility : ActivatedAbility :=
  { cost := CostSpec.exileBlackManaSymbols 15
    printed := "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
    effect := { resolution := .zemoBoastCopies
                phrase := "Copy those exiled cards. You may cast up to three of the copies without paying their mana costs" }
    turnLimit? := some 1
    condition? := some condSourceAttackedThisTurn
    tag? := some .boast }

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array Effect :=
  #[ab.effect] ++ ab.otherModes

/-- True when zero targets is a legal announcement (CR 115.1c). -/
def allowsZeroTargets (ab : ActivatedAbility) : Bool :=
  ab.effect.allowsZeroTargets

/-- True when the player must choose among two or more modes (CR 700.2). -/
def isModal (ab : ActivatedAbility) : Bool :=
  !ab.otherModes.isEmpty

/-- Canonical Oracle rendering of an `ActivatedAbility` (CR 602.1 / 605). -/
def toOracle (ctx : PrintCtx) (ab : ActivatedAbility) : String :=
  let body :=
    match ab.mana? with
    | some mp => mp.toOracleSentence ctx
    | none =>
      if ab.isModal then
        let modes := ab.allModes.toList.map Effect.toNotation
        s!"Choose one — {String.intercalate "; " modes}"
      else
        ab.effect.toNotation
  let prefixTag :=
    match ab.tag? with
    | some .exhaust => "Exhaust — "
    | some .boast => "Boast — "
    | _ => ""
  let clauses : List String := Id.run do
    let mut clauses : List String := []
    if ab.timing == .sorcery && !ab.isEquip then
      clauses := clauses ++ ["Activate only as a sorcery."]
    if let some cond := ab.condition? then
      if !ab.isBoast || cond != condSourceAttackedThisTurn then
        if cond == .isYourTurn then
          clauses := clauses ++ ["Activate only during your turn."]
        else if cond == condEnteredThisTurnOrControlBasicLand then
          clauses := clauses ++ ["Activate only if this land entered this turn or if you control a basic land."]
        else
          clauses := clauses ++ [s!"Activate only if {toOracleStr cond { ctx with capitalize := false }}."]
    if let some n := ab.turnLimit? then
      if !ab.isBoast then
        if n == 1 then clauses := clauses ++ ["Activate only once each turn."]
        else clauses := clauses ++ [s!"Activate no more than {englishNumber n} times each turn."]
    if let some n := ab.lifetimeLimit? then
      if !ab.isExhaust && !ab.isPowerUp then
        if n == 1 then clauses := clauses ++ ["Activate only once."]
        else clauses := clauses ++ [s!"Activate no more than {englishNumber n} times."]
    if ab.activeZones == #[.graveyard] then
      clauses := clauses ++ ["Activate only from your graveyard."]
    else if ab.activeZones == #[.hand] && !ab.isCycling then
      clauses := clauses ++ ["Activate only from your hand."]
    return clauses
  let base := s!"{prefixTag}{ab.cost.toNotation}: {body}"
  if clauses.isEmpty then base
  else s!"{base} {String.intercalate " " clauses}"

def toNotation (ab : ActivatedAbility) : String :=
  if ab.mana?.isSome then
    ab.toOracle {}
  else if ab.isBoast && !ab.printed.isEmpty then
    ab.printed
  else
    let timing :=
      (if ab.timing == .sorcery then " (activate only as a sorcery)" else "") ++
      (match ab.condition? with
       | some .isYourTurn => " (activate only during your turn)"
       | some c =>
         if ab.isBoast && c == condSourceAttackedThisTurn then ""
         else s!" (activate only if {toOracleStr c})"
       | none => "") ++
      (match ab.turnLimit? with
       | some 1 => if ab.isBoast then "" else " (activate only once each turn)"
       | some n => s!" (activate at most {n} times each turn)"
       | none => "") ++
      (if ab.activeZones == #[.graveyard] then " (activate only from the graveyard)" else "") ++
      (if ab.activeZones == #[.hand] then " (activate only from your hand)" else "")
    let body :=
      if ab.isModal then
        let modes := ab.allModes.toList.map Effect.toNotation
        s!"Choose one — {String.intercalate "; " modes}"
      else
        ab.effect.toNotation
    let prefixTag := if ab.isBoast then "Boast — " else ""
    s!"{prefixTag}{ab.cost.toNotation}: {body}{timing}"

instance : ToOracle ActivatedAbility where
  toOracle := toOracle

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
        mana? := ab.mana?.map (HasTextChange.applyTextChanges tcs)
        condition? := ab.condition?.map (HasTextChange.applyTextChanges tcs)
        costReductions := ab.costReductions.map (HasTextChange.applyTextChanges tcs)
        tag? := ab.tag?.map (HasTextChange.applyTextChanges tcs) }

end Mtg.Engine
