import Mtg.Engine.Card.Effect

/-!
# Activated abilities (CR 602, 605, 606, 305.6)

Unified helper methods, CR 605.1a structural mana classification, CR 305.6
intrinsic basic-land mana synthesis, modal/mana body projections, and canonical
`ToOracle` rendering for `ActivatedAbility` (defined in `Ability.lean`).
Mana production (`PlayerOp.addMana`) and modes (`Instruction.chooseModes`) live
directly inside `ActivatedAbility.effect.body`.
-/

namespace Mtg.Engine

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

/-! ### Body Projections (Folded Mana & Modes) -/

/-- Declarative mana production carried directly in `ab.effect.body`, if any. -/
def manaProduction? (ab : ActivatedAbility) : Option ManaProductionSpec :=
  ab.effect.manaProduction?

/-- Modal specification carried directly in `ab.effect.body`, if any (CR 700.2). -/
def modalSpec? (ab : ActivatedAbility) : Option ModalSpec :=
  ab.effect.modalSpec?

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array Effect :=
  match ab.modalSpec? with
  | some spec => if spec.modes.isEmpty then #[ab.effect] else spec.modes
  | none => #[ab.effect]

/-- True when the player must choose among two or more modes (CR 700.2). -/
def isModal (ab : ActivatedAbility) : Bool :=
  match ab.modalSpec? with
  | some spec => spec.modes.size >= 2
  | none => false

/-- True when zero targets is a legal announcement (CR 115.1c). -/
def allowsZeroTargets (ab : ActivatedAbility) : Bool :=
  ab.effect.allowsZeroTargets

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

/-- True when this entry represents a Morph turn-face-up special action (CR 702.37e). -/
def isTurnFaceUp (ab : ActivatedAbility) : Bool :=
  ab.effect.body == .permanent (.turnFaceUp .this)

/-- An equip ability (CR 702.6): attach to target creature you control,
only as a sorcery. -/
def isEquip (ab : ActivatedAbility) : Bool :=
  match ab.tag? with
  | some (.equip _) => true
  | _ =>
    ab.effect.body == .permanent (.attach .this (.target 0)) &&
      ab.timing == .sorcery && !ab.isModal

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
       match ab.effect.body with
       | .player (.drawCards .you (.const 1)) => ab.printed.isEmpty
       | .player (.searchLibrary spec) =>
         spec.filter != .hasSubtype (.literal .plan) && spec.dest == .hand .controller
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
  ab.allModes.any Effect.couldAddMana

/-- CR 605.1a (25 September 2026): an activated ability is a mana ability iff:
1. it does not require a target;
2. it could add mana to a player's mana pool when it resolves;
3. it is not a loyalty ability; AND
4. its instructions do not include moving a card to or from a library.
All modes of a modal ability are inspected uniformly. -/
def isManaAbility (ab : ActivatedAbility) : Bool :=
  let modes := ab.allModes
  !ab.isLoyaltyAbility &&
    !modes.any (fun m => !m.targetSpec.isEmpty) &&
    ab.couldAddMana &&
    !ab.cost.movesToOrFromLibrary &&
    !modes.any Effect.movesToOrFromLibrary

/-! ### Canonical Ability Constructors -/

/-- Build a modal `ActivatedAbility` folding `modes` into `Instruction.chooseModes` (CR 700.2). -/
def mkModal (cost : CostSpec) (modes : Array Effect)
    (timing : ActivationTiming := .instant)
    (activeZones : Array ZoneKind := #[.battlefield])
    (turnLimit? : Option Nat := none)
    (lifetimeLimit? : Option Nat := none)
    (condition? : Option Condition := none)
    (costReductions : Array ActivationCostReduction := #[])
    (tag? : Option ActivationMechanicTag := none)
    (printed : String := "") : ActivatedAbility :=
  { cost, printed, timing, activeZones, turnLimit?, lifetimeLimit?,
    condition?, costReductions, tag?
    effect :=
      match modes.toList with
      | [single] => single
      | _ => { body := .chooseModes { modes } } }

/-- Intrinsic `{T}: Add {M}` mana ability granted by a basic land type (CR 305.6). -/
def intrinsicBasicLandMana (c : Color) : ActivatedAbility :=
  { cost := CostSpec.tapOnly
    effect := { body := .player (.addMana .you { spec := .fixedOne (.colored c) }) } }

/-- Declarative mana ability builder with configurable cost, `ManaSpec`,
spending restriction, spell riders, self-damage, and activation condition. -/
def manaAbility (spec : ManaSpec) (cost : CostSpec := CostSpec.tapOnly)
    (restriction : Option ManaSpendRestriction := none)
    (riders : Array SpellRiderSpec := #[]) (damageYou : Nat := 0)
    (condition? : Option Condition := none) (turnLimit? : Option Nat := none)
    (lifetimeLimit? : Option Nat := none) (timing : ActivationTiming := .instant)
    (chooseColorPrefix : Bool := false) (filterPairFormat : Bool := false)
    (printed : String := "") : ActivatedAbility :=
  let mp : ManaProductionSpec :=
    { spec, restriction, riders, damageYou, chooseColorPrefix, filterPairFormat }
  { cost
    printed
    effect := { body := .player (.addMana .you mp) }
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
    effect := {
      body := .installEffect (.applyContinuous .untilEndOfTurn .this
        (.modifyTypes { types := #[.artifact, .creature] }))
      phrase := "This Vehicle becomes an artifact creature until end of turn"
    }
    tag? := some (.crew n) }

/-- Baron Helmut Zemo's boast ability (CR 702.142a: activate only if this
creature attacked this turn and only once each turn). -/
def zemoBoastAbility : ActivatedAbility :=
  { cost := CostSpec.exileBlackManaSymbols 15
    printed := "Boast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
    effect := {
      body := .stack (.mayCastOrPlay .costPaidObjects
        { duration := .untilEndOfTurn, landsAllowed := false, freeCast := true,
          copyAndCast := true, maxCasts? := some 3 })
      phrase := "Copy those exiled cards. You may cast up to three of the copies without paying their mana costs"
    }
    turnLimit? := some 1
    condition? := some condSourceAttackedThisTurn
    tag? := some .boast }

/-- Canonical Oracle rendering of an `ActivatedAbility` (CR 602.1 / 605). -/
def toOracle (ctx : PrintCtx) (ab : ActivatedAbility) : String :=
  let body :=
    match ab.manaProduction? with
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
  if ab.manaProduction?.isSome then
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

end Mtg.Engine
