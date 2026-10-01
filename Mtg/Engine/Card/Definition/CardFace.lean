import Mtg.Engine.Card.Definition.Ability

/-!
# Compiling a card face

`CardFace` accumulates one face of a `TraditionalCardDefinition`.
`toCardDef` compiles that face to the engine `CardDef`.
-/

namespace Mtg.Engine

/-- A traditional (non-token, non-DFC-only) printed card. -/
inductive TraditionalCardDefinition where
  | card : List CardPart → TraditionalCardDefinition
deriving Repr, Inhabited, BEq

/-- Accumulator for one face of a `TraditionalCardDefinition`. -/
structure CardFace where
  name : String := ""
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[]
  supertypes : Array Supertype := #[]
  subtypes : Array Subtype := #[]
  power : Option Int := none
  toughness : Option Int := none
  keywords : Keywords := Keywords.none
  action : Option CardAction := none
  alternatives : Array (List CardPart) := #[]
  activatedAbilities : Array ActivatedAbility := #[]
  triggeredAbilities : Array TriggeredAbility := #[]
  costReductionIfTargetTapped : Nat := 0
  costReductionIfTargetAttackingNontoken : Nat := 0
  costReductionIfTargetAttacking : Nat := 0
  costReductionIfCreatureDied : Nat := 0
  /-- This spell costs {X} less, where X is the total power of creatures you
  control with flying. -/
  costReductionEqualFlyingPower : Bool := false
  costReductionIfYouControl : Option (Nat × String) := none
  /-- Spells this object's controller casts from anywhere other than their
  hand cost this much generic mana less. -/
  costReductionNotFromHand : Nat := 0
  additionalCostSacrificeArtifactOrCreature : Bool := false
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
  additionalCostOrPayGeneric : Option Nat := none
  extraLandIfOtherSubtype : Option String := none
  staticAbilities : Array StaticAbility := #[]
  /-- If one or more tokens would be created under your control, twice that
  many of those tokens are created instead. -/
  tokenDoubling : Bool := false
  /-- If you would draw a card except the first one you draw in each of your
  draw steps, draw two cards instead. -/
  drawTwoExceptFirstDrawStep : Bool := false
  tapAddMana : Array ManaType := #[]
  tapAddAnyColorEqualToPower : Bool := false
  tapAddAnyColorForInstantOrSorcery : Bool := false
  tapAddOneOf : Array ManaType := #[]
  entersTapped : Bool := false
  /-- This enchantment enters with a hope counter for each creature its
  controller controls (Dawn of a New Age). -/
  entersWithHopePerCreature : Bool := false
  /-- As this enters, its controller chooses a creature type (CR 614.12). -/
  asEntersChooseCreatureType : Bool := false
  /-- This land enters tapped unless you control an Equipment. -/
  entersTappedUnlessEquipment : Bool := false
  /-- Crew N (CR 702.122). `N` is the number of creatures to tap. -/
  crew : Option Nat := none
  /-- Choose one or both (CR 700.2). The controller may choose two modes. -/
  chooseOneOrBoth : Bool := false
  /-- This spell can't be countered (CR 701.5). -/
  cantBeCountered : Bool := false
  /-- You may cast this spell as though it had flash if you control this subtype. -/
  flashIfYouControlSubtype : Option String := none
  /-- Flashback cost (CR 702.34). -/
  flashback : Option ManaCost := none
  /-- Teamwork N (CR 702.194). `N` is the total power of creatures that may be tapped. -/
  teamwork : Option Nat := none
  /-- How many times cascade is printed. Each instance is one ability. -/
  cascade : Nat := 0
  /-- Optional kicker cost (CR 702.32). -/
  kicker : Option ManaCost := none
  /-- Gift this spell may promise (CR 702.174). -/
  gift : Option Gift := none
  /-- Affinity for this subtype (CR 702.40). -/
  affinityForSubtype : Option String := none
  /-- Ward cost (CR 702.21). A generic mana cost. -/
  ward : Option Nat := none
  colorIndicator : Option ColorSet := none
  sagaChapters : Array SagaChapter := #[]
  /-- The first creature spell you cast each turn costs this much generic less. -/
  firstCreatureCostsLess : Nat := 0
  /-- The first creature spell you cast each turn can be cast as though it had flash. -/
  firstCreatureHasFlash : Bool := false
  tapAddManaForEach : Array TapAddForEach := #[]
  tapAddTwoAmong : Array ManaType := #[]
  tapAddRestricted : Option (Array ManaType × String) := none
  tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none
  /-- This enters tapped unless you control a legendary creature. -/
  entersTappedUnlessLegendary : Bool := false
  /-- `{T}: Add {A} or {B}` usable only if this land entered this turn or you
  control a basic land. -/
  tapAddOneOfIfEnteredOrBasic : Array ManaType := #[]
  /-- This spell costs this much generic less if your graveyard has at least
  this many creature cards: `(count, generic)`. -/
  costReductionIfGyCreaturesAtLeast : Option (Nat × Nat) := none
  /-- As an additional cost, discard a card or pay this much generic mana. -/
  additionalCostDiscardOrPayGeneric : Option Nat := none
  /-- Static `removeAllAbilities` effects. While this face is on the
  battlefield, objects matching a selector lose all abilities. -/
  removesAllAbilitiesFrom : Array Selector := #[]
deriving Inhabited

namespace CardFace

def hostBonus (enchanted : Bool) (p t : Int) (k : Keywords) : StaticAbility :=
  if enchanted then
    if k == Keywords.none then .enchantedCreatureGets p t
    else .enchantedCreatureGetsAndHas p t k
  else if k == Keywords.none then
    .equippedCreatureGets p t
  else if p == 0 && t == 0 then
    .equippedCreatureHasKeywords k
  else
    .equippedCreatureGetsAndHas p t k

def mergeHostBonus (prev : StaticAbility) (p t : Int) (k : Keywords)
    (enchanted : Bool) : Option StaticAbility :=
  if enchanted then
    match prev with
    | .enchantedCreatureGets p0 t0 =>
      some (hostBonus true (p0 + p) (t0 + t) k)
    | .enchantedCreatureGetsAndHas p0 t0 k0 =>
      some (hostBonus true (p0 + p) (t0 + t) (k0.merge k))
    | _ => none
  else
    match prev with
    | .equippedCreatureGets p0 t0 =>
      some (hostBonus false (p0 + p) (t0 + t) k)
    | .equippedCreatureHasKeywords k0 =>
      some (hostBonus false p t (k0.merge k))
    | .equippedCreatureGetsAndHas p0 t0 k0 =>
      some (hostBonus false (p0 + p) (t0 + t) (k0.merge k))
    | _ => none

/-- Replace a trailing equipped +P/+T with the same bonus and ward `{w}`. -/
def pushHostWard (b : CardFace) (w : Nat) : CardFace :=
  if w == 0 then b
  else if b.types.contains .enchantment then
    match b.staticAbilities.back? with
    | some (.enchantedCreatureGetsAndHas p t k) =>
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push (.enchantedCreatureGetsHasAndWard p t k w) }
    | _ => b
  else
    match b.staticAbilities.back? with
    | some (.equippedCreatureGets p t) =>
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push (.equippedCreatureGetsAndWard p t w) }
    | some (.equippedCreatureGetsAndHas p t k) =>
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push (.equippedCreatureGetsHasAndWard p t k w) }
    | _ => b

def pushHostBonus (b : CardFace) (p t : Int) (k : Keywords) : CardFace :=
  let enchanted := b.types.contains .enchantment
  match b.staticAbilities.back? with
  | some prev =>
    match mergeHostBonus prev p t k enchanted with
    | some merged =>
      { b with staticAbilities := b.staticAbilities.pop.push merged }
    | none =>
      { b with staticAbilities := b.staticAbilities.push (hostBonus enchanted p t k) }
  | none =>
    { b with staticAbilities := b.staticAbilities.push (hostBonus enchanted p t k) }

def applyReduceCost (assign : CardFace → Nat → CardFace) (b : CardFace)
    (e : ContinuousEffect) : CardFace :=
  match e with
  | .reduceCost _ costs =>
    assign b (ManaCost.manaValue (Cost.manaCost costs))
  | _ => b

/-- Cost-reduction leftovers implied by a selector-shaped condition. -/
def applyIfShape (b : CardFace) (s : Selector.Shape)
    (inners : List ContinuousEffect) : CardFace :=
  if s.tappedCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with costReductionIfTargetTapped := b.costReductionIfTargetTapped + n })
      b
  else if s.attackingNontokenCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfTargetAttackingNontoken :=
            b.costReductionIfTargetAttackingNontoken + n })
      b
  else if s.attackingCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfTargetAttacking :=
            b.costReductionIfTargetAttacking + n })
      b
  else if s.diedThisTurnCreature then
    inners.foldl
      (applyReduceCost fun b n =>
        { b with
          costReductionIfCreatureDied := b.costReductionIfCreatureDied + n })
      b
  else b

/-- Extra land plays while you control another of a subtype. -/
def extraLandIfOtherSubtype? (among : Selector) (inners : List ContinuousEffect)
    : Option String :=
  match inners with
  | [.increaseLandPlayLimit who (Value.nat 1)] =>
    if who == .controller .this then among.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- This has haste as long as you control another of a subtype. -/
def leftoverHasteIfOtherSubtype? (among : Selector) (inners : List ContinuousEffect)
    : Option String :=
  match inners with
  | [.gainAbility who (.keyword .haste)] =>
    if who == .this || who == .source .this then
      among.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- This has lifelink as long as you control another of a subtype. -/
def leftoverLifelinkIfOtherSubtype? (among : Selector) (inners : List ContinuousEffect)
    : Option String :=
  match inners with
  | [.gainAbility who (.keyword .lifelink)] =>
    if who == .this || who == .source .this then
      among.shape.anotherSubtypeYouControl
    else none
  | _ => none

/-- A permanent of one subtype controlled by `Selector.caster`. -/
def casterControlsPermanentSubtype? : Selector → Option String
  | .intersection parts =>
    let subtypes := parts.filterMap fun
      | .subtype st => some st.toString
      | _ => none
    let only := parts.all fun
      | .zone .battlefield | .controlled .caster | .subtype _ => true
      | _ => false
    if only && parts.contains (.zone .battlefield) && parts.contains (.controlled .caster) then
      match subtypes with
      | [t] => some t
      | _ => none
    else none
  | _ => none

/-- This spell may be cast as though it had flash while the caster controls
that subtype. The spell does not gain flash. -/
def leftoverCanBeCastAsThoughWithFlashIf? (card : Selector) (cond : Condition) :
    Option String :=
  if card == .this || card == .source .this then
    match cond with
    | .any among => casterControlsPermanentSubtype? among
    | _ => none
  else none

/-- Creature spells this object's controller casts. -/
def firstCreatureSpellYouCast? (sel : Selector) : Bool :=
  sel == .intersection [.spell, .cardType .creature, .controlled (.controller .this)]

/-- Equip abilities you activate that target this, reduced by that much. -/
def leftoverEquipAbilitiesTargetingThisCostLess? (who : Selector) (costs : List Cost)
    : Option Nat :=
  let n := ManaCost.manaValue (Cost.manaCost costs)
  if n != 0 &&
      Selector.leftoverKeywordAbility? who == some .equip &&
      Selector.leftoverHasTarget? who == some .this &&
      who.shape.sameController then
    some n
  else none

def mergeOtherCreaturesGet (b : CardFace) (subtypes : Array String) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.otherCreaturesGet prev p0 t0) =>
    if prev == subtypes then
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push (.otherCreaturesGet subtypes (p0 + p) (t0 + t)) }
    else
      { b with staticAbilities := b.staticAbilities.push (.otherCreaturesGet subtypes p t) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.otherCreaturesGet subtypes p t) }

def mergeSubtypeCreaturesYouControlGet (b : CardFace) (subtype : String) (p t : Int) :
    CardFace :=
  match b.staticAbilities.back? with
  | some (.creaturesYouControlOfSubtypeGet prev p0 t0) =>
    if prev == subtype then
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push (.creaturesYouControlOfSubtypeGet subtype (p0 + p) (t0 + t)) }
    else
      { b with staticAbilities := b.staticAbilities.push (.creaturesYouControlOfSubtypeGet subtype p t) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.creaturesYouControlOfSubtypeGet subtype p t) }

def mergeOpponentsCreaturesGet (b : CardFace) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.opponentsCreaturesGet p0 t0) =>
    { b with
      staticAbilities :=
        b.staticAbilities.pop.push (.opponentsCreaturesGet (p0 + p) (t0 + t)) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.opponentsCreaturesGet p t) }

def mergeCreaturesYouControlGet (b : CardFace) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.creaturesYouControlGet p0 t0) =>
    { b with
      staticAbilities :=
        b.staticAbilities.pop.push (.creaturesYouControlGet (p0 + p) (t0 + t)) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.creaturesYouControlGet p t) }

/-- Creatures this object's controller controls of the creature type chosen
by an action. -/
def chosenTypeCreaturesYouControl? : Selector → Bool
  | .intersection [
      .zone .battlefield,
      .cardType .creature,
      .controlled (.controller .this),
      .hasCreatureTypeChosenByAction _] => true
  | _ => false

def mergeChosenTypeCreaturesGet (b : CardFace) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.chosenTypeCreaturesGet p0 t0) =>
    { b with
      staticAbilities :=
        b.staticAbilities.pop.push (.chosenTypeCreaturesGet (p0 + p) (t0 + t)) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.chosenTypeCreaturesGet p t) }

/-- Legendary creatures this object's controller controls. -/
def legendaryCreaturesYouControl : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this), .supertype .legendary]

/-- Nonlegendary creatures this object's controller controls. -/
def nonlegendaryCreaturesYouControl : Selector :=
  .intersection
    [.zone .battlefield, .cardType .creature, .not (.supertype .legendary), .controlled (.controller .this)]

def mergeLegendaryCreaturesGet (b : CardFace) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.legendaryCreaturesGetAndWard p0 t0 w) =>
    { b with
      staticAbilities :=
        b.staticAbilities.pop.push (.legendaryCreaturesGetAndWard (p0 + p) (t0 + t) w) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.legendaryCreaturesGetAndWard p t 0) }

def mergeNonlegendaryCreaturesGet (b : CardFace) (p t : Int) : CardFace :=
  match b.staticAbilities.back? with
  | some (.nonlegendaryCreaturesGet p0 t0) =>
    { b with
      staticAbilities :=
        b.staticAbilities.pop.push (.nonlegendaryCreaturesGet (p0 + p) (t0 + t)) }
  | _ =>
    { b with staticAbilities := b.staticAbilities.push (.nonlegendaryCreaturesGet p t) }

/-- Integer `addPower` / `addToughness`. Adjacent bonuses on the same objects combine. -/
def applyIntegerPowerToughness (b : CardFace) (sel : Selector) (p t : Int) : CardFace :=
  match sel with
  | .hostOf .this => pushHostBonus b p t Keywords.none
  | _ =>
    let s := sel.shape
    if sel == legendaryCreaturesYouControl then
      mergeLegendaryCreaturesGet b p t
    else if sel == nonlegendaryCreaturesYouControl then
      mergeNonlegendaryCreaturesGet b p t
    else if chosenTypeCreaturesYouControl? sel then
      mergeChosenTypeCreaturesGet b p t
    else if s.other && s.sameController && s.types.eqTypes [.creature] then
      mergeOtherCreaturesGet b sel.includedSubtypes.toArray p t
    else if s.opponentControls && s.types.eqTypes [.creature] then
      mergeOpponentsCreaturesGet b p t
    else if CardAction.leftoverCreaturesYouControlMass? sel then
      mergeCreaturesYouControlGet b p t
    else
      match sel with
      | .intersection [.zone .battlefield, .cardType .creature, .subtype st, .controlled (.controller .this)] =>
        mergeSubtypeCreaturesYouControlGet b st.toString p t
      | _ => b

/-- Total power of creature permanents with flying that this object's
controller controls. -/
def isTotalPowerOfFlyingCreaturesYouControl : Value → Bool
  | .totalPower among =>
    let s := among.shape
    s.mustBePermanent && s.sameController && s.flying && !s.other &&
      !s.opponentControls && !s.attacking && !s.token && !s.nontoken &&
      s.types.eqTypes [.creature] && s.subtype.isNone &&
      s.powerAtLeast.isNone && s.powerAtMost.isNone && !s.hasPlusOneCounter
  | _ => false

/-- Power of the creature this Equipment is attached to. -/
def isEquippedCreaturePower : Value → Bool
  | .greatestPower (.hostOf .this) | .greatestPower (.hostOf (.source .this)) => true
  | _ => false

/-- Instant and sorcery spells this object's controller casts. -/
def instantSorcerySpellsYouCast : Selector → Bool
  | who =>
    let s := who.shape
    Selector.includesSpell who && s.isSpell && s.sameController &&
      !s.opponentControls && !s.mustBePermanent && s.subtype.isNone &&
      s.types.eqTypes [.instant, .sorcery] && !Selector.includesNoncreature who

/-- `+P/+T` and keywords on this object. A zero bonus with no keywords is
not an effect. -/
def selfGetsAndHas? (effects : List ContinuousEffect) : Option (Int × Int × Keywords) :=
  go effects 0 0 Keywords.none false
where
  go : List ContinuousEffect → Int → Int → Keywords → Bool →
      Option (Int × Int × Keywords)
    | [], p, t, k, seen =>
      if seen && (p != 0 || t != 0 || k != Keywords.none) then some (p, t, k)
      else none
    | .addPower who v :: rest, p, t, k, _ =>
      match valToInt? v with
      | some dp =>
        if isThisOrItsSource who then go rest (p + dp) t k true else none
      | none => none
    | .addToughness who v :: rest, p, t, k, _ =>
      match valToInt? v with
      | some dt =>
        if isThisOrItsSource who then go rest p (t + dt) k true else none
      | none => none
    | .gainAbility who (.keyword kw) :: rest, p, t, k, _ =>
      if isThisOrItsSource who then go rest p t (k.merge kw.toKeywords) true
      else none
    | _, _, _, _, _ => none

/-- `+P/+T` on creatures this object's controller controls. A zero bonus is
not an effect. -/
def teamGetsIfEnduringStory? (effects : List ContinuousEffect) : Option (Int × Int) :=
  match ContinuousEffect.addedPT? effects with
  | some (p, t) =>
    if (p != 0 || t != 0) &&
        effects.all fun e =>
          match e with
          | .addPower who _ | .addToughness who _ =>
            CardAction.leftoverCreaturesYouControlMass? who
          | _ => false then
      some (p, t)
    else none
  | none => none

/-- Artifacts and creatures this object's controller controls. -/
def artifactsAndCreaturesYouControl? : Selector → Bool
  | .intersection
      [.zone .battlefield,
        .union [.cardType .artifact, .cardType .creature],
        .controlled (.controller .this)] => true
  | _ => false

/-- Ward `{n}` on artifacts and creatures this object's controller controls.
Zero ward is not an effect. -/
def teamWardIfEnduringStory? : List ContinuousEffect → Option Nat
  | [.gainAbility who (.keywordWithCost .ward [.mana [.generic n]])] =>
    if n != 0 && artifactsAndCreaturesYouControl? who then some n else none
  | _ => none

/-- Creature permanents, with no further restriction. -/
def allCreaturePermanents? : Selector → Bool
  | .intersection [.zone .battlefield, .cardType .creature] => true
  | _ => false

/-- Creatures with power at most `n`, and nothing else. -/
def powerAtMostCreatureBlocker? : Selector → Option Int
  | .intersection [.zone .battlefield, .cardType .creature, .powerAtMost v] =>
    valToInt? v
  | _ => none

/-- Add `{k}` to the last activated ability's per-Equipment cost reduction.
The reduction is `{k}` times the number of Equipment its controller controls.
No activated ability means the static text did not follow one. -/
def addEquipmentCostReduction (b : CardFace) (k : Nat) : CardFace :=
  if k == 0 then b
  else
    match b.activatedAbilities.back? with
    | none => b
    | some ab =>
      { b with
        activatedAbilities :=
          b.activatedAbilities.pop.push
            { ab with
              costReductionPerEquipment := ab.costReductionPerEquipment + k } }

/-- `replace` of a triggered ability of one subtype of permanent this object's
controller controls, so that ability triggers twice instead of once. -/
def extraTriggerSubtypeYouControl? : List ContinuousEffect → Option String
  | [.replace
      (.abilityTriggers (.intersection [.zone .battlefield, .subtype st, ctl]))
      [.duplicateReplacingTrigger (.nat 2)]] =>
    if ctl == .controlled (.controller .this) then some st.toString else none
  | _ => none

/-- Spells this object's controller casts from anywhere other than their hand. -/
def spellsYouCastNotFromHand (who : Selector) : Bool :=
  who == .intersection [
    .spell,
    .controlled (.controller .this),
    .not (.castFromZone .hand)]

/-- Creatures can't attack this object's controller unless their controller
pays `{n}` for each. Zero is not a cost. -/
def attackTaxIfEnduringStory? : List ContinuousEffect → Option Nat
  | [.cantAttackUnlessPays attackers dest [.mana [.generic n]]] =>
    if n != 0 && allCreaturePermanents? attackers && dest == .controller .this then
      some n
    else none
  | _ => none

/-- Equip abilities of permanents this object's controller controls. -/
def equipAbilitiesYouControl : Selector :=
  .intersection [
    Selector.keywordAbility .equip,
    .controlled (.controller .this)]

/-- Printed static abilities of cards read with `parseOracleParts` that
compile to one named static ability or ability field. -/
def printedStaticApplied? (b : CardFace) : ContinuousEffect → Option CardFace
  | .replace (.damage .all who) [] =>
    if who == .this || who == .source .this then
      some { b with staticAbilities := b.staticAbilities.push .preventAllDamageToThis }
    else none
  | .canBeCastAsThoughWithFlashIf card cond =>
    if card == .intersection [.spell, .controlled (.controller .this)] &&
        cond == .happened
          (.castSpell (.intersection [.spell, .controlled (.opponent (.controller .this))]))
          .turnStart then
      some { b with staticAbilities := b.staticAbilities.push .flashIfOpponentCastThisTurn }
    else none
  | .if (.not (.and (.not (.any a)) (.not (.any p)))) [.gainAbility who (.keyword .indestructible)] =>
    let you := Selector.controlled (.controller .this)
    if (who == .this || who == .source .this) &&
        a == .intersection [.zone .battlefield, .cardType .artifact, .cardType .creature, you] &&
        p == .intersection [.zone .battlefield, .subtype .plan, you] then
      some { b with staticAbilities := b.staticAbilities.push .indestructibleIfArtifactCreatureOrPlan }
    else none
  | .addPower who (.count (.intersection [.not .this, .zone .battlefield, .cardType .artifact, you])) =>
    if (who == .this || who == .source .this) && you == .controlled (.controller .this) then
      some { b with staticAbilities := b.staticAbilities.push (.getsPowerPerOtherArtifact 1) }
    else none
  | .if (.lessOrEqual (.greatestPower who) (.nat n)) [.forbid (.block .any blocked)] =>
    if (who == .this || who == .source .this) &&
        (blocked == .this || blocked == .source .this) then
      some { b with
        staticAbilities :=
          b.staticAbilities.push (.cantBeBlockedIfPowerAtMost (n : Int)) }
    else none
  | .canPlay who card =>
    if who == .controller .this &&
        card == .intersection
          [.zone .graveyard, .cardType .land, .owner (.controller .this)] then
      some { b with staticAbilities := b.staticAbilities.push .mayPlayLandsFromGraveyard }
    else none
  | .if (.any (.intersection [
        .zone .battlefield,
        .cardType .creature,
        .powerAtMost (.int k),
        .isTargetOf .this]))
      [.reduceCost .this [.mana [.generic n]]] =>
    match b.activatedAbilities.back? with
    | some ab =>
      if n != 0 then
        some { b with
          activatedAbilities :=
            b.activatedAbilities.pop.push
              { ab with costReductionIfTargetPowerAtMost := some (n, k) } }
      else none
    | none => none
  | _ => none

def applyContinuousEffect (b : CardFace) : ContinuousEffect → CardFace
  | .gainAbility (.hostOf .this) (.keyword k) =>
    pushHostBonus b 0 0 k.toKeywords
  | .gainAbility (.hostOf .this) (.keywordWithCost .ward [.mana [.generic n]]) =>
    pushHostWard b n
  | .gainAbility sel (.keyword .menace) =>
    let s := sel.shape
    if s.sameController && s.mustBePermanent && s.types.eqTypes [.creature] &&
        s.hasPlusOneCounter && !s.other && s.subtype.isNone &&
        !s.opponentControls then
      { b with
        staticAbilities :=
          b.staticAbilities.push .creaturesYouControlWithPlusOneHaveMenace }
    else if s.attacking && s.token && s.sameController then
      { b with staticAbilities := b.staticAbilities.push (.attackingTokensHave Keyword.menace) }
    else b
  | .gainAbility sel (.keyword k) =>
    let s := sel.shape
    if s.attacking && s.token && s.sameController then
      { b with staticAbilities := b.staticAbilities.push (.attackingTokensHave k.toKeywords) }
    else if k == .trample && sel.includedSubtype? == some "Army" && s.sameController then
      { b with staticAbilities := b.staticAbilities.push .armiesYouControlHaveTrample }
    else if s.sameController && s.mustBePermanent && s.types.eqTypes [.creature] &&
        s.hasPlusOneCounter && !s.other && s.subtype.isNone && !s.opponentControls then
      { b with staticAbilities := b.staticAbilities.push (.creaturesWithPlusOneHave k.toKeywords) }
    else
      match k, Selector.subtypesYouControl? sel with
      | .trample, some (subtypes, true) =>
        { b with staticAbilities := b.staticAbilities.push (.otherCreaturesHaveTrample subtypes) }
      | _, _ => b
  | .gainAbility sel (.keywordWithCost .ward [.mana [.generic n]]) =>
    match b.staticAbilities.back? with
    | some (.legendaryCreaturesGetAndWard p t 0) =>
      if sel == legendaryCreaturesYouControl && n != 0 then
        { b with
          staticAbilities := b.staticAbilities.pop.push (.legendaryCreaturesGetAndWard p t n) }
      else b
    | _ => b
  | .gainAbility sel (.activated costs action) =>
    match Selector.subtypesYouControl? sel, CardAction.leftoverTapAddOneOf? costs action with
    | some (subtypes, true), some mana =>
      { b with
        staticAbilities := b.staticAbilities.push (.otherSubtypeHaveTapAddOneOf subtypes mana) }
    | _, _ => b
  | .gainAbility _ _ => b
  | .addPower sel v =>
    match valToInt? v with
    | some p => applyIntegerPowerToughness b sel p 0
    | none => b
  | .addToughness sel v =>
    match valToInt? v with
    | some t => applyIntegerPowerToughness b sel 0 t
    | none => b
  | .if (.any among) inners =>
    match extraLandIfOtherSubtype? among inners with
    | some t => { b with extraLandIfOtherSubtype := some t }
    | none =>
        match leftoverHasteIfOtherSubtype? among inners with
      | some t =>
        { b with
          staticAbilities :=
            b.staticAbilities.push (.hasteIfYouControlOtherSubtype t) }
      | none =>
        match leftoverLifelinkIfOtherSubtype? among inners with
        | some t =>
          { b with
            staticAbilities :=
              b.staticAbilities.push (.lifelinkIfYouControlOtherSubtype t) }
        | none =>
          if Selector.includesLegendary among && among.shape.sameController &&
              among.shape.types.eqTypes [.creature] then
            inners.foldl
              (applyReduceCost fun b n =>
                { b with
                  activatedAbilities :=
                    b.activatedAbilities.map fun ab =>
                      { ab with
                        costReductionIfYouControlLegendary :=
                          ab.costReductionIfYouControlLegendary + n } })
              b
          else applyIfShape b among.shape inners
  | .if (.anySubtype among st) inners =>
    match inners with
    | [.increaseLandPlayLimit who (Value.nat 1)] =>
      if who == .controller .this && among.shape.other &&
          among.shape.sameController then
        { b with extraLandIfOtherSubtype := some st.toString }
      else b
    | _ =>
      if among.shape.sameController then
        inners.foldl
          (applyReduceCost fun b n =>
            { b with costReductionIfYouControl := some (n, st.toString) })
          b
      else b
  | .if (.not (.happened (.castSpell cast) .turnStart)) [.reduceCost cast' costs] =>
    if cast == cast' && firstCreatureSpellYouCast? cast then
      { b with
        firstCreatureCostsLess :=
          b.firstCreatureCostsLess + ManaCost.manaValue (Cost.manaCost costs) }
    else b
  | .if (.happened (.die who) .turnStart) inners =>
    applyIfShape b { who.shape with diedThisTurn := true } inners
  | .if (.happened (.putCountersSimultaneously who on .plusOnePlusOne) .turnStart)
      [.gainAbility flyingWho (.keyword .flying)] =>
    if who == .controller .this &&
        (on == .this || on == .source .this) &&
        (flyingWho == .this || flyingWho == .source .this) then
      { b with staticAbilities := b.staticAbilities.push .flyingIfPlusOneThisTurn }
    else b
  | .if (.happened _ _) _ => b
  | .if (.timeToCastSorcery _) _ => b
  | .if (.turn _) _ | .if (.drawStep _) _ => b
  | .if (.not (.enduringStory who)) [.doesntUntap self] =>
    if who == .controller .this && (self == .this || self == .source .this) then
      { b with staticAbilities := b.staticAbilities.push .doesntUntapUnlessEnduringStory }
    else b
  | .if (.not (.any among)) [.replace (.enter who) actions] =>
    if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersTapped? actions &&
        among.includedSubtype? == some "Equipment" &&
        among.shape.sameController then
      { b with entersTappedUnlessEquipment := true }
    else if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersTapped? actions &&
        among == Selector.aLegendaryCreatureYouControl then
      { b with entersTappedUnlessLegendary := true }
    else b
  | .if (.not (.and
      (.drawStep step)
      (.not (.happened (.draw drawer .all) (.drawStep since)))))
      [.replace (.draw who .all) [.draw instead (.nat 2)]] =>
    if step == .controller .this && since == .controller .this &&
        drawer == .controller .this && who == .controller .this &&
        instead == .controller .this then
      { b with drawTwoExceptFirstDrawStep := true }
    else b
  | .if (.not (.any among)) [.forbid (.block who .all)] =>
    match Selector.subtypesYouControl? among with
    | some (subtypes, false) =>
      if who == .this || who == .source .this then
        { b with staticAbilities := b.staticAbilities.push (.cantBlockUnlessYouControl subtypes) }
      else b
    | _ => b
  | .if (.not _) _ => b
  | .if (.enduringStory who) inners =>
    if who == .controller .this then
      match selfGetsAndHas? inners with
      | some (p, t, k) =>
        { b with
          staticAbilities :=
            b.staticAbilities.push (.getsAndHasIfEnduringStory p t k) }
      | none =>
        match teamGetsIfEnduringStory? inners with
        | some (p, t) =>
          { b with
            staticAbilities :=
              b.staticAbilities.push (.creaturesYouControlGetIfEnduringStory p t) }
        | none =>
          match teamWardIfEnduringStory? inners with
          | some n =>
            { b with
              staticAbilities :=
                b.staticAbilities.push
                  (.artifactsAndCreaturesHaveWardIfEnduringStory n) }
          | none =>
            match attackTaxIfEnduringStory? inners with
            | some n =>
              { b with
                staticAbilities :=
                  b.staticAbilities.push
                    (.creaturesCantAttackYouUnlessPayIfEnduringStory n) }
            | none =>
              match extraTriggerSubtypeYouControl? inners with
              | some st =>
                { b with
                  staticAbilities :=
                    b.staticAbilities.push (.extraTriggerIfEnduringStorySubtype st) }
              | none => b
    else b
  | .if
      (.and
        (.enduringStory who)
        (.not (.happened (.activateAbility among) .turnStart)))
      [.alternativeCost who' costs] =>
    if who == .controller .this &&
        among == equipAbilitiesYouControl &&
        who' == equipAbilitiesYouControl &&
        costs == [.mana [.generic 0]] then
      { b with
        staticAbilities :=
          b.staticAbilities.push .firstEquipFreeIfEnduringStory }
    else b
  | .if (.and _ _) _ => b
  | .if (.greaterOrEqual (.count among) threshold) [.reduceCost .this [.mana [.generic k]]] =>
    match valToNat? threshold with
    | some t =>
      if CardAction.leftoverYourGyCreatures? among && t != 0 && k != 0 then
        { b with costReductionIfGyCreaturesAtLeast := some (t, k) }
      else b
    | none => b
  | .if (.greaterOrEqual (.count among) threshold) inners =>
    if valToNat? threshold == some 7 then
      match CardAction.leftoverThresholdGets? among inners with
      | some ab => { b with staticAbilities := b.staticAbilities.push ab }
      | none => b
    else if valToNat? threshold == some 2 then
      match CardAction.leftoverGetsIfGyCreatureCards? among inners with
      | some ab => { b with staticAbilities := b.staticAbilities.push ab }
      | none => b
    else b
  | .if (.less (.count among) threshold) [.forbid (.attack who .all)] =>
    match valToNat? threshold, among.shape.anotherSubtypeYouControl with
    | some n, some subtype =>
      if (who == .this || who == .source .this) && n != 0 then
        { b with
          staticAbilities :=
            b.staticAbilities.push (.cantAttackUnlessYouControlNOther n subtype) }
      else b
    | _, _ => b
  | .if (.less _ _) _ | .if (.lessOrEqual _ _) _ | .if (.greater _ _) _
  | .if (.greaterOrEqual _ _) _ | .if (.equal _ _) _ => b
  | .replace (.enter who) actions =>
    if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersTapped? actions then
      { b with entersTapped := true }
    else if (who == .this || who == .source .this) &&
        CardAction.leftoverChooseCreatureTypeAsEnters? actions then
      { b with asEntersChooseCreatureType := true }
    else if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersWithXPlusOne? actions then
      { b with staticAbilities := b.staticAbilities.push .entersWithXPlusOne }
    else if (who == .this || who == .source .this) &&
        CardAction.leftoverEntersWithHopePerCreature? actions then
      { b with entersWithHopePerCreature := true }
    else b
  | .replace (.damage src who) actions =>
    if (who == .this || who == .source .this) && src == .all &&
        CardAction.leftoverHealThenKeepReplaced? actions then
      { b with staticAbilities := b.staticAbilities.push .healOtherDamageWhenDealt }
    else b
  | .replace (.combatDamage _ _) _ => b
  | .replace (.createTokens which) [.modifyReplacementCreatedTokenCount f] =>
    if which == .intersection [.token, .controlled (.controller .this)] &&
        doublesCreatedTokenCount f then
      { b with tokenDoubling := true }
    else b
  | .replace _ _ => b
  | .forbid
      (.or
        (.attack who dest)
        (.block blocker blocked)) =>
    if who.shape.flying && (dest == .controller .this || dest == .this) &&
        blocker.shape.flying && blocked.shape.sameController &&
        blocked.shape.types.eqTypes [.creature] then
      { b with
        staticAbilities := b.staticAbilities.push .flyingCantAttackYouOrBlockYours }
    else b
  | .forbid (.attack _ _) =>
    b
  | .forbid (.block .this .all) =>
    { b with staticAbilities := b.staticAbilities.push (.cantBlockUnlessYouControl #[]) }
  | .forbid (.block who .this) =>
    if who == .any then
      { b with keywords := { b.keywords with cantBeBlocked := true } }
    else if who == .token then
      { b with staticAbilities := b.staticAbilities.push .cantBeBlockedByTokens }
    else
      match powerAtMostCreatureBlocker? who with
      | some n =>
        { b with
          staticAbilities :=
            b.staticAbilities.push (.cantBeBlockedByPowerAtMost n) }
      | none => b
  | .forbid (.counter who) =>
    if isThisOrItsSource who then { b with cantBeCountered := true } else b
  | .forbid (.block .any (.hostOf .this)) =>
    match b.staticAbilities.back? with
    | some (.equippedCreatureHasKeywords k) =>
      { b with
        staticAbilities :=
          b.staticAbilities.pop.push
            (.equippedCreatureHasKeywordsAndCantBeBlocked k) }
    | _ => b
  | .forbid _ => b
  | .canCastWithoutPayingManaCost _ _ => b
  | .canPlay _ _ => b
  | .setBasePower _ _ | .setBaseToughness _ _ => b
  | .gainType _ _ => b
  | .gainSubtype _ _ => b
  | .gainAllSubtypes _ _ => b
  | .setPower _ _ | .setToughness _ _ => b
  | .increaseLandPlayLimit _ _ => b
  | .canBeCastAsThoughWithFlashIf card cond =>
    match leftoverCanBeCastAsThoughWithFlashIf? card cond with
    | some t => { b with flashIfYouControlSubtype := some t }
    | none =>
      if firstCreatureSpellYouCast? card &&
          cond == .not (.happened (.castSpell card) .turnStart) then
        { b with firstCreatureHasFlash := true }
      else b
  | .doesntUntap who =>
    if who == .hostOf .this && b.removesAllAbilitiesFrom.contains (.hostOf .this) then
      { b with
        staticAbilities :=
          b.staticAbilities.push .enchantedLosesAbilitiesDoesntUntap }
    else b
  | .cantAttackUnlessPays _ _ _ => b
  | .removeAllAbilities who =>
    { b with removesAllAbilitiesFrom := b.removesAllAbilitiesFrom.push who }
  | .alternativeCost _ _ => b
  | .additionalCost _ cs =>
    { b with
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature ||
          Cost.sacrificesArtifactOrCreature cs
      additionalCostSacrificeCreature :=
        b.additionalCostSacrificeCreature || Cost.sacrificesOneCreature cs
      additionalCostOrPayGeneric :=
        if (Cost.discardOrPayGeneric? cs).isSome then b.additionalCostOrPayGeneric
        else b.additionalCostOrPayGeneric.orElse (fun _ => Cost.orPayGeneric? cs)
      additionalCostDiscardOrPayGeneric :=
        b.additionalCostDiscardOrPayGeneric.orElse (fun _ => Cost.discardOrPayGeneric? cs) }
  | .reduceCostWithX who costs v =>
    if (who == .this || who == .source .this) &&
        costs == [.mana [.x]] &&
        isTotalPowerOfFlyingCreaturesYouControl v then
      { b with costReductionEqualFlyingPower := true }
    else if costs == [.mana [.x]] && isEquippedCreaturePower v &&
        instantSorcerySpellsYouCast who then
      { b with
        staticAbilities :=
          b.staticAbilities.push .instantSorceryCostReductionEqualEquippedPower }
    else
      match costs, v with
      | [.mana [.generic k]], .count among =>
        match who with
        | .abilityWithId _ =>
          if k != 0 &&
              among.includedSubtype? == some "Equipment" &&
              among.shape.sameController then
            addEquipmentCostReduction b k
          else b
        | _ => b
      | _, _ => b
  | .reduceCost who costs =>
    if spellsYouCastNotFromHand who then
      { b with
        costReductionNotFromHand :=
          b.costReductionNotFromHand + ManaCost.manaValue (Cost.manaCost costs) }
    else
      match leftoverEquipAbilitiesTargetingThisCostLess? who costs with
      | some n =>
        { b with
          staticAbilities :=
            b.staticAbilities.push (.equipAbilitiesTargetingThisCostLess n) }
      | none =>
        { b with
          costReductionIfTargetTapped :=
            b.costReductionIfTargetTapped + ManaCost.manaValue (Cost.manaCost costs) }

def applyAbility (b : CardFace) : Ability → CardFace
  | .keyword (.crew n) =>
    if n == 0 then b else { b with crew := some n }
  | .keyword (.teamwork n) =>
    if n == 0 then b else { b with teamwork := some n }
  | .keyword .improvise =>
    { b with staticAbilities := b.staticAbilities.push .improvise }
  | .keyword (.affinity types subtypes) =>
    match types, subtypes with
    | [], [st] => { b with affinityForSubtype := some st.toString }
    | _, _ => b
  | .keyword .boast =>
    { b with staticAbilities := b.staticAbilities.push .boast }
  | .keyword .cascade =>
    { b with cascade := b.cascade + 1 }
  | .keyword .extort =>
    { b with staticAbilities := b.staticAbilities.push .extort }
  | .keyword (.gift g) =>
    { b with gift := some g }
  | .keyword k => { b with keywords := b.keywords.merge k.toKeywords }
  | .keywordWithCost .flashback costs =>
    { b with flashback := some (Cost.manaCost costs) }
  | .keywordWithCost .kicker costs =>
    let cost := Cost.manaCost costs
    if cost.symbols.isEmpty then b else { b with kicker := some cost }
  | .keywordWithCost .sneak costs =>
    let cost := Cost.manaCost costs
    if cost.symbols.isEmpty then b
    else { b with staticAbilities := b.staticAbilities.push (.sneak cost) }
  | .keywordWithCost .ward [.mana [.generic n]] =>
    if n == 0 then b else { b with ward := some n }
  | .keywordWithCost .ward costs =>
    match Cost.discardOrPayGeneric? costs with
    | some n => { b with staticAbilities := b.staticAbilities.push (.wardDiscardOrPay n) }
    | none => b
  | .keywordWithCost k costs =>
    match (Ability.keywordWithCost k costs).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .keywordWithSubtypeAndCost k st cost =>
    match (Ability.keywordWithSubtypeAndCost k st cost).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .keywordWithTarget _ _ _ => b
  | .keywordWithEffect k actions =>
    match k with
    | .chapter n =>
      match CardAction.leftoverChapterEffect? actions with
      | some e =>
        let ch := SagaChapter.of (toRomanNumeral n) e.phrase e
        -- `III, IV — <effect>` is one catalog line for consecutive chapters.
        match b.sagaChapters.back? with
        | some last =>
          if last.chapterEffect == ch.chapterEffect && last.effect == ch.effect &&
              last.chapterNumbers.back? == some (n - 1) then
            { b with
              sagaChapters :=
                b.sagaChapters.pop.push
                  (SagaChapter.of (last.roman ++ ", " ++ toRomanNumeral n) e.phrase e) }
          else { b with sagaChapters := b.sagaChapters.push ch }
        | none => { b with sagaChapters := b.sagaChapters.push ch }
      | none => b
    | _ => b
  | .keywordWithAbility k inner =>
    match k, inner with
    | .infinity, .triggered (.endStep who) action =>
      if who == .controller .this && CardAction.leftoverHarnessFlicker? action then
        { b with
          triggeredAbilities :=
            b.triggeredAbilities.push (.onStep Effect.stepHarnessedFlicker) }
      else b
    | _, _ => b
  | .activated costs action =>
    if CardAction.leftoverTapAddAnyColorEqualToPower? costs action then
      { b with tapAddAnyColorEqualToPower := true }
    else if CardAction.leftoverTapAddAnyColorForInstantOrSorcery? costs action then
      { b with tapAddAnyColorForInstantOrSorcery := true }
    else
      match CardAction.leftoverTapAddMana? costs action with
      | some types => { b with tapAddMana := types }
      | none =>
        match CardAction.leftoverTapAddOneOf? costs action with
        | some types => { b with tapAddOneOf := types }
        | none =>
        match CardAction.leftoverTapAddManaForEach? costs action with
        | some each => { b with tapAddManaForEach := b.tapAddManaForEach.push each }
        | none =>
        match CardAction.leftoverTapAddTwoAmong? costs action with
        | some types => { b with tapAddTwoAmong := types }
        | none =>
        match CardAction.leftoverTapAddRestricted? costs action with
        | some r => { b with tapAddRestricted := some r }
        | none =>
        match CardAction.leftoverTapPayLifeAddOneOf? costs action with
        | some r => { b with tapPayLifeAddOneOf := some r }
        | none =>
          { b with
            activatedAbilities :=
              b.activatedAbilities.push (Ability.activatedAbility costs action) }
  | .activatedIf cond costs action =>
    match (if CardAction.leftoverEnteredThisTurnOrBasic? cond then
        CardAction.leftoverTapAddOneOf? costs action else none) with
    | some types => { b with tapAddOneOfIfEnteredOrBasic := types }
    | none =>
    match (Ability.activatedIf cond costs action).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .activatedWithStaticIf cond costs action e =>
    match (Ability.activatedWithStaticIf cond costs action e).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .graveyardActivatedIf cond costs action =>
    match (Ability.graveyardActivatedIf cond costs action).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => b
  | .abilityId n
      (.activatedWithStaticIf (.not (.happened (.abilityWithIdActivated n') .gameStart)) costs action
        (.if (.happened (.enter (.source .this)) .turnStart) [.reduceCost .this [.mana syms]])) =>
    -- Power-up: once, and this card's mana cost less the turn it entered.
    if n == n' && (syms : ManaCost) == b.manaCost then
      { b with
        activatedAbilities :=
          b.activatedAbilities.push { Ability.activatedAbility costs action with powerUp := true } }
    else b
  | .abilityId n a =>
    match (Ability.abilityId n a).toActivatedAbility? with
    | some ab => { b with activatedAbilities := b.activatedAbilities.push ab }
    | none => applyAbility b a
  | .triggered w action =>
    match (Ability.triggered w action).toTriggeredAbility? with
    | some t => { b with triggeredAbilities := b.triggeredAbilities.push t }
    | none => b
  | .triggeredWhile w cond action =>
    match (Ability.triggeredWhile w cond action).toTriggeredAbility? with
    | some t => { b with triggeredAbilities := b.triggeredAbilities.push t }
    | none => b
  | .static e => (printedStaticApplied? b e).getD (applyContinuousEffect b e)
  | .stackStatic e => (printedStaticApplied? b e).getD (applyContinuousEffect b e)
  | .everywhereStatic e => (printedStaticApplied? b e).getD (applyContinuousEffect b e)

def apply (b : CardFace) : CardPart → CardFace
  | .name n => { b with name := n }
  | .manaCost c => { b with manaCost := (c : ManaCost) }
  | .type t => { b with types := b.types.push t }
  | .supertype s => { b with supertypes := b.supertypes.push s }
  | .subtype s => { b with subtypes := b.subtypes.push s.toString }
  | .colorIndicator cs =>
    { b with colorIndicator := some (cs.foldl ColorSet.insert ColorSet.empty) }
  | .power n => { b with power := some n }
  | .toughness n => { b with toughness := some n }
  | .ability a => applyAbility b a
  | .alternative parts => { b with alternatives := b.alternatives.push parts }
  | .actions as =>
    let action :=
      match as with
      | [a] => a
      | as => .sequence as
    { b with
      action := some action
      chooseOneOrBoth :=
        b.chooseOneOrBoth || CardAction.isChooseOneOrBoth action }

/-- A static ability that sets power or toughness to the number of lands
you control. -/
def partSetsLandsCharacteristic (power : Bool) : CardPart → Bool
  | .ability (.static e) | .ability (.stackStatic e) | .ability (.everywhereStatic e) =>
    setsCharacteristicToLandsYouControl power e
  | _ => false

/-- A static ability that sets power to the number of creatures you control. -/
def partSetsCreaturesYouControlPower : CardPart → Bool
  | .ability (.static e) => setsPowerToCreaturesYouControl e
  | _ => false

/-- A static ability that sets this object's power to the number of cards in
its controller's hand. -/
def partSetsCardsInHandPower : CardPart → Bool
  | .ability (.static (.setPower .this (.count among))) =>
    among == .intersection [.zone .hand, .owner (.controller .this)]
  | _ => false

/-- A static continuous effect, if this part is one. -/
def staticContinuous? : CardPart → Option ContinuousEffect
  | .ability (.static e) | .ability (.stackStatic e) | .ability (.everywhereStatic e) => some e
  | _ => none

/-- Other-subtype +1/+0 for each artifact token. Toughness is not changed. -/
def otherSubtypePerArtifactToken? (parts : List CardPart) : Option String :=
  let effects := parts.filterMap staticContinuous?
  effects.findSome? fun power =>
    match CardAction.leftoverOtherSubtypeGetPowerPerArtifactToken? power with
    | some st =>
      let alsoToughness :=
        effects.any fun
          | .addToughness who _ => who == power.selector
          | _ => false
      if alsoToughness then none else some st
    | none => none

def ofParts (parts : List CardPart) : CardFace :=
  let b := parts.foldl apply {}
  let b :=
    if parts.any (partSetsLandsCharacteristic true) &&
        parts.any (partSetsLandsCharacteristic false) then
      { b with
        staticAbilities :=
          b.staticAbilities.push .powerToughnessEqualLandsYouControl }
    else
      b
  let b :=
    if parts.any partSetsCreaturesYouControlPower then
      { b with
        staticAbilities :=
          b.staticAbilities.push .powerEqualCreaturesYouControl }
    else
      b
  let b :=
    if parts.any partSetsCardsInHandPower then
      { b with staticAbilities := b.staticAbilities.push .powerEqualCardsInHand }
    else
      b
  match otherSubtypePerArtifactToken? parts with
  | some st =>
    { b with
      staticAbilities :=
        b.staticAbilities.push (.otherSubtypeGetPowerPerArtifactToken st) }
  | none => b

def toAdventure (b : CardFace) : AdventureFace := {
  name := b.name
  manaCost := b.manaCost
  types := if b.types.isEmpty then #[.sorcery] else b.types
  subtypes := if b.subtypes.isEmpty then #["Adventure"] else b.subtypes
  oracleText :=
    match b.action with
    | some a => a.toEffect.phrase
    | none => ""
  spellEffect := b.action.map (·.toEffect)
  additionalCostSacrificeCreature := b.additionalCostSacrificeCreature
}

end CardFace

namespace TraditionalCardDefinition

/-- Compile printed parts to the engine `CardDef`. When `oracleText` is
omitted, keywords and the Adventure face are reconstructed so the card
still has ability text. -/
def toCardDef (d : TraditionalCardDefinition) (oracleText : String := "") : CardDef :=
  match d with
  | .card parts =>
    let b := CardFace.ofParts parts
    let adventure :=
      match b.alternatives[0]? with
      | some alt => some (CardFace.ofParts alt).toAdventure
      | none => none
    let generated :=
      let kw :=
        let s := toString b.keywords
        if s.isEmpty then [] else [s]
      let adv :=
        match adventure with
        | none => []
        | some a =>
          let typeLine := formatTypeLine #[] a.types a.subtypes
          let effect :=
            match a.spellEffect with
            | some e => e.phrase
            | none => a.oracleText
          ["//ADV//", s!"{a.name} {a.manaCost}", typeLine, effect]
      String.intercalate "\n" (kw ++ adv)
    {
      name := b.name
      manaCost := b.manaCost
      types := b.types
      subtypes := b.subtypes
      supertypes := b.supertypes
      power := b.power
      toughness := b.toughness
      keywords := b.keywords
      spellModes :=
        match b.action with
        | some a => (CardAction.leftoverModes? a).getD #[]
        | none => #[]
      spellEffect :=
        match b.action with
        | some a =>
          if (CardAction.leftoverModes? a).isSome then none
          else some a.toEffect
        | none => none
      activatedAbilities := b.activatedAbilities
      triggeredAbilities := b.triggeredAbilities
      costReductionIfTargetTapped := b.costReductionIfTargetTapped
      costReductionIfTargetAttackingNontoken := b.costReductionIfTargetAttackingNontoken
      costReductionIfTargetAttacking := b.costReductionIfTargetAttacking
      costReductionIfCreatureDied := b.costReductionIfCreatureDied
      costReductionEqualFlyingPower := b.costReductionEqualFlyingPower
      costReductionIfYouControl := b.costReductionIfYouControl
      costReductionNotFromHand := b.costReductionNotFromHand
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature
      additionalCostSacrificeCreature := b.additionalCostSacrificeCreature
      additionalCostOrPayGeneric := b.additionalCostOrPayGeneric
      extraLandIfOtherSubtype := b.extraLandIfOtherSubtype
      staticAbilities := b.staticAbilities
      tokenDoubling := b.tokenDoubling
      drawTwoExceptFirstDrawStep := b.drawTwoExceptFirstDrawStep
      tapAddMana := b.tapAddMana
      tapAddAnyColorEqualToPower := b.tapAddAnyColorEqualToPower
      tapAddAnyColorForInstantOrSorcery := b.tapAddAnyColorForInstantOrSorcery
      tapAddOneOf := b.tapAddOneOf
      entersTapped := b.entersTapped
      entersWithHopePerCreature := b.entersWithHopePerCreature
      asEntersChooseCreatureType := b.asEntersChooseCreatureType
      entersTappedUnlessEquipment := b.entersTappedUnlessEquipment
      crew := b.crew
      chooseOneOrBoth := b.chooseOneOrBoth
      cantBeCountered := b.cantBeCountered
      flashIfYouControlSubtype := b.flashIfYouControlSubtype
      flashback := b.flashback
      teamwork := b.teamwork
      cascade := b.cascade
      kicker := b.kicker
      gift := b.gift
      affinityForSubtype := b.affinityForSubtype
      ward := b.ward
      colorIndicator := b.colorIndicator
      firstCreatureCostsLess := b.firstCreatureCostsLess
      firstCreatureHasFlash := b.firstCreatureHasFlash
      tapAddManaForEach := b.tapAddManaForEach
      tapAddTwoAmong := b.tapAddTwoAmong
      tapAddRestricted := b.tapAddRestricted
      tapPayLifeAddOneOf := b.tapPayLifeAddOneOf
      entersTappedUnlessLegendary := b.entersTappedUnlessLegendary
      tapAddOneOfIfEnteredOrBasic := b.tapAddOneOfIfEnteredOrBasic
      costReductionIfGyCreaturesAtLeast := b.costReductionIfGyCreaturesAtLeast
      additionalCostDiscardOrPayGeneric := b.additionalCostDiscardOrPayGeneric
      removesAllAbilitiesFrom := b.removesAllAbilitiesFrom
      adventure := adventure
      saga :=
        if b.sagaChapters.isEmpty then none
        else
          let final :=
            b.sagaChapters.foldl (fun acc ch =>
              ch.chapterNumbers.foldl (fun acc n => max acc n) acc) 0
          -- A chapter's text is its printed Oracle line when there is one.
          let printed (ch : SagaChapter) : SagaChapter :=
            match (oracleText.splitOn "\n").findSome? fun line =>
                match line.splitOn " — " with
                | roman :: rest@(_ :: _) =>
                  if roman == ch.roman then some (" — ".intercalate rest) else none
                | _ => none with
            | some text => { ch with effect := text }
            | none => ch
          some {
            sacrificeAfter := toRomanNumeral final
            chapters := b.sagaChapters.map printed }
      oracleText := if oracleText.isEmpty then generated else oracleText
    }

instance : Coe TraditionalCardDefinition CardDef where
  coe d := d.toCardDef

end TraditionalCardDefinition

end Mtg.Engine
