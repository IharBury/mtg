import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.SpellEffects
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Traditional card definitions

A printed card as a list of `CardPart`s: name, mana cost, type line,
abilities, and (for adventurer cards) an `alternative` face. Compiles to
`CardDef` so the engine and existing catalogs stay unchanged.

Mechanics the part language does not yet compose can be attached as
leftover engine values (`CardAction.effect`, `triggered`, `static`,
`activatedAbility`) or as the CardDef flags they already compile to.
-/

namespace Mtg.Engine

/-- Timing and extra payment pieces of an activated-ability cost (CR 602.1). -/
structure CostRestrictions where
  onlyAsSorcery : Bool := false
  onlyDuringYourTurn : Bool := false
  onceEachTurn : Bool := false
  activateFromGraveyard : Bool := false
  activateFromHand : Bool := false
  costReductionPerEquipment : Nat := 0
  equipSubtype : Option String := none
deriving Repr, Inhabited, BEq

/-- A payment or restriction in an activated-ability cost (CR 602.1). -/
inductive Cost where
  | mana : List ManaSymbol → Cost
  | tap
  | payLife : Nat → Cost
  | sacrificeSource
  | sacrificeAnotherCreatureOrArtifact
  | sacrificeAnotherSubtype : String → Cost
  | sacrificeArtifact
  | discardACard
  | discardSource
  | discardLegendarySameName
  | onceEachTurn
  | onlyAsSorcery
  | onlyDuringYourTurn
  | activateFromGraveyard
  | activateFromHand
  | costReductionPerEquipment : Nat → Cost
  | equipSubtype : String → Cost
deriving Repr, Inhabited, BEq

namespace Cost

def manaCost : List Cost → ManaCost
  | [] => ManaCost.empty
  | .mana syms :: rest =>
    { symbols := (syms : ManaCost).symbols ++ (manaCost rest).symbols }
  | _ :: rest => manaCost rest

def applyOne (acc : ActivationCost × CostRestrictions) : Cost →
    ActivationCost × CostRestrictions
  | .mana syms =>
    let (cost, r) := acc
    ({ cost with mana :=
        { symbols := cost.mana.symbols ++ (syms : ManaCost).symbols } }, r)
  | .tap =>
    let (cost, r) := acc
    ({ cost with tap := true }, r)
  | .payLife n =>
    let (cost, r) := acc
    ({ cost with payLife := n }, r)
  | .sacrificeSource =>
    let (cost, r) := acc
    ({ cost with sacrificeSource := true }, r)
  | .sacrificeAnotherCreatureOrArtifact =>
    let (cost, r) := acc
    ({ cost with sacrificeAnotherCreatureOrArtifact := true }, r)
  | .sacrificeAnotherSubtype s =>
    let (cost, r) := acc
    ({ cost with sacrificeAnotherSubtype := some s }, r)
  | .sacrificeArtifact =>
    let (cost, r) := acc
    ({ cost with sacrificeArtifact := true }, r)
  | .discardACard =>
    let (cost, r) := acc
    ({ cost with discardACard := true }, r)
  | .discardSource =>
    let (cost, r) := acc
    ({ cost with discardSource := true }, r)
  | .discardLegendarySameName =>
    let (cost, r) := acc
    ({ cost with discardLegendarySameName := true }, r)
  | .onceEachTurn =>
    let (cost, r) := acc
    (cost, { r with onceEachTurn := true })
  | .onlyAsSorcery =>
    let (cost, r) := acc
    (cost, { r with onlyAsSorcery := true })
  | .onlyDuringYourTurn =>
    let (cost, r) := acc
    (cost, { r with onlyDuringYourTurn := true })
  | .activateFromGraveyard =>
    let (cost, r) := acc
    (cost, { r with activateFromGraveyard := true })
  | .activateFromHand =>
    let (cost, r) := acc
    (cost, { r with activateFromHand := true })
  | .costReductionPerEquipment n =>
    let (cost, r) := acc
    (cost, { r with costReductionPerEquipment := n })
  | .equipSubtype s =>
    let (cost, r) := acc
    (cost, { r with equipSubtype := some s })

def toActivation (costs : List Cost) : ActivationCost × CostRestrictions :=
  costs.foldl applyOne ({}, {})

/-- Equip `{mana}`: attach to target creature you control, only as a sorcery. -/
def equipAbility (syms : List ManaSymbol) (subtype : Option String := none) :
    ActivatedAbility :=
  let (cost, r) :=
    toActivation
      ([.mana syms, .onlyAsSorcery] ++
        match subtype with
        | some s => [.equipSubtype s]
        | none => [])
  { cost
    effect := Effect.attachToTargetCreatureYouControl
    onlyAsSorcery := true
    costReductionPerEquipment := r.costReductionPerEquipment
    equipSubtype := r.equipSubtype }

end Cost

/-- Whom or what a spell or ability may target (CR 115.1). -/
inductive Filter where
  | and : List Filter → Filter
  | any
  | cardType : CardType → Filter
  | or : List Filter → Filter
  /-- A permanent (CR 110.1). -/
  | permanent
  /-- Permanent the spell’s controller controls. -/
  | sameController
deriving Repr, Inhabited, BEq

namespace Filter

/-- Card types a filter allows. `any` means the filter does not mention type. -/
inductive TypeSet where
  | any
  | oneOf (ts : List CardType)
deriving Repr, Inhabited, BEq

namespace TypeSet

def intersect : TypeSet → TypeSet → TypeSet
  | .any, s | s, .any => s
  | .oneOf a, .oneOf b => .oneOf (a.filter b.contains)

def union : TypeSet → TypeSet → TypeSet
  | .any, _ | _, .any => .any
  | .oneOf a, .oneOf b =>
    .oneOf (a ++ b.filter (fun t => !a.contains t))

def contains (s : TypeSet) (t : CardType) : Bool :=
  match s with
  | .any => true
  | .oneOf ts => ts.contains t

/-- True when `s` is exactly the listed types, ignoring order. -/
def eqTypes (s : TypeSet) (ts : List CardType) : Bool :=
  match s with
  | .any => false
  | .oneOf us => us.all ts.contains && ts.all us.contains

end TypeSet

/-- Flattened constraints implied by a filter, so `.and` / `.or` lists
compile without depending on conjunct order. -/
structure Shape where
  sameController : Bool := false
  mustBePermanent : Bool := false
  types : TypeSet := .any
deriving Repr, Inhabited, BEq

namespace Shape

def meet (a b : Shape) : Shape :=
  { sameController := a.sameController || b.sameController
    mustBePermanent := a.mustBePermanent || b.mustBePermanent
    types := a.types.intersect b.types }

def join (a b : Shape) : Shape :=
  { sameController := a.sameController && b.sameController
    mustBePermanent := a.mustBePermanent && b.mustBePermanent
    types := a.types.union b.types }

end Shape

def shape : Filter → Shape
  | .any => {}
  | .permanent => { mustBePermanent := true }
  | .sameController => { sameController := true }
  | .cardType t => { types := .oneOf [t] }
  | .and fs => fs.foldl (fun acc f => acc.meet f.shape) {}
  | .or [] => {}
  | .or (f :: fs) => fs.foldl (fun acc g => acc.join g.shape) f.shape

/-- Compile a filter to a targeting shape the engine already understands. -/
def toTargetKind (f : Filter) : EffectTargetKind :=
  let s := f.shape
  if s.sameController then
    if s.types.eqTypes [.artifact, .creature] then .artifactOrCreatureYouControl
    else if s.types.eqTypes [.creature] then .creatureYouControl
    else if s.types.eqTypes [.artifact] then .artifactYouControl
    else .permanent
  else if s.types.eqTypes [.creature] then .creature
  else if s.types.eqTypes [.artifact] then .artifact
  else .permanent

end Filter

/-- How many objects matching `filter` a spell or ability may target. -/
structure TargetSelector where
  minimumTargets : Nat := 1
  maximumTargets : Nat := 1
  filter : Filter := .any
deriving Repr, Inhabited, BEq

namespace TargetSelector

def toTargeting (s : TargetSelector) : EffectTargeting :=
  .of s.filter.toTargetKind

end TargetSelector

/-- When a continuous effect ends. -/
inductive Trigger where
  | endOfGame
  | endOfTurn
deriving Repr, Inhabited, BEq

-- Printed abilities, continuous effects, and actions are mutually inductive:
-- an activated ability has an action, and a continuous effect may grant an
-- ability.
mutual
/-- A keyword or other printed ability on a card or granted by an effect. -/
inductive Ability where
  | keyword : Keyword → Ability
  | activated : List Cost → CardAction → Ability
deriving Repr, Inhabited, BEq

/-- A continuous effect granted by a spell or ability. -/
inductive ContinuousEffect where
  | gainAbility : Ability → ContinuousEffect
  | addPowerToughness : Int → Int → ContinuousEffect
deriving Repr, Inhabited, BEq

/-- What a spell or ability does. `CardAction` is the printed-card name for
this tree; player input uses `Action` in `Game`. Leftover `effect` wraps an
engine `Effect` the part language does not yet compose. -/
inductive CardAction where
  | continuous : List ContinuousEffect → Trigger → CardAction
  | targeted : TargetSelector → CardAction → CardAction
  | filtered : Filter → CardAction → CardAction
  | effect : Effect → CardAction
deriving Repr, Inhabited, BEq
end

namespace ContinuousEffect

/-- Combined +P/+T if every effect is `addPowerToughness`. -/
def addedPT? : List ContinuousEffect → Option (Int × Int)
  | [] => some (0, 0)
  | .addPowerToughness p t :: rest =>
    match addedPT? rest with
    | some (p', t') => some (p + p', t + t')
    | none => none
  | .gainAbility _ :: _ => none

end ContinuousEffect

namespace CardAction

/-- Until-end-of-turn keyword grants implied by `continuous` effects. -/
def grantedKeywords : List ContinuousEffect → Keywords
  | [] => Keywords.none
  | .gainAbility (.keyword k) :: rest =>
    k.toKeywords.merge (grantedKeywords rest)
  | _ :: rest => grantedKeywords rest

/-- Mass +P/+T on creatures you control. -/
def creaturesYouControlPumpEffect (p t : Int) (asAbility : Bool) : Effect :=
  if asAbility then Effect.abilityCreaturesYouControlGet p t
  else Effect.creaturesYouControlGet p t

/-- Keyword grants, optionally targeted. -/
def grantKeywordsEffect (sel : Option TargetSelector) (effects : List ContinuousEffect)
    (asAbility : Bool) : Effect :=
  let kws := grantedKeywords effects
  let targeting :=
    match sel with
    | some s => s.toTargeting
    | none => .of .none
  if asAbility then
    Effect.mkAbility targeting (.onPermanent (.grantKeywords kws))
  else
    Effect.mkSpell targeting (.onPermanent (.grantKeywords kws)) (castKind := .pump)

/-- Compile a `continuous` action, optionally wrapped in targeting. -/
def continuousEffect (sel : Option TargetSelector) (effects : List ContinuousEffect)
    (asAbility : Bool) : Effect :=
  match ContinuousEffect.addedPT? effects with
  | some (p, t) =>
    match sel with
    | some s =>
      let targeting := s.toTargeting
      if asAbility then
        Effect.mkAbility targeting (.onPermanent (.pump p t))
      else
        Effect.mkSpell targeting (.onPermanent (.pump p t)) (castKind := .pump)
    | none => creaturesYouControlPumpEffect p t asAbility
  | none => grantKeywordsEffect sel effects asAbility

/-- Compile a mass (`filtered`) action. Creatures you control getting +P/+T
is the shape Dwarven Provisioner prints. -/
def filteredEffect (f : Filter) (inner : CardAction) (asAbility : Bool) : Effect :=
  match inner with
  | .continuous effects _duration =>
    match ContinuousEffect.addedPT? effects, f.shape with
    | some (p, t), s =>
      if s.sameController && s.types.eqTypes [.creature] then
        creaturesYouControlPumpEffect p t asAbility
      else
        continuousEffect none effects asAbility
    | none, _ =>
      continuousEffect none effects asAbility
  | .targeted sel inner =>
    let e := continuousEffect (some sel) (match inner with
      | .continuous effects _ => effects
      | _ => []) asAbility
    { e with targeting := sel.toTargeting }
  | .filtered f' inner' => filteredEffect f' inner' asAbility
  | .effect e => e

/-- Compile to a spell-shaped `Effect`. -/
def toEffect : CardAction → Effect
  | .continuous effects _duration =>
    continuousEffect none effects false
  | .targeted sel (.continuous effects _duration) =>
    let e := continuousEffect (some sel) effects false
    { e with
      maxTargets :=
        if sel.maximumTargets ≤ 1 then e.maxTargets else sel.maximumTargets
      allowsZeroTargets := e.allowsZeroTargets || sel.minimumTargets == 0 }
  | .targeted sel inner =>
    let e := inner.toEffect
    { e with
      targeting := sel.toTargeting
      maxTargets :=
        if sel.maximumTargets ≤ 1 then e.maxTargets else sel.maximumTargets
      allowsZeroTargets := e.allowsZeroTargets || sel.minimumTargets == 0 }
  | .filtered f inner =>
    filteredEffect f inner false
  | .effect e => e

/-- Compile to an activated-ability `Effect`. -/
def toAbilityEffect : CardAction → Effect
  | .continuous effects _duration =>
    continuousEffect none effects true
  | .targeted sel (.continuous effects _duration) =>
    continuousEffect (some sel) effects true
  | .targeted sel inner =>
    let e := inner.toAbilityEffect
    { e with targeting := sel.toTargeting }
  | .filtered f inner =>
    filteredEffect f inner true
  | .effect e => e

end CardAction

namespace Ability

def ofActivated (costs : List Cost) (action : CardAction) : ActivatedAbility :=
  let (cost, r) := Cost.toActivation costs
  { cost
    effect := action.toAbilityEffect
    onlyAsSorcery := r.onlyAsSorcery
    onlyDuringYourTurn := r.onlyDuringYourTurn
    onceEachTurn := r.onceEachTurn
    activateFromGraveyard := r.activateFromGraveyard
    activateFromHand := r.activateFromHand
    costReductionPerEquipment := r.costReductionPerEquipment
    equipSubtype := r.equipSubtype }

/-- Compile an `.activated` ability; `none` for a keyword. -/
def toActivatedAbility? : Ability → Option ActivatedAbility
  | .keyword _ => none
  | .activated costs action => some (ofActivated costs action)

end Ability

/-- One printed characteristic or ability of a card face. -/
inductive CardPart where
  | name : String → CardPart
  /-- Printed symbols; `ManaCost` is the engine structure, this list is the
  prototype spelling (`.manaCost [.mono .white]`). -/
  | manaCost : List ManaSymbol → CardPart
  | type : CardType → CardPart
  | supertype : CardSupertype → CardPart
  | subtype : CardSubtype → CardPart
  | power : Nat → CardPart
  | toughness : Nat → CardPart
  | ability : Ability → CardPart
  | alternative : List CardPart → CardPart
  | action : CardAction → CardPart
  | oracleText : String → CardPart
  | triggered : TriggeredAbility → CardPart
  | static : StaticAbility → CardPart
  | activatedAbility : ActivatedAbility → CardPart
  | chooseOne : List Effect → CardPart
  | chooseOneOrBoth : List Effect → CardPart
  | equip : List ManaSymbol → CardPart
  | equipFor : String → List ManaSymbol → CardPart
  | flashback : List ManaSymbol → CardPart
  | ward : Nat → CardPart
  | crew : Nat → CardPart
  | kicker : List ManaSymbol → CardPart
  | saga : String → Array SagaChapter → CardPart
  | tapAddOneOf : List ManaType → CardPart
  | tapAddAnyColorEqualToPower
  | tapAddColorlessPerSubtype : String → CardPart
  | entersTapped
  | entersTappedUnlessEquipment
  | cantBeCountered
  | flashIfYouControlSubtype : String → CardPart
  | costReductionIfTargetTapped : Nat → CardPart
  | costReductionIfTargetAttackingNontoken : Nat → CardPart
  | costReductionIfCreatureDied : Nat → CardPart
  | costReductionEqualFlyingPower
  | additionalCostSacrificeArtifactOrCreature
  | additionalCostOrPayGeneric : Nat → CardPart
  | additionalCostSacrificeCreature
  | asEntersChooseCreatureType
  | asEntersChooseOddEven
  | tokenDoubling
  | drawTwoExceptFirstDrawStep
  | giftTreasure
  | costReductionNotFromHand : Nat → CardPart
  | affinityForSubtype : String → CardPart
  | powerPerMountain : Nat → CardPart
  | exileOppCreaturesInstead
  | firstCreatureCostsLess : Nat → CardPart
  | firstCreatureHasFlash
  | extraLandIfOtherSubtype : String → CardPart
deriving Repr, Inhabited, BEq

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
  staticAbilities : Array StaticAbility := #[]
  oracleText : String := ""
  spellModes : Array Effect := #[]
  chooseOneOrBoth : Bool := false
  flashback : Option ManaCost := none
  ward : Option Nat := none
  crew : Option Nat := none
  kicker : Option ManaCost := none
  saga : Option SagaDef := none
  tapAddOneOf : Array ManaType := #[]
  tapAddAnyColorEqualToPower : Bool := false
  tapAddColorlessPerSubtype : Option String := none
  entersTapped : Bool := false
  entersTappedUnlessEquipment : Bool := false
  cantBeCountered : Bool := false
  flashIfYouControlSubtype : Option String := none
  costReductionIfTargetTapped : Nat := 0
  costReductionIfTargetAttackingNontoken : Nat := 0
  costReductionIfCreatureDied : Nat := 0
  costReductionEqualFlyingPower : Bool := false
  additionalCostSacrificeArtifactOrCreature : Bool := false
  additionalCostOrPayGeneric : Option Nat := none
  additionalCostSacrificeCreature : Bool := false
  asEntersChooseCreatureType : Bool := false
  asEntersChooseOddEven : Bool := false
  tokenDoubling : Bool := false
  drawTwoExceptFirstDrawStep : Bool := false
  giftTreasure : Bool := false
  costReductionNotFromHand : Nat := 0
  affinityForSubtype : Option String := none
  powerPerMountain : Nat := 0
  exileOppCreaturesInstead : Bool := false
  firstCreatureCostsLess : Nat := 0
  firstCreatureHasFlash : Bool := false
  extraLandIfOtherSubtype : Option String := none
deriving Inhabited

namespace CardFace

def apply (b : CardFace) : CardPart → CardFace
  | .name n => { b with name := n }
  | .manaCost c => { b with manaCost := (c : ManaCost) }
  | .type t => { b with types := b.types.push t }
  | .supertype s => { b with supertypes := b.supertypes.push s }
  | .subtype s => { b with subtypes := b.subtypes.push s.toString }
  | .power n => { b with power := some n }
  | .toughness n => { b with toughness := some n }
  | .ability (.keyword k) => { b with keywords := b.keywords.merge k.toKeywords }
  | .ability (.activated costs action) =>
    { b with activatedAbilities := b.activatedAbilities.push (Ability.ofActivated costs action) }
  | .alternative parts => { b with alternatives := b.alternatives.push parts }
  | .action a => { b with action := some a }
  | .oracleText t => { b with oracleText := t }
  | .triggered t => { b with triggeredAbilities := b.triggeredAbilities.push t }
  | .static s => { b with staticAbilities := b.staticAbilities.push s }
  | .activatedAbility a => { b with activatedAbilities := b.activatedAbilities.push a }
  | .chooseOne es => { b with spellModes := b.spellModes ++ es.toArray }
  | .chooseOneOrBoth es =>
    { b with spellModes := b.spellModes ++ es.toArray, chooseOneOrBoth := true }
  | .equip syms =>
    { b with activatedAbilities := b.activatedAbilities.push (Cost.equipAbility syms) }
  | .equipFor subtype syms =>
    { b with
      activatedAbilities :=
        b.activatedAbilities.push (Cost.equipAbility syms (subtype := some subtype)) }
  | .flashback syms => { b with flashback := some (syms : ManaCost) }
  | .ward n => { b with ward := some n }
  | .crew n => { b with crew := some n }
  | .kicker syms => { b with kicker := some (syms : ManaCost) }
  | .saga after chapters => { b with saga := some { sacrificeAfter := after, chapters } }
  | .tapAddOneOf ts => { b with tapAddOneOf := b.tapAddOneOf ++ ts.toArray }
  | .tapAddAnyColorEqualToPower => { b with tapAddAnyColorEqualToPower := true }
  | .tapAddColorlessPerSubtype s => { b with tapAddColorlessPerSubtype := some s }
  | .entersTapped => { b with entersTapped := true }
  | .entersTappedUnlessEquipment => { b with entersTappedUnlessEquipment := true }
  | .cantBeCountered => { b with cantBeCountered := true }
  | .flashIfYouControlSubtype s => { b with flashIfYouControlSubtype := some s }
  | .costReductionIfTargetTapped n => { b with costReductionIfTargetTapped := n }
  | .costReductionIfTargetAttackingNontoken n =>
    { b with costReductionIfTargetAttackingNontoken := n }
  | .costReductionIfCreatureDied n => { b with costReductionIfCreatureDied := n }
  | .costReductionEqualFlyingPower => { b with costReductionEqualFlyingPower := true }
  | .additionalCostSacrificeArtifactOrCreature =>
    { b with additionalCostSacrificeArtifactOrCreature := true }
  | .additionalCostOrPayGeneric n => { b with additionalCostOrPayGeneric := some n }
  | .additionalCostSacrificeCreature => { b with additionalCostSacrificeCreature := true }
  | .asEntersChooseCreatureType => { b with asEntersChooseCreatureType := true }
  | .asEntersChooseOddEven => { b with asEntersChooseOddEven := true }
  | .tokenDoubling => { b with tokenDoubling := true }
  | .drawTwoExceptFirstDrawStep => { b with drawTwoExceptFirstDrawStep := true }
  | .giftTreasure => { b with giftTreasure := true }
  | .costReductionNotFromHand n => { b with costReductionNotFromHand := n }
  | .affinityForSubtype s => { b with affinityForSubtype := some s }
  | .powerPerMountain n => { b with powerPerMountain := n }
  | .exileOppCreaturesInstead => { b with exileOppCreaturesInstead := true }
  | .firstCreatureCostsLess n => { b with firstCreatureCostsLess := n }
  | .firstCreatureHasFlash => { b with firstCreatureHasFlash := true }
  | .extraLandIfOtherSubtype s => { b with extraLandIfOtherSubtype := some s }

def ofParts (parts : List CardPart) : CardFace :=
  parts.foldl apply {}

def toAdventure (b : CardFace) : AdventureFace := {
  name := b.name
  manaCost := b.manaCost
  types := if b.types.isEmpty then #[.sorcery] else b.types
  subtypes := if b.subtypes.isEmpty then #["Adventure"] else b.subtypes
  oracleText :=
    if !b.oracleText.isEmpty then b.oracleText
    else
      match b.action with
      | some a => a.toEffect.phrase
      | none => ""
  spellEffect :=
    match b.action with
    | some a => some a.toEffect
    | none => none
  additionalCostSacrificeCreature := b.additionalCostSacrificeCreature
}

end CardFace

namespace TraditionalCardDefinition

/-- Compile printed parts to the engine `CardDef`. When `oracleText` is
omitted (and no `.oracleText` part is present), keywords and the Adventure
face are reconstructed so the card still has ability text. -/
def toCardDef (d : TraditionalCardDefinition) (oracleText : String := "") : CardDef :=
  match d with
  | .card parts =>
    let b := CardFace.ofParts parts
    let adventure :=
      match b.alternatives[0]? with
      | some alt => some (CardFace.ofParts alt).toAdventure
      | none => none
    let official := if oracleText.isEmpty then b.oracleText else oracleText
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
      spellEffect :=
        if b.spellModes.isEmpty then b.action.map (·.toEffect) else none
      activatedAbilities := b.activatedAbilities
      adventure := adventure
      oracleText := if official.isEmpty then generated else official
      triggeredAbilities := b.triggeredAbilities
      staticAbilities := b.staticAbilities
      spellModes := b.spellModes
      chooseOneOrBoth := b.chooseOneOrBoth
      flashback := b.flashback
      ward := b.ward
      crew := b.crew
      kicker := b.kicker
      saga := b.saga
      tapAddOneOf := b.tapAddOneOf
      tapAddAnyColorEqualToPower := b.tapAddAnyColorEqualToPower
      tapAddColorlessPerSubtype := b.tapAddColorlessPerSubtype
      entersTapped := b.entersTapped
      entersTappedUnlessEquipment := b.entersTappedUnlessEquipment
      cantBeCountered := b.cantBeCountered
      flashIfYouControlSubtype := b.flashIfYouControlSubtype
      costReductionIfTargetTapped := b.costReductionIfTargetTapped
      costReductionIfTargetAttackingNontoken := b.costReductionIfTargetAttackingNontoken
      costReductionIfCreatureDied := b.costReductionIfCreatureDied
      costReductionEqualFlyingPower := b.costReductionEqualFlyingPower
      additionalCostSacrificeArtifactOrCreature :=
        b.additionalCostSacrificeArtifactOrCreature
      additionalCostOrPayGeneric := b.additionalCostOrPayGeneric
      additionalCostSacrificeCreature := b.additionalCostSacrificeCreature
      asEntersChooseCreatureType := b.asEntersChooseCreatureType
      asEntersChooseOddEven := b.asEntersChooseOddEven
      tokenDoubling := b.tokenDoubling
      drawTwoExceptFirstDrawStep := b.drawTwoExceptFirstDrawStep
      giftTreasure := b.giftTreasure
      costReductionNotFromHand := b.costReductionNotFromHand
      affinityForSubtype := b.affinityForSubtype
      powerPerMountain := b.powerPerMountain
      exileOppCreaturesInstead := b.exileOppCreaturesInstead
      firstCreatureCostsLess := b.firstCreatureCostsLess
      firstCreatureHasFlash := b.firstCreatureHasFlash
      extraLandIfOtherSubtype := b.extraLandIfOtherSubtype
    }

instance : Coe TraditionalCardDefinition CardDef where
  coe d := d.toCardDef

/-- Compile parts to a `CardDef`. Catalogs use this so a definition can stay
typed as `CardDef` without a `*Card` twin. -/
def traditional (parts : List CardPart) : CardDef :=
  toCardDef (.card parts)

end TraditionalCardDefinition

export TraditionalCardDefinition (traditional)

-- Concerted Care: target artifact or creature you control gains hexproof
-- and indestructible until end of turn.
#guard
  let action : CardAction :=
    .targeted
      ({filter := .and [
          .permanent,
          .or [.cardType .artifact, .cardType .creature],
          .sameController
        ]})
      (.continuous
        [
          .gainAbility (.keyword .hexproof),
          .gainAbility (.keyword .indestructible)]
        .endOfTurn)
  action.toEffect == Effect.grantHexproofIndestructible

#guard Filter.toTargetKind
  (.and [
    .permanent,
    .or [.cardType .artifact, .cardType .creature],
    .sameController])
  == .artifactOrCreatureYouControl

#guard Filter.toTargetKind
  (.and [
    .sameController,
    .or [.cardType .creature, .cardType .artifact],
    .permanent])
  == .artifactOrCreatureYouControl

-- Dwarven Provisioner: {3}{W}: creatures you control get +1/+1 until end of turn.
#guard
  let action : CardAction :=
    .filtered
      (.and [.permanent, .cardType .creature, .sameController])
      (.continuous [.addPowerToughness 1 1] .endOfTurn)
  action.toAbilityEffect == Effect.abilityCreaturesYouControlGet 1 1

#guard
  match
    (Ability.activated
      [.mana [.generic 3, .mono .white]]
      (.filtered
        (.and [.permanent, .cardType .creature, .sameController])
        (.continuous [.addPowerToughness 1 1] .endOfTurn))).toActivatedAbility? with
  | some ab =>
    ab.cost.mana == ManaCost.ofGenericAndColor 3 .white &&
      ab.effect == Effect.abilityCreaturesYouControlGet 1 1
  | none => false

#guard
  match
    (Ability.activated
      [.payLife 2, .onceEachTurn]
      (.effect (Effect.sourceGets 2 2))).toActivatedAbility? with
  | some ab =>
    ab.cost.payLife == 2 && ab.onceEachTurn &&
      ab.effect == Effect.sourceGets 2 2
  | none => false

#guard
  (traditional [
    .name "Silent Bolt",
    .manaCost [.mono .red],
    .type .instant,
    .action (.effect (Effect.dealDamageToCreature 5)),
    .oracleText "Silent Bolt deals 5 damage to target creature."
  ]).spellEffect == some (Effect.dealDamageToCreature 5)

end Mtg.Engine
