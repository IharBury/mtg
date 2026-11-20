import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility

/-!
# Keyword Expansion (CR 702.1)

Pure projection `KeywordAbility.expand : KeywordAbility → ExpandedKeyword`
translating every CR 702 keyword ability into its exact Comprehensive Rules
(25 September 2026) sub-abilities:

- Intrinsic `ActivatedAbility`s: Equip (CR 702.6a), Cycling / Typecycling
  (CR 702.29a,e), Crew (CR 702.122a).
- Special actions (`SpecialActionSpec`, CR 116.2b): Morph's turn-face-up
  special action (CR 702.37e — kept distinct from `ActivatedAbility` so
  Split second CR 702.61b does not forbid it).
- Intrinsic `TriggeredAbility` specifications (`KeywordTriggerSpec`): Prowess
  (CR 702.108a), Exalted (CR 702.83a), Decayed's attack trigger scheduling an
  end-of-combat delayed sacrifice (CR 702.147a / 603.7 / 511.2), Ward
  (CR 702.21a), Cascade (CR 702.85a), Myriad (CR 702.116a), Undying
  (CR 702.93a), Extort (CR 702.101a), Impending's intervening-if end-step
  trigger (CR 702.176a / 603.4), and Gift's intervening-if permanent ETB
  trigger (CR 702.174b / 603.4).
- Intrinsic static/replacement rules (`KeywordStaticSpec`): Changeling CDA
  (CR 702.73a), Decayed `"can't block"` (CR 702.147a), evergreen combat/evasion/
  targeting/damage/timing keywords, Affinity (CR 702.41a), Convoke (CR 702.51a),
  Improvise (CR 702.126a), Ascend (CR 702.131b), Storied, Flashback's
  leave-the-stack exile replacement (CR 702.34a), Impending's ETB counters and
  Layer-4 noncreature static (CR 702.176a), Sneak's ETB tapped-and-attacking
  same-defender modification (CR 702.190b / 506.2 / 506.3a), and Daybound /
  Nightbound (CR 702.145).
- Alternative and additional casting costs (`AlternativeCostSpec` /
  `AdditionalCostSpec`): Morph's `{3}` face-down alternative cast (CR 702.37a/c),
  Flashback (CR 702.34a), Impending (CR 702.176a), Sneak (CR 702.190a), Kicker
  (CR 702.33a), Teamwork (CR 702.194a), and Gift (CR 702.174a).
- Prepended instant/sorcery spell instructions (`KeywordSpellInstruction`):
  Gift (CR 702.174b/j), Ascend (CR 702.131a), and Storied.
-/

namespace Mtg.Engine

/-- A keyword-generated special action (CR 116.2b). Kept distinct from
`ActivatedAbility` so Split second (CR 702.61b) never forbids it. -/
inductive SpecialActionSpec where
  /-- Morph turn-face-up special action (CR 702.37e / 116.2b): reveal the
  printed morph cost, pay `cost`, and turn the face-down permanent face up. -/
  | turnFaceUp (cost : CostSpec)
deriving Repr, Inhabited, BEq

instance : HasTextChange SpecialActionSpec where
  applyTextChanges tcs
    | .turnFaceUp cost => .turnFaceUp (HasTextChange.applyTextChanges tcs cost)

/-- Semantic classification of an intrinsic static or replacement sub-ability
implied by a CR 702 keyword ability. -/
inductive KeywordStaticSpec where
  /-- CR 702.73a: Layer-4 characteristic-defining ability granting every
  creature type in all zones. -/
  | changelingCda
  /-- CR 702.147a: `"This creature can't block"` static restriction on Decayed. -/
  | cantBlock
  /-- Evergreen combat, evasion, targeting, damage, or cast-timing static
  (Flying, First strike, Double strike, Deathtouch, Defender, Flash, Haste,
  Hexproof, Indestructible, Lifelink, Menace, Protection, Reach, Shadow,
  Split second, Toxic, Trample, Vigilance, Landwalk). -/
  | combatOrEvasion (kw : KeywordAbility)
  /-- CR 702.41a: Affinity cost reduction per matching object you control. -/
  | affinityReduction (forWhat : ObjectFilter)
  /-- CR 702.51a: Convoke mana-payment assist. -/
  | convokeAssist
  /-- CR 702.126a: Improvise mana-payment assist. -/
  | improviseAssist
  /-- CR 702.131b: Permanent Ascend check for the city's blessing. -/
  | ascendPermanent
  /-- HOB permanent Storied check for enduring story. -/
  | storiedPermanent
  /-- CR 702.34a: `"If the flashback cost was paid, exile this card instead of
  putting it anywhere else any time it would leave the stack."` -/
  | flashbackExileOnLeaveStack
  /-- CR 702.176a (ability 2): `"If you cast this spell for its impending cost,
  it enters with N time counters on it."` -/
  | impendingEntersWithTimeCounters (n : Nat)
  /-- CR 702.176a (ability 3): Layer-4 static — `"isn't a creature as long as
  its impending cost was paid and it has a time counter on it."` -/
  | impendingNotACreatureWhileTimeCounters
  /-- CR 702.190b / 506.2 / 506.3a: If the sneak cost was paid, the permanent
  enters tapped and attacking the same player, planeswalker, or battle the
  returned creature was attacking (CR 506.3a applies if noncreature). -/
  | sneakEntersTappedAndAttackingSameDefender
  /-- CR 702.145: Daybound / Nightbound day-night transformation static. -/
  | dayboundNightbound (isNight : Bool)
deriving Repr, Inhabited, BEq

/-- Semantic descriptor of an intrinsic keyword triggered ability (CR 702 / 603). -/
inductive KeywordTriggerKind where
  /-- CR 702.108a: Whenever you cast a noncreature spell, this gets +1/+1 until EOT. -/
  | prowess
  /-- CR 702.83a: Whenever a creature you control attacks alone, that creature gets +1/+1 until EOT. -/
  | exalted
  /-- CR 702.147a / 603.7 / 511.2: When this creature attacks, schedule a CR 603.7
  delayed trigger that sacrifices it at end of combat. -/
  | decayedAttackDelayedSacrifice
  /-- CR 702.21a: Whenever this permanent becomes the target of a spell or ability
  an opponent controls, counter it unless that player pays `cost`. -/
  | ward (cost : CostSpec)
  /-- CR 702.85a: When you cast this spell, exile cards from top of library until
  nonland with lesser MV; may cast without paying mana cost. -/
  | cascade
  /-- CR 702.116a: Whenever this creature attacks, for each opponent other than
  defending player, create a tapped and attacking token copy; exile at end of combat. -/
  | myriad
  /-- CR 702.93a: When this permanent dies, if it had no +1/+1 counters on it,
  return it under its owner's control with a +1/+1 counter on it. -/
  | undying
  /-- CR 702.101a: Whenever you cast a spell, you may pay {W/B}. If you do, each
  opponent loses 1 life and you gain that much life. -/
  | extort
  /-- CR 702.176a / 603.4: At the beginning of your end step, if this permanent's
  impending cost was paid and it has a time counter on it, remove a time counter. -/
  | impendingEndStepRemoveTimeCounter
  /-- CR 702.174b / 603.4: When this permanent enters, if its gift cost was paid,
  the chosen opponent gets the promised gift. -/
  | giftPermanentEnters (kind : GiftKind)
deriving Repr, Inhabited, BEq

/-- One intrinsic triggered ability expanded from a keyword, carrying its CR 603.4
intervening-if condition and optional directly-executable `TriggeredAbility`. -/
structure KeywordTriggerSpec where
  kind : KeywordTriggerKind
  interveningIf? : Option Condition := none
  modeled? : Option TriggeredAbility := none
deriving Repr, Inhabited, BEq

/-- Prepended spell-ability instruction generated by a keyword on an instant or
sorcery (CR 702.174b,j / 702.131a). Resolves before the card's printed spell effect. -/
inductive KeywordSpellInstruction where
  /-- CR 702.174b / 702.174j: `"If this spell's gift cost was paid, [effect]"`
  prepended ahead of the spell's other instructions. -/
  | giftGrant (kind : GiftKind)
  /-- CR 702.131a: If you control ten or more permanents, you get the city's blessing. -/
  | ascendSpell
  /-- HOB instant/sorcery Storied designation check. -/
  | storiedSpell
deriving DecidableEq, Repr, Inhabited, BEq

/-- Result of expanding one or more `KeywordAbility` values into their exact
CR 702 sub-abilities. -/
structure ExpandedKeyword where
  activatedAbilities : Array ActivatedAbility := #[]
  triggeredSpecs : Array KeywordTriggerSpec := #[]
  staticSpecs : Array KeywordStaticSpec := #[]
  specialActions : Array SpecialActionSpec := #[]
  additionalCosts : Array AdditionalCostSpec := #[]
  alternativeCosts : Array AlternativeCostSpec := #[]
  spellInstructions : Array KeywordSpellInstruction := #[]
deriving Repr, Inhabited, BEq

namespace ExpandedKeyword

def empty : ExpandedKeyword := {}

def merge (a b : ExpandedKeyword) : ExpandedKeyword :=
  { activatedAbilities := a.activatedAbilities ++ b.activatedAbilities
    triggeredSpecs := a.triggeredSpecs ++ b.triggeredSpecs
    staticSpecs := a.staticSpecs ++ b.staticSpecs
    specialActions := a.specialActions ++ b.specialActions
    additionalCosts := a.additionalCosts ++ b.additionalCosts
    alternativeCosts := a.alternativeCosts ++ b.alternativeCosts
    spellInstructions := a.spellInstructions ++ b.spellInstructions }

def mergeAll (xs : Array ExpandedKeyword) : ExpandedKeyword :=
  xs.foldl merge empty

/-- Directly modeled `TriggeredAbility`s synthesized by this expansion (e.g. Ward, Cascade). -/
def modeledTriggeredAbilities (e : ExpandedKeyword) : Array TriggeredAbility :=
  e.triggeredSpecs.filterMap (·.modeled?)

/-- True when this expansion introduces a `"can't block"` restriction (Decayed CR 702.147a). -/
def hasCantBlock (e : ExpandedKeyword) : Bool :=
  e.staticSpecs.any fun | .cantBlock => true | _ => false

/-- True when this expansion introduces the Changeling Layer-4 CDA (CR 702.73a). -/
def hasChangelingCda (e : ExpandedKeyword) : Bool :=
  e.staticSpecs.any fun | .changelingCda => true | _ => false

end ExpandedKeyword

namespace KeywordAbility

/-- Construct the CR 702.6a sorcery-speed Equip activated ability. -/
def equipActivatedAbility (filter : ObjectPred) (cost : CostSpec) : ActivatedAbility :=
  let extraPred? : Option ObjectPred :=
    if filter == .anyObject then none else some filter
  let targetDomain : TargetDomain :=
    .object .battlefield (.all #[.hasType .creature, .controlledBy .you, filter])
  { cost
    effect := { targeting := .of (.ofDomain targetDomain)
                resolution := .attach .source .target
                phrase := "Attach to target creature you control" }
    timing := .sorcery
    tag? := some (.equip extraPred?) }

/-- Construct the CR 702.29a / 702.29e hand-zone Cycling / Typecycling activated ability. -/
def cyclingActivatedAbility (typeFilter? : Option ObjectPred) (cost : CostSpec) : ActivatedAbility :=
  let fullCost := cost.append (CostSpec.ofItem (.discard (.exact 1) .self))
  let (eff, subLabel?) : Effect × Option String :=
    match typeFilter? with
    | none => ({ resolution := .draw 1, phrase := "Draw a card" }, none)
    | some (.hasSubtype (.literal sub)) =>
      ({ resolution := .searchLandTypeToHand sub.englishName
         phrase := s!"Search your library for a {sub} card, reveal it, put it into your hand, then shuffle" },
       some sub.englishName)
    | some (.all #[.hasSupertype .basic, .hasType .land]) =>
      ({ resolution := .searchLandTypeToHand "Basic land"
         phrase := "Search your library for a basic land card, reveal it, put it into your hand, then shuffle" },
       some "Basic land")
    | some _ =>
      ({ resolution := .draw 1, phrase := "Draw a card" }, none)
  { cost := fullCost
    effect := eff
    activeZones := #[.hand]
    tag? := some (.cycling subLabel?) }

/-- Pure CR 702.1 expansion of one `KeywordAbility` into its exact intrinsic
activated abilities, triggered abilities, static/replacement rules, special
actions, additional/alternative casting costs, and prepended spell instructions. -/
def expand : KeywordAbility → ExpandedKeyword
  -- Simple combat / evasion / damage / cast-timing keywords
  | .simple .flying => { staticSpecs := #[.combatOrEvasion (.simple .flying)] }
  | .simple .firstStrike => { staticSpecs := #[.combatOrEvasion (.simple .firstStrike)] }
  | .simple .doubleStrike => { staticSpecs := #[.combatOrEvasion (.simple .doubleStrike)] }
  | .simple .deathtouch => { staticSpecs := #[.combatOrEvasion (.simple .deathtouch)] }
  | .simple .defender => { staticSpecs := #[.combatOrEvasion (.simple .defender)] }
  | .simple .flash => { staticSpecs := #[.combatOrEvasion (.simple .flash)] }
  | .simple .haste => { staticSpecs := #[.combatOrEvasion (.simple .haste)] }
  | .simple .indestructible => { staticSpecs := #[.combatOrEvasion (.simple .indestructible)] }
  | .simple .lifelink => { staticSpecs := #[.combatOrEvasion (.simple .lifelink)] }
  | .simple .menace => { staticSpecs := #[.combatOrEvasion (.simple .menace)] }
  | .simple .reach => { staticSpecs := #[.combatOrEvasion (.simple .reach)] }
  | .simple .trample => { staticSpecs := #[.combatOrEvasion (.simple .trample)] }
  | .simple .vigilance => { staticSpecs := #[.combatOrEvasion (.simple .vigilance)] }
  | .simple .shadow => { staticSpecs := #[.combatOrEvasion (.simple .shadow)] }
  | .simple .splitSecond => { staticSpecs := #[.combatOrEvasion (.simple .splitSecond)] }
  -- CR 702.147a: Decayed = static "can't block" + attack trigger scheduling EOT delayed sacrifice (CR 603.7 / 511.2)
  | .simple .decayed =>
    { staticSpecs := #[.cantBlock]
      triggeredSpecs := #[{ kind := .decayedAttackDelayedSacrifice }] }
  -- CR 702.83a: Exalted
  | .simple .exalted =>
    { triggeredSpecs := #[{ kind := .exalted }] }
  -- CR 702.73a: Changeling Layer-4 CDA
  | .simple .changeling =>
    { staticSpecs := #[.changelingCda] }
  -- CR 702.51a: Convoke
  | .simple .convoke =>
    { staticSpecs := #[.convokeAssist] }
  -- CR 702.126a: Improvise
  | .simple .improvise =>
    { staticSpecs := #[.improviseAssist] }
  -- CR 702.131a–b: Ascend (permanent static + instant/sorcery spell instruction)
  | .simple .ascend =>
    { staticSpecs := #[.ascendPermanent]
      spellInstructions := #[.ascendSpell] }
  -- HOB Storied (permanent static + instant/sorcery spell instruction)
  | .simple .storied =>
    { staticSpecs := #[.storiedPermanent]
      spellInstructions := #[.storiedSpell] }
  -- CR 702.145: Daybound / Nightbound
  | .simple .daybound => { staticSpecs := #[.dayboundNightbound false] }
  | .simple .nightbound => { staticSpecs := #[.dayboundNightbound true] }
  -- CR 702.108a: Prowess
  | .simple .prowess => { triggeredSpecs := #[{ kind := .prowess }] }
  -- CR 702.85a: Cascade
  | .simple .cascade =>
    { triggeredSpecs := #[{ kind := .cascade, modeled? := some TriggeredAbility.onCastCascade }] }
  -- CR 702.116a: Myriad
  | .simple .myriad => { triggeredSpecs := #[{ kind := .myriad }] }
  -- CR 702.93a: Undying (CR 603.4 intervening-if: no +1/+1 counters)
  | .simple .undying =>
    { triggeredSpecs := #[{
        kind := .undying
        interveningIf? := some (.cmp .eq (.counterCount (some .plusOnePlusOne) .this) (.const 0)) }] }
  -- CR 702.101a: Extort
  | .simple .extort => { triggeredSpecs := #[{ kind := .extort }] }
  -- Parameterized keywords (16 constructors)
  -- CR 702.11 / 702.11d: Hexproof / Hexproof from [quality]
  | .hexproof q? => { staticSpecs := #[.combatOrEvasion (.hexproof q?)] }
  -- CR 702.21a: Ward [cost]
  | .ward cost =>
    { triggeredSpecs := #[{ kind := .ward cost, modeled? := some (TriggeredAbility.onWard cost) }] }
  -- CR 702.16: Protection from [quality]
  | .protection q => { staticSpecs := #[.combatOrEvasion (.protection q)] }
  -- CR 702.14: [Land-predicate]walk
  | .landwalk pred => { staticSpecs := #[.combatOrEvasion (.landwalk pred)] }
  -- CR 702.164c: Toxic N
  | .toxic n => { staticSpecs := #[.combatOrEvasion (.toxic n)] }
  -- CR 702.41a: Affinity for [filter]
  | .affinity forWhat => { staticSpecs := #[.affinityReduction forWhat] }
  -- CR 702.6a: Equip [filter] [cost] (sorcery-speed activated ability)
  | .equip filter cost =>
    { activatedAbilities := #[equipActivatedAbility filter cost] }
  -- CR 702.29a / 702.29e: Cycling / Typecycling [cost] (hand-zone activated ability)
  | .cycling typeFilter? cost =>
    { activatedAbilities := #[cyclingActivatedAbility typeFilter? cost] }
  -- CR 702.33a: Kicker [cost] (optional additional cost)
  | .kicker cost =>
    { additionalCosts := #[AdditionalCostSpec.opt cost (some .kicker)] }
  -- CR 702.174a–b,j / 603.4: Gift [kind]
  -- Optional additional promise cost (CR 702.174a), intervening-if permanent ETB
  -- trigger (CR 702.174b / 603.4), and prepended instant/sorcery instruction (CR 702.174j).
  | .gift kind =>
    { additionalCosts := #[AdditionalCostSpec.opt {} (some .gift)]
      triggeredSpecs := #[{
        kind := .giftPermanentEnters kind
        interveningIf? := some (.castPred (.giftPromised .this)) }]
      spellInstructions := #[.giftGrant kind] }
  -- CR 702.34a: Flashback [cost] (graveyard alternative cost + leave-stack exile replacement)
  | .flashback cost =>
    { alternativeCosts := #[{
        cost
        fromZones := #[.graveyard]
        keywordTag? := some .flashback }]
      staticSpecs := #[.flashbackExileOnLeaveStack] }
  -- CR 702.37a/c/e / 116.2b: Morph [cost]
  -- Face-down cast alternative cost is ALWAYS `{3}` (CR 702.37a/c); the printed
  -- `cost` belongs to the CR 116.2b / 702.37e turn-face-up special action.
  | .morph cost =>
    { alternativeCosts := #[{
        cost := CostSpec.ofGeneric 3
        fromZones := #[.hand]
        keywordTag? := some .morph
        faceDown := true }]
      specialActions := #[.turnFaceUp cost] }
  -- CR 702.176a / 603.4: Impending N—[cost]
  -- (1) Alternative cost, (2) ETB N time counters, (3) Layer-4 noncreature static,
  -- (4) Intervening-if end-step trigger removing a time counter.
  | .impending counters cost =>
    { alternativeCosts := #[{
        cost
        fromZones := #[.hand]
        keywordTag? := some .impending }]
      staticSpecs := #[
        .impendingEntersWithTimeCounters counters,
        .impendingNotACreatureWhileTimeCounters]
      triggeredSpecs := #[{
        kind := .impendingEndStepRemoveTimeCounter
        interveningIf? := some (.all #[
          .castPred (.impendingPaid .this),
          .cmp .ge (.counterCount (some .time) .this) (.const 1)]) }] }
  -- CR 702.190a–b / 506.2 / 506.3a: Sneak [cost]
  -- Declare-blockers instant-timing alternative cost paying `cost` and returning
  -- an unblocked attacking creature you control to its owner's hand + ETB modification.
  | .sneak cost =>
    { alternativeCosts := #[{
        cost := CostSpec.sneakFullCost cost
        fromZones := #[.hand]
        condition? := some (.duringStep .declareBlockers)
        keywordTag? := some .sneak }]
      staticSpecs := #[.sneakEntersTappedAndAttackingSameDefender] }
  -- CR 702.122a: Crew N (activated ability)
  | .crew power =>
    { activatedAbilities := #[ActivatedAbility.crewAbility power] }
  -- CR 702.194a: Teamwork N (optional additional cost)
  | .teamwork count =>
    { additionalCosts := #[AdditionalCostSpec.opt (CostSpec.teamworkCost count) (some .teamwork)] }

/-- Pure CR 702.1 expansion of an entire keyword array, preserving multiplicity. -/
def expandAll (ks : Array KeywordAbility) : ExpandedKeyword :=
  ExpandedKeyword.mergeAll (ks.map expand)

end KeywordAbility

-- Compile-time CR 702.1 expansion guards.
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).alternativeCosts[0]!.cost ==
  CostSpec.ofGeneric 3
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).alternativeCosts[0]!.faceDown == true
#guard (KeywordAbility.expand (.morph (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] }))).specialActions ==
  #[.turnFaceUp (CostSpec.ofMana { symbols := #[.generic 2, .colored .blue] })]
#guard (KeywordAbility.expand (.morph (CostSpec.ofGeneric 2))).activatedAbilities.isEmpty
#guard (KeywordAbility.expand Keyword.decayed).hasCantBlock == true
#guard (KeywordAbility.expand Keyword.decayed).triggeredSpecs.size == 1
#guard (KeywordAbility.expand (.impending 4 (CostSpec.ofGeneric 2))).triggeredSpecs[0]!.interveningIf?.isSome
#guard (KeywordAbility.expand (.gift .treasure)).triggeredSpecs[0]!.interveningIf? ==
  some (.castPred (.giftPromised .this))
#guard (KeywordAbility.expand (.gift .treasure)).spellInstructions == #[.giftGrant .treasure]
#guard (KeywordAbility.expand (.crew 3)).activatedAbilities.size == 1
#guard (KeywordAbility.expand (.flashback (CostSpec.ofGeneric 2))).staticSpecs ==
  #[.flashbackExileOnLeaveStack]
#guard (KeywordAbility.expand (.sneak (CostSpec.ofGeneric 1))).alternativeCosts[0]!.condition? ==
  some (.duringStep .declareBlockers)
#guard (KeywordAbility.expandAll #[.ward (CostSpec.ofGeneric 2), .ward CostSpec.discardCard]).triggeredSpecs.size == 2

end Mtg.Engine
