import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.Cost
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.ManaSpec
import Mtg.Engine.Card.Targeting
import Mtg.Engine.Card.TriggerPattern

/-!
# Unified CR 113.3 Ability & One-Shot `Instruction` AST (Phase 8 / Phase 9)

Unifies all MTG ability categories (CR 113.3a–d), tokens (CR 111 / 707.9),
emblems (CR 114), continuous modifications (CR 611 / 613), replacements
(CR 614–615), and one-shot `Instruction`s (CR 608) into a single stratified
`mutual` block anchored to the 6 November 2026 Comprehensive Rules:

- Every `inductive` in this module stays at `≤ 24` constructors (`< 10%` of the
  Lean 4 C runtime `LeanMaxCtorTag = 243` ceiling).
- Zero card-named or set-named constructors.
- Single-tuple derived `BEq` / `Repr` across the 16-type mutual block.
- Single mutual functorial Layer-3 `HasTextChange` (CR 612 / 613.1c) including
  token and copy `GrantedAbility`s.
- Family-stratified `Instruction` has **18 top-level constructors**: 10 action
  wrappers aligned with `RulesEvent` families (`moveZone`, `create`, `permanent`,
  `damage`, `life`, `player`, `turn`, `stack`, `installEffect`,
  `queueReflexiveTrigger`) and 8 combinators (`noop`, `seq`, `bind`, `ifCond`,
  `optional`, `unlessPays`, `chooseModes`, `forEach`), with every sub-family
  enum at `≤ 17` constructors.
-/

namespace Mtg.Engine

/-! ### 1. Activation Metadata (CR 602 / 606 / 702) -/

/-- Activation timing class of an activated ability (CR 117.1b / 307.5 / 606.3). -/
inductive ActivationTiming where
  /-- Any time the player has priority (default). -/
  | instant
  /-- "Activate only as a sorcery" (CR 307.5). -/
  | sorcery
  /-- Loyalty ability timing (CR 606.3): main phase, empty stack, once per
  permanent per turn (subject to static exceptions such as instant-speed loyalty). -/
  | loyalty
deriving DecidableEq, Repr, Inhabited, BEq

/-- Keyword / mechanic tag carried by an `ActivatedAbility` so keyword-sensitive
rules (Equip CR 702.6, Cycling CR 702.29, Boast CR 702.142a, Power-up
CR 702.193a–b, Exhaust CR 702.177a, Crew CR 702.122a) identify it directly. -/
inductive ActivationMechanicTag where
  /-- Equip (CR 702.6), with an optional extra creature filter. -/
  | equip (filter? : Option ObjectPred := none)
  /-- Cycling / typecycling (CR 702.29). -/
  | cycling (subtype? : Option String := none)
  /-- Boast (CR 702.142a). -/
  | boast
  /-- Power-up (CR 702.193a–b). -/
  | powerUp
  /-- Exhaust (CR 702.177a). -/
  | exhaust
  /-- Crew N (CR 702.122a). -/
  | crew (minPower : Nat)
  /-- Station (CR 702.184a). -/
  | station
deriving Repr, Inhabited, BEq

instance : HasTextChange ActivationMechanicTag where
  applyTextChanges tcs tag :=
    if tcs.isEmpty then tag
    else
      match tag with
      | .equip (some pred) => .equip (some (HasTextChange.applyTextChanges tcs pred))
      | other => other

/-- Declarative generic-mana cost reduction on an activated ability
(CR 602.2b / 601.2f). -/
structure ActivationCostReduction where
  amount : ValueExpr
  condition? : Option Condition := none
deriving Repr, Inhabited, BEq

instance : HasTextChange ActivationCostReduction where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      { amount := HasTextChange.applyTextChanges tcs r.amount
        condition? := r.condition?.map (HasTextChange.applyTextChanges tcs) }

/-! ### 2. Static Ability Supporting Types (CR 601.2f / 604 / 613 / 614–616) -/

/-- Characteristic-defining ability specification (CR 604.3, functions in all zones;
4 constructors). -/
inductive CdaSpec where
  /-- Layer 7a (CR 613.4a): sets power and/or toughness (`*/*`, `*/1`, `*/1+*`). -/
  | setPT (power? toughness? : Option ValueExpr)
  /-- Layer 4 (CR 613.1d): defines types/subtypes in all zones. -/
  | setTypes (mod : TypeSetMod)
  /-- Layer 4 (CR 702.73a): this card is every creature type in all zones. -/
  | allCreatureTypes
  /-- Layer 5 (CR 613.1e): defines colors in all zones. -/
  | setColors (colors : ColorSet)
deriving Repr, Inhabited, BEq

instance : HasTextChange CdaSpec where
  applyTextChanges tcs cda :=
    if tcs.isEmpty then cda
    else
      match cda with
      | .setPT p? t? =>
        .setPT (HasTextChange.applyTextChanges tcs p?) (HasTextChange.applyTextChanges tcs t?)
      | .setTypes m => .setTypes (HasTextChange.applyTextChanges tcs m)
      | .allCreatureTypes => .allCreatureTypes
      | .setColors cs => .setColors (HasTextChange.applyTextChanges tcs cs)

/-- Subject of a combat, untap, or replacement static rule (2 constructors). -/
inductive StaticSubject where
  | self
  | matching (filter : ObjectFilter)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticSubject where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      match s with
      | .self => .self
      | .matching f => .matching (HasTextChange.applyTextChanges tcs f)

/-- Rule-modifying static abilities affecting players (CR 104 / 119.7–8 / 305.2 /
402.3 / 601.2 / 602.5 / 702.11c / 702.16j / 702.131b / 724; 17 constructors). -/
inductive StaticPlayerRule where
  /-- Maximum hand size: `none` = no maximum hand size; `some n` = `n` (CR 402.3). -/
  | maxHandSize (who : PlayerFilter := .you) (limit? : Option Nat)
  /-- Matching players may play `count` additional land(s) on each of their turns (CR 305.2). -/
  | additionalLands (who : PlayerFilter := .you) (count : Nat := 1)
  /-- Matching players can't gain life (CR 119.7). -/
  | cantGainLife (who : PlayerFilter)
  /-- Matching players can't lose the game (CR 104.3). -/
  | cantLoseGame (who : PlayerFilter)
  /-- Matching players don't lose the game for having 0 or less life (CR 104.3b). -/
  | dontLoseForZeroLife (who : PlayerFilter)
  /-- Matching players can't win the game (CR 104.2). -/
  | cantWinGame (who : PlayerFilter)
  /-- Matching players have hexproof (optionally from `from?`, CR 702.11c–d). -/
  | hexproof (who : PlayerFilter) (from? : Option QualityFilter := none)
  /-- Matching players have protection from `quality` (CR 702.16j). -/
  | protectionFrom (who : PlayerFilter) (quality : ProtectionQuality)
  /-- Matching players can't cast matching spells (CR 601.2 / 101.2). -/
  | cantCastSpells (who : PlayerFilter) (spellPred : ObjectPred := .anyObject)
  /-- Matching players can't sacrifice matching permanents (CR 701.21 / 101.2). -/
  | cantSacrifice (who : PlayerFilter) (pred : ObjectPred)
  /-- Matching players can't attack (CR 508.1c / 101.2). -/
  | cantAttack (who : PlayerFilter)
  /-- Matching players may activate abilities of matching permanents as though they had haste. -/
  | activateAsThoughHaste (who : PlayerFilter := .you) (scope : ObjectFilter)
  /-- Each matching ability of matching permanents may be activated `extra` additional time(s). -/
  | extraAbilityActivation (tag : ActivationMechanicTag) (scope : ObjectFilter) (extra : Nat := 1)
  /-- Matching players' life totals can't change (CR 119.8). -/
  | lifeTotalCantChange (who : PlayerFilter)
  /-- Matching players can't activate abilities carrying `tag` (CR 101.2 / 602.5). -/
  | forbidAbilityActivation (who : PlayerFilter) (tag : ActivationMechanicTag)
  /-- Static designation check (e.g. permanent Ascend CR 702.131b / Storied). -/
  | gainDesignation (who : PlayerFilter := .you) (designation : PlayerDesignation)
  /-- CR 724: you control matching player(s) during their next turn. -/
  | controlPlayer (who : PlayerFilter)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticPlayerRule where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .maxHandSize w lim => .maxHandSize (HasTextChange.applyTextChanges tcs w) lim
      | .additionalLands w n => .additionalLands (HasTextChange.applyTextChanges tcs w) n
      | .cantGainLife w => .cantGainLife (HasTextChange.applyTextChanges tcs w)
      | .cantLoseGame w => .cantLoseGame (HasTextChange.applyTextChanges tcs w)
      | .dontLoseForZeroLife w => .dontLoseForZeroLife (HasTextChange.applyTextChanges tcs w)
      | .cantWinGame w => .cantWinGame (HasTextChange.applyTextChanges tcs w)
      | .hexproof w fq =>
        .hexproof (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs fq)
      | .protectionFrom w q =>
        .protectionFrom (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs q)
      | .cantCastSpells w p =>
        .cantCastSpells (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs p)
      | .cantSacrifice w p =>
        .cantSacrifice (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs p)
      | .cantAttack w => .cantAttack (HasTextChange.applyTextChanges tcs w)
      | .activateAsThoughHaste w sc =>
        .activateAsThoughHaste (HasTextChange.applyTextChanges tcs w)
          (HasTextChange.applyTextChanges tcs sc)
      | .extraAbilityActivation tag sc n =>
        .extraAbilityActivation (HasTextChange.applyTextChanges tcs tag)
          (HasTextChange.applyTextChanges tcs sc) n
      | .lifeTotalCantChange w => .lifeTotalCantChange (HasTextChange.applyTextChanges tcs w)
      | .forbidAbilityActivation w tag =>
        .forbidAbilityActivation (HasTextChange.applyTextChanges tcs w)
          (HasTextChange.applyTextChanges tcs tag)
      | .gainDesignation w d => .gainDesignation (HasTextChange.applyTextChanges tcs w) d
      | .controlPlayer w => .controlPlayer (HasTextChange.applyTextChanges tcs w)

/-- Rule-modifying static abilities affecting play permissions, timing,
counterability, opening-hand placement, and commander eligibility
(CR 101.2 / 103.6 / 401.2 / 601.2–3 / 606.3 / 903.3; 9 constructors). -/
inductive StaticPlayRule where
  /-- Players may look at the top card of their library any time (CR 401.2). -/
  | lookAtTopOfLibrary (who : PlayerFilter := .you)
  /-- Players may play lands (`landsAllowed`) or cast matching spells from `fromZone`
  (and optionally `secondZone?`), optionally once each turn, with an entry counter,
  or via beam me up (CR 702.196). -/
  | mayPlayFrom (who : PlayerFilter := .you) (fromZone : ZoneKind)
      (pred : ObjectPred := .anyObject) (landsAllowed : Bool := false)
      (linkedExile : Bool := false) (castAnyColorMana : Bool := false)
      (freeCast : Bool := false) (onceEachTurn : Bool := false)
      (secondZone? : Option ZoneKind := none)
      (enterCounter? : Option CounterKind := none)
      (asBeamMeUp : Bool := false)
  /-- Players may cast matching spells (or this spell when `thisSpell := true`) as though
  they had flash (CR 601.3b). -/
  | castAsThoughFlash (who : PlayerFilter := .you) (spellPred : ObjectPred := .anyObject)
      (thisSpell : Bool := false) (nthEachTurn? : Option Nat := none)
  /-- This spell (`spellPred := none`) or matching spells can't be countered (CR 101.2 / 701.6). -/
  | spellCantBeCountered (spellPred : Option ObjectPred := none)
  /-- The next matching spell cast by `who` can't be countered (CR 101.2 / 701.6). -/
  | nextSpellCantBeCountered (who : PlayerFilter := .you) (spellPred : ObjectPred := .anyObject)
  /-- This spell can't be cast unless `unlessCond` holds (CR 601.2 / 101.2). -/
  | castRestriction (unlessCond : Condition)
  /-- If this card is in your opening hand, you may begin the game with it on the
  battlefield (CR 103.6). -/
  | mayBeginOnBattlefield
  /-- This card can be your commander (CR 903.3). -/
  | canBeCommander
  /-- Loyalty abilities of matching planeswalkers `who` controls may be activated any
  time they could cast an instant (CR 606.3). -/
  | activateLoyaltyAsInstant (who : PlayerFilter := .you)
      (planeswalkerPred : ObjectPred := .hasType .planeswalker)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticPlayRule where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .lookAtTopOfLibrary w => .lookAtTopOfLibrary (HasTextChange.applyTextChanges tcs w)
      | .mayPlayFrom w z p la le anyC free once z2? ec? bmu =>
        .mayPlayFrom (HasTextChange.applyTextChanges tcs w) z
          (HasTextChange.applyTextChanges tcs p) la le anyC free once z2? ec? bmu
      | .castAsThoughFlash w p ts nth =>
        .castAsThoughFlash (HasTextChange.applyTextChanges tcs w)
          (HasTextChange.applyTextChanges tcs p) ts nth
      | .spellCantBeCountered p? => .spellCantBeCountered (HasTextChange.applyTextChanges tcs p?)
      | .nextSpellCantBeCountered w p =>
        .nextSpellCantBeCountered (HasTextChange.applyTextChanges tcs w)
          (HasTextChange.applyTextChanges tcs p)
      | .castRestriction c => .castRestriction (HasTextChange.applyTextChanges tcs c)
      | .mayBeginOnBattlefield => .mayBeginOnBattlefield
      | .canBeCommander => .canBeCommander
      | .activateLoyaltyAsInstant w p =>
        .activateLoyaltyAsInstant (HasTextChange.applyTextChanges tcs w)
          (HasTextChange.applyTextChanges tcs p)

/-- Rule-modifying static abilities affecting combat declarations and combat damage
assignment (CR 508 / 509 / 510; 17 constructors). -/
inductive StaticCombatRule where
  /-- Matching creatures can't attack (CR 508.1c). -/
  | cantAttack (subject : StaticSubject := .self)
  /-- Matching creatures can't attack alone (CR 508.1c). -/
  | cantAttackAlone (subject : StaticSubject := .self)
  /-- Matching creatures can't attack unless `unlessCond` holds (CR 508.1c). -/
  | cantAttackUnless (subject : StaticSubject := .self) (unlessCond : Condition)
  /-- Creatures matching `attackerPred` can't attack `defending` unless their controller
  pays `costPerAttacker` for each (CR 508.1d / 508.1h). -/
  | attackTax (attackerPred : ObjectPred := .hasType .creature)
      (defending : PlayerFilter := .you) (costPerAttacker : CostSpec)
  /-- Creatures matching `attackerPred` can't attack planeswalkers matching
  `planeswalkerPred` unless their controller pays `costPerAttacker` (CR 508.1d). -/
  | attackPlaneswalkerTax (attackerPred : ObjectPred := .hasType .creature)
      (planeswalkerPred : ObjectPred) (costPerAttacker : CostSpec)
  /-- Creatures matching `attackerPred` can't attack `defending` (or planeswalkers matching
  `planeswalkerPred?` controlled by `defending`, CR 508.1c). -/
  | cantAttackPlayer (attackerPred : ObjectPred) (defending : PlayerFilter := .you)
      (planeswalkerPred? : Option ObjectPred := none)
  /-- Matching creatures attack each combat if able (CR 508.1d). -/
  | attacksEachCombatIfAble (subject : StaticSubject := .self)
  /-- Matching creatures can attack as though they didn't have defender (CR 702.3b). -/
  | attackDespiteDefender (subject : StaticSubject := .self)
  /-- No more than `maxAttackers` creature(s) can attack `subject` each combat (CR 508.1c). -/
  | maxAttackersPerPermanent (subject : StaticSubject := .self) (maxAttackers : Nat)
  /-- Matching creatures can't block, or can't block unless `unlessCond?` holds (CR 509.1b). -/
  | cantBlock (subject : StaticSubject := .self) (unlessCond? : Option Condition := none)
  /-- Creatures matching `blockerPred` can't block creatures matching `attackerPred` (CR 509.1b). -/
  | cantBlockMatching (blockerPred : ObjectPred) (attackerPred : ObjectPred)
  /-- Matching creatures can't be blocked (CR 509.1b). -/
  | cantBeBlocked (subject : StaticSubject := .self)
  /-- Matching creatures can't be blocked by creatures matching `blockerPred` (CR 509.1b). -/
  | cantBeBlockedBy (subject : StaticSubject := .self) (blockerPred : ObjectPred)
  /-- Matching creatures can't be blocked except by `min` or more creatures (CR 509.1b). -/
  | minBlockers (subject : StaticSubject := .self) (min : Nat)
  /-- Matching creatures can't be blocked by more than `max` creature(s) (CR 509.1b). -/
  | maxBlockers (subject : StaticSubject := .self) (max : Nat)
  /-- Matching creatures assign combat damage equal to toughness rather than power (CR 510.1a). -/
  | assignCombatDamageByToughness (scope : ObjectFilter) (onlyIfToughnessGreater : Bool := false)
  /-- If a matching creature's power is negative, it assigns combat damage as though
  its power were positive (CR 510.1a). -/
  | assignNegativePowerAsPositive (subject : StaticSubject := .self)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticCombatRule where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .cantAttack s => .cantAttack (HasTextChange.applyTextChanges tcs s)
      | .cantAttackAlone s => .cantAttackAlone (HasTextChange.applyTextChanges tcs s)
      | .cantAttackUnless s c =>
        .cantAttackUnless (HasTextChange.applyTextChanges tcs s)
          (HasTextChange.applyTextChanges tcs c)
      | .attackTax ap df cs =>
        .attackTax (HasTextChange.applyTextChanges tcs ap)
          (HasTextChange.applyTextChanges tcs df) (HasTextChange.applyTextChanges tcs cs)
      | .attackPlaneswalkerTax ap pp cs =>
        .attackPlaneswalkerTax (HasTextChange.applyTextChanges tcs ap)
          (HasTextChange.applyTextChanges tcs pp) (HasTextChange.applyTextChanges tcs cs)
      | .cantAttackPlayer ap df pw? =>
        .cantAttackPlayer (HasTextChange.applyTextChanges tcs ap)
          (HasTextChange.applyTextChanges tcs df) (HasTextChange.applyTextChanges tcs pw?)
      | .attacksEachCombatIfAble s => .attacksEachCombatIfAble (HasTextChange.applyTextChanges tcs s)
      | .attackDespiteDefender s => .attackDespiteDefender (HasTextChange.applyTextChanges tcs s)
      | .maxAttackersPerPermanent s n =>
        .maxAttackersPerPermanent (HasTextChange.applyTextChanges tcs s) n
      | .cantBlock s c? =>
        .cantBlock (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs c?)
      | .cantBlockMatching bp ap =>
        .cantBlockMatching (HasTextChange.applyTextChanges tcs bp)
          (HasTextChange.applyTextChanges tcs ap)
      | .cantBeBlocked s => .cantBeBlocked (HasTextChange.applyTextChanges tcs s)
      | .cantBeBlockedBy s bp =>
        .cantBeBlockedBy (HasTextChange.applyTextChanges tcs s)
          (HasTextChange.applyTextChanges tcs bp)
      | .minBlockers s n => .minBlockers (HasTextChange.applyTextChanges tcs s) n
      | .maxBlockers s n => .maxBlockers (HasTextChange.applyTextChanges tcs s) n
      | .assignCombatDamageByToughness sc onlyGt =>
        .assignCombatDamageByToughness (HasTextChange.applyTextChanges tcs sc) onlyGt
      | .assignNegativePowerAsPositive s =>
        .assignNegativePowerAsPositive (HasTextChange.applyTextChanges tcs s)

/-- Rule-modifying static abilities affecting triggered abilities (CR 603.2 / 603.2d;
2 constructors). -/
inductive StaticTriggerRule where
  /-- If a triggered ability of a permanent matching `sourceScope` triggers
  (optionally caused by `causeEvent?`), it triggers `extra` additional time(s) (CR 603.2d). -/
  | extraTrigger (sourceScope : ObjectFilter) (extra : Nat := 1)
      (causeEvent? : Option EventPattern := none)
  /-- Permanents matching `enteringScope` entering the battlefield don't cause abilities
  to trigger (CR 603.2 / 101.2). -/
  | suppressEnteringTriggers (enteringScope : ObjectFilter)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticTriggerRule where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .extraTrigger sc n ev? =>
        .extraTrigger (HasTextChange.applyTextChanges tcs sc) n
          (HasTextChange.applyTextChanges tcs ev?)
      | .suppressEnteringTriggers sc =>
        .suppressEnteringTriggers (HasTextChange.applyTextChanges tcs sc)

/-- Rule-modifying static abilities affecting untap rules, phase locks, state-based
actions, beam me up, phasing, targeting, and counter placement prohibitions
(CR 122.1 / 502.3 / 702.26 / 702.196b / 704.5i,j; 10 constructors). -/
inductive StaticGameRule where
  /-- Matching permanents don't untap during their controller's untap step, optionally
  unless `unlessCond?` holds (CR 502.3). -/
  | doesntUntapDuringUntapStep (subject : StaticSubject := .self)
      (unlessCond? : Option Condition := none)
  /-- Matching permanents may choose not to untap during their controller's untap step (CR 502.3). -/
  | mayChooseNotToUntap (subject : StaticSubject := .self)
  /-- Matching permanents can't become untapped (CR 101.2 / 502.3). -/
  | cantBecomeUntapped (subject : StaticSubject := .self)
  /-- Matching permanents can't be beamed up (CR 702.196b). -/
  | cantBeBeamedUp (subject : StaticSubject := .self)
  /-- Matching permanents can't phase in (CR 702.26). -/
  | cantPhaseIn (scope : ObjectFilter)
  /-- Matching permanents can't be targeted by matching spells/abilities (CR 115 / 101.2). -/
  | cantBeTargetedBy (subject : StaticSubject := .self) (sourcePred : ObjectPred)
      (controller : PlayerFilter) (abilitiesOnly : Bool := false)
  /-- During `phase`, matching players can't cast spells or activate non-mana abilities. -/
  | lockNonManaDuringPhase (phase : Phase) (who : PlayerFilter := .any)
  /-- Planeswalkers matching `scope` aren't put into their owners' graveyards for having
  0 loyalty (CR 704.5i). -/
  | planeswalkersSurviveZeroLoyalty (scope : ObjectFilter)
  /-- Matching permanents can't have counters of `counterKind?` (`none` = any) put on them (CR 122.1). -/
  | cantHaveCountersPutOn (scope : ObjectFilter) (counterKind? : Option CounterKind)
  /-- The legend rule doesn't apply to permanents controlled by `who` (CR 704.5j). -/
  | legendRuleDisabled (who : PlayerFilter := .you)
deriving Repr, Inhabited, BEq

instance : HasTextChange StaticGameRule where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .doesntUntapDuringUntapStep s c? =>
        .doesntUntapDuringUntapStep (HasTextChange.applyTextChanges tcs s)
          (HasTextChange.applyTextChanges tcs c?)
      | .mayChooseNotToUntap s => .mayChooseNotToUntap (HasTextChange.applyTextChanges tcs s)
      | .cantBecomeUntapped s => .cantBecomeUntapped (HasTextChange.applyTextChanges tcs s)
      | .cantBeBeamedUp s => .cantBeBeamedUp (HasTextChange.applyTextChanges tcs s)
      | .cantPhaseIn sc => .cantPhaseIn (HasTextChange.applyTextChanges tcs sc)
      | .cantBeTargetedBy s sp ctrl abOnly =>
        .cantBeTargetedBy (HasTextChange.applyTextChanges tcs s)
          (HasTextChange.applyTextChanges tcs sp)
          (HasTextChange.applyTextChanges tcs ctrl) abOnly
      | .lockNonManaDuringPhase ph w =>
        .lockNonManaDuringPhase ph (HasTextChange.applyTextChanges tcs w)
      | .planeswalkersSurviveZeroLoyalty sc =>
        .planeswalkersSurviveZeroLoyalty (HasTextChange.applyTextChanges tcs sc)
      | .cantHaveCountersPutOn sc k? =>
        .cantHaveCountersPutOn (HasTextChange.applyTextChanges tcs sc) k?
      | .legendRuleDisabled w => .legendRuleDisabled (HasTextChange.applyTextChanges tcs w)

/-- Target spells or activated abilities of a cost modifier
(CR 601.2f / 602.2b / 113.6m; 3 constructors). -/
inductive CostTargetSpec where
  /-- This spell itself (active on the stack during CR 601.2f cost determination). -/
  | thisSpell
  /-- Spells cast by `caster` matching `spellPred`. -/
  | spells (caster : PlayerFilter := .you) (spellPred : ObjectPred := .anyObject)
      (nthEachTurn? : Option Nat := none) (notFromZone? : Option ZoneKind := none)
      (activeZones : Array ZoneKind := #[.battlefield])
  /-- Activated abilities matching `tag?` on sources matching `sourceScope`. -/
  | abilities (activator : PlayerFilter := .you)
      (tag? : Option ActivationMechanicTag := none)
      (sourceScope : ObjectFilter := { zones := .battlefield, pred := .anyObject })
      (targetPred? : Option ObjectPred := none)
      (nthEachTurn? : Option Nat := none)
deriving Repr, Inhabited, BEq

instance : HasTextChange CostTargetSpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      match s with
      | .thisSpell => .thisSpell
      | .spells caster pred nth notFrom az =>
        .spells (HasTextChange.applyTextChanges tcs caster)
          (HasTextChange.applyTextChanges tcs pred) nth notFrom az
      | .abilities act tag? sc tgt? nth =>
        .abilities (HasTextChange.applyTextChanges tcs act)
          (HasTextChange.applyTextChanges tcs tag?)
          (HasTextChange.applyTextChanges tcs sc)
          (HasTextChange.applyTextChanges tcs tgt?) nth

/-- Cost modification applied by `StaticAbility.costModifier` or `RuleModification.costMod`
(CR 601.2f / 602.2b / 118.9; 3 constructors). -/
inductive CostModification where
  /-- Reduce generic mana cost by `amount` (CR 601.2f / 118.7a). -/
  | reduceGeneric (amount : ValueExpr)
  /-- Increase generic mana cost by `amount` (CR 601.2f). -/
  | increaseGeneric (amount : ValueExpr)
  /-- Alternative cost `{0}` — cast or activate without paying mana / equip cost (CR 118.9). -/
  | alternativeFree
deriving Repr, Inhabited, BEq

instance : HasTextChange CostModification where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      match m with
      | .reduceGeneric v => .reduceGeneric (HasTextChange.applyTextChanges tcs v)
      | .increaseGeneric v => .increaseGeneric (HasTextChange.applyTextChanges tcs v)
      | .alternativeFree => .alternativeFree

/-- Stratified rule-modifying static ability payload (CR 604 / 101.2; 7 constructors). -/
inductive RuleModification where
  | player (rule : StaticPlayerRule)
  | play (rule : StaticPlayRule)
  | combat (rule : StaticCombatRule)
  | trigger (rule : StaticTriggerRule)
  | game (rule : StaticGameRule)
  /-- Duration-scoped spell/ability cost modification (CR 601.2f / 118.9). -/
  | costMod (appliesTo : CostTargetSpec) (mod : CostModification) (nextOnly : Bool := false)
  | all (rules : Array RuleModification)
deriving Repr, Inhabited, BEq

private def applyTcRuleMod (tcs : Array TextChange) : RuleModification → RuleModification
  | .player r => .player (HasTextChange.applyTextChanges tcs r)
  | .play r => .play (HasTextChange.applyTextChanges tcs r)
  | .combat r => .combat (HasTextChange.applyTextChanges tcs r)
  | .trigger r => .trigger (HasTextChange.applyTextChanges tcs r)
  | .game r => .game (HasTextChange.applyTextChanges tcs r)
  | .costMod tgt mod next =>
    .costMod (HasTextChange.applyTextChanges tcs tgt) (HasTextChange.applyTextChanges tcs mod) next
  | .all rs => .all (rs.attach.map fun ⟨r, _⟩ => applyTcRuleMod tcs r)

instance : HasTextChange RuleModification where
  applyTextChanges tcs r := if tcs.isEmpty then r else applyTcRuleMod tcs r

namespace RuleModification

/-- Flatten nested `.all` rules in printed order. -/
def flatten : RuleModification → Array RuleModification
  | .all rs => rs.attach.foldl (fun acc ⟨r, _⟩ => acc ++ flatten r) #[]
  | r => #[r]

end RuleModification

/-- Choice made as a permanent enters the battlefield (CR 614.1c / 614.12; 7 constructors). -/
inductive AsEntersChoiceKind where
  | color
  | creatureType
  | cardType
  | nonlandCardName
  | oddOrEven
  | namedAnchors (options : Array String)
  | numberRange (lo hi : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-! ### 3. Predefined Tokens & One-Shot Instruction Sub-Families (Every Enum ≤ 17 Ctors) -/

/-- Predefined tokens defined directly by CR 111.10a–x (6 November 2026; 10 constructors). -/
inductive PredefinedToken where
  /-- CR 111.10a: Colorless Treasure artifact token. -/
  | treasure
  /-- CR 111.10b: Colorless Food artifact token. -/
  | food
  /-- CR 111.10f: Colorless Clue artifact token. -/
  | clue
  /-- CR 111.10i: Transforming colorless Incubator artifact token. -/
  | incubator
  /-- CR 111.10s: Colorless Map artifact token. -/
  | map
  /-- CR 111.10t: Colorless Junk artifact token. -/
  | junk
  /-- CR 111.10u: Colorless Lander artifact token. -/
  | lander
  /-- CR 111.10v: Colorless Mutagen artifact token. -/
  | mutagen
  /-- CR 111.10w: Colorless Vibranium artifact token. -/
  | vibranium
  /-- CR 111.10x: Red and green Heartwood artifact token. -/
  | heartwood
deriving DecidableEq, Repr, Inhabited, BEq

/-- Whose zone or control a moved object enters (3 constructors). -/
inductive DestOwnerSpec where
  /-- Under the resolving ability/spell controller's control or into their zone. -/
  | controller
  /-- Under each moved object's owner's control or into its owner's zone (CR 400.3). -/
  | owner
  /-- Under the evaluated player's control or into that player's zone. -/
  | player (who : PlayerExpr)
deriving Repr, Inhabited, BEq

instance : HasTextChange DestOwnerSpec where
  applyTextChanges tcs d :=
    if tcs.isEmpty then d
    else
      match d with
      | .player w => .player (HasTextChange.applyTextChanges tcs w)
      | other => other

/-- Destination zone for `Instruction.moveZone` and library searches (5 constructors). -/
inductive DestZoneSpec where
  | battlefield (under : DestOwnerSpec := .owner)
  | graveyard
  | hand (to : DestOwnerSpec := .owner)
  | exile
  | library (whose : DestOwnerSpec := .owner) (pos : LibraryPosSpec := .bottom)
      (ownerChoosesTopOrBottom : Bool := false)
deriving Repr, Inhabited, BEq

instance : HasTextChange DestZoneSpec where
  applyTextChanges tcs d :=
    if tcs.isEmpty then d
    else
      match d with
      | .battlefield u => .battlefield (HasTextChange.applyTextChanges tcs u)
      | .graveyard => .graveyard
      | .hand u => .hand (HasTextChange.applyTextChanges tcs u)
      | .exile => .exile
      | .library u pos opt =>
        .library (HasTextChange.applyTextChanges tcs u)
          (HasTextChange.applyTextChanges tcs pos) opt

/-- Play / cast permission granted to moved or referenced cards (CR 601.2 / 611.2b). -/
structure GrantPlayPermSpec where
  duration : DurationExpr := .untilEndOfTurn
  landsAllowed : Bool := true
  freeCast : Bool := false
  anyManaColor : Bool := false
  payLifeInsteadOfMana : Bool := false
  /-- Copy the exiled cards and allow casting the copies (CR 707.12). -/
  copyAndCast : Bool := false
  /-- Flashback permission granting cast from graveyard with mana cost as flashback cost. -/
  asFlashback : Bool := false
  /-- Cast immediately during resolution rather than granting a later-in-turn play permission (CR 608.2g). -/
  castNow : Bool := false
  /-- If an instant or sorcery spell cast this way would be put into its owner's graveyard, exile it instead. -/
  exileOnResolveInstead : Bool := false
  maxCasts? : Option Nat := none
  maxTotalManaValue? : Option ValueExpr := none
  condition? : Option Condition := none
  filter? : Option ObjectPred := none
  /-- Extra generic mana cost added to spells cast via this permission (e.g. Zero, Incorporeal Sensate). -/
  extraGenericCost : Nat := 0
  /-- Player granted the permission (`none` = controller of the resolving effect). -/
  beneficiary? : Option PlayerExpr := none
  /-- True when mana of any type (including colorless) may be spent (CR 106.1a). -/
  anyManaType : Bool := false
deriving Repr, Inhabited, BEq

instance : HasTextChange GrantPlayPermSpec where
  applyTextChanges tcs g :=
    if tcs.isEmpty then g
    else
      { g with
        duration := HasTextChange.applyTextChanges tcs g.duration
        maxTotalManaValue? := HasTextChange.applyTextChanges tcs g.maxTotalManaValue?
        condition? := HasTextChange.applyTextChanges tcs g.condition?
        filter? := HasTextChange.applyTextChanges tcs g.filter?
        beneficiary? := HasTextChange.applyTextChanges tcs g.beneficiary? }

/-- Blink / temporary exile return specification on `MoveMods` (4 constructors). -/
inductive DelayedReturnSpec where
  /-- Exile then immediately return to the battlefield (CR 400.7). -/
  | immediately (tapped : Bool := false) (under : DestOwnerSpec := .owner)
  /-- Return to the battlefield at the beginning of the next end step (CR 603.7). -/
  | atNextEndStep (tapped : Bool := false) (under : DestOwnerSpec := .owner)
  /-- Return to the battlefield immediately, then exile it at the beginning of the next end step. -/
  | returnThenExileAtEndStep (tapped : Bool := false) (under : DestOwnerSpec := .controller)
  /-- If moved object satisfies `cond`, return it immediately and exile it at the next end step. -/
  | returnIfThenExileAtEndStep (cond : ObjectPred) (tapped : Bool := false)
      (under : DestOwnerSpec := .controller)
deriving Repr, Inhabited, BEq

instance : HasTextChange DelayedReturnSpec where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .immediately tap u => .immediately tap (HasTextChange.applyTextChanges tcs u)
      | .atNextEndStep tap u => .atNextEndStep tap (HasTextChange.applyTextChanges tcs u)
      | .returnThenExileAtEndStep tap u =>
        .returnThenExileAtEndStep tap (HasTextChange.applyTextChanges tcs u)
      | .returnIfThenExileAtEndStep p tap u =>
        .returnIfThenExileAtEndStep (HasTextChange.applyTextChanges tcs p) tap
          (HasTextChange.applyTextChanges tcs u)

/-- Who selects objects during an interactive `moveZone` step (3 constructors). -/
inductive MoveChooser where
  | controller
  | owner
  | player (who : PlayerExpr)
deriving Repr, Inhabited, BEq

instance : HasTextChange MoveChooser where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else
      match c with
      | .player w => .player (HasTextChange.applyTextChanges tcs w)
      | other => other

/-- Dynamic count range for resolution choices, counter removal, and searches (4 constructors). -/
inductive ExprCountRange where
  | exact (n : ValueExpr)
  | upTo (n : ValueExpr)
  | between (lo hi : ValueExpr)
  | anyNumber
deriving Repr, Inhabited, BEq

instance : HasTextChange ExprCountRange where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .exact n => .exact (HasTextChange.applyTextChanges tcs n)
      | .upTo n => .upTo (HasTextChange.applyTextChanges tcs n)
      | .between lo hi =>
        .between (HasTextChange.applyTextChanges tcs lo) (HasTextChange.applyTextChanges tcs hi)
      | .anyNumber => .anyNumber

/-- Interactive selection parameters for `MoveMods.choice?`. -/
structure MoveChoiceSpec where
  chooser : MoveChooser := .controller
  count : ExprCountRange := .exact (.const 1)
  filter? : Option ObjectPred := none
  groupConstraint? : Option GroupTargetConstraint := none
  /-- Move the UNCHOSEN objects instead of the chosen ones (e.g. "choose up to two, destroy the rest"). -/
  invertSelection : Bool := false
  atRandom : Bool := false
  revealFirst : Bool := false
  /-- "Discard N cards unless you discard a card matching `pred`." -/
  unlessMatching? : Option ObjectPred := none
  /-- Restrict choices to objects achieving the extremum (`true` = max, `false` = min) of `metric`. -/
  extremeMetric? : Option (Bool × ObjectMetric) := none
deriving Repr, Inhabited, BEq

instance : HasTextChange MoveChoiceSpec where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else
      { c with
        chooser := HasTextChange.applyTextChanges tcs c.chooser
        count := HasTextChange.applyTextChanges tcs c.count
        filter? := HasTextChange.applyTextChanges tcs c.filter?
        groupConstraint? := HasTextChange.applyTextChanges tcs c.groupConstraint?
        unlessMatching? := HasTextChange.applyTextChanges tcs c.unlessMatching? }

/-- Modifiers applied to objects moved by `Instruction.moveZone` (CR 608.2c / 610.3). -/
structure MoveMods where
  tapped : Bool := false
  attacking : Bool := false
  goaded : Bool := false
  attachTo? : Option ObjectExpr := none
  enterCounters : Array (CounterKind × ValueExpr) := #[]
  enterFaceDown : Bool := false
  mayTransformOnEnter : Bool := false
  /-- CR 610.3: exile until the source permanent leaves the battlefield. -/
  exileUntilSourceLeaves : Bool := false
  /-- CR 607: link exiled cards to the source object. -/
  linkToSource : Bool := false
  delayedReturn? : Option DelayedReturnSpec := none
  grantPlayPerm? : Option GrantPlayPermSpec := none
  choice? : Option MoveChoiceSpec := none
  shuffleAfter : Bool := false
  /-- Optional entering type modification (e.g. enters as a Food artifact in addition to other types). -/
  enterTypeMod? : Option TypeSetMod := none
  /-- Optional predefined-token ability grant on enter (e.g. Food `{2}, {T}, Sacrifice: Gain 3 life`). -/
  enterAsPredefined? : Option PredefinedToken := none
  enterKeywords : Array KeywordAbility := #[]
  enterLoseAllAbilities : Bool := false
deriving Repr, Inhabited, BEq

instance : HasTextChange MoveMods where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      { m with
        attachTo? := HasTextChange.applyTextChanges tcs m.attachTo?
        enterCounters := m.enterCounters.map fun (k, v) => (k, HasTextChange.applyTextChanges tcs v)
        delayedReturn? := HasTextChange.applyTextChanges tcs m.delayedReturn?
        grantPlayPerm? := HasTextChange.applyTextChanges tcs m.grantPlayPerm?
        choice? := HasTextChange.applyTextChanges tcs m.choice?
        enterTypeMod? := HasTextChange.applyTextChanges tcs m.enterTypeMod?
        enterKeywords := HasTextChange.applyTextChanges tcs m.enterKeywords }

/-- Delayed cleanup scheduled on tokens created by `CreateOp.tokens` (4 constructors). -/
inductive DelayedTokenAction where
  | sacrificeAtEndStep
  | exileAtEndStep
  | exileAtEndOfCombat
  | sacrificeAtEndStepUnless (cond : Condition)
deriving Repr, Inhabited, BEq

instance : HasTextChange DelayedTokenAction where
  applyTextChanges tcs a :=
    if tcs.isEmpty then a
    else
      match a with
      | .sacrificeAtEndStepUnless c =>
        .sacrificeAtEndStepUnless (HasTextChange.applyTextChanges tcs c)
      | other => other

/-- Entry modifiers applied to tokens created by `CreateOp.tokens` (CR 111.3 / 508.4). -/
structure EnterMods where
  tapped : Bool := false
  attacking : Bool := false
  goaded : Bool := false
  attachTo? : Option ObjectExpr := none
  counters : Array (CounterKind × ValueExpr) := #[]
  grantKeywordsUntilEot : Array KeywordAbility := #[]
  delayedAction? : Option DelayedTokenAction := none
deriving Repr, Inhabited, BEq

instance : HasTextChange EnterMods where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      { m with
        attachTo? := HasTextChange.applyTextChanges tcs m.attachTo?
        counters := m.counters.map fun (k, v) => (k, HasTextChange.applyTextChanges tcs v)
        grantKeywordsUntilEot := HasTextChange.applyTextChanges tcs m.grantKeywordsUntilEot
        delayedAction? := HasTextChange.applyTextChanges tcs m.delayedAction? }

/-- Damage recipient expression for `DamageOp.deal` (CR 120; 5 constructors). -/
inductive RecipientExpr where
  | objects (objs : ObjectExpr)
  | players (who : PlayerExpr)
  /-- Any announced target at slot `slot` (creature, planeswalker, battle, or player; CR 115.4). -/
  | targetSlot (slot : Nat := 0)
  /-- Both matching objects and matching players simultaneously. -/
  | both (objs : ObjectExpr) (players : PlayerExpr)
  /-- All announced targets across slots. -/
  | allTargets
deriving Repr, Inhabited, BEq

instance : HasTextChange RecipientExpr where
  applyTextChanges tcs r :=
    if tcs.isEmpty then r
    else
      match r with
      | .objects o => .objects (HasTextChange.applyTextChanges tcs o)
      | .players p => .players (HasTextChange.applyTextChanges tcs p)
      | .targetSlot i => .targetSlot i
      | .both o p =>
        .both (HasTextChange.applyTextChanges tcs o) (HasTextChange.applyTextChanges tcs p)
      | .allTargets => .allTargets

/-- Modifier flags for `DamageOp.deal` (CR 120 / 601.2d). -/
structure DamageFlags where
  divided : Bool := false
  trackExcess : Bool := false
  cantBePrevented : Bool := false
deriving DecidableEq, Repr, Inhabited, BEq

/-- Damage actions aligned with `RulesEvent.damage` (CR 120 / 701.14; 2 constructors). -/
inductive DamageOp where
  | deal (source : ObjectExpr) (to : RecipientExpr) (amount : ValueExpr)
      (flags : DamageFlags := {})
  | fight (a b : ObjectExpr) (oneWay : Bool := false)
deriving Repr, Inhabited, BEq

instance : HasTextChange DamageOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .deal src to amt fl =>
        .deal (HasTextChange.applyTextChanges tcs src) (HasTextChange.applyTextChanges tcs to)
          (HasTextChange.applyTextChanges tcs amt) fl
      | .fight a b ow =>
        .fight (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs b) ow

/-- Life actions aligned with `RulesEvent.life` (CR 119; 3 constructors). -/
inductive LifeOp where
  | gain (who : PlayerExpr) (amount : ValueExpr)
  | lose (who : PlayerExpr) (amount : ValueExpr)
  | set (who : PlayerExpr) (amount : ValueExpr)
deriving Repr, Inhabited, BEq

instance : HasTextChange LifeOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .gain w a => .gain (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .lose w a => .lose (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .set w a => .set (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)

/-- Counter modification mode for `PermanentOp.modifyCounters` (CR 122; 9 constructors). -/
inductive CounterModifyMode where
  | put (kind : CounterKind) (count : ValueExpr)
  | distribute (kind : CounterKind) (count : ValueExpr)
  | remove (kind? : Option CounterKind) (count : ExprCountRange)
  | moveAll (fromObj : ObjectExpr) (kind? : Option CounterKind := none)
  | moveOne (fromObj : ObjectExpr) (kind : CounterKind)
  | copyFromLki (fromObj : ObjectExpr)
  | copyMissingKeywords (fromObj : ObjectExpr)
  | double (kind? : Option CounterKind := none)
  | putAnotherOfChosen
deriving Repr, Inhabited, BEq

instance : HasTextChange CounterModifyMode where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      match m with
      | .put k c => .put k (HasTextChange.applyTextChanges tcs c)
      | .distribute k c => .distribute k (HasTextChange.applyTextChanges tcs c)
      | .remove k? c => .remove k? (HasTextChange.applyTextChanges tcs c)
      | .moveAll src k? => .moveAll (HasTextChange.applyTextChanges tcs src) k?
      | .moveOne src k => .moveOne (HasTextChange.applyTextChanges tcs src) k
      | .copyFromLki src => .copyFromLki (HasTextChange.applyTextChanges tcs src)
      | .copyMissingKeywords src => .copyMissingKeywords (HasTextChange.applyTextChanges tcs src)
      | .double k? => .double k?
      | .putAnotherOfChosen => .putAnotherOfChosen

/-- Permanent-state actions aligned with `RulesEvent.permanent` (CR 701; 8 constructors). -/
inductive PermanentOp where
  | setTapped (objs : ObjectExpr) (tapped : Bool) (choice? : Option MoveChoiceSpec := none)
  | modifyCounters (mode : CounterModifyMode) (objs : ObjectExpr)
      (choice? : Option MoveChoiceSpec := none)
  | attach (attachment : ObjectExpr) (toObj : ObjectExpr) (chooseFromPool : Bool := false)
  | transform (objs : ObjectExpr)
  | turnFaceUp (objs : ObjectExpr)
  | phaseOut (objs : ObjectExpr) (untilPlayerNextTurn? : Option PlayerExpr := none)
  | setDesignation (objs : ObjectExpr) (tag : PermanentDesignationTag) (value : Bool := true)
  /-- CR 701.72: Assimilate permanent(s) or permanent card(s) (put onto battlefield /
  gain control with a +1/+1 counter; becomes a Borg artifact creature). -/
  | assimilate (objs : ObjectExpr) (choice? : Option MoveChoiceSpec := none)
deriving Repr, Inhabited, BEq

instance : HasTextChange PermanentOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .setTapped o t ch? =>
        .setTapped (HasTextChange.applyTextChanges tcs o) t (HasTextChange.applyTextChanges tcs ch?)
      | .modifyCounters m o ch? =>
        .modifyCounters (HasTextChange.applyTextChanges tcs m) (HasTextChange.applyTextChanges tcs o)
          (HasTextChange.applyTextChanges tcs ch?)
      | .attach a b ch =>
        .attach (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs b) ch
      | .transform o => .transform (HasTextChange.applyTextChanges tcs o)
      | .turnFaceUp o => .turnFaceUp (HasTextChange.applyTextChanges tcs o)
      | .phaseOut o p? =>
        .phaseOut (HasTextChange.applyTextChanges tcs o) (HasTextChange.applyTextChanges tcs p?)
      | .setDesignation o tag v =>
        .setDesignation (HasTextChange.applyTextChanges tcs o) tag v
      | .assimilate o ch? =>
        .assimilate (HasTextChange.applyTextChanges tcs o) (HasTextChange.applyTextChanges tcs ch?)

/-- Card source inspected by `PlayerOp.inspectLibrary` (5 constructors). -/
inductive InspectSource where
  | topCards (who : PlayerExpr) (count : ValueExpr) (reveal : Bool := false)
  | revealUntil (who : PlayerExpr) (matchPred : ObjectPred)
      (matchCount : ValueExpr := .const 1) (exileWhileRevealing : Bool := false)
  | millCards (who : PlayerExpr) (count : ValueExpr)
  | allButBottom (who : PlayerExpr)
  | outsideTheGame (who : PlayerExpr) (count : Nat)
deriving Repr, Inhabited, BEq

instance : HasTextChange InspectSource where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      match s with
      | .topCards w c rev =>
        .topCards (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs c) rev
      | .revealUntil w p c ex =>
        .revealUntil (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs p)
          (HasTextChange.applyTextChanges tcs c) ex
      | .millCards w c =>
        .millCards (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs c)
      | .allButBottom w => .allButBottom (HasTextChange.applyTextChanges tcs w)
      | .outsideTheGame w n => .outsideTheGame (HasTextChange.applyTextChanges tcs w) n

/-- Where unchosen cards from `PlayerOp.inspectLibrary` go (6 constructors). -/
inductive RestPlacement where
  | leaveInPlace
  | bottomRandom
  | bottomAnyOrder
  | graveyard
  | exile
  | shuffleIntoLibrary
deriving DecidableEq, Repr, Inhabited, BEq

/-- What happens to inspected cards in `PlayerOp.inspectLibrary` (5 constructors). -/
inductive InspectAction where
  /-- Choose matching cards from the inspected set and move them to `dest`. -/
  | takeMatching (filter : ObjectPred) (count : ExprCountRange) (dest : DestZoneSpec)
      (mods : MoveMods := {}) (revealTaken : Bool := false) (atRandom : Bool := false)
  /-- Split inspected cards into piles (`Fact or Fiction`, `Riddles in the Dark`). -/
  | splitIntoPiles (splitter : PlayerExpr) (chooser : PlayerExpr) (pileCount : Nat := 2)
      (chosenDest : DestZoneSpec) (otherDest : DestZoneSpec)
      (canDrawInsteadOfPile? : Option Nat := none)
  /-- Put matched cards onto the battlefield and distribute one under each opponent's control. -/
  | distributeEachOpponent (dest : DestZoneSpec) (mods : MoveMods := {})
  /-- Move all inspected cards to `dest` with `mods`. -/
  | moveAll (dest : DestZoneSpec) (mods : MoveMods := {})
  /-- Just look/reveal (subsequent `.bind` inspects `stepObjects`). -/
  | none
deriving Repr, Inhabited, BEq

instance : HasTextChange InspectAction where
  applyTextChanges tcs a :=
    if tcs.isEmpty then a
    else
      match a with
      | .takeMatching f cnt dest mods rev rand =>
        .takeMatching (HasTextChange.applyTextChanges tcs f) (HasTextChange.applyTextChanges tcs cnt)
          (HasTextChange.applyTextChanges tcs dest) (HasTextChange.applyTextChanges tcs mods) rev rand
      | .splitIntoPiles sp ch n d1 d2 opt =>
        .splitIntoPiles (HasTextChange.applyTextChanges tcs sp) (HasTextChange.applyTextChanges tcs ch)
          n (HasTextChange.applyTextChanges tcs d1) (HasTextChange.applyTextChanges tcs d2) opt
      | .distributeEachOpponent dest mods =>
        .distributeEachOpponent (HasTextChange.applyTextChanges tcs dest)
          (HasTextChange.applyTextChanges tcs mods)
      | .moveAll dest mods =>
        .moveAll (HasTextChange.applyTextChanges tcs dest) (HasTextChange.applyTextChanges tcs mods)
      | .none => .none

/-- Declarative library/mill/wish inspection specification unifying look-at-top,
reveal-until, mill-then-put, pile-splitting, and sideboard wishes. -/
structure InspectLibrarySpec where
  source : InspectSource
  action : InspectAction
  rest : RestPlacement := .bottomRandom
  chooser : PlayerExpr := .you
deriving Repr, Inhabited, BEq

instance : HasTextChange InspectLibrarySpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      { source := HasTextChange.applyTextChanges tcs s.source
        action := HasTextChange.applyTextChanges tcs s.action
        rest := s.rest
        chooser := HasTextChange.applyTextChanges tcs s.chooser }

/-- Declarative library (or library + graveyard/hand) search specification (CR 701.23). -/
structure SearchLibrarySpec where
  searcher : PlayerExpr := .you
  zones : ZoneSetSpec := .yourLibrary
  filter : ObjectPred := .anyObject
  count : ExprCountRange := .upTo (.const 1)
  groupConstraint? : Option GroupTargetConstraint := none
  dest : DestZoneSpec := .hand .controller
  mods : MoveMods := {}
  /-- Optional split destination for a second found card (e.g. one to battlefield tapped, one to hand). -/
  secondDest? : Option (DestZoneSpec × MoveMods) := none
  reveal : Bool := true
  shuffle : Bool := true
  /-- Optional condition checked after entering tapped to untap the found card. -/
  untapIf? : Option Condition := none
deriving Repr, Inhabited, BEq

instance : HasTextChange SearchLibrarySpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      { s with
        searcher := HasTextChange.applyTextChanges tcs s.searcher
        zones := HasTextChange.applyTextChanges tcs s.zones
        filter := HasTextChange.applyTextChanges tcs s.filter
        count := HasTextChange.applyTextChanges tcs s.count
        groupConstraint? := HasTextChange.applyTextChanges tcs s.groupConstraint?
        dest := HasTextChange.applyTextChanges tcs s.dest
        mods := HasTextChange.applyTextChanges tcs s.mods
        secondDest? := s.secondDest?.map fun (d, m) =>
          (HasTextChange.applyTextChanges tcs d, HasTextChange.applyTextChanges tcs m)
        untapIf? := HasTextChange.applyTextChanges tcs s.untapIf? }

/-- Player status/designation granted by `PlayerOp.setStatus` (4 constructors). -/
inductive PlayerStatusKind where
  | designation (d : PlayerDesignation)
  | monarch
  | winGame
  | loseGame
deriving DecidableEq, Repr, Inhabited, BEq

/-- Resolution-time choice bound into `stepEnv` via `Instruction.bind` (4 constructors). -/
inductive ResolutionChoiceKind where
  | creatureType
  | oddOrEven
  | keyword (options : Array KeywordAbility)
  | playerWithMostLife
deriving Repr, Inhabited, BEq

instance : HasTextChange ResolutionChoiceKind where
  applyTextChanges tcs c :=
    if tcs.isEmpty then c
    else
      match c with
      | .keyword ks => .keyword (HasTextChange.applyTextChanges tcs ks)
      | other => other

/-- Player actions aligned with `RulesEvent.player` (CR 106 / 121 / 701 / 726;
17 constructors). -/
inductive PlayerOp where
  | drawCards (who : PlayerExpr) (amount : ValueExpr)
  | scry (who : PlayerExpr) (amount : ValueExpr)
  | surveil (who : PlayerExpr) (amount : ValueExpr)
  | inspectLibrary (spec : InspectLibrarySpec)
  | searchLibrary (spec : SearchLibrarySpec)
  | reveal (who : PlayerExpr) (objs : ObjectExpr) (count? : Option ExprCountRange := none)
  | shuffle (who : PlayerExpr)
  | addMana (who : PlayerExpr) (spec : ManaProductionSpec)
  | proliferate (who : PlayerExpr) (times : ValueExpr := .const 1)
      (targetOnly? : Option ObjectExpr := none)
  | temptWithRing (who : PlayerExpr)
  | explore (objs : ObjectExpr)
  | amass (who : PlayerExpr) (subtype : CardSubtype) (amount : ValueExpr)
  | connive (objs : ObjectExpr)
  | empowerPlaneswalker (subtype : CardSubtype) (amount : ValueExpr)
  | discover (who : PlayerExpr) (amount : ValueExpr)
  | setStatus (who : PlayerExpr) (kind : PlayerStatusKind)
      (condition? : Option Condition := none)
  | choose (who : PlayerExpr) (kind : ResolutionChoiceKind)
deriving Repr, Inhabited, BEq

namespace PlayerOp

/-- Smart constructor for lasting player designations (Ascend CR 702.131a, Storied). -/
def setPlayerDesignation (who : PlayerExpr) (d : PlayerDesignation)
    (condition? : Option Condition := none) : PlayerOp :=
  .setStatus who (.designation d) condition?

/-- Smart constructor for becoming the monarch (CR 726). -/
def becomeMonarch (who : PlayerExpr := .you) : PlayerOp :=
  .setStatus who .monarch none

end PlayerOp

instance : HasTextChange PlayerOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .drawCards w a =>
        .drawCards (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .scry w a =>
        .scry (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .surveil w a =>
        .surveil (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .inspectLibrary s => .inspectLibrary (HasTextChange.applyTextChanges tcs s)
      | .searchLibrary s => .searchLibrary (HasTextChange.applyTextChanges tcs s)
      | .reveal w o cnt? =>
        .reveal (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs o)
          (HasTextChange.applyTextChanges tcs cnt?)
      | .shuffle w => .shuffle (HasTextChange.applyTextChanges tcs w)
      | .addMana w s =>
        .addMana (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs s)
      | .proliferate w t tgt? =>
        .proliferate (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs t)
          (HasTextChange.applyTextChanges tcs tgt?)
      | .temptWithRing w => .temptWithRing (HasTextChange.applyTextChanges tcs w)
      | .explore o => .explore (HasTextChange.applyTextChanges tcs o)
      | .amass w sub a =>
        .amass (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs sub)
          (HasTextChange.applyTextChanges tcs a)
      | .connive o => .connive (HasTextChange.applyTextChanges tcs o)
      | .empowerPlaneswalker sub a =>
        .empowerPlaneswalker (HasTextChange.applyTextChanges tcs sub)
          (HasTextChange.applyTextChanges tcs a)
      | .discover w a =>
        .discover (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs a)
      | .setStatus w k c? =>
        .setStatus (HasTextChange.applyTextChanges tcs w) k (HasTextChange.applyTextChanges tcs c?)
      | .choose w k =>
        .choose (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs k)

/-- Turn-structure actions aligned with `RulesEvent.turn` (CR 500.7–8; 3 constructors). -/
inductive TurnOp where
  | extraTurn (who : PlayerExpr) (rule? : Option RuleModification := none)
  | extraPhase (phase : Phase) (afterCurrent : Bool := true)
  | extraStep (step : Step) (afterCurrent : Bool := true)
deriving Repr, Inhabited, BEq

instance : HasTextChange TurnOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .extraTurn w r? =>
        .extraTurn (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs r?)
      | .extraPhase ph ac => .extraPhase ph ac
      | .extraStep st ac => .extraStep st ac

/-- Stack & mid-resolution cast actions aligned with `RulesEvent.stackObject` /
`RulesEvent.cast` (CR 115.7d / 601 / 701.5 / 707.10; 4 constructors). -/
inductive StackOp where
  | counterStack (objs : ObjectExpr) (exileInstead : Bool := false)
      (ifPermanentMayCastFree : Bool := false)
  | copyStackObject (objs : ObjectExpr) (copies : ValueExpr := .const 1)
      (mayChooseNewTargets : Bool := true)
  | chooseNewTargets (objs : ObjectExpr) (optional : Bool := true)
  | mayCastOrPlay (objs : ObjectExpr) (perm : GrantPlayPermSpec)
deriving Repr, Inhabited, BEq

instance : HasTextChange StackOp where
  applyTextChanges tcs op :=
    if tcs.isEmpty then op
    else
      match op with
      | .counterStack o ex fc => .counterStack (HasTextChange.applyTextChanges tcs o) ex fc
      | .copyStackObject o n nt =>
        .copyStackObject (HasTextChange.applyTextChanges tcs o)
          (HasTextChange.applyTextChanges tcs n) nt
      | .chooseNewTargets o opt =>
        .chooseNewTargets (HasTextChange.applyTextChanges tcs o) opt
      | .mayCastOrPlay o p =>
        .mayCastOrPlay (HasTextChange.applyTextChanges tcs o)
          (HasTextChange.applyTextChanges tcs p)

/-- Iteration domain for `Instruction.forEach` (4 constructors). -/
inductive ForEachSpec where
  | eachPlayer (filter : PlayerFilter)
  | eachObject (objs : ObjectExpr)
  | eachTargetSlot
  | repeatTimes (count : ValueExpr)
deriving Repr, Inhabited, BEq

instance : HasTextChange ForEachSpec where
  applyTextChanges tcs f :=
    if tcs.isEmpty then f
    else
      match f with
      | .eachPlayer pf => .eachPlayer (HasTextChange.applyTextChanges tcs pf)
      | .eachObject o => .eachObject (HasTextChange.applyTextChanges tcs o)
      | .eachTargetSlot => .eachTargetSlot
      | .repeatTimes c => .repeatTimes (HasTextChange.applyTextChanges tcs c)

/-! ### 4. Unified 16-Type Stratified `mutual` Block (CR 111 / 113.3 / 114 / 608 / 613 / 614) -/

mutual

/-- An ability carried by a custom token, token copy exception, or continuous grant
(CR 111.3 / 613.1f / 707.9; 4 constructors). -/
inductive GrantedAbility where
  | keyword (kw : KeywordAbility)
  | activated (ab : ActivatedAbility)
  | triggered (ab : TriggeredAbility)
  | static (ab : StaticAbility)

/-- Characteristics of a custom token (CR 111.3 / 111.4 / 111.11). -/
structure CustomTokenSpec where
  name? : Option String := none
  supertypes : Array Supertype := #[]
  types : Array CardType := #[.creature]
  subtypes : Array CardSubtype := #[]
  colors : ColorSet := ColorSet.empty
  power? : Option ValueExpr := none
  toughness? : Option ValueExpr := none
  loyalty? : Option Int := none
  keywords : Array KeywordAbility := #[]
  abilities : Array GrantedAbility
  useCardNameShorthand : Bool := false

/-- Modification applied while creating a token copy or copy effect (CR 707.9; 10 constructors). -/
inductive CopyModification where
  | setName (name : String)
  | setBasePT (power toughness : Int)
  | addSupertypes (supertypes : Array Supertype)
  | addTypes (types : Array CardType)
  | addSubtypes (subtypes : Array CardSubtype)
  | replaceCreatureSubtypes (subtypes : Array CardSubtype)
  | addColors (colors : ColorSet)
  | removeSupertype (supertype : Supertype)
  | addKeywords (keywords : Array KeywordAbility)
  | addAbilities (abilities : Array GrantedAbility)

/-- Unified, parameterized token specification (CR 111 / 707.9; 3 constructors). -/
inductive TokenSpec where
  | predefined (kind : PredefinedToken)
  | custom (spec : CustomTokenSpec)
  | copyOf (ref : ObjectExpr) (mods : Array CopyModification)

/-- Static replacement or prevention effect specification (CR 614 / 615; 24 constructors). -/
inductive StaticReplacementSpec where
  | entersTapped (subject : StaticSubject := .self) (unlessCond? : Option Condition := none)
  | entersTappedUnlessPay (cost : CostSpec)
  | entersUntapped (scope : ObjectFilter)
  | entersTappedAndAttacking (scope : ObjectFilter)
  | entersWithCounters (subject : StaticSubject := .self) (kind : CounterKind)
      (count : ValueExpr) (additional : Bool := false)
  | entersWithDesignation (tag : PermanentDesignationTag)
  | asEntersChoose (kind : AsEntersChoiceKind)
  | asEntersMayCopy (copyFilter : ObjectFilter) (duration : DurationExpr := .indefinite)
      (mods : Array CopyModification) (copyCounters : Bool := false)
  | exileInsteadOfDying (scope : ObjectFilter) (bonusToken? : Option TokenSpec)
  | saveFromDestroyRemoveCounters (scope : ObjectFilter) (kind : CounterKind)
  | multiplyTokens (who : PlayerFilter := .you) (factor : Nat := 2)
  | extraTokenWith (who : PlayerFilter := .you) (triggerPred : ObjectPred)
      (extraToken : TokenSpec) (count : Nat := 1)
  | replaceTokens (who : PlayerFilter := .you) (fromPred : ObjectPred)
      (replacement : TokenSpec)
  | extraDraw (who : PlayerFilter := .you) (drawCount : Nat := 2)
      (exceptFirstDrawStep : Bool := false)
  | extraDrawOnConnive (who : PlayerFilter := .you) (scope : ObjectFilter)
      (extraCards : Nat := 1)
  | modifyCountersPut (scope : ObjectFilter) (kind? : Option CounterKind := none)
      (byPlayer? : Option PlayerFilter := none) (addCount : Nat := 1) (multFactor : Nat := 1)
  | preventDamage (subject : StaticSubject := .self) (amount? : Option ValueExpr := none)
  | preventDamageToPlayer (who : PlayerFilter) (amount? : Option ValueExpr := none)
  | modifyDamage (sourceScope : ObjectFilter) (noncombatOnly : Bool := false)
      (recipient : RecipientFilter := .any) (multiplier : Nat := 1)
      (addAmount : ValueExpr := .const 0)
  | healOtherDamageWhenDealt (subject : StaticSubject := .self)
  | unspentManaBecomesColorless (who : PlayerFilter := .you)
  /-- CR 702.34a: If this card would leave the stack, exile it instead of putting it anywhere else. -/
  | exileOnLeaveStack
  /-- CR 702.190b / 506.2: Enters tapped and attacking the same defender as the returned creature. -/
  | entersTappedAndAttackingSameDefender
  | all (specs : Array StaticReplacementSpec)

/-- Emblem specification (CR 114; functions in the command zone). -/
structure EmblemSpec where
  staticAbilities : Array StaticAbility
  triggeredAbilities : Array TriggeredAbility
  activatedAbilities : Array ActivatedAbility

/-- Creation actions aligned with `RulesEvent.zone` / `ZoneEvent.created` (2 constructors). -/
inductive CreateOp where
  | tokens (who : PlayerExpr) (count : ValueExpr) (spec : TokenSpec) (mods : EnterMods := {})
  | emblem (who : PlayerExpr) (emblem : EmblemSpec)

/-- Delayed triggered ability specification (CR 603.7). -/
structure DelayedTriggerSpec where
  pattern : TriggerPattern
  grouping : BatchGrouping := .perOccurrence
  duration : DurationExpr := .untilEndOfTurn
  oneShot : Bool := true
  interveningIf? : Option Condition := none
  effect : Effect

/-- Modal effect specification (CR 700.2). Unifies modal spells, modal activated
abilities, modal triggered abilities, and resolution-time modal choices. -/
structure ModalSpec where
  minModes : ValueExpr := .const 1
  maxModes : ValueExpr := .const 1
  altCountIf? : Option (Condition × ValueExpr × ValueExpr) := none
  allowRepeat : Bool := false
  chooseAtResolution : Bool := false
  unusedThisTurn : Bool := false
  unusedEver : Bool := false
  modes : Array Effect

/-- Continuous-effect & delayed-trigger installation aligned with
`RulesEvent.continuousEffect` / `RulesEvent.delayedTrigger` (4 constructors). -/
inductive InstallEffectOp where
  | applyContinuous (duration : DurationExpr) (affected : ObjectExpr)
      (mod : ContinuousModification)
  | applyRule (duration : DurationExpr) (rule : RuleModification)
  | applyReplacement (duration : DurationExpr) (spec : StaticReplacementSpec)
  | createDelayedTrigger (spec : DelayedTriggerSpec)

/-- Family-stratified one-shot instruction AST (CR 608; 18 top-level constructors:
10 action wrappers + 8 combinators). -/
inductive Instruction where
  -- 10 action wrappers aligned with `RulesEvent` families
  | moveZone (objs : ObjectExpr) (dest : DestZoneSpec) (verb : ZoneVerb) (mods : MoveMods := {})
  | create (op : CreateOp)
  | permanent (op : PermanentOp)
  | damage (op : DamageOp)
  | life (op : LifeOp)
  | player (op : PlayerOp)
  | turn (op : TurnOp)
  | stack (op : StackOp)
  | installEffect (op : InstallEffectOp)
  | queueReflexiveTrigger (whenDone : TriggeredAbility)
  -- 8 compositional combinators
  | noop
  | seq (steps : Array Instruction)
  | bind (var : VarId) (step : Instruction) (cont : Instruction)
  | ifCond (cond : Condition) (thenBranch : Instruction) (elseBranch : Instruction)
  | optional (who : PlayerExpr) (cost? : Option CostSpec) (onYes : Instruction)
      (onNo : Instruction) (maxTimes : Nat := 1)
  | unlessPays (payer : PlayerExpr) (cost : CostSpec) (ifUnpaid : Instruction)
  | chooseModes (spec : ModalSpec)
  | forEach (iter : ForEachSpec) (var : VarId) (body : Instruction)

/-- Unified one-shot effect shared by spells, activated abilities, Saga chapters,
and triggered abilities (CR 608). `SpellCastKind`, `AbilityCastKind`, targeting
preferences, and default-mode hints are computed purely from `targets` and `body`. -/
structure Effect where
  targets : TargetSpec := .none
  /-- Unified one-shot `Instruction` body. -/
  body : Instruction

/-- Unified activated ability (CR 113.3b / 602 / 605.1a / 606.2–6 / 305.6).
Mana production (`PlayerOp.addMana`) and multiple modes (`Instruction.chooseModes`)
live directly in `effect.body`. -/
structure ActivatedAbility where
  cost : CostSpec := {}
  effect : Effect
  timing : ActivationTiming := .instant
  activeZones : Array ZoneKind := #[.battlefield]
  turnLimit? : Option Nat := none
  lifetimeLimit? : Option Nat := none
  condition? : Option Condition := none
  costReductions : Array ActivationCostReduction := #[]
  tag? : Option ActivationMechanicTag := none

/-- Unified triggered ability (CR 113.3c / 603 / 605.1b / 700.1 / 715.2b,d).
Multiple modes (`Instruction.chooseModes`) live directly in `effect.body`. -/
structure TriggeredAbility where
  word : TriggerWord := .whenever
  pattern : TriggerPattern := TriggerPattern.thisEnters
  grouping : BatchGrouping := .perOccurrence
  interveningIf? : Option Condition := none
  activeZones : Array ZoneKind := #[.battlefield]
  limit : TriggerLimit := .unlimited
  effect : Effect

/-- Compositional Layer 1–7d continuous modification (CR 611.3 / 613; 17 constructors). -/
inductive ContinuousModification where
  | modifyTypes (mod : TypeSetMod)
  | addAllCreatureTypes
  | modifyColors (mod : ColorSetMod)
  | grantKeywords (keywords : Array KeywordAbility)
  | loseKeywords (keywords : Array KeywordAbility)
  | grantActivated (abilities : Array ActivatedAbility)
  | grantTriggered (abilities : Array TriggeredAbility)
  | grantStatic (abilities : Array StaticAbility)
  | copyActivatedFrom (source : ObjectFilter)
  | loseAllAbilities
  | setBasePT (power? toughness? : Option ValueExpr)
  | modifyPT (power toughness : ValueExpr)
  | gainControl (newController : PlayerExpr)
  | exchangeControl (other : ObjectExpr)
  | becomeCopyOf (source : ObjectExpr) (mods : Array CopyModification)
  | applyRule (rule : RuleModification)
  | all (mods : Array ContinuousModification)

/-- CR-stratified static ability (CR 113.3d / 303.4a / 601.2f / 604 / 613 / 614–616;
6 constructors). -/
inductive StaticAbility where
  | characteristicDefining (cda : CdaSpec)
  | continuous (cond? : Option Condition) (scope : ObjectFilter) (mod : ContinuousModification)
  | ruleModifying (cond? : Option Condition) (rule : RuleModification)
  | costModifier (cond? : Option Condition) (appliesTo : CostTargetSpec) (mod : CostModification)
  | replacement (cond? : Option Condition) (spec : StaticReplacementSpec)
  | enchantRestriction (filter : TargetSlot)

end

/-! ### 5. Default Field Values, `Inhabited`, Single-Tuple `BEq` / `Repr`, and `HasTextChange` -/

-- Default values for structure fields whose types belong to the mutual block.
def CustomTokenSpec.abilities._default : Array GrantedAbility := #[]
def EmblemSpec.staticAbilities._default : Array StaticAbility := #[]
def EmblemSpec.triggeredAbilities._default : Array TriggeredAbility := #[]
def EmblemSpec.activatedAbilities._default : Array ActivatedAbility := #[]
def Effect.body._default : Instruction := .noop
def DelayedTriggerSpec.effect._default : Effect := {}
def ModalSpec.modes._default : Array Effect := #[]
def ActivatedAbility.effect._default : Effect := {}
def TriggeredAbility.effect._default : Effect := {}

instance : Inhabited GrantedAbility := ⟨.keyword Keyword.flying⟩
instance : Inhabited CustomTokenSpec := ⟨{}⟩
instance : Inhabited CopyModification := ⟨.setName ""⟩
instance : Inhabited TokenSpec := ⟨.predefined .treasure⟩
instance : Inhabited StaticReplacementSpec := ⟨.all #[]⟩
instance : Inhabited EmblemSpec := ⟨{}⟩
instance : Inhabited CreateOp := ⟨.emblem .you {}⟩
instance : Inhabited DelayedTriggerSpec := ⟨{ pattern := TriggerPattern.thisEnters }⟩
instance : Inhabited ModalSpec := ⟨{}⟩
instance : Inhabited InstallEffectOp := ⟨.applyRule .untilEndOfTurn (.all #[])⟩
instance : Inhabited Instruction := ⟨.noop⟩
instance : Inhabited Effect := ⟨{}⟩
instance : Inhabited ActivatedAbility := ⟨{}⟩
instance : Inhabited TriggeredAbility := ⟨{}⟩
instance : Inhabited ContinuousModification := ⟨.all #[]⟩
instance : Inhabited StaticAbility := ⟨.ruleModifying none (.all #[])⟩

-- Derive the 16-way mutual `BEq` and `Repr` tuples ONCE and project per-type instances.
deriving instance BEq, Repr for GrantedAbility

instance : BEq CustomTokenSpec := ⟨instBEqGrantedAbility.beq_2⟩
instance : BEq CopyModification := ⟨instBEqGrantedAbility.beq_3⟩
instance : BEq TokenSpec := ⟨instBEqGrantedAbility.beq_4⟩
instance : BEq StaticReplacementSpec := ⟨instBEqGrantedAbility.beq_5⟩
instance : BEq EmblemSpec := ⟨instBEqGrantedAbility.beq_6⟩
instance : BEq CreateOp := ⟨instBEqGrantedAbility.beq_7⟩
instance : BEq DelayedTriggerSpec := ⟨instBEqGrantedAbility.beq_8⟩
instance : BEq ModalSpec := ⟨instBEqGrantedAbility.beq_9⟩
instance : BEq InstallEffectOp := ⟨instBEqGrantedAbility.beq_10⟩
instance : BEq Instruction := ⟨instBEqGrantedAbility.beq_11⟩
instance : BEq Effect := ⟨instBEqGrantedAbility.beq_12⟩
instance : BEq ActivatedAbility := ⟨instBEqGrantedAbility.beq_13⟩
instance : BEq TriggeredAbility := ⟨instBEqGrantedAbility.beq_14⟩
instance : BEq ContinuousModification := ⟨instBEqGrantedAbility.beq_15⟩
instance : BEq StaticAbility := ⟨instBEqGrantedAbility.beq_16⟩

instance : Repr CustomTokenSpec := ⟨instReprGrantedAbility.repr_2⟩
instance : Repr CopyModification := ⟨instReprGrantedAbility.repr_3⟩
instance : Repr TokenSpec := ⟨instReprGrantedAbility.repr_4⟩
instance : Repr StaticReplacementSpec := ⟨instReprGrantedAbility.repr_5⟩
instance : Repr EmblemSpec := ⟨instReprGrantedAbility.repr_6⟩
instance : Repr CreateOp := ⟨instReprGrantedAbility.repr_7⟩
instance : Repr DelayedTriggerSpec := ⟨instReprGrantedAbility.repr_8⟩
instance : Repr ModalSpec := ⟨instReprGrantedAbility.repr_9⟩
instance : Repr InstallEffectOp := ⟨instReprGrantedAbility.repr_10⟩
instance : Repr Instruction := ⟨instReprGrantedAbility.repr_11⟩
instance : Repr Effect := ⟨instReprGrantedAbility.repr_12⟩
instance : Repr ActivatedAbility := ⟨instReprGrantedAbility.repr_13⟩
instance : Repr TriggeredAbility := ⟨instReprGrantedAbility.repr_14⟩
instance : Repr ContinuousModification := ⟨instReprGrantedAbility.repr_15⟩
instance : Repr StaticAbility := ⟨instReprGrantedAbility.repr_16⟩

/-! ### 6. Mutual Functorial Layer-3 `HasTextChange` (CR 612 / 613.1c) -/

mutual

private partial def applyTcGranted (tcs : Array TextChange) : GrantedAbility → GrantedAbility
  | .keyword kw => .keyword (HasTextChange.applyTextChanges tcs kw)
  | .activated ab => .activated (applyTcActivated tcs ab)
  | .triggered ab => .triggered (applyTcTriggered tcs ab)
  | .static ab => .static (applyTcStatic tcs ab)

private partial def applyTcCustomToken (tcs : Array TextChange)
    (s : CustomTokenSpec) : CustomTokenSpec :=
  { s with
    subtypes := HasTextChange.applyTextChanges tcs s.subtypes
    colors := HasTextChange.applyTextChanges tcs s.colors
    power? := HasTextChange.applyTextChanges tcs s.power?
    toughness? := HasTextChange.applyTextChanges tcs s.toughness?
    keywords := HasTextChange.applyTextChanges tcs s.keywords
    abilities := s.abilities.map (applyTcGranted tcs) }

private partial def applyTcCopyMod (tcs : Array TextChange) :
    CopyModification → CopyModification
  | .addSubtypes subs => .addSubtypes (HasTextChange.applyTextChanges tcs subs)
  | .replaceCreatureSubtypes subs =>
    .replaceCreatureSubtypes (HasTextChange.applyTextChanges tcs subs)
  | .addColors cols => .addColors (HasTextChange.applyTextChanges tcs cols)
  | .addKeywords kws => .addKeywords (HasTextChange.applyTextChanges tcs kws)
  | .addAbilities abs => .addAbilities (abs.map (applyTcGranted tcs))
  | other => other

private partial def applyTcTokenSpec (tcs : Array TextChange) : TokenSpec → TokenSpec
  | .predefined k => .predefined k
  | .custom s => .custom (applyTcCustomToken tcs s)
  | .copyOf tgt mods =>
    .copyOf (HasTextChange.applyTextChanges tcs tgt) (mods.map (applyTcCopyMod tcs))

private partial def applyTcReplacementSpec (tcs : Array TextChange) :
    StaticReplacementSpec → StaticReplacementSpec
  | .entersTapped s c? =>
    .entersTapped (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs c?)
  | .entersTappedUnlessPay cs => .entersTappedUnlessPay (HasTextChange.applyTextChanges tcs cs)
  | .entersUntapped sc => .entersUntapped (HasTextChange.applyTextChanges tcs sc)
  | .entersTappedAndAttacking sc => .entersTappedAndAttacking (HasTextChange.applyTextChanges tcs sc)
  | .entersWithCounters s k v add =>
    .entersWithCounters (HasTextChange.applyTextChanges tcs s) k
      (HasTextChange.applyTextChanges tcs v) add
  | .entersWithDesignation tag => .entersWithDesignation tag
  | .asEntersChoose kind => .asEntersChoose kind
  | .asEntersMayCopy f dur mods cc =>
    .asEntersMayCopy (HasTextChange.applyTextChanges tcs f)
      (HasTextChange.applyTextChanges tcs dur) (mods.map (applyTcCopyMod tcs)) cc
  | .exileInsteadOfDying sc tok? =>
    .exileInsteadOfDying (HasTextChange.applyTextChanges tcs sc)
      (tok?.map (applyTcTokenSpec tcs))
  | .saveFromDestroyRemoveCounters sc k =>
    .saveFromDestroyRemoveCounters (HasTextChange.applyTextChanges tcs sc) k
  | .multiplyTokens w n => .multiplyTokens (HasTextChange.applyTextChanges tcs w) n
  | .extraTokenWith w tp tok n =>
    .extraTokenWith (HasTextChange.applyTextChanges tcs w)
      (HasTextChange.applyTextChanges tcs tp) (applyTcTokenSpec tcs tok) n
  | .replaceTokens w fp tok =>
    .replaceTokens (HasTextChange.applyTextChanges tcs w)
      (HasTextChange.applyTextChanges tcs fp) (applyTcTokenSpec tcs tok)
  | .extraDraw w n ex => .extraDraw (HasTextChange.applyTextChanges tcs w) n ex
  | .extraDrawOnConnive w sc n =>
    .extraDrawOnConnive (HasTextChange.applyTextChanges tcs w)
      (HasTextChange.applyTextChanges tcs sc) n
  | .modifyCountersPut sc k? bp? n mult =>
    .modifyCountersPut (HasTextChange.applyTextChanges tcs sc) k?
      (HasTextChange.applyTextChanges tcs bp?) n mult
  | .preventDamage s amt? =>
    .preventDamage (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs amt?)
  | .preventDamageToPlayer w amt? =>
    .preventDamageToPlayer (HasTextChange.applyTextChanges tcs w)
      (HasTextChange.applyTextChanges tcs amt?)
  | .modifyDamage sc nc rec mult add =>
    .modifyDamage (HasTextChange.applyTextChanges tcs sc) nc
      (HasTextChange.applyTextChanges tcs rec) mult (HasTextChange.applyTextChanges tcs add)
  | .healOtherDamageWhenDealt s =>
    .healOtherDamageWhenDealt (HasTextChange.applyTextChanges tcs s)
  | .unspentManaBecomesColorless w =>
    .unspentManaBecomesColorless (HasTextChange.applyTextChanges tcs w)
  | .exileOnLeaveStack => .exileOnLeaveStack
  | .entersTappedAndAttackingSameDefender => .entersTappedAndAttackingSameDefender
  | .all xs => .all (xs.map (applyTcReplacementSpec tcs))

private partial def applyTcEmblem (tcs : Array TextChange) (e : EmblemSpec) : EmblemSpec :=
  { staticAbilities := e.staticAbilities.map (applyTcStatic tcs)
    triggeredAbilities := e.triggeredAbilities.map (applyTcTriggered tcs)
    activatedAbilities := e.activatedAbilities.map (applyTcActivated tcs) }

private partial def applyTcCreateOp (tcs : Array TextChange) : CreateOp → CreateOp
  | .tokens w cnt spec mods =>
    .tokens (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs cnt)
      (applyTcTokenSpec tcs spec) (HasTextChange.applyTextChanges tcs mods)
  | .emblem w emb =>
    .emblem (HasTextChange.applyTextChanges tcs w) (applyTcEmblem tcs emb)

private partial def applyTcDelayedTrigger (tcs : Array TextChange)
    (d : DelayedTriggerSpec) : DelayedTriggerSpec :=
  { d with
    pattern := HasTextChange.applyTextChanges tcs d.pattern
    duration := HasTextChange.applyTextChanges tcs d.duration
    interveningIf? := HasTextChange.applyTextChanges tcs d.interveningIf?
    effect := applyTcEffect tcs d.effect }

private partial def applyTcModalSpec (tcs : Array TextChange) (m : ModalSpec) : ModalSpec :=
  { m with
    minModes := HasTextChange.applyTextChanges tcs m.minModes
    maxModes := HasTextChange.applyTextChanges tcs m.maxModes
    altCountIf? := m.altCountIf?.map fun (c, lo, hi) =>
      (HasTextChange.applyTextChanges tcs c,
       HasTextChange.applyTextChanges tcs lo,
       HasTextChange.applyTextChanges tcs hi)
    modes := m.modes.map (applyTcEffect tcs) }

private partial def applyTcInstallOp (tcs : Array TextChange) : InstallEffectOp → InstallEffectOp
  | .applyContinuous dur aff mod =>
    .applyContinuous (HasTextChange.applyTextChanges tcs dur)
      (HasTextChange.applyTextChanges tcs aff) (applyTcContMod tcs mod)
  | .applyRule dur r =>
    .applyRule (HasTextChange.applyTextChanges tcs dur) (HasTextChange.applyTextChanges tcs r)
  | .applyReplacement dur spec =>
    .applyReplacement (HasTextChange.applyTextChanges tcs dur) (applyTcReplacementSpec tcs spec)
  | .createDelayedTrigger spec =>
    .createDelayedTrigger (applyTcDelayedTrigger tcs spec)

private partial def applyTcInstr (tcs : Array TextChange) : Instruction → Instruction
  | .moveZone objs dest verb mods =>
    .moveZone (HasTextChange.applyTextChanges tcs objs) (HasTextChange.applyTextChanges tcs dest)
      verb (HasTextChange.applyTextChanges tcs mods)
  | .create op => .create (applyTcCreateOp tcs op)
  | .permanent op => .permanent (HasTextChange.applyTextChanges tcs op)
  | .damage op => .damage (HasTextChange.applyTextChanges tcs op)
  | .life op => .life (HasTextChange.applyTextChanges tcs op)
  | .player op => .player (HasTextChange.applyTextChanges tcs op)
  | .turn op => .turn (HasTextChange.applyTextChanges tcs op)
  | .stack op => .stack (HasTextChange.applyTextChanges tcs op)
  | .installEffect op => .installEffect (applyTcInstallOp tcs op)
  | .queueReflexiveTrigger ab => .queueReflexiveTrigger (applyTcTriggered tcs ab)
  | .noop => .noop
  | .seq steps => .seq (steps.map (applyTcInstr tcs))
  | .bind v step cont => .bind v (applyTcInstr tcs step) (applyTcInstr tcs cont)
  | .ifCond c t e =>
    .ifCond (HasTextChange.applyTextChanges tcs c) (applyTcInstr tcs t) (applyTcInstr tcs e)
  | .optional w cost? y n mt =>
    .optional (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs cost?)
      (applyTcInstr tcs y) (applyTcInstr tcs n) mt
  | .unlessPays p cost ifUnp =>
    .unlessPays (HasTextChange.applyTextChanges tcs p) (HasTextChange.applyTextChanges tcs cost)
      (applyTcInstr tcs ifUnp)
  | .chooseModes spec => .chooseModes (applyTcModalSpec tcs spec)
  | .forEach iter v body =>
    .forEach (HasTextChange.applyTextChanges tcs iter) v (applyTcInstr tcs body)

private partial def applyTcEffect (tcs : Array TextChange) (e : Effect) : Effect :=
  { targets := HasTextChange.applyTextChanges tcs e.targets
    body := applyTcInstr tcs e.body }

private partial def applyTcActivated (tcs : Array TextChange)
    (ab : ActivatedAbility) : ActivatedAbility :=
  { ab with
    cost := HasTextChange.applyTextChanges tcs ab.cost
    effect := applyTcEffect tcs ab.effect
    condition? := ab.condition?.map (HasTextChange.applyTextChanges tcs)
    costReductions := ab.costReductions.map (HasTextChange.applyTextChanges tcs)
    tag? := ab.tag?.map (HasTextChange.applyTextChanges tcs) }

private partial def applyTcTriggered (tcs : Array TextChange)
    (ab : TriggeredAbility) : TriggeredAbility :=
  { ab with
    pattern := HasTextChange.applyTextChanges tcs ab.pattern
    interveningIf? := ab.interveningIf?.map (HasTextChange.applyTextChanges tcs)
    effect := applyTcEffect tcs ab.effect }

private partial def applyTcContMod (tcs : Array TextChange) :
    ContinuousModification → ContinuousModification
  | .modifyTypes m => .modifyTypes (HasTextChange.applyTextChanges tcs m)
  | .addAllCreatureTypes => .addAllCreatureTypes
  | .modifyColors m => .modifyColors (HasTextChange.applyTextChanges tcs m)
  | .grantKeywords ks => .grantKeywords (HasTextChange.applyTextChanges tcs ks)
  | .loseKeywords ks => .loseKeywords (HasTextChange.applyTextChanges tcs ks)
  | .grantActivated abs => .grantActivated (abs.map (applyTcActivated tcs))
  | .grantTriggered trs => .grantTriggered (trs.map (applyTcTriggered tcs))
  | .grantStatic sas => .grantStatic (sas.map (applyTcStatic tcs))
  | .copyActivatedFrom src => .copyActivatedFrom (HasTextChange.applyTextChanges tcs src)
  | .loseAllAbilities => .loseAllAbilities
  | .setBasePT p? t? =>
    .setBasePT (HasTextChange.applyTextChanges tcs p?) (HasTextChange.applyTextChanges tcs t?)
  | .modifyPT p t =>
    .modifyPT (HasTextChange.applyTextChanges tcs p) (HasTextChange.applyTextChanges tcs t)
  | .gainControl w => .gainControl (HasTextChange.applyTextChanges tcs w)
  | .exchangeControl o => .exchangeControl (HasTextChange.applyTextChanges tcs o)
  | .becomeCopyOf src mods =>
    .becomeCopyOf (HasTextChange.applyTextChanges tcs src) (mods.map (applyTcCopyMod tcs))
  | .applyRule r => .applyRule (HasTextChange.applyTextChanges tcs r)
  | .all ms => .all (ms.map (applyTcContMod tcs))

private partial def applyTcStatic (tcs : Array TextChange) : StaticAbility → StaticAbility
  | .characteristicDefining cda =>
    .characteristicDefining (HasTextChange.applyTextChanges tcs cda)
  | .continuous cond? sc mod =>
    .continuous (HasTextChange.applyTextChanges tcs cond?)
      (HasTextChange.applyTextChanges tcs sc) (applyTcContMod tcs mod)
  | .ruleModifying cond? rule =>
    .ruleModifying (HasTextChange.applyTextChanges tcs cond?)
      (HasTextChange.applyTextChanges tcs rule)
  | .costModifier cond? tgt mod =>
    .costModifier (HasTextChange.applyTextChanges tcs cond?)
      (HasTextChange.applyTextChanges tcs tgt) (HasTextChange.applyTextChanges tcs mod)
  | .replacement cond? spec =>
    .replacement (HasTextChange.applyTextChanges tcs cond?) (applyTcReplacementSpec tcs spec)
  | .enchantRestriction slot =>
    .enchantRestriction (HasTextChange.applyTextChanges tcs slot)

end

instance : HasTextChange GrantedAbility where
  applyTextChanges tcs a := if tcs.isEmpty then a else applyTcGranted tcs a
instance : HasTextChange CustomTokenSpec where
  applyTextChanges tcs s := if tcs.isEmpty then s else applyTcCustomToken tcs s
instance : HasTextChange CopyModification where
  applyTextChanges tcs m := if tcs.isEmpty then m else applyTcCopyMod tcs m
instance : HasTextChange TokenSpec where
  applyTextChanges tcs t := if tcs.isEmpty then t else applyTcTokenSpec tcs t
instance : HasTextChange StaticReplacementSpec where
  applyTextChanges tcs s := if tcs.isEmpty then s else applyTcReplacementSpec tcs s
instance : HasTextChange EmblemSpec where
  applyTextChanges tcs e := if tcs.isEmpty then e else applyTcEmblem tcs e
instance : HasTextChange CreateOp where
  applyTextChanges tcs op := if tcs.isEmpty then op else applyTcCreateOp tcs op
instance : HasTextChange DelayedTriggerSpec where
  applyTextChanges tcs d := if tcs.isEmpty then d else applyTcDelayedTrigger tcs d
instance : HasTextChange ModalSpec where
  applyTextChanges tcs m := if tcs.isEmpty then m else applyTcModalSpec tcs m
instance : HasTextChange InstallEffectOp where
  applyTextChanges tcs op := if tcs.isEmpty then op else applyTcInstallOp tcs op
instance : HasTextChange Instruction where
  applyTextChanges tcs i := if tcs.isEmpty then i else applyTcInstr tcs i
instance : HasTextChange Effect where
  applyTextChanges tcs e := if tcs.isEmpty then e else applyTcEffect tcs e
instance : HasTextChange ActivatedAbility where
  applyTextChanges tcs ab := if tcs.isEmpty then ab else applyTcActivated tcs ab
instance : HasTextChange TriggeredAbility where
  applyTextChanges tcs ab := if tcs.isEmpty then ab else applyTcTriggered tcs ab
instance : HasTextChange ContinuousModification where
  applyTextChanges tcs m := if tcs.isEmpty then m else applyTcContMod tcs m
instance : HasTextChange StaticAbility where
  applyTextChanges tcs s := if tcs.isEmpty then s else applyTcStatic tcs s

/-- Spell ability on a card or sub-face, uniting the resolving `Effect` with
spell-level additional casting costs (CR 113.3a / 118.8). Spell-casting
restrictions and free-cast cost modifiers live on `StaticAbility`
(`.ruleModifying` / `.costModifier`, CR 113.3d / 604.2) while keyword
alternative costs expand via `KeywordAbility.expand` (`ExpandedKeyword.alternativeCosts`). -/
structure SpellAbility where
  effect : Effect := {}
  additionalCosts : Array AdditionalCostSpec := #[]
deriving Repr, Inhabited, BEq

instance : HasTextChange SpellAbility where
  applyTextChanges tcs sa :=
    if tcs.isEmpty then sa
    else
      { effect := HasTextChange.applyTextChanges tcs sa.effect
        additionalCosts := HasTextChange.applyTextChanges tcs sa.additionalCosts }

namespace StaticReplacementSpec

/-- Flatten nested `.all` replacement specs in printed order. -/
partial def flatten : StaticReplacementSpec → Array StaticReplacementSpec
  | .all xs => xs.foldl (fun acc x => acc ++ flatten x) #[]
  | x => #[x]

end StaticReplacementSpec

namespace Instruction

/-- Flatten nested `.seq` instructions, eliding `.noop` steps. -/
partial def flatten : Instruction → Array Instruction
  | .noop => #[]
  | .seq steps => steps.foldl (fun acc s => acc ++ flatten s) #[]
  | i => #[i]

/-- Smart sequence constructor flattening nested `.seq` and eliding `.noop`. -/
def mkSeq (steps : Array Instruction) : Instruction :=
  let flat := steps.foldl (fun acc s => acc ++ flatten s) #[]
  match flat.toList with
  | [] => .noop
  | [s] => s
  | _ => .seq flat

end Instruction

end Mtg.Engine
