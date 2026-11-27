import Mtg.Engine.Card.Expr

/-!
# Unified trigger patterns and batch groupings (CR 603 / 605.1b / 700.1 / 715.2b)

Declarative trigger matching over `RulesEvent` families using the Layer-1
expression algebra (`ObjectPred`, `PlayerFilter`, `RecipientFilter`,
`Condition`).

Includes:
- `TriggerWord` (`.when` / `.whenever` / `.at`, CR 603.1);
- `BatchGrouping` (CR 603.2c / 700.1 / 715.2b counter thresholds);
- `TriggerLimit` (CR 603.2h per-turn caps);
- `TriggerPattern` (27 constructors, `< 40`), with structural:
  - `usesLookBack` (exact CR 603.10a–f look-back classification),
  - `triggersOnActivatedManaAbilityOrManaAdded` (CR 605.1b criterion 2),
  - `isAnotherAbilityTriggering` (CR 603.3b part 2),
  - functorial `HasTextChange`, and canonical `ToOracle`;
- Roman numeral chapter helpers (`parseRomanNumeral`, `parseChapterNumbers`,
  `romanNumeral`, `formatChapterRoman`, CR 715.2).
-/

namespace Mtg.Engine

/-! ## Roman numeral helpers for Saga chapters (CR 715.2) -/

/-- Parse one Roman chapter numeral (`I`–`X`). Returns `0` when unrecognized. -/
def parseRomanNumeral (s : String) : Nat :=
  match s.replace " " "" with
  | "I" => 1
  | "II" => 2
  | "III" => 3
  | "IV" => 4
  | "V" => 5
  | "VI" => 6
  | "VII" => 7
  | "VIII" => 8
  | "IX" => 9
  | "X" => 10
  | _ => 0

/-- Chapter numbers on a printed Saga line (`I`, `III, IV`, `I, II, III, IV`). -/
def parseChapterNumbers (roman : String) : Array Nat :=
  (roman.splitOn ",").toArray |>.map parseRomanNumeral |>.filter (· != 0)

/-- Roman numeral for a chapter count (`4` → `IV`). `0` is empty. -/
def romanNumeral (n : Nat) : String :=
  Id.run do
    let mut n := n
    let mut acc : String := ""
    let digits : Array (Nat × String) := #[
      (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")
    ]
    for (v, s) in digits do
      while n >= v do
        acc := acc ++ s
        n := n - v
    return acc

/-- Format a chapter number list as `"I"` or `"II, III"` (CR 715.2). -/
def formatChapterRoman (ns : Array Nat) : String :=
  String.intercalate ", " (ns.toList.map romanNumeral)

/-! ## Core trigger metadata enums -/

/-- Leading word of a triggered ability (CR 603.1). -/
inductive TriggerWord where
  | when
  | whenever
  | at
deriving DecidableEq, Repr, Inhabited, BEq

namespace TriggerWord

def toOracleStr : TriggerWord → String
  | .when => "When"
  | .whenever => "Whenever"
  | .at => "At"

end TriggerWord

instance : ToOracle TriggerWord where
  toOracle ctx w :=
    let s := w.toOracleStr
    if ctx.capitalize then s else s.map Char.toLower

/-- How a triggered ability batches simultaneous occurrences in a rules-event
batch (CR 603.2c / 700.1 / 715.2b). -/
inductive BatchGrouping where
  /-- Triggers once per matching event occurrence (CR 603.2c). -/
  | perOccurrence
  /-- Triggers once per batch when one or more matching events occur (CR 700.1 / 603.2c). -/
  | oncePerBatch
  /-- Triggers once per distinct matching player in the batch (CR 700.1). -/
  | perPlayerInBatch
  /-- Triggers once per distinct matching source/object in the batch (CR 603.2c). -/
  | perSourceInBatch
  /-- CR 715.2b counter-threshold trigger (Sagas / Plans): fires for each `n ∈ chapters`
  such that the permanent had `< n` `kind` counters before the event and `≥ n` after. -/
  | counterThreshold (kind : CounterKind) (chapters : Array Nat)
deriving Repr, Inhabited, BEq

/-- Per-turn frequency cap on a triggered ability (CR 603.2h). -/
inductive TriggerLimit where
  | unlimited
  /-- "This ability triggers only once each turn." -/
  | onceEachTurn
  /-- "Do this only once each turn." (keeps triggering until the controller chooses
  to perform the optional action, MSH 69). -/
  | optionalOnceEachTurn
  /-- Triggers only on the `n`th occurrence of the event each turn (e.g. second card drawn). -/
  | nthEachTurn (n : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-! ## Stratified sub-specs for `TriggerPattern` -/

/-- Whose turn a step/phase trigger watches (CR 500 / 603.1). -/
inductive TurnOwnerSpec where
  | player (who : PlayerFilter)
  | controllerOf (obj : ObjectExpr)
deriving Repr, Inhabited, BEq

instance : HasTextChange TurnOwnerSpec where
  applyTextChanges tcs spec :=
    if tcs.isEmpty then spec
    else
      match spec with
      | .player pf => .player (HasTextChange.applyTextChanges tcs pf)
      | .controllerOf oe => .controllerOf (HasTextChange.applyTextChanges tcs oe)

/-- Endpoint zone constraint for `TriggerPattern.zoneChange`. -/
inductive ZoneEndpointSpec where
  | any
  | inZones (zones : ZoneSetSpec)
  | notIn (zone : ZoneKind)
deriving Repr, Inhabited, BEq

namespace ZoneEndpointSpec

/-- Convenience constructor for a single zone kind with unrestricted owner. -/
def ofZone (z : ZoneKind) : ZoneEndpointSpec :=
  .inZones { zones := #[z], owner := .any }

/-- Convenience constructor for a single zone kind owned by `who`. -/
def ofOwnedZone (z : ZoneKind) (who : PlayerFilter) : ZoneEndpointSpec :=
  .inZones { zones := #[z], owner := .matching who }

def battlefield : ZoneEndpointSpec := ofZone .battlefield
def graveyard : ZoneEndpointSpec := ofZone .graveyard
def yourGraveyard : ZoneEndpointSpec := ofOwnedZone .graveyard .you
def hand : ZoneEndpointSpec := ofZone .hand
def library : ZoneEndpointSpec := ofZone .library
def exile : ZoneEndpointSpec := ofZone .exile

/-- True iff this endpoint matches exclusively `.battlefield`. -/
def isBattlefieldOnly : ZoneEndpointSpec → Bool
  | .inZones zs => !zs.zones.isEmpty && zs.zones.all (· == .battlefield)
  | _ => false

/-- True iff this endpoint matches exclusively `.graveyard`. -/
def isGraveyardOnly : ZoneEndpointSpec → Bool
  | .inZones zs => !zs.zones.isEmpty && zs.zones.all (· == .graveyard)
  | _ => false

/-- True iff every zone permitted by this endpoint is a public zone (CR 400.2). -/
def isPublicOnly : ZoneEndpointSpec → Bool
  | .inZones zs => !zs.zones.isEmpty && zs.zones.all ZoneKind.isPublic
  | _ => false

/-- True iff this endpoint can target a hand or library zone (CR 603.10a). -/
def targetsHandOrLibrary : ZoneEndpointSpec → Bool
  | .inZones zs => zs.zones.any (fun z => z == .hand || z == .library)
  | _ => false

/-- True iff concrete `Zone` `z` satisfies this endpoint when owner filtering is
not needed (owner filtering on `inZones` is checked by callers with `Game`). -/
def matchesZoneKind (spec : ZoneEndpointSpec) (zk : ZoneKind) : Bool :=
  match spec with
  | .any => true
  | .inZones zs => zs.zones.contains zk
  | .notIn forbidden => zk != forbidden

end ZoneEndpointSpec

instance : HasTextChange ZoneEndpointSpec where
  applyTextChanges tcs spec :=
    if tcs.isEmpty then spec
    else
      match spec with
      | .inZones zs => .inZones (HasTextChange.applyTextChanges tcs zs)
      | other => other

/-- Attack destination filter for `TriggerPattern.attacks` (CR 508.3). -/
inductive AttackTargetFilter where
  | any
  | player (who : PlayerFilter)
  | playerOrPlaneswalker (who : PlayerFilter)
deriving Repr, Inhabited, BEq

instance : HasTextChange AttackTargetFilter where
  applyTextChanges tcs f :=
    if tcs.isEmpty then f
    else
      match f with
      | .any => .any
      | .player pf => .player (HasTextChange.applyTextChanges tcs pf)
      | .playerOrPlaneswalker pf => .playerOrPlaneswalker (HasTextChange.applyTextChanges tcs pf)

/-- Player action watched by `TriggerPattern.playerAction`. -/
inductive PlayerActionTrigger where
  | scry
  | surveil
  | proliferate
  | ringTempts
  | chooseRingBearer
  | manaAdded
  | losesGame
deriving DecidableEq, Repr, Inhabited, BEq

/-- Activated-ability category watched by `TriggerPattern.activateAbility`. -/
inductive ActivatedTriggerKind where
  | any
  | loyalty (minRemoved : Nat := 0)
  | manaAbility
  | nonMana
deriving DecidableEq, Repr, Inhabited, BEq

/-- Stack source category watched by `TriggerPattern.becomesTarget`. -/
inductive TargetingSourceKind where
  | spellOrAbility
  | spell
  | ability
deriving DecidableEq, Repr, Inhabited, BEq

/-- Target subject watched by `TriggerPattern.becomesTarget`. -/
inductive TargetSubjectFilter where
  | object (pred : ObjectPred)
  | playerOrPermanent
deriving Repr, Inhabited, BEq

instance : HasTextChange TargetSubjectFilter where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      match s with
      | .object p => .object (HasTextChange.applyTextChanges tcs p)
      | .playerOrPermanent => .playerOrPermanent

/-! ## Unified `TriggerPattern` (27 constructors) -/

/-- Declarative trigger condition matching `RulesEvent` families (CR 603). -/
inductive TriggerPattern where
  /-- An object moves between zones (CR 603.6a, 603.6c, 603.10a, 700.4). -/
  | zoneChange (subject : ObjectPred) (fromZone toZone : ZoneEndpointSpec)
      (verb? : Option ZoneVerb := none) (actor? : Option PlayerFilter := none)
  /-- A player creates one or more matching tokens (CR 111 / 701.7). -/
  | createTokens (who : PlayerFilter) (tokenPred : ObjectPred := .anyObject)
  /-- A player sacrifices a matching permanent (CR 603.10a / 701.21). -/
  | sacrifice (who : PlayerFilter) (subject : ObjectPred)
  /-- A player draws a card (CR 121). `exceptFirstDrawStep` excludes the first
  card drawn in each of that player's draw steps. -/
  | drawCard (who : PlayerFilter) (exceptFirstDrawStep : Bool := false)
  /-- A player discards a matching card (CR 701.9). `mustBeCycle := true` matches
  only discards paying a cycling cost (CR 702.29a). -/
  | discard (who : PlayerFilter) (cardPred : ObjectPred := .anyObject)
      (mustBeCycle : Bool := false)
  /-- A matching permanent becomes tapped (CR 603.2e). -/
  | becomesTapped (subject : ObjectPred) (onlyDuringYourTurn : Bool := false)
      (firstTimeThisTurn : Bool := false) (costKind? : Option CostKind := none)
  /-- A matching permanent becomes untapped (CR 603.2e). -/
  | becomesUntapped (subject : ObjectPred)
  /-- A matching permanent phases out (CR 603.10b / 702.26). -/
  | phasesOut (subject : ObjectPred)
  /-- An attachment becomes unattached (CR 603.10c). -/
  | becomesUnattached (attachment : ObjectPred) (fromHost : ObjectPred := .anyObject)
  /-- A player loses control of a permanent (CR 603.10d). -/
  | controlLost (subject : ObjectPred) (formerController : PlayerFilter := .you)
  /-- One or more counters are put on a matching permanent (CR 122.6 / 715.2b). -/
  | putCounters (putter? : Option PlayerFilter) (counterKind? : Option CounterKind)
      (subject : ObjectPred)
  /-- One or more matching creatures are declared as attackers (CR 508.3). -/
  | attacks (attacker : ObjectPred) (target : AttackTargetFilter := .any)
      (alone : Bool := false) (minAttackers : Nat := 1)
      (minTotalPower? : Option Int := none) (countIntoLastKnown : Bool := false)
  /-- A matching creature is declared as a blocker (CR 509.1). -/
  | blocks (blocker : ObjectPred)
  /-- A matching attacking creature becomes blocked (CR 509.3c). -/
  | becomesBlocked (attacker : ObjectPred)
  /-- Damage is dealt from `source` to `recipient` (CR 120 / 510.2). -/
  | damageDealt (source : ObjectPred := .anyObject) (recipient : RecipientFilter := .any)
      (combatOnly : Bool := false) (noncombatOnly : Bool := false)
      (duringYourTurn : Bool := false)
  /-- A player gains life (CR 119). -/
  | gainLife (who : PlayerFilter)
  /-- A player loses life (CR 119). -/
  | loseLife (who : PlayerFilter)
  /-- A player casts a matching spell (CR 601.2i). -/
  | castSpell (caster : PlayerFilter) (spell : ObjectPred := .anyObject)
      (fromZone? : Option ZoneKind := none) (manaSpent? : Option ManaSpentPred := none)
      (mustBePrepared : Bool := false) (nthOfFilter? : Option Nat := none)
      (targets? : Option RecipientFilter := none)
  /-- A player activates an ability of a matching source (CR 602 / 605.1b). -/
  | activateAbility (activator : PlayerFilter) (source : ObjectPred := .anyObject)
      (kind : ActivatedTriggerKind := .any)
  /-- A permanent or player becomes the target of a spell or ability (CR 603.2). -/
  | becomesTarget (subject : TargetSubjectFilter) (byController : PlayerFilter)
      (sourceKind : TargetingSourceKind := .spellOrAbility)
  /-- A spell is countered (CR 603.10e). -/
  | spellCountered (spell : ObjectPred := .anyObject)
  /-- A player performs a keyword/resource action (scry, surveil, proliferate, Ring,
  mana added, or loses the game per CR 603.10f). -/
  | playerAction (who : PlayerFilter) (action : PlayerActionTrigger)
  /-- Beginning of a step on a matching player's turn (CR 500 / 603.1). -/
  | stepBegins (step : Step) (whoseTurn : TurnOwnerSpec)
  /-- A stack object resolves (e.g. final chapter ability of a Saga you control). -/
  | stackObjectResolves (pred : ObjectPred) (finalSagaChapterOnly : Bool := false)
  /-- Another triggered ability triggers (CR 603.3b part 2). -/
  | abilityTriggers (source : ObjectPred := .anyObject)
  /-- Non-intervening trigger-time condition (CR 603.2: checked when the event
  occurs, NOT rechecked on resolution — e.g. `"while you control..."`,
  `"while you're the monarch"`, CR 702.186 `∞` harnessed). -/
  | whenCond (inner : TriggerPattern) (cond : Condition)
  /-- Disjunction of trigger patterns (e.g., `"enters or attacks"`, `"enters or dies"`).
  Each disjunct consults `pre` or `post` according to its own `usesLookBack`. -/
  | or (left right : TriggerPattern)
deriving Repr, Inhabited, BEq

namespace TriggerPattern

/-! ### Structural CR queries -/

/-- Exact CR 603.10a–f look-back classification:
- **603.10a**: leaves the battlefield (including `"dies"`), is sacrificed,
  leaves a graveyard, or a public object is put into a hand or library;
- **603.10b**: phases out;
- **603.10c**: becomes unattached;
- **603.10d**: a player loses control of an object;
- **603.10e**: a spell is countered;
- **603.10f**: a player loses the game.

Becoming tapped/untapped (**CR 603.2e**), damage dealt, entering the battlefield,
drawing/discarding cards, and casting spells are **not** look-back triggers and
evaluate `post`. For `.or a b`, callers should flatten disjuncts via `flattenOr`
so each disjunct evaluates on `pre` or `post` independently. -/
def usesLookBack : TriggerPattern → Bool
  | .zoneChange _ fromZ toZ verb? _ =>
    verb? == some .sacrifice ||
      (fromZ.isBattlefieldOnly && !toZ.isBattlefieldOnly) ||
      (fromZ.isGraveyardOnly && !toZ.isGraveyardOnly) ||
      (fromZ.isPublicOnly && toZ.targetsHandOrLibrary)
  | .sacrifice _ _ => true
  | .phasesOut _ => true
  | .becomesUnattached _ _ => true
  | .controlLost _ _ => true
  | .spellCountered _ => true
  | .playerAction _ .losesGame => true
  | .whenCond inner _ => inner.usesLookBack
  | .or a b => a.usesLookBack || b.usesLookBack
  | _ => false

/-- CR 605.1b criterion 2: true iff this trigger pattern triggers exclusively
from the activation or resolution of an activated mana ability or from mana
being added to a player's mana pool. -/
def triggersOnActivatedManaAbilityOrManaAdded : TriggerPattern → Bool
  | .activateAbility _ _ .manaAbility => true
  | .playerAction _ .manaAdded => true
  | .whenCond inner _ => inner.triggersOnActivatedManaAbilityOrManaAdded
  | .or a b =>
    a.triggersOnActivatedManaAbilityOrManaAdded &&
      b.triggersOnActivatedManaAbilityOrManaAdded
  | _ => false

/-- CR 603.3b part 2: true when this trigger's condition is another ability triggering. -/
def isAnotherAbilityTriggering : TriggerPattern → Bool
  | .abilityTriggers _ => true
  | .whenCond inner _ => inner.isAnotherAbilityTriggering
  | .or a b => a.isAnotherAbilityTriggering || b.isAnotherAbilityTriggering
  | _ => false

/-- True when this trigger is caused by a creature attacking (e.g. Windcrag Siege Mardu). -/
def isAttackTrigger : TriggerPattern → Bool
  | .attacks .. => true
  | .whenCond inner _ => inner.isAttackTrigger
  | .or a b => a.isAttackTrigger || b.isAttackTrigger
  | _ => false

/-- Collect all outermost CR 603.2 `.whenCond` conditions wrapping a pattern. -/
def outerWhenConds : TriggerPattern → Array Condition
  | .whenCond inner c => inner.outerWhenConds.push c
  | _ => #[]

/-- Flatten `.or` disjunctions into atomic `(pattern, whenConds)` branches,
recursively distributing any enclosing `.whenCond` over `.or` so each atomic
branch can independently check `usesLookBack` (`pre` vs `post`) and evaluate
every attached CR 603.2 condition. -/
def flattenDisjuncts : TriggerPattern → Array (TriggerPattern × Array Condition)
  | .or a b => a.flattenDisjuncts ++ b.flattenDisjuncts
  | .whenCond inner c =>
    inner.flattenDisjuncts.map fun (atom, conds) => (atom, conds.push c)
  | other => #[(other, #[])]

/-- Flatten `.or` disjunctions into individual branch patterns, distributing
any enclosing `.whenCond` over `.or` so each branch can independently check
`usesLookBack` (`pre` vs `post`). -/
def flattenOr : TriggerPattern → Array TriggerPattern
  | .or a b => a.flattenOr ++ b.flattenOr
  | .whenCond inner c => inner.flattenOr.map (TriggerPattern.whenCond · c)
  | other => #[other]

/-- Check whether `p` structurally contains a pattern satisfying `pred`. -/
def anyBranch (p : TriggerPattern) (pred : TriggerPattern → Bool) : Bool :=
  p.flattenOr.any pred || p.flattenDisjuncts.any (fun (atom, _) => pred atom)

/-- Default leading trigger word for canonical Oracle rendering (CR 603.1). -/
def defaultWord : TriggerPattern → TriggerWord
  | .stepBegins _ _ => .at
  | .zoneChange (.sameAs .this) _ _ _ _
  | .zoneChange (.all #[.sameAs .this, .hasType .creature]) _ _ _ _
  | .zoneChange (.sameAs .attachedHost) _ (.inZones { zones := #[.graveyard], .. }) _ _
  | .castSpell _ (.sameAs .this) _ _ _ _ _
  | .spellCountered (.sameAs .this)
  | .discard _ (.sameAs .this) _
  | .putCounters none (some .lore) (.sameAs .this)
  | .putCounters none (some .plan) (.sameAs .this) => .when
  | .whenCond inner _ => inner.defaultWord
  | .or a b =>
    match a.defaultWord, b.defaultWord with
    | .when, .when => .when
    | _, _ => .whenever
  | _ => .whenever

/-- Human-readable stack log label for this trigger pattern. -/
def label : TriggerPattern → String
  | .zoneChange subj fromZ toZ _ _ =>
    if toZ.isBattlefieldOnly then
      match subj with
      | .sameAs .this => "enters trigger"
      | .all #[.hasType .land, .controlledBy .you] => "landfall trigger"
      | .all #[.hasSubtype (.literal .forest), .controlledBy .you] => "forest-enters trigger"
      | .all #[.hasSubtype (.literal .mountain), .controlledBy .you] => "mountain-enters trigger"
      | .all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy .you] =>
        s!"{s.englishName}-enters trigger"
      | .all #[.hasSubtype (.literal s), .controlledBy .you] =>
        s!"{s.englishName}-enters trigger"
      | .all #[.hasType .artifact, .controlledBy .you] => "artifact-enters trigger"
      | .all #[.isToken true, .controlledBy .you] => "token-enters trigger"
      | .all #[.hasType .creature, .controlledBy .you] => "creature-enters trigger"
      | .all #[.otherThan .this, .hasType .creature, .controlledBy .you] => "creature-enters trigger"
      | _ => "enters trigger"
    else if fromZ.isBattlefieldOnly && toZ.isGraveyardOnly then
      match subj with
      | .sameAs .this | .all #[.sameAs .this, .hasType .creature]
      | .sameAs .attachedHost => "dies trigger"
      | _ => "dies trigger"
    else if fromZ.isBattlefieldOnly && toZ == .hand then "return trigger"
    else if fromZ.isBattlefieldOnly then "leaves trigger"
    else if fromZ.isGraveyardOnly then "leaves-graveyard trigger"
    else if toZ.isGraveyardOnly then "graveyard trigger"
    else "zone-change trigger"
  | .createTokens _ _ => "token-creation trigger"
  | .sacrifice _ _ => "sacrifice trigger"
  | .drawCard _ _ => "draw trigger"
  | .discard _ _ true => "cycle trigger"
  | .discard _ _ false => "discard trigger"
  | .becomesTapped _ _ _ (some .teamwork) => "teamwork-tap trigger"
  | .becomesTapped (.sameAs .this) _ _ _ => "becomes-tapped trigger"
  | .becomesTapped (.sameAs .attachedHost) _ _ _ => "equipped-tapped trigger"
  | .becomesTapped _ _ _ _ => "tap trigger"
  | .becomesUntapped _ => "untap trigger"
  | .phasesOut _ => "phases-out trigger"
  | .becomesUnattached _ _ => "unattach trigger"
  | .controlLost _ _ => "control-lost trigger"
  | .putCounters _ (some .lore) (.sameAs .this) => "saga chapter"
  | .putCounters _ (some .plan) (.sameAs .this) => "plan trigger"
  | .putCounters _ _ _ => "put-counters trigger"
  | .attacks _ _ true _ _ _ => "attacks-alone trigger"
  | .attacks _ _ _ _ (some _) _ => "total-power-attack trigger"
  | .attacks _ _ _ _ _ _ => "attack trigger"
  | .blocks _ => "blocks trigger"
  | .becomesBlocked _ => "becomes-blocked trigger"
  | .damageDealt _ (.object { pred := .sameAs .this, .. }) false true _ => "noncombat-damage trigger"
  | .damageDealt _ (.object _) _ _ _ => "dealt-damage trigger"
  | .damageDealt _ _ true _ _ => "combat-damage trigger"
  | .damageDealt _ _ _ _ _ => "damage trigger"
  | .gainLife _ => "gain-life trigger"
  | .loseLife _ => "lose-life trigger"
  | .castSpell _ (.sameAs .this) _ _ _ _ _ => "cast trigger"
  | .castSpell _ _ _ (some .fromTreasure) _ _ _ => "treasure-cast trigger"
  | .castSpell _ _ _ _ _ _ _ => "cast trigger"
  | .activateAbility _ _ (.loyalty _) => "loyalty trigger"
  | .activateAbility _ _ _ => "activate-ability trigger"
  | .becomesTarget .playerOrPermanent _ _ => "you-target trigger"
  | .becomesTarget _ _ _ => "becomes-target trigger"
  | .spellCountered _ => "countered-spell trigger"
  | .playerAction _ .scry => "scry trigger"
  | .playerAction _ .surveil => "surveil trigger"
  | .playerAction _ .proliferate => "proliferate trigger"
  | .playerAction _ .ringTempts => "Ring-tempts trigger"
  | .playerAction _ .chooseRingBearer => "Ring-bearer trigger"
  | .playerAction _ .manaAdded => "mana trigger"
  | .playerAction _ .losesGame => "player-loses trigger"
  | .stepBegins .upkeep _ => "upkeep trigger"
  | .stepBegins .draw _ => "draw-step trigger"
  | .stepBegins .precombatMain _ => "main-phase trigger"
  | .stepBegins .beginningOfCombat _ => "begin-combat trigger"
  | .stepBegins .end _ => "end-step trigger"
  | .stepBegins _ _ => "step trigger"
  | .stackObjectResolves _ true => "saga-chapter trigger"
  | .stackObjectResolves _ false => "resolution trigger"
  | .abilityTriggers _ => "ability-trigger trigger"
  | .whenCond inner _ => inner.label
  | .or a _ => a.label

/-! ### Canonical smart constructors -/

/-- Shorthand for a battlefield `ObjectFilter` over `pred`. -/
def bfFilter (pred : ObjectPred) : ObjectFilter :=
  { zones := .battlefield, pred }

/-- Enters the battlefield from any non-battlefield zone (CR 603.6a). -/
def permanentEnters (subject : ObjectPred) : TriggerPattern :=
  .zoneChange subject (.notIn .battlefield) .battlefield

/-- Dies (moves from battlefield to a graveyard, CR 700.4 / 603.10a). -/
def permanentDies (subject : ObjectPred) : TriggerPattern :=
  .zoneChange subject .battlefield .graveyard

/-- Leaves the battlefield (CR 603.6c / 603.10a). -/
def permanentLeaves (subject : ObjectPred) : TriggerPattern :=
  .zoneChange subject .battlefield (.notIn .battlefield)

def thisEnters : TriggerPattern := permanentEnters (.sameAs .this)
def thisDies : TriggerPattern := permanentDies (.sameAs .this)
def thisCreatureDies : TriggerPattern := permanentDies (.all #[.sameAs .this, .hasType .creature])
def thisLeaves : TriggerPattern := permanentLeaves (.sameAs .this)
def thisAttacks : TriggerPattern := .attacks (.sameAs .this)
def thisAttacksAlone : TriggerPattern := .attacks (.sameAs .this) .any (alone := true)
def thisBecomesBlocked : TriggerPattern := .becomesBlocked (.sameAs .this)
def thisBecomesTapped : TriggerPattern := .becomesTapped (.sameAs .this)
def thisTappedForTeamwork : TriggerPattern :=
  .becomesTapped (.sameAs .this) (costKind? := some .teamwork)
def thisDealtDamage : TriggerPattern := .damageDealt .anyObject (.object (bfFilter (.sameAs .this)))
def thisDealtNoncombatDamage : TriggerPattern :=
  .damageDealt .anyObject (.object (bfFilter (.sameAs .this))) (noncombatOnly := true)
def thisDealsCombatDamageToPlayer : TriggerPattern :=
  .damageDealt (.sameAs .this) (.player .any) (combatOnly := true)
def thisDealsCombatDamageToPlayerOrBattle : TriggerPattern :=
  .damageDealt (.sameAs .this) (.playerOrObject .any (bfFilter (.hasType .battle))) (combatOnly := true)
def thisDealsCombatDamageToPlayerOrPlaneswalker : TriggerPattern :=
  .damageDealt (.sameAs .this) (.playerOrObject .any (bfFilter (.hasType .planeswalker))) (combatOnly := true)
def thisBecomesTargetByOpponent : TriggerPattern :=
  .becomesTarget (.object (.sameAs .this)) .opponent .spellOrAbility
def spellTargetsThis : TriggerPattern :=
  .becomesTarget (.object (.sameAs .this)) .any .spell
def thisCast : TriggerPattern := .castSpell .you (.sameAs .this)
def thisDiscarded : TriggerPattern := .discard .you (.sameAs .this)
def thisCycled : TriggerPattern := .discard .you (.sameAs .this) (mustBeCycle := true)

def enchantedDies : TriggerPattern := permanentDies (.sameAs .attachedHost)
def equippedAttacks : TriggerPattern := .attacks (.sameAs .attachedHost)
def equippedAttacksAlone : TriggerPattern := .attacks (.sameAs .attachedHost) .any (alone := true)
def equippedBecomesTapped : TriggerPattern := .becomesTapped (.sameAs .attachedHost)
def equippedDealsCombatDamageToPlayer : TriggerPattern :=
  .damageDealt (.sameAs .attachedHost) (.player .any) (combatOnly := true)
def enchantedAttacksOrBlocks : TriggerPattern :=
  .or (.attacks (.sameAs .attachedHost)) (.blocks (.sameAs .attachedHost))

def landYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.hasType .land, .controlledBy .you])
def subtypeYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.all #[.hasSubtype (.literal sub), .controlledBy .you])
def forestYouControlEnters : TriggerPattern := subtypeYouControlEnters .forest
def mountainYouControlEnters : TriggerPattern := subtypeYouControlEnters .mountain
def artifactYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.hasType .artifact, .controlledBy .you])
def creatureYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.hasType .creature, .controlledBy .you])
def equipmentYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.hasType .artifact, .hasSubtype (.literal .equipment), .controlledBy .you])
def tokenYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.isToken true, .controlledBy .you])

def anotherCreatureYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])
def anotherArtifactYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .hasType .artifact, .controlledBy .you])
def anotherSubtypeYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])
def anotherNontokenCreatureYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .isToken false, .hasType .creature, .controlledBy .you])
def anotherNontokenArtifactYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .isToken false, .hasType .artifact, .controlledBy .you])
def anotherNontokenSubtypeYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .isToken false, .hasSubtype (.literal sub), .controlledBy .you])
def anotherVillainOrArtifactYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .controlledBy .you,
    .any #[.hasSubtype (.literal .villain), .hasType .artifact]])
def anotherCreatureOrPlaneswalkerYouControlEnters : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .controlledBy .you,
    .any #[.hasType .creature, .hasType .planeswalker]])
def thisOrAnotherCreatureYouControlEnters : TriggerPattern :=
  permanentEnters (.any #[.sameAs .this, .all #[.hasType .creature, .controlledBy .you]])
def thisOrNontokenSubtypeYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal sub), .controlledBy .you]])
def thisOrAnotherSubtypeYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.any #[.sameAs .this, .all #[.hasSubtype (.literal sub), .controlledBy .you]])
def anotherSubtypeOrEquipmentYouControlEnters (sub : CardSubtype) : TriggerPattern :=
  permanentEnters (.all #[.otherThan .this, .controlledBy .you,
    .any #[.hasSubtype (.literal sub), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]])
def creatureOpponentControlsEnters : TriggerPattern :=
  permanentEnters (.all #[.hasType .creature, .controlledBy .opponent])
def creatureYouControlPowerAtLeastEnters (n : Int) : TriggerPattern :=
  permanentEnters (.all #[.hasType .creature, .controlledBy .you, .stat .power .ge (.const n)])

def creatureYouControlDies : TriggerPattern :=
  permanentDies (.all #[.hasType .creature, .controlledBy .you])
def nontokenCreatureYouControlDies : TriggerPattern :=
  permanentDies (.all #[.isToken false, .hasType .creature, .controlledBy .you])
def otherCreaturesDie : TriggerPattern :=
  permanentDies (.all #[.otherThan .this, .hasType .creature])
def anotherCreatureOrPlaneswalkerYouControlDies : TriggerPattern :=
  permanentDies (.all #[.otherThan .this, .controlledBy .you,
    .any #[.hasType .creature, .hasType .planeswalker]])
def anotherGoblinOrcArmyYouControlDies : TriggerPattern :=
  permanentDies (.all #[.otherThan .this, .hasType .creature, .controlledBy .you,
    .any #[.hasSubtype (.literal .goblin), .hasSubtype (.literal .orc), .hasSubtype (.literal .army)]])
def villainYouControlDies : TriggerPattern :=
  permanentDies (.all #[.hasType .creature, .hasSubtype (.literal .villain), .controlledBy .you])
def attackingCreatureYouControlDies : TriggerPattern :=
  permanentDies (.all #[.hasType .creature, .combatRole .attacking, .controlledBy .you])
def anotherCreatureYouControlLeaves : TriggerPattern :=
  permanentLeaves (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])
def anotherNonlandYouControlReturnedToHand : TriggerPattern :=
  .zoneChange (.all #[.otherThan .this, .not (.hasType .land), .controlledBy .you])
    .battlefield .hand
def creatureCardLeavesYourGy : TriggerPattern :=
  .zoneChange (.all #[.hasType .creature, .isKind .card]) .yourGraveyard (.notIn .graveyard)
def creatureCardPutIntoYourGy : TriggerPattern :=
  .zoneChange (.all #[.hasType .creature, .isKind .card]) .any .yourGraveyard

def youAttack : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you])
def youAttackWithSubtype (sub : CardSubtype) : TriggerPattern :=
  .attacks (.all #[.hasSubtype (.literal sub), .controlledBy .you])
def youAttackWithTwoOrMoreToPlayer : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you]) (.player .any) (minAttackers := 2)
def youAttackWithTotalPower (n : Int) : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you]) .any (minTotalPower? := some n)
def creatureYouControlAttacks : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you])
def creatureYouControlAttacksAlone : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you]) .any (alone := true)
def creatureYouControlAttacksPlayerAlone : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you]) (.player .any) (alone := true)
def equippedCreatureYouControlAttacks : TriggerPattern :=
  .attacks (.all #[.hasType .creature, .controlledBy .you,
    .hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }])
def creatureAttacksYouOrYourPlaneswalker : TriggerPattern :=
  .attacks (.hasType .creature) (.playerOrPlaneswalker .you)
def creaturesAttackYourOpponent : TriggerPattern :=
  .attacks (.hasType .creature) (.player .opponent)
def zombieTokenPowerSixAttacks : TriggerPattern :=
  .attacks (.all #[.isToken true, .hasSubtype (.literal .zombie), .controlledBy .you,
    .stat .power .ge (.const 6)])
def sphinxesYouControlAttack : TriggerPattern :=
  .attacks (.all #[.hasSubtype (.literal .sphinx), .controlledBy .you])
    (countIntoLastKnown := true)
def merfolkYouControlAttackPlayer : TriggerPattern :=
  .attacks (.all #[.hasSubtype (.literal .merfolk), .controlledBy .you]) (.player .any)
def opponentSmallCreatureBlocks : TriggerPattern :=
  .blocks (.all #[.hasType .creature, .controlledBy .opponent,
    .any #[.stat .power .le (.const 1), .stat .toughness .le (.const 1)]])

def combatDamageToYou : TriggerPattern :=
  .damageDealt (.hasType .creature) (.player .you) (combatOnly := true)
def opponentsDealtCombatDamageYourTurn : TriggerPattern :=
  .damageDealt .anyObject (.player .opponent) (combatOnly := true) (duringYourTurn := true)
def opponentsDealtNoncombatDamage : TriggerPattern :=
  .damageDealt .anyObject (.player .opponent) (noncombatOnly := true)
def heroesYouControlDealDamageToPlayer : TriggerPattern :=
  .damageDealt (.all #[.hasSubtype (.literal .hero), .controlledBy .you]) (.player .any)
def armyYouControlCombatDamageToPlayer : TriggerPattern :=
  .damageDealt (.all #[.hasSubtype (.literal .army), .controlledBy .you]) (.player .any) (combatOnly := true)
def creatureYouControlDealtDamage : TriggerPattern :=
  .damageDealt .anyObject (.object (bfFilter (.all #[.hasType .creature, .controlledBy .you])))

def youCastSpell : TriggerPattern := .castSpell .you .anyObject
def opponentCastsSpell : TriggerPattern := .castSpell .opponent .anyObject
def youCastCreature : TriggerPattern := .castSpell .you (.hasType .creature)
def youCastNoncreature : TriggerPattern := .castSpell .you (.not (.hasType .creature))
def youCastInstantOrSorcery : TriggerPattern :=
  .castSpell .you (.any #[.hasType .instant, .hasType .sorcery])
def youCastArtifactOrCreature : TriggerPattern :=
  .castSpell .you (.any #[.hasType .artifact, .hasType .creature])
def youCastColor (c : Color) : TriggerPattern := .castSpell .you (.hasColor (.literal c))
def youCastColorFromHand (c : Color) : TriggerPattern :=
  .castSpell .you (.hasColor (.literal c)) (fromZone? := some .hand)
def youCastSubtype (sub : CardSubtype) : TriggerPattern :=
  .castSpell .you (.hasSubtype (.literal sub))
def youCastWithTreasure : TriggerPattern :=
  .castSpell .you .anyObject (manaSpent? := some .fromTreasure)
def youCastPreparedSpell : TriggerPattern :=
  .castSpell .you .anyObject (mustBePrepared := true)
def youCastSecondSpell : TriggerPattern :=
  .castSpell .you .anyObject (nthOfFilter? := some 2)
def anyPlayerCastsSecondSpell : TriggerPattern :=
  .castSpell .any .anyObject (nthOfFilter? := some 2)
def youCastFirstNoncreature : TriggerPattern :=
  .castSpell .you (.not (.hasType .creature)) (nthOfFilter? := some 1)
def opponentCastsFirstNoncreature : TriggerPattern :=
  .castSpell .opponent (.not (.hasType .creature)) (nthOfFilter? := some 1)
def opponentCastsSpellMvAtMost (n : Nat) : TriggerPattern :=
  .castSpell .opponent (.stat .manaValue .le (.const n))
def opponentCastsMatchingParity : TriggerPattern :=
  .castSpell .opponent (.statParity .manaValue .chosenOnSource)
def youCastTargetingCreatureYouControl : TriggerPattern :=
  .castSpell .you .anyObject
    (targets? := some (.object (bfFilter (.all #[.hasType .creature, .controlledBy .you]))))
def youCastTargetingCreature : TriggerPattern :=
  .castSpell .you .anyObject (targets? := some (.object (bfFilter (.hasType .creature))))
def youCastInstantSorceryTargetingArtifactOrLand : TriggerPattern :=
  .castSpell .you (.any #[.hasType .instant, .hasType .sorcery])
    (targets? := some (.object (bfFilter (.any #[.hasType .artifact, .hasType .land]))))
def youCastTargetingOpponentOrTheirCreature : TriggerPattern :=
  .castSpell .you .anyObject
    (targets? := some (.playerOrObject .opponent (bfFilter (.all #[.hasType .creature, .controlledBy .opponent]))))
def youCastEquipmentOrTargetingCreatureYouControl : TriggerPattern :=
  .or (.castSpell .you (.hasSubtype (.literal .equipment)))
      youCastTargetingCreatureYouControl

def youActivateCreatureAbility : TriggerPattern :=
  .activateAbility .you (.hasType .creature) .any
def youActivateLoyaltyAbility (minRemoved : Nat := 0) : TriggerPattern :=
  .activateAbility .you .anyObject (.loyalty minRemoved)
def opponentActivatesLoyaltyAbility : TriggerPattern :=
  .activateAbility .opponent .anyObject (.loyalty 0)
def youTargetPlayerOrPermanentWithAbility : TriggerPattern :=
  .becomesTarget .playerOrPermanent .you .ability

def putCountersOnSelf (kind : CounterKind) : TriggerPattern :=
  .putCounters none (some kind) (.sameAs .this)
def youPutCountersOnGoblinOrcArmy : TriggerPattern :=
  .putCounters (some .you) none (.all #[.controlledBy .you,
    .any #[.hasSubtype (.literal .goblin), .hasSubtype (.literal .orc), .hasSubtype (.literal .army)]])
def youPutLoyaltyCounters : TriggerPattern :=
  .putCounters (some .you) (some .loyalty) (.hasType .planeswalker)
def youPutPlusOneOnCreature : TriggerPattern :=
  .putCounters (some .you) (some .plusOnePlusOne) (.hasType .creature)
def youPutPlusOneOnOtherCreature : TriggerPattern :=
  .putCounters (some .you) (some .plusOnePlusOne) (.all #[.otherThan .this, .hasType .creature])
def youPutPlusOneOnOtherHeroYouControl : TriggerPattern :=
  .putCounters (some .you) (some .plusOnePlusOne)
    (.all #[.otherThan .this, .hasSubtype (.literal .hero), .controlledBy .you])

def youSacrificeToken : TriggerPattern := .sacrifice .you (.isToken true)
def youSacrificeOtherCreature : TriggerPattern :=
  .sacrifice .you (.all #[.otherThan .this, .hasType .creature])
def creaturesYouControlBecomeTapped : TriggerPattern :=
  .becomesTapped (.all #[.hasType .creature, .controlledBy .you])
def creatureYouControlFirstTappedYourTurn : TriggerPattern :=
  .becomesTapped (.all #[.hasType .creature, .controlledBy .you])
    (onlyDuringYourTurn := true) (firstTimeThisTurn := true)

def stepYourUpkeep : TriggerPattern := .stepBegins .upkeep (.player .you)
def stepEachUpkeep : TriggerPattern := .stepBegins .upkeep (.player .any)
def stepEachOpponentDrawStep : TriggerPattern := .stepBegins .draw (.player .opponent)
def stepYourFirstMain : TriggerPattern := .stepBegins .precombatMain (.player .you)
def stepYourBeginCombat : TriggerPattern := .stepBegins .beginningOfCombat (.player .you)
def stepEachBeginCombat : TriggerPattern := .stepBegins .beginningOfCombat (.player .any)
def stepOpponentBeginCombat : TriggerPattern := .stepBegins .beginningOfCombat (.player .opponent)
def stepYourEndStep : TriggerPattern := .stepBegins .end (.player .you)
def stepEachEndStep : TriggerPattern := .stepBegins .end (.player .any)
def stepEnchantedControllerUpkeep : TriggerPattern :=
  .stepBegins .upkeep (.controllerOf .attachedHost)

def finalSagaChapterResolves : TriggerPattern :=
  .stackObjectResolves (.all #[.hasSubtype (.literal .saga), .controlledBy .you])
    (finalSagaChapterOnly := true)

def youScry : TriggerPattern := .playerAction .you .scry
def youScryOrSurveil : TriggerPattern :=
  .or (.playerAction .you .scry) (.playerAction .you .surveil)
def youProliferate : TriggerPattern := .playerAction .you .proliferate
def theRingTemptsYou : TriggerPattern := .playerAction .you .ringTempts
def youChooseRingBearer : TriggerPattern := .playerAction .you .chooseRingBearer

def enterOrAttack : TriggerPattern := .or thisEnters thisAttacks
def castGreenOrForestEnters : TriggerPattern := .or (youCastColor .green) forestYouControlEnters
def enterOrOpponentDrawsExceptFirst : TriggerPattern :=
  .or thisEnters (.drawCard .opponent (exceptFirstDrawStep := true))

/-! ### Functorial `HasTextChange` (CR 612 / 613.1c) -/

def applyTextChangesAux (tcs : Array TextChange) : TriggerPattern → TriggerPattern
  | .zoneChange s f t v a =>
    .zoneChange (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs f)
      (HasTextChange.applyTextChanges tcs t) v (a.map (HasTextChange.applyTextChanges tcs))
  | .createTokens w tp =>
    .createTokens (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs tp)
  | .sacrifice w s =>
    .sacrifice (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs s)
  | .drawCard w ex => .drawCard (HasTextChange.applyTextChanges tcs w) ex
  | .discard w cp cyc =>
    .discard (HasTextChange.applyTextChanges tcs w) (HasTextChange.applyTextChanges tcs cp) cyc
  | .becomesTapped s yt ft ck =>
    .becomesTapped (HasTextChange.applyTextChanges tcs s) yt ft ck
  | .becomesUntapped s => .becomesUntapped (HasTextChange.applyTextChanges tcs s)
  | .phasesOut s => .phasesOut (HasTextChange.applyTextChanges tcs s)
  | .becomesUnattached a h =>
    .becomesUnattached (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs h)
  | .controlLost s fc =>
    .controlLost (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs fc)
  | .putCounters p k s =>
    .putCounters (p.map (HasTextChange.applyTextChanges tcs)) k (HasTextChange.applyTextChanges tcs s)
  | .attacks a t al ma mp cl =>
    .attacks (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs t) al ma mp cl
  | .blocks b => .blocks (HasTextChange.applyTextChanges tcs b)
  | .becomesBlocked a => .becomesBlocked (HasTextChange.applyTextChanges tcs a)
  | .damageDealt s r co nco yt =>
    .damageDealt (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs r) co nco yt
  | .gainLife w => .gainLife (HasTextChange.applyTextChanges tcs w)
  | .loseLife w => .loseLife (HasTextChange.applyTextChanges tcs w)
  | .castSpell c sp fz ms prep nth tgt =>
    .castSpell (HasTextChange.applyTextChanges tcs c) (HasTextChange.applyTextChanges tcs sp)
      fz (ms.map (HasTextChange.applyTextChanges tcs)) prep nth
      (tgt.map (HasTextChange.applyTextChanges tcs))
  | .activateAbility a s k =>
    .activateAbility (HasTextChange.applyTextChanges tcs a) (HasTextChange.applyTextChanges tcs s) k
  | .becomesTarget s bc sk =>
    .becomesTarget (HasTextChange.applyTextChanges tcs s) (HasTextChange.applyTextChanges tcs bc) sk
  | .spellCountered sp => .spellCountered (HasTextChange.applyTextChanges tcs sp)
  | .playerAction w act => .playerAction (HasTextChange.applyTextChanges tcs w) act
  | .stepBegins st who => .stepBegins st (HasTextChange.applyTextChanges tcs who)
  | .stackObjectResolves p fsc =>
    .stackObjectResolves (HasTextChange.applyTextChanges tcs p) fsc
  | .abilityTriggers s => .abilityTriggers (HasTextChange.applyTextChanges tcs s)
  | .whenCond inner c =>
    .whenCond (applyTextChangesAux tcs inner) (HasTextChange.applyTextChanges tcs c)
  | .or a b => .or (applyTextChangesAux tcs a) (applyTextChangesAux tcs b)

instance : HasTextChange TriggerPattern where
  applyTextChanges tcs p := if tcs.isEmpty then p else applyTextChangesAux tcs p

/-! ### Canonical `ToOracle` rendering -/

private def indArt (noun : String) : String :=
  match noun.toList with
  | c :: _ =>
    let cl := c.toLower
    if cl == 'a' || cl == 'e' || cl == 'i' || cl == 'o' || cl == 'u' then "an" else "a"
  | [] => "a"

private def subjPhrase (ctx : PrintCtx) (pred : ObjectPred) (plural : Bool := false)
    (zone : ZoneSetSpec := .battlefield) : String :=
  match pred with
  | .sameAs .this => ctx.selfRef
  | .sameAs .attachedHost => "enchanted creature"
  | .all #[.hasType .creature, .controlledBy .you,
      .hasAttachment { zones := { zones := #[.battlefield], owner := .any }, pred := .hasSubtype (.literal .equipment) }] =>
    if plural then "equipped creatures you control" else "an equipped creature you control"
  | .all #[.otherThan .this, .hasType .creature, .controlledBy .you,
      .any #[.hasSubtype (.literal .goblin), .hasSubtype (.literal .orc), .hasSubtype (.literal .army)]] =>
    if plural then "other Goblins, Orcs, or Armies you control" else "another Goblin, Orc, or Army you control"
  | _ =>
    let noun := ToOracle.toOracle { ctx with capitalize := false, plural } ({ zones := zone, pred } : ObjectFilter)
    if plural then noun
    else if noun.startsWith "another " || noun.startsWith "other " || noun.startsWith "this " ||
        noun.startsWith "equipped " || noun.startsWith "enchanted " then noun
    else s!"{indArt noun} {noun}"

private def playerClause (ctx : PrintCtx) (pf : PlayerFilter) : String :=
  if pf == .you then "you"
  else if pf == .opponent then "an opponent"
  else if pf == .any then "a player"
  else ToOracle.toOracle { ctx with capitalize := false } pf

private def pluralVerb (pf : PlayerFilter) (sg pl : String) : String :=
  if pf == .you then pl else sg

/-- Render the trigger clause after the leading `When` / `Whenever` / `At` word,
incorporating `BatchGrouping` and `TriggerLimit` where they belong in the clause
(e.g. `"one or more"`, `"their second card"`, `"the Nth plan counter"`). -/
def renderClause (ctx : PrintCtx) (grouping : BatchGrouping := .perOccurrence)
    (limit : TriggerLimit := .unlimited) : TriggerPattern → String
  | .zoneChange subj fromZ toZ _ _ =>
    let batch := grouping == .oncePerBatch
    let s :=
      if batch then s!"one or more {subjPhrase ctx subj (plural := true)}"
      else subjPhrase ctx subj (plural := false)
    if toZ.isBattlefieldOnly then
      if batch then s!"{s} enter" else s!"{s} enters"
    else if fromZ.isBattlefieldOnly && toZ.isGraveyardOnly then
      if batch then s!"{s} die" else s!"{s} dies"
    else if fromZ.isBattlefieldOnly && toZ == .hand then
      if batch then s!"{s} are returned to their owners' hands"
      else s!"{s} is returned to its owner's hand"
    else if fromZ.isBattlefieldOnly then
      if batch then s!"{s} leave the battlefield" else s!"{s} leaves the battlefield"
    else if fromZ.isGraveyardOnly then
      let gy :=
        match fromZ with
        | .inZones { owner := .matching pf, .. } =>
          if pf == PlayerFilter.you then "your graveyard" else "a graveyard"
        | _ => "a graveyard"
      if batch then s!"{s} leave {gy}" else s!"{s} leaves {gy}"
    else if toZ.isGraveyardOnly then
      let gy :=
        match toZ with
        | .inZones { owner := .matching pf, .. } =>
          if pf == PlayerFilter.you then "your graveyard" else "a graveyard"
        | _ => "a graveyard"
      if batch then s!"{s} are put into {gy} from anywhere"
      else s!"{s} is put into {gy} from anywhere"
    else
      s!"{s} changes zones"
  | .createTokens who tp =>
    let w := playerClause ctx who
    let v := pluralVerb who "creates" "create"
    let batch := grouping == .oncePerBatch
    let noun :=
      if tp == .anyObject then if batch then "one or more tokens" else "a token"
      else if batch then s!"one or more {subjPhrase ctx tp (plural := true)} tokens"
      else s!"{subjPhrase ctx tp (plural := false)} token"
    s!"{w} {v} {noun}"
  | .sacrifice who subj =>
    let w := playerClause ctx who
    let v := pluralVerb who "sacrifices" "sacrifice"
    s!"{w} {v} {subjPhrase ctx subj}"
  | .drawCard who exceptFirst =>
    let w := playerClause ctx who
    let v := pluralVerb who "draws" "draw"
    if exceptFirst then
      s!"{w} {v} a card except the first one they draw in each of their draw steps"
    else
      match limit with
      | .nthEachTurn 2 =>
        let poss := if who == .you then "your" else "their"
        s!"{w} {v} {poss} second card each turn"
      | .nthEachTurn n =>
        let poss := if who == .you then "your" else "their"
        s!"{w} {v} {poss} {n}th card each turn"
      | _ => s!"{w} {v} a card"
  | .discard who cp mustBeCycle =>
    let w := playerClause ctx who
    if mustBeCycle then
      s!"{w} {pluralVerb who "cycles" "cycle"} {subjPhrase ctx cp}"
    else if grouping == .oncePerBatch || grouping == .perPlayerInBatch then
      s!"{w} {pluralVerb who "discards" "discard"} one or more cards"
    else if cp == .anyObject then
      s!"{w} {pluralVerb who "discards" "discard"} a card"
    else
      s!"{w} {pluralVerb who "discards" "discard"} {subjPhrase ctx cp}"
  | .becomesTapped subj yt ft ck? =>
    let batch := grouping == .oncePerBatch
    let s :=
      if batch then s!"one or more {subjPhrase ctx subj (plural := true)}"
      else subjPhrase ctx subj
    let base := if batch then s!"{s} become tapped" else s!"{s} becomes tapped"
    let base :=
      match ck? with
      | some .teamwork => s!"{base} to pay a teamwork cost"
      | _ => base
    let base := if yt then s!"{base} during your turn" else base
    if ft then s!"{base}, if it's the first time that creature has become tapped this turn"
    else base
  | .becomesUntapped subj => s!"{subjPhrase ctx subj} becomes untapped"
  | .phasesOut subj => s!"{subjPhrase ctx subj} phases out"
  | .becomesUnattached att _ => s!"{subjPhrase ctx att} becomes unattached"
  | .controlLost subj _ => s!"you lose control of {subjPhrase ctx subj}"
  | .putCounters putter? kind? subj =>
    match grouping with
    | .counterThreshold .lore _ => "a lore counter is put on this Saga"
    | .counterThreshold .plan #[n] =>
      let ord :=
        match n with
        | 1 => "first" | 2 => "second" | 3 => "third" | 4 => "fourth"
        | 5 => "fifth" | 6 => "sixth" | 7 => "seventh" | 8 => "eighth"
        | _ => s!"{n}th"
      s!"the {ord} plan counter is put on this enchantment"
    | _ =>
      let cnt :=
        if grouping == .perOccurrence then
          match kind? with
          | some k => s!"{indArt k.oracleName} {k.oracleName} counter"
          | none => "a counter"
        else
          match kind? with
          | some k => s!"one or more {k.oracleName} counters"
          | none => "one or more counters"
      match putter? with
      | some w =>
        s!"{playerClause ctx w} {pluralVerb w "puts" "put"} {cnt} on {subjPhrase ctx subj}"
      | none =>
        let cop := if grouping == .perOccurrence then "is" else "are"
        s!"{cnt} {cop} put on {subjPhrase ctx subj}"
  | .attacks att tgt alone minAtt minPow? _ =>
    match minPow? with
    | some p => s!"you attack with creatures with total power {p} or greater"
    | none =>
      if minAtt ≥ 2 then
        let nWord :=
          match minAtt with
          | 2 => "two"
          | 3 => "three"
          | n => toString n
        s!"{nWord} or more {subjPhrase ctx att (plural := true)} attack a player"
      else if grouping == .oncePerBatch || grouping == .perPlayerInBatch then
        let suffix :=
          match tgt with
          | .any => ""
          | .player pf => s!" {playerClause ctx pf}"
          | .playerOrPlaneswalker pf => s!" {playerClause ctx pf} or a planeswalker they control"
        if att == .all #[.hasType .creature, .controlledBy .you] && tgt == .any then "you attack"
        else
          match att, tgt, grouping with
          | .all #[.hasSubtype (.literal s), .controlledBy .you], .any, .oncePerBatch =>
            s!"you attack with one or more {s.pluralName}"
          | _, _, _ =>
            s!"one or more {subjPhrase ctx att (plural := true)} attack{suffix}"
      else
        let s :=
          if att == .sameAs .attachedHost then "equipped creature"
          else subjPhrase ctx att
        let tgtS :=
          match tgt with
          | .any => ""
          | .player pf => s!" {playerClause ctx pf}"
          | .playerOrPlaneswalker pf =>
            if pf == PlayerFilter.you then " you or a planeswalker you control"
            else s!" {playerClause ctx pf} or a planeswalker they control"
        let aloneS := if alone then " alone" else ""
        s!"{s} attacks{tgtS}{aloneS}"
  | .blocks b => s!"{subjPhrase ctx b} blocks"
  | .becomesBlocked a => s!"{subjPhrase ctx a} becomes blocked"
  | .damageDealt src rec combatOnly noncombatOnly duringYourTurn =>
    let dmg :=
      if combatOnly then "combat damage"
      else if noncombatOnly then "noncombat damage"
      else "damage"
    let turnS := if duringYourTurn then " during your turn" else ""
    match src, rec with
    | .anyObject, .object objFilter =>
      s!"{subjPhrase ctx objFilter.pred (zone := objFilter.zones)} is dealt {dmg}{turnS}"
    | .anyObject, .player pf =>
      if grouping == .oncePerBatch then
        let who := if pf == .opponent then "one or more of your opponents" else s!"one or more {playerClause ctx pf}"
        s!"{who} are dealt {dmg}{turnS}"
      else s!"{playerClause ctx pf} is dealt {dmg}{turnS}"
    | _, _ =>
      let batch := grouping == .oncePerBatch || grouping == .perPlayerInBatch
      let s :=
        if batch then s!"one or more {subjPhrase ctx src (plural := true)}"
        else if src == .sameAs .attachedHost then "equipped creature"
        else subjPhrase ctx src
      let v := if batch then "deal" else "deals"
      let recS :=
        match rec with
        | .any => "a player or permanent"
        | .player pf => playerClause ctx pf
        | .object f => subjPhrase ctx f.pred (zone := f.zones)
        | .playerOrObject pf f =>
          let objS := ToOracle.toOracle { ctx with capitalize := false } f
          s!"{playerClause ctx pf} or {objS}"
      s!"{s} {v} {dmg} to {recS}{turnS}"
  | .gainLife who => s!"{playerClause ctx who} {pluralVerb who "gains" "gain"} life"
  | .loseLife who => s!"{playerClause ctx who} {pluralVerb who "loses" "lose"} life"
  | .castSpell caster sp fromZ? manaSpent? prep nth? tgt? =>
    let w := playerClause ctx caster
    let v := pluralVerb caster "casts" "cast"
    if sp == .sameAs .this then s!"{w} {v} this spell"
    else
      let spS :=
        if prep then "a prepare spell"
        else if sp == .anyObject then "a spell"
        else
          match sp with
          | .not (.hasType .creature) => "a noncreature spell"
          | .hasType .creature => "a creature spell"
          | .hasType .artifact => "an artifact spell"
          | .hasType .enchantment => "an enchantment spell"
          | .hasType .instant => "an instant spell"
          | .hasType .sorcery => "a sorcery spell"
          | .any #[.hasType .instant, .hasType .sorcery] => "an instant or sorcery spell"
          | .any #[.hasType .artifact, .hasType .creature] => "an artifact or creature spell"
          | .hasColor (.literal c) => s!"{indArt c.englishName} {c.englishName} spell"
          | .hasSubtype (.literal s) => s!"{indArt s.englishName} {s.englishName} spell"
          | .stat .manaValue .le (.const n) => s!"a spell with mana value {n} or less"
          | .statParity .manaValue .chosenOnSource => "a spell with mana value of the chosen quality"
          | _ =>
            let base := ToOracle.toOracle { ctx with capitalize := false } ({ zones := .stack, pred := sp } : ObjectFilter)
            let base := (base.replace " on the stack" "").replace " permanent" ""
            let base := if base.endsWith " spell" then base else s!"{base} spell"
            s!"{indArt base} {base}"
      let spS :=
        match nth? with
        | some 1 =>
          let poss := if caster == PlayerFilter.you then "your" else "their"
          let stripped := if spS.startsWith "a " then (spS.drop 2).copy else if spS.startsWith "an " then (spS.drop 3).copy else spS
          s!"{poss} first {stripped} each turn"
        | some 2 =>
          let poss := if caster == PlayerFilter.you then "your" else "their"
          let stripped := if spS.startsWith "a " then (spS.drop 2).copy else if spS.startsWith "an " then (spS.drop 3).copy else spS
          s!"{poss} second {stripped} each turn"
        | some n =>
          let poss := if caster == PlayerFilter.you then "your" else "their"
          let stripped := if spS.startsWith "a " then (spS.drop 2).copy else if spS.startsWith "an " then (spS.drop 3).copy else spS
          s!"{poss} {n}th {stripped} each turn"
        | none => spS
      let fromS :=
        match fromZ? with
        | some .hand => if caster == PlayerFilter.you then " from your hand" else " from their hand"
        | some .graveyard => " from a graveyard"
        | some .exile => " from exile"
        | some .library => " from a library"
        | some .command => " from the command zone"
        | some _ => ""
        | none => ""
      let tgtS :=
        match tgt? with
        | none => ""
        | some (.object f) => s!" that targets {subjPhrase ctx f.pred (zone := f.zones)}"
        | some (.player pf) => s!" that targets {playerClause ctx pf}"
        | some (.playerOrObject pf f) =>
          s!" that targets {playerClause ctx pf} or {subjPhrase ctx f.pred (zone := f.zones)}"
        | some .any => " that has a target"
      let manaS :=
        match manaSpent? with
        | some .fromTreasure => ", if mana from a Treasure was spent to cast it"
        | some .fromSource => ", if mana produced by this permanent was spent to cast it"
        | some (.ofColor c) => s!", if {c.englishName} mana was spent to cast it"
        | _ => ""
      s!"{w} {v} {spS}{fromS}{tgtS}{manaS}"
  | .activateAbility act src kind =>
    let w := playerClause ctx act
    let v := pluralVerb act "activates" "activate"
    match kind with
    | .loyalty minRem =>
      if minRem == 0 then s!"{w} {v} a loyalty ability"
      else s!"{w} {v} a loyalty ability, if you removed {minRem} or more loyalty counters to activate it"
    | .manaAbility =>
      if src == .anyObject then s!"{w} {v} a mana ability"
      else s!"{w} {v} a mana ability of {subjPhrase ctx src}"
    | .nonMana =>
      if src == .anyObject then s!"{w} {v} an ability that isn't a mana ability"
      else s!"{w} {v} a non-mana ability of {subjPhrase ctx src}"
    | .any =>
      if src == .anyObject then s!"{w} {v} an ability"
      else s!"{w} {v} an ability of {subjPhrase ctx src}"
  | .becomesTarget subj byCtrl srcKind =>
    let what :=
      match srcKind with
      | .spellOrAbility => "a spell or ability"
      | .spell => "a spell"
      | .ability => "an ability"
    let ctrlS :=
      if byCtrl == .you then " you control"
      else if byCtrl == .opponent then " an opponent controls"
      else ""
    match subj with
    | .playerOrPermanent => s!"a player or permanent becomes the target of {what}{ctrlS}"
    | .object p => s!"{subjPhrase ctx p} becomes the target of {what}{ctrlS}"
  | .spellCountered sp =>
    if sp == .anyObject then "a spell is countered"
    else if sp == .sameAs .this then "this spell is countered"
    else s!"{subjPhrase ctx sp (zone := .stack)} is countered"
  | .playerAction who act =>
    let w := playerClause ctx who
    match act with
    | .scry => s!"{w} {pluralVerb who "scries" "scry"}"
    | .surveil => s!"{w} {pluralVerb who "surveils" "surveil"}"
    | .proliferate => s!"{w} {pluralVerb who "proliferates" "proliferate"}"
    | .ringTempts => "the Ring tempts you"
    | .chooseRingBearer => s!"{w} {pluralVerb who "chooses" "choose"} a creature as your Ring-bearer"
    | .manaAdded => s!"{w} {pluralVerb who "adds" "add"} mana"
    | .losesGame => s!"{w} {pluralVerb who "loses" "lose"} the game"
  | .stepBegins step who =>
    match step, who with
    | .upkeep, .player pf =>
      if pf == .you then "the beginning of your upkeep"
      else if pf == .opponent then "the beginning of each opponent's upkeep"
      else "the beginning of each upkeep"
    | .upkeep, .controllerOf .attachedHost => "the beginning of the upkeep of enchanted creature's controller"
    | .upkeep, .controllerOf _ => "the beginning of that player's upkeep"
    | .draw, .player pf =>
      if pf == .you then "the beginning of your draw step"
      else if pf == .opponent then "the beginning of each opponent's draw step"
      else "the beginning of each draw step"
    | .precombatMain, .player pf =>
      if pf == .you then "the beginning of your first main phase"
      else "the beginning of each first main phase"
    | .beginningOfCombat, .player pf =>
      if pf == .you then "the beginning of combat on your turn"
      else if pf == .opponent then "the beginning of combat on each opponent's turn"
      else "the beginning of each combat"
    | .end, .player pf =>
      if pf == .you then "the beginning of your end step"
      else if pf == .opponent then "the beginning of each opponent's end step"
      else "the beginning of each end step"
    | st, _ => s!"the beginning of {st.englishName}"
  | .stackObjectResolves _ true => "the final chapter ability of a Saga you control resolves"
  | .stackObjectResolves p false => s!"{subjPhrase ctx p (zone := .stack)} resolves"
  | .abilityTriggers s =>
    if s == .anyObject then "an ability triggers"
    else s!"an ability of {subjPhrase ctx s} triggers"
  | .whenCond inner cond =>
    s!"{inner.renderClause ctx grouping limit} while {ToOracle.toOracle { ctx with capitalize := false } cond}"
  | .or a b =>
    match a, b with
    | .zoneChange (.sameAs .this) (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none,
      .attacks (.sameAs .this) .any false 1 none false =>
      s!"{ctx.selfRef} enters or attacks"
    | .zoneChange (.sameAs .this) (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none,
      .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.inZones { zones := #[.graveyard], .. }) none none =>
      s!"{ctx.selfRef} enters or dies"
    | .attacks (.sameAs .attachedHost) .any false 1 none false,
      .blocks (.sameAs .attachedHost) =>
      "enchanted creature attacks or blocks"
    | .playerAction who .scry, .playerAction _ .surveil =>
      s!"{playerClause ctx who} scry or surveil"
    | _, _ =>
      s!"{a.renderClause ctx grouping limit} or {b.renderClause ctx grouping limit}"

instance : ToOracle TriggerPattern where
  toOracle ctx p :=
    let w := ToOracle.toOracle ctx p.defaultWord
    s!"{w} {p.renderClause { ctx with capitalize := false }}"

end TriggerPattern

end Mtg.Engine
