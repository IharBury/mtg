import Mtg.Engine.Game.Phasing

/-!
# Removing abilities (CR 613.1f)

`ContinuousEffect.removeAllAbilities` and the other lose-all-abilities
effects. Printed abilities are absent while one applies. Abilities granted
by a later effect still apply.
-/

namespace Mtg.Engine
namespace Game

/-- Whom a player-selector names, relative to `src` or the fallback `you`. -/
inductive AbilityPlayer where
  | one (p : PlayerId)
  | opponentsOf (p : PlayerId)
  | anyPlayer
  | unknown
deriving Repr, Inhabited, BEq

/-- The object a singular selector names, if it can be read without targets. -/
def namedObject? (g : Game) (src : Option GameObject) (you : PlayerId) :
    Selector → Option GameObject
  | .this | .source .this => src
  | .source s =>
    (g.namedObject? src you s).bind fun o => o.sourceId.bind g.findObject?
  | .hostOf s =>
    (g.namedObject? src you s).bind fun o => o.attachedTo.bind g.findObject?
  | _ => none

/-- The players a selector names. `you` is the source's controller, or the
spell's controller when the resolving spell has no source object. -/
def abilityPlayer? (g : Game) (src : Option GameObject) (you : PlayerId) :
    Selector → AbilityPlayer
  | .controller s =>
    match g.namedObject? src you s with
    | some obj => .one obj.you
    | none =>
      if s == .this || s == .source .this then .one you else .unknown
  | .owner s =>
    match g.namedObject? src you s with
    | some obj => .one obj.owner
    | none =>
      if s == .this || s == .source .this then .one you else .unknown
  | .opponent inner =>
    match g.abilityPlayer? src you inner with
    | .one p => .opponentsOf p
    | _ => .unknown
  | .player => .anyPlayer
  | .caster => .one you
  | _ => .unknown

/-- Printed keywords plus until-end-of-turn grants, ignoring ability loss so
keyword constraints do not depend on this effect. -/
def printedKeyword (k : Keywords) : Keyword → Option Bool
  | .flash => some k.flash
  | .haste => some k.haste
  | .vigilance => some k.vigilance
  | .flying => some k.flying
  | .menace => some k.menace
  | .hexproof => some k.hexproof
  | .indestructible => some k.indestructible
  | .reach => some k.reach
  | .trample => some k.trample
  | .deathtouch => some k.deathtouch
  | .defender => some k.defender
  | .lifelink => some k.lifelink
  | .firstStrike => some k.firstStrike
  | .islandwalk => some k.islandwalk
  | .storied => some k.storied
  | .doubleStrike => some k.doubleStrike
  | .prowess => some k.prowess
  | .ascend => some k.ascend
  | .shadow => some k.shadow
  | .changeling => some k.changeling
  | .equip | .enchant | .typecycling _ _ _ | .recruit | .amass _ _
  | .connive _ | .chapter _ | .flashback | .ward | .crew _
  | .teamwork _ | .improvise | .kicker | .affinity _ _ | .boast | .cascade
  | .extort | .sneak | .gift _ | .behold _ | .harness | .infinity => none

def hasCounterKind (o : GameObject) : CounterKind → Bool
  | .plusOnePlusOne => o.status.plusOnePlusOne > 0
  | .burden => o.status.burden > 0
  | .finality => o.status.finality > 0
  | .hone => o.status.hone > 0
  | .hope => o.status.hope > 0
  | .indestructible => o.status.indestructibleCounters > 0
  | .influence => o.status.influence > 0
  | .invasion => o.status.invasion > 0
  | .lifelink => o.status.lifelinkCounters > 0
  | .plan => o.status.plan > 0
  | .quest => o.status.quest > 0
  | .shadow => o.status.shadow > 0
  | .shield => o.status.shield > 0
  | .trample => o.status.trampleCounters > 0
  | _ => false

def inZone (o : GameObject) : Zone → Bool
  | .library _ =>
    match o.zone with
    | .library _ => true
    | _ => false
  | .hand _ =>
    match o.zone with
    | .hand _ => true
    | _ => false
  | .graveyard _ =>
    match o.zone with
    | .graveyard _ => true
    | _ => false
  | .battlefield => o.isOnBattlefield
  | .stack => o.zone == .stack
  | .exile => o.zone == .exile
  | .command => o.zone == .command
  | .ante => o.zone == .ante

/-- The runtime zone of this kind. Library, hand, and graveyard belong to
`owner`. Battlefield, stack, exile, and command are shared. -/
def zoneOfKind : ZoneKind → PlayerId → Zone
  | .library, p => .library p
  | .hand, p => .hand p
  | .battlefield, _ => .battlefield
  | .graveyard, p => .graveyard p
  | .stack, _ => .stack
  | .exile, _ => .exile
  | .command, _ => .command

/-- Combine two optional Booleans with and. A `false` decides the result. -/
def andMatch (a b : Option Bool) : Option Bool :=
  match a, b with
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Combine two optional Booleans with or. A `true` decides the result. -/
def orMatch (a b : Option Bool) : Option Bool :=
  match a, b with
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- `some b` when `sel` decides whether `o` matches. `none` when the selector
cannot be read here, so the caller does not strip an unknown set.
Selectors nest, so this walks the tree directly. -/
partial def selectorMatches? (g : Game) (src : Option GameObject) (you : PlayerId)
    (sel : Selector) (o : GameObject) : Option Bool :=
  match sel with
  | .this | .source .this =>
    match src with
    | some s => some (o.id == s.id)
    | none => some false
  | .source _ | .hostOf _ =>
    match g.namedObject? src you sel with
    | some named => some (named.id == o.id)
    | none => some false
  | .all => some true
  | .zone z => some (inZone o (zoneOfKind z o.owner))
  | .cardType t => some (o.types.contains t)
  | .subtype st => some (o.hasSubtype st.toString)
  | .supertype st => some (o.printed.hasSupertype st)
  | .token => some o.printed.isToken
  | .tapped => some o.status.tapped
  | .spell =>
    some (o.zone == .stack && o.abilityEffect.isNone && o.triggeredAbility.isNone)
  | .ability =>
    some (o.zone == .stack && (o.abilityEffect.isSome || o.triggeredAbility.isSome))
  | .permanentSpell =>
    if o.zone == .stack && o.abilityEffect.isNone && o.triggeredAbility.isNone then
      some (o.types.any fun t =>
        t == .creature || t == .artifact || t == .enchantment ||
          t == .land || t == .planeswalker || t == .battle)
    else some false
  | .keyword k =>
    printedKeyword (Keywords.merge o.printed.keywords o.grantedUntilEot) k
  | .hasCounter k => some (hasCounterKind o k)
  | .powerAtLeast v =>
    match valToInt? v with
    | some n => some (o.power ≥ n)
    | none => none
  | .powerAtMost v =>
    match valToInt? v with
    | some n => some (o.power ≤ n)
    | none => none
  | .attacking whom =>
    if !o.status.attacking then some false
    else
      match g.abilityPlayer? src you whom with
      | .unknown | .anyPlayer => some true
      | .one p => some (o.status.attackingWhom == some p)
      | .opponentsOf p =>
        match o.status.attackingWhom with
        | some q => some ((g.livingOpponents p).any (·.id == q))
        | none => some false
  | .blocking _ => some !o.status.blocking.isEmpty
  | .controlled who =>
    match g.abilityPlayer? src you who with
    | .one p => some (o.controlledBy p)
    | .opponentsOf p =>
      match o.controller with
      | some c => some ((g.livingOpponents p).any (·.id == c))
      | none => some false
    | .anyPlayer => some o.controller.isSome
    | .unknown => none
  | .intersection fs =>
    fs.foldl (fun acc s => andMatch acc (g.selectorMatches? src you s o)) (some true)
  | .union fs =>
    fs.foldl (fun acc s => orMatch acc (g.selectorMatches? src you s o)) (some false)
  | .not inner =>
    match g.selectorMatches? src you inner o with
    | some b => some !b
    | none => none
  | .controller _ | .owner _ | .opponent _ | .player | .caster
  | .target _ _ | .targets _ _ _ | .targetSet _ _ _ _
  | .targetReference _ | .selected _ _ _ | .keywordAbility _
  | .abilityWithId _ | .hasTarget _ | .isTargetOf _
  | .wasObjectOfAction _ | .wasArgumentOfTrigger _ _ | .replacingObject
  | .wasCreatedByAction _ | .affectedByAction _ | .wasObjectSince _ _
  | .variable _ | .topOfLibrary _ _ | .hasCreatureTypeChosenByAction _
  | .manaValueAtMost _ | .castFromZone _ | .chooseRandom _ | .sharesNameWith _ => none

/-- Whether `o` matches `sel` from `src`. Unknown selectors do not match. -/
def selectorMatches (g : Game) (src : Option GameObject) (you : PlayerId)
    (sel : Selector) (o : GameObject) : Bool :=
  (g.selectorMatches? src you sel o).getD false

/-- An attached Aura's printed static ability removes `o`'s abilities.
Unfiltered, so this check does not depend on whether the Aura itself has
lost abilities. -/
def auraStripsAbilities (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any fun aura =>
    aura.attachedTo == some o.id &&
      aura.staticAbilities.any fun
        | .enchantedLosesAbilitiesDoesntUntap => true
        | .enchantedLosesAbilitiesCantUntap => true
        | _ => false

/-- `o` currently loses all of its abilities (CR 613.1f). -/
def losesAllAbilities (g : Game) (o : GameObject) : Bool :=
  o.status.losesAllAbilitiesUntilEot ||
  g.auraStripsAbilities o ||
  o.status.losesAbilitiesGrantedBy.any (fun id =>
    match g.findObject? id with
    | some src => src.isOnBattlefield
    | none => false) ||
  g.battlefield.any fun src =>
    src.printed.removesAllAbilitiesFrom.any fun sel =>
      g.selectorMatches (some src) src.you sel o

/-- Printed static abilities that still apply, plus later grants. -/
def staticAbilitiesOf (g : Game) (o : GameObject) : Array StaticAbility :=
  let printed := if g.losesAllAbilities o then #[] else o.printed.staticAbilities
  printed ++ o.status.grantedStaticAbilities

/-- Waiting-trigger snapshots of `source`'s abilities that fire on `event`.
Printed abilities are omitted while `source` loses all abilities. -/
def waitingTriggersFor (g : Game) (source : GameObject) (controller : PlayerId)
    (event : TriggerEvent) (lastKnownPower : Option Int := none)
    (lastKnownToughness : Option Int := none) : Array WaitingTrigger :=
  let printed :=
    if g.losesAllAbilities source then #[] else source.printed.triggeredAbilities
  let abs :=
    (printed ++ source.status.grantedTriggeredAbilities).filter (·.firesOn event)
  abs.map fun ab =>
    { controller, source, ability := ab, event, lastKnownPower, lastKnownToughness }

end Game
end Mtg.Engine
