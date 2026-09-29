import Mtg.Engine.Game.Library

/-!
# Current keywords (CR 613.1f)

Which keyword abilities an object currently has: printed, granted until
end of turn, granted by attachments or leftover text, or lost with lose-
abilities effects — haste, flying, menace, hexproof, indestructible,
trample, and the attack and block permission checks built on them
(CR 509.1b).
-/

namespace Mtg.Engine
namespace Game

/-- True when an Aura attached to `o` makes it only a listed subtype and
unable to attack or block (e.g. Fog on the Barrow-Downs). -/
def enchantedCantAttackOrBlock (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun a =>
    a.attachedTo == some o.id &&
      (g.staticAbilitiesOf a).any (fun ab => ab.enchantedOnlySubtype?.isSome))

/-- Printed abilities still apply unless a lose-all-abilities effect selects
this object (CR 613.1f). -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  !g.losesAllAbilities o

/-- Printed keywords that still apply, plus until-end-of-turn grants.
Later grants apply even while printed abilities are lost (CR 613.1f). -/
def retainedOrUntilEot (g : Game) (o : GameObject) : Keywords :=
  let printed :=
    if g.retainsPrintedAbilities o then o.printed.keywords else Keywords.none
  Keywords.merge printed o.grantedUntilEot

/-- Printed haste, until-EOT haste, or a static “haste as long as you control
another …” ability. Printed haste is absent while `o` loses all abilities. -/
def hasHaste (g : Game) (o : GameObject) : Bool :=
  (g.retainedOrUntilEot o).haste ||
  (o.isOnBattlefield &&
    (g.staticAbilitiesOf o).any (fun ab =>
      match ab.hasteIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

/-- Summoning sickness (CR 302.6). Printed haste does not apply while the
creature loses all abilities (CR 613.1f). -/
def hasSummoningSickness (g : Game) (o : GameObject) : Bool :=
  o.isCreature && o.status.summoningSick && !g.hasHaste o

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && !(g.retainedOrUntilEot o).defender &&
  !(o.status.summoningSick && !g.hasHaste o) &&
  !g.enchantedCantAttackOrBlock o &&
  (g.staticAbilitiesOf o).all (fun ab =>
    match ab.cantAttackUnlessNOther? with
    | none => true
    | some (n, subtype) =>
      match o.controller with
      | none => false
      | some p =>
        let others :=
          (g.permanentsOf p).filter (fun x =>
            x.id != o.id && g.hasSubtype x subtype) |>.size
        others >= n)

/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array String) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any (g.hasSubtype o))

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.isCreature && o.printed.hasSupertype .legendary)

/-- Whether `p` currently controls an Equipment. -/
def controlsEquipment (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.isEquipment)

/-- Whether this face should enter tapped given the controller's board. -/
def entersTapped (g : Game) (p : PlayerId) (card : CardDef) : Bool :=
  card.entersTapped ||
    (card.entersTappedUnlessLegendary && !g.controlsLegendaryCreature p) ||
    (card.entersTappedUnlessEquipment && !g.controlsEquipment p)

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  (g.staticAbilitiesOf blocker).all (fun ab =>
    match ab.cantBlockUnless? with
    | some subtypes =>
      match blocker.controller with
      | none => false
      | some p => g.controlsAnySubtype p subtypes
    | none => true)

/-- Keywords an attached Aura or Equipment currently grants `o`. -/
def attachedGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    g.battlefield.foldl (fun acc aura =>
      if aura.attachedTo == some o.id then
        Keywords.merge acc
          ((g.staticAbilitiesOf aura).foldl (fun k ab =>
            Keywords.merge k ab.hostKeywords) Keywords.none)
      else acc) Keywords.none

/-- True when an attached Aura makes `o` lose all abilities (Enchanted
River's Grasp; Frozen in Ice). -/
def attachedLosesAbilities (g : Game) (o : GameObject) : Bool :=
  g.auraStripsAbilities o

/-- True when leftover “has flying if you've put a +1/+1 counter on this
this turn” currently applies. Cards entering a graveyard do not count. -/
def leftoverFlyingIfPlusOneThisTurn (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (g.staticAbilitiesOf o).any (fun
      | .flyingIfPlusOneThisTurn => o.status.gotPlusOneThisTurn
      | _ => false)

def leftoverGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  let self :=
    if g.leftoverFlyingIfPlusOneThisTurn o then Keyword.flying.toKeywords
    else Keywords.none
  let self :=
    if g.leftoverAllCreatureTypes o then Keywords.merge self Keyword.changeling else self
  let fromTeam :=
    match o.controller with
    | none => Keywords.none
    | some p =>
      (g.permanentsOf p).foldl (fun acc src =>
        (g.staticAbilitiesOf src).foldl (fun acc ab =>
          match ab with
          | .creaturesWithPlusOneHave k =>
            if o.isCreature && o.status.plusOnePlusOne > 0 then
              Keywords.merge acc k
            else acc
          | .attackingTokensHave k =>
            if o.isOnBattlefield && o.status.attacking && o.printed.isToken then
              Keywords.merge acc k
            else acc
          | _ => acc) acc) Keywords.none
  Keywords.merge self fromTeam

def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  let base :=
    Keywords.merge
      (Keywords.merge
        (Keywords.merge (g.retainedOrUntilEot o)
          (g.attachedGrantedKeywords o))
        (g.enduringStoryKeywords o))
      (g.leftoverGrantedKeywords o)
  if o.status.shadow > 0 then { base with shadow := true } else base

/-- Whether `o` currently has shadow (printed, granted, or from a counter).
Multiple instances are redundant. -/
def hasShadow (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).shadow

/-- Printed or until-end-of-turn keyword selected by `sel`. -/
def hasPrintedOrEot (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel o.printedOrUntilEot

/-- Current keyword including attached grants. -/
def hasKeyword (g : Game) (o : GameObject) (sel : Keywords → Bool) : Bool :=
  sel (g.currentKeywords o)

/-- Whether `o` has vigilance (CR 702.20). Attacking does not cause it to tap. -/
def hasVigilance (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.vigilance)

/-- Whether `o` has flying, printed or granted (CR 702.9). -/
def hasFlying (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.flying)

/-- Okoye: attacking creature tokens you control have first strike. -/
def okoyeGrantsFirstStrike (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.status.attacking && o.printed.isToken &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        (g.staticAbilitiesOf src).any (fun
          | .attackingTokensHave k => k.firstStrike
          | _ => false))

/-- Whether `o` has first strike, printed or granted (CR 702.7). -/
def hasFirstStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.firstStrike) || g.hasKeyword o (·.doubleStrike) ||
    g.okoyeGrantsFirstStrike o

/-- Whether `o` has double strike (CR 702.4). -/
def hasDoubleStrike (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.doubleStrike)

/-- Whether `o` has islandwalk, printed or granted (CR 702.14). -/
def hasIslandwalk (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.islandwalk)

/-- During the Equipment's controller's turn, the equipped creature has
hexproof and can't be blocked (Bilbo's Ring). -/
def equippedHexproofUnblockableThisTurn (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        (g.staticAbilitiesOf eq).any (fun
          | .equippedHexproofUnblockableDuringYourTurn => true
          | _ => false) &&
        match eq.controller with
        | some p => g.activePlayer == p
        | none => false)

/-- Equipment that grants "can't be blocked" to its host (My Precious). -/
def equippedCantBeBlockedNow (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        (g.staticAbilitiesOf eq).any StaticAbility.equippedCantBeBlocked)

/-- Whether `o` can't be blocked, printed or granted until end of turn
(CR 509.1b / 611.2a), or while its power is at most a listed value. -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.cantBeBlocked) ||
  g.equippedHexproofUnblockableThisTurn o ||
  g.equippedCantBeBlockedNow o ||
  (o.isOnBattlefield &&
    (g.staticAbilitiesOf o).any (fun ab =>
      match ab.cantBeBlockedIfPowerAtMost? with
      | some n => g.snapshotPower o <= n
      | none => false))

/-- Whether `o` has lifelink, printed, granted until end of turn, or from a
lifelink counter (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  o.status.lifelinkCounters > 0 ||
  g.hasKeyword o (·.lifelink) ||
  (o.isOnBattlefield &&
    (g.staticAbilitiesOf o).any (fun ab =>
      match ab.lifelinkIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

/-- Whether `o` has menace, printed or granted until end of turn (CR 702.111).
Pairwise `canBlock` stays true; the two-or-more restriction is checked on the
declaration as a whole (CR 509.1c). -/
def hasMenace (g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.menace) ||
  (g.leftoverGrantedKeywords o).menace ||
  (o.isOnBattlefield && o.status.plusOnePlusOne > 0 &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        (g.staticAbilitiesOf src).any StaticAbility.creaturesWithPlusOneHaveMenace))

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let fromStatic :=
    (g.staticAbilitiesOf o).foldl (fun acc ab =>
      match ab.cantBeBlockedExcept? with
      | some n => max acc n
      | none => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- True when `n` blockers is a legal number for `attacker` (CR 702.111b).
Zero is always legal (the attacker is unblocked). -/
def legalBlockerCount (g : Game) (attacker : GameObject) (n : Nat) : Bool :=
  let need := g.minBlockersRequired attacker
  n == 0 || need <= 1 || n >= need

/-- Creatures with flying can't attack this player or block their creatures. -/
def leftoverFlyingRestriction (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    (g.staticAbilitiesOf o).any (fun
      | .flyingCantAttackYouOrBlockYours => true
      | _ => false))

/-- Whether `blocker` may be assigned to `attacker` as one creature in a
declaration (CR 509.1b). Menace is not a pairwise restriction. -/
def canBlock (g : Game) (blocker attacker : GameObject) : Bool :=
  let defender :=
    match attacker.status.attackingWhom with
    | some pid => pid
    | none => g.defendingPlayer
  let islandwalkUnblockable :=
    g.hasIslandwalk attacker &&
      (g.permanentsOf defender).any (fun o => g.hasSubtype o "Island")
  blocker.isOnBattlefield && blocker.isCreature &&
  blocker.controlledBy defender && !blocker.status.tapped &&
  blocker.status.blocking.isEmpty &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.hasCantBeBlocked attacker &&
  !islandwalkUnblockable &&
  !((g.staticAbilitiesOf attacker).any StaticAbility.blocksTokens &&
    blocker.printed.isToken) &&
  !((g.staticAbilitiesOf attacker).any (fun ab =>
      match ab.cantBeBlockedByPowerAtMost? with
      | some n => g.snapshotPower blocker <= n
      | none => false)) &&
  !((g.staticAbilitiesOf attacker).any (fun ab =>
      match ab.cantBeBlockedByPowerAtLeast? with
      | some n => g.snapshotPower blocker >= n
      | none => false)) &&
  (!g.hasFlying attacker ||
    g.hasFlying blocker || (g.currentKeywords blocker).reach) &&
  !(g.hasFlying blocker &&
    match attacker.controller with
    | some p => g.leftoverFlyingRestriction p
    | none => false) &&
  (!(g.hasShadow attacker) || g.hasShadow blocker) &&
  (!(g.hasShadow blocker) || g.hasShadow attacker) &&
  !(match attacker.status.cantBeBlockedByPlayer with
    | some pid => blocker.controlledBy pid
    | none => false) &&
  !(attacker.status.cantBeBlockedExceptByHasteUntilEot && !g.hasHaste blocker)

/-- Whether `src` currently grants trample to `target` (CR 604.2). -/
def grantsTrampleTo (g : Game) (src target : GameObject) : Bool :=
  isLordOf src target &&
  (g.staticAbilitiesOf src).any (fun ab =>
    match ab.trampleSubtypes? with
    | some subtypes => subtypes.any (g.hasSubtype target)
    | none => false)

/-- Lore counters among Sagas `p` controls. -/
def loreAmongSagas (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.saga.isSome then acc + o.status.lore else acc) 0

/-- True when `id` is the source of a chapter ability waiting or on the stack
(CR 714.4). -/
def sagaChapterPending (g : Game) (id : ObjectId) : Bool :=
  let waiting :=
    g.waitingTriggers.any (fun wt =>
      wt.source.id == id &&
        match wt.ability.shared with
        | .chapter .. => true
        | _ => false)
  let stacked :=
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.sourceId == some id &&
          match o.triggeredAbility with
          | some t =>
            match t.shared with
            | .chapter .. => true
            | _ => false
          | none => false
      | none => false)
  waiting || stacked

/-- Whether `o` currently has hexproof and indestructible from Tom Bombadil's
lore-threshold static. -/
def loreThresholdProtection (g : Game) (o : GameObject) : Bool :=
  match o.printed.hexproofIndestructibleIfLore, o.controller with
  | some n, some p => g.loreAmongSagas p ≥ n
  | _, _ => false

/-- True when a grantor of hexproof or damage prevention is still on the
battlefield. -/
def grantorStillInPlay (g : Game) (id : ObjectId) : Bool :=
  match g.findObject? id with
  | some o => o.isOnBattlefield
  | none => false

def hasHexproof (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.hexproof) || g.loreThresholdProtection o ||
    o.status.hexproofGrantedBy.any g.grantorStillInPlay ||
    g.equippedHexproofUnblockableThisTurn o ||
    (match o.controller with
     | none => false
     | some p =>
       (o.isCreature && o.status.gotPlusOneThisTurn &&
         (g.permanentsOf p).any (fun src =>
           src.printed.staticAbilities.any (fun
             | .hexproofIfPlusOneThisTurn => true
             | _ => false))) ||
       (g.permanentsOf p).any (fun src =>
         src.status.shield > 0 &&
           (g.staticAbilitiesOf src).any (fun
             | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
               src.id == o.id ||
                 (o.id != src.id && g.hasSubtype o subtype) ||
                 -- "you and other Heroes" — the player has hexproof via a dummy check
                 false
             | _ => false)))

/-- True when damage that would be dealt by `src` is prevented (Old Fat
Spider chapter II). -/
def sourceDamagePrevented (g : Game) (src : GameObject) : Bool :=
  src.status.preventDamageGrantedBy.any g.grantorStillInPlay

/-- Whether `o` has deathtouch, printed or granted until end of turn (CR 702.2). -/
def hasDeathtouch (g : Game) (o : GameObject) : Bool :=
  (g.retainedOrUntilEot o).deathtouch

/-- Whether `o` has indestructible (CR 702.12). An until-end-of-turn effect can
make it lose the keyword. -/
def leftoverIndestructible (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (g.staticAbilitiesOf o).any (fun
      | .indestructibleIfArtifactCreatureOrPlan => true
      | _ => false) &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun x =>
        (x.isCreature && x.printed.isArtifact) || g.hasSubtype x "Plan")

def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  ((g.retainedOrUntilEot o).indestructible ||
    o.status.indestructibleCounters > 0 ||
    g.loreThresholdProtection o ||
    g.leftoverIndestructible o) &&
  !(o.isOnBattlefield && o.status.untilEotLosesIndestructible)

/-- Mana value of `o` (CR 202.3). `{X}` is the chosen value while the object
is on the stack and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (_g : Game) (o : GameObject) : Nat :=
  let printed := o.printed.manaValue
  if o.zone != .stack then printed
  else printed + o.chosenX.getD 0

/-- Whether `o` has trample, printed, granted until end of turn, or granted by
a static ability (CR 702.19, 604.2). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  (g.retainedOrUntilEot o).trample ||
  o.status.trampleCounters > 0 ||
  (g.leftoverGrantedKeywords o).trample ||
  (o.isOnBattlefield && g.battlefield.any (fun src =>
    g.grantsTrampleTo src o ||
      (src.attachedTo == some o.id &&
        (g.staticAbilitiesOf src).any (fun
          | .equippedGetsTrampleAndCombatTreasures _ _ => true
          | _ => false))))

/-- Keywords including those granted by static abilities and until-EOT effects.
Printed keywords are absent while the object loses all abilities. Only
trample (lords) and indestructible (until-EOT loss) differ from
`retainedOrUntilEot`. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { g.retainedOrUntilEot o with
    indestructible := g.hasIndestructible o
    trample := g.hasTrample o }

end Game
end Mtg.Engine
