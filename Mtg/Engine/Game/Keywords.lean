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
      a.staticAbilities.any (fun ab => ab.enchantedOnlySubtype?.isSome))

/-- Whether `p` controls a Jace planeswalker. -/
def controlsJacePlaneswalker (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun x => x.printed.isPlaneswalker && g.hasSubtype x "Jace")

/-- Keywords Reality Fracture static abilities grant `o`: its own conditional
keywords, grants from permanents its controller controls, and grants from
attached Auras and Equipment. -/
def fraGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield then Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      let gy := (g.player p).graveyard.size
      let self := o.staticAbilities.foldl (fun acc ab =>
        match ab with
        | .firstStrikeDuringYourTurn =>
          if g.activePlayer == p then Keywords.merge acc Keyword.firstStrike else acc
        | .vigilanceIfJace =>
          if g.controlsJacePlaneswalker p then Keywords.merge acc Keyword.vigilance else acc
        | .powerAndFlyingIfSevenInGraveyard =>
          if gy ≥ 7 then Keywords.merge acc Keyword.flying else acc
        | .flyingHasteIfOpponentDealtNoncombat =>
          if (g.livingOpponents p).any (·.dealtNoncombatDamageThisTurn) then
            Keywords.merge acc (Keyword.flying.merge Keyword.haste)
          else acc
        | .hexproofUntilCombatDamage =>
          if o.status.dealtCombatDamage then acc else Keywords.merge acc Keyword.hexproof
        | _ => acc) Keywords.none
      let team := (g.permanentsOf p).foldl (fun acc src =>
        let other := src.id != o.id
        src.staticAbilities.foldl (fun acc ab =>
          let grant (cond : Bool) (k : Keywords) := if cond then Keywords.merge acc k else acc
          match ab with
          | .creaturesYouControlHaveTrample => grant o.isCreature Keyword.trample
          | .plusOneCreaturesHaveVigilance =>
            grant (o.isCreature && o.status.plusOnePlusOne > 0) Keyword.vigilance
          | .creatureTokensGetOneAndVigilance =>
            grant (o.isCreature && o.printed.isToken) Keyword.vigilance
          | .otherPlusOneCreaturesHaveHaste =>
            grant (other && o.isCreature && o.status.plusOnePlusOne > 0) Keyword.haste
          | .creaturesYouControlHaveHaste => grant o.isCreature Keyword.haste
          | .otherCreaturesHaveTrample #[] => grant (other && o.isCreature) Keyword.trample
          | .landsHaveHexproof => grant o.printed.isLand Keyword.hexproof
          | .thoptersHaveHaste => grant (g.hasSubtype o "Thopter") Keyword.haste
          | .artifactCreaturesHaveVigilance =>
            grant (o.isCreature && o.printed.isArtifact) Keyword.vigilance
          | _ => acc) acc) Keywords.none
      let attached := g.battlefield.foldl (fun acc a =>
        if a.attachedTo != some o.id then acc
        else
          a.staticAbilities.foldl (fun acc ab =>
            match ab with
            | .equippedMedicsKitesail => Keywords.merge acc Keyword.flying
            | .enchantedGetsOneAndDeathtouch => Keywords.merge acc Keyword.deathtouch
            | _ => acc) acc) Keywords.none
      Keywords.mergeAll #[self, team, attached]

/-- Whether `o` may attack as though it didn't have defender (Surveillance
Phantasm; Ghalta the Immovable). -/
def mayAttackDespiteDefender (g : Game) (o : GameObject) : Bool :=
  match o.controller with
  | none => false
  | some p =>
    let pl := g.player p
    (o.staticAbilities.any (· == .fra .attackDespiteDefenderIfScried) &&
      (pl.scriedThisTurn || pl.surveilledThisTurn)) ||
    (g.permanentsOf p).any (·.staticAbilities.any (· == .fra .creaturesAttackDespiteDefender))


/-- Whether `p` currently controls a permanent with any of these subtypes. -/
def controlsAnySubtype (g : Game) (p : PlayerId) (subtypes : Array String) : Bool :=
  (g.permanentsOf p).any (fun o => subtypes.any (g.hasSubtype o))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : String) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Whether `p` currently controls a legendary creature. -/
def controlsLegendaryCreature (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.isCreature && o.printed.hasSupertype .legendary)

/-- Whether `p` currently controls an Equipment. -/
def controlsEquipment (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.isEquipment)

/-- Whether `blocker`'s static abilities currently allow it to be declared as
a blocker (CR 509.1b). Checked only when declaring blockers. -/
def mayDeclareAsBlocker (g : Game) (blocker : GameObject) : Bool :=
  blocker.staticAbilities.all (fun ab =>
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
          (aura.staticAbilities.foldl (fun k ab =>
            Keywords.merge k ab.hostKeywords) Keywords.none)
      else acc) Keywords.none

/-- True when an attached Aura makes `o` lose all abilities (Enchanted
River's Grasp; Frozen in Ice). -/
def attachedLosesAbilities (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun aura =>
    aura.attachedTo == some o.id &&
      aura.staticAbilities.any (fun
        | .enchantedLosesAbilitiesDoesntUntap => true
        | .enchantedLosesAbilitiesCantUntap => true
        | _ => false))

/-- Printed abilities still apply unless The Wondrous Wasp (or similar)
is making the permanent lose them (MSH 145 / 190), or an Aura strips them. -/
def retainsPrintedAbilities (g : Game) (o : GameObject) : Bool :=
  !o.status.faceDown &&
  !g.attachedLosesAbilities o && !o.status.losesAbilitiesUntilEot &&
  !o.status.losesAbilitiesGrantedBy.any (fun id =>
    match g.findObject? id with
    | some src => src.isOnBattlefield
    | none => false)

/-- During your turn, creatures you control that are equipped gain these
keywords (Long-Lost Lances). -/
def equippedDuringYourTurnKeywords (g : Game) (o : GameObject) : Keywords :=
  if !o.isOnBattlefield || !o.isCreature || g.attachedEquipmentCount o == 0 then
    Keywords.none
  else
    match o.controller with
    | none => Keywords.none
    | some p =>
      if g.activePlayer != p then Keywords.none
      else
        (g.permanentsOf p).foldl (fun acc src =>
          src.staticAbilities.foldl (fun acc ab =>
            Keywords.merge acc (ab.equippedTeamKeywordsDuringYourTurn)) acc)
          Keywords.none

def leftoverGrantedKeywords (g : Game) (o : GameObject) : Keywords :=
  let self :=
    o.staticAbilities.foldl (fun acc ab =>
      match ab with
      | .flyingIfPlusOneThisTurn =>
        if o.status.gotPlusOneThisTurn then Keywords.merge acc Keyword.flying else acc
      | _ => acc) Keywords.none
  let fromTeam :=
    match o.controller with
    | none => Keywords.none
    | some p =>
      (g.permanentsOf p).foldl (fun acc src =>
        src.staticAbilities.foldl (fun acc ab =>
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
  Keywords.merge (Keywords.merge self fromTeam) (g.fraGrantedKeywords o)

def currentKeywords (g : Game) (o : GameObject) : Keywords :=
  let printedKw :=
    if g.retainsPrintedAbilities o then o.printed.keywords else Keywords.none
  let base :=
    Keywords.merge
      (Keywords.merge
        (Keywords.merge
          (Keywords.merge
            (Keywords.merge (Keywords.merge printedKw o.grantedUntilEot)
              (g.attachedGrantedKeywords o))
            (g.enduringStoryKeywords o))
          (g.leftoverGrantedKeywords o))
        (g.equippedDuringYourTurnKeywords o))
      o.status.keywordCounters.toKeywords
  let base := if o.status.shadow > 0 then { base with shadow := true } else base
  let base :=
    if o.status.firstStrikeOnYourTurn && o.controller == some g.activePlayer then
      { base with firstStrike := true }
    else base
  let base :=
    match o.controller with
    | some p =>
      let flying :=
        o.isCreature &&
          (g.objects.filter (fun e => e.zone == .command && e.controlledBy p)).any
            (·.printed.grantTeamPlusTwoFlying)
      let toxicLink :=
        o.printed.toxic > 0 &&
          (g.permanentsOf p).any (·.printed.corruptedToxicLifelink) &&
          (g.livingOpponents p).any (fun opp => opp.poison >= 3)
      let base := if flying then { base with flying := true } else base
      if toxicLink then { base with lifelink := true } else base
    | none => base
  base

/-- Haste from printed text, attachments, enduring story, counters, or
“haste as long as you control another …”. Lost abilities are omitted. -/
def hasHaste (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).haste ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.hasteIfOtherSubtype? with
      | none => false
      | some t =>
        match o.controller with
        | none => false
        | some p =>
          (g.permanentsOf p).any (fun x => x.id != o.id && g.hasSubtype x t)))

def canAttack (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature &&
  o.controlledBy g.activePlayer &&
  !o.status.tapped && (!(g.currentKeywords o).defender || g.mayAttackDespiteDefender o) &&
  !(o.status.summoningSick && !g.hasHaste o) &&
  !g.enchantedCantAttackOrBlock o &&
  o.staticAbilities.all (fun ab =>
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

/-- Loyalty counters among Jace planeswalkers `p` controls. -/
def jaceLoyaltyAmong (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if o.printed.isPlaneswalker && g.hasSubtype o "Jace" then acc + o.status.loyaltyCounters
    else acc) 0

/-- Evaluate a `NumberSelector` on `p`'s board state (CR 107.1 / 601.2f). -/
def boardNumber (g : Game) (p : PlayerId) (amount : NumberSelector)
    (target : Option GameObject := none) : Option Int :=
  match amount with
  | .fixed n => some n
  | .count .landsYouControl => some (Int.ofNat (g.landsYouControl p))
  | .basicLandsYouControl =>
    some (Int.ofNat ((g.permanentsOf p).filter (fun o => isBasicLandCard o.printed)).size)
  | .opponentLands =>
    some (Int.ofNat ((g.livingOpponents p).foldl (fun acc pl =>
      acc + ((g.permanentsOf pl.id).filter (·.printed.isLand)).size) 0))
  | .count .planeswalkersYouControl =>
    some (Int.ofNat ((g.permanentsOf p).filter (·.printed.isPlaneswalker)).size)
  | .count .equipmentYouControl =>
    some (Int.ofNat ((g.permanentsOf p).filter (·.printed.isEquipment)).size)
  | .creaturesDiedThisTurn =>
    some (Int.ofNat (Nat.max g.creatureDeathsThisTurn (if g.creatureDiedThisTurn then 1 else 0)))
  | .subtypeCount st | .perSubtype st =>
    let n :=
      if st == "legendary creature" then
        ((g.permanentsOf p).filter (fun o => o.isCreature && o.isLegendary)).size
      else if st == "Equipment" then
        ((g.permanentsOf p).filter (·.printed.isEquipment)).size
      else
        g.countSubtype p (if st == "Elves" then "Elf" else st)
    some (Int.ofNat n)
  | .totalFlyingPower =>
    some (Int.ofNat ((g.permanentsOf p).foldl (fun acc o =>
      if o.isCreature && g.hasFlying o then acc + (g.power o).toNat else acc) 0))
  | .greatestPower =>
    some (Int.ofNat ((g.creaturesControlledBy p).foldl (fun acc o => Nat.max acc (g.power o).toNat) 0))
  | .greatestToughness =>
    some (Int.ofNat ((g.creaturesControlledBy p).foldl (fun acc o => Nat.max acc (g.toughness o).toNat) 0))
  | .oppArtifacts =>
    some (Int.ofNat (g.players.foldl (fun acc pl =>
      if pl.id == p || pl.lost then acc
      else max acc ((g.permanentsOf pl.id).filter (·.printed.isArtifact)).size) 0))
  | .targetPlusOneCounters =>
    target.map (fun o => Int.ofNat o.status.plusOnePlusOne)
  | _ => none

/-- Evaluate a `ConditionSelector` on `p`'s board state (CR 601.2 / 602.5b / 603.4 / 614.1c). -/
partial def boardConditionHolds (g : Game) (p : PlayerId) (cond : ConditionSelector)
    (target : Option GameObject := none) (source : Option GameObject := none)
    (causeStatus : Option Status := none) : Bool :=
  let pl := g.player p
  match cond with
  | .none => true
  | .not inner => !g.boardConditionHolds p inner target source causeStatus
  | .or conds => conds.any (fun c => g.boardConditionHolds p c target source causeStatus)
  | .atLeast left right =>
    match g.boardNumber p left target, g.boardNumber p right target with
    | some a, some b => a ≥ b
    | _, _ => false
  | .youControlLegendary => g.controlsLegendaryCreature p
  | .youControlSubtype st =>
    if st == "legendary creature" then g.controlsLegendaryCreature p
    else if st == "Equipment" then g.controlsEquipment p
    else g.controlsAnySubtype p #[st]
  | .youControlAnySubtype sts => g.controlsAnySubtype p sts
  | .youControlCreatureWithPower n => g.greatestPowerAmongCreatures p ≥ n
  | .youControlCreatureToughnessAtLeast n =>
    (g.permanentsOf p).any (fun x => x.isCreature && g.toughness x >= (n : Int))
  | .graveyardAtLeast n => pl.graveyard.size ≥ n
  | .gyCreaturesAtLeast n =>
    (pl.graveyard.filter (fun id => (g.findObject? id).any (·.printed.isCreature))).size ≥ n
  | .jaceLoyaltyAtLeast n => g.jaceLoyaltyAmong p ≥ n
  | .sourceNotToken => !(source.any (·.printed.isToken))
  | .sourceWasCast => source.any (·.wasCast)
  | .causeHadCounters => causeStatus.any (·.hasCounters)
  | .sourceHasCounters =>
    source.any (fun o => (g.findObject? o.id).any (·.status.hasCounters))
  | .targetDamaged => target.any (fun o => o.status.damage > 0)
  | .targetTapped => target.any (·.status.tapped)
  | .targetAttackingNontoken => target.any (fun o => o.status.attacking && !o.printed.isToken)
  | .targetAttacking => target.any (·.status.attacking)
  | .targetPowerAtMost most => target.any (fun o => o.isCreature && g.power o ≤ most)
  | .anotherCreaturePowerAtMost _ => true
  | .scriedThisTurn => pl.scriedThisTurn
  | .surveilledThisTurn => pl.surveilledThisTurn
  | .scriedOrSurveilledThisTurn => pl.scriedThisTurn || pl.surveilledThisTurn
  | .youAttackedWithTwoOrMore => pl.creaturesAttackedWithThisTurn ≥ 2
  | .opponentDealtNoncombatDamage =>
    (g.livingOpponents p).any (·.dealtNoncombatDamageThisTurn)
  | .opponentDealtNoncombatDamageLastTurn =>
    (g.livingOpponents p).any (·.dealtNoncombatDamageLastTurn)
  | .twoCreaturesDiedThisTurn => g.creatureDeathsThisTurn ≥ 2
  | .drewThreeThisTurn => pl.cardsDrawnThisTurn ≥ 3
  | .castNoSpellThisTurn => pl.spellsCastThisTurn == 0
  | .activatedLoyaltyThisTurn => pl.activatedLoyaltyThisTurn
  | .gainedLifeAtLeast n => pl.lifeGainedThisTurn ≥ n
  | _ => false

/-- Generic mana subtracted from a spell or activated ability cost by `r`
(CR 601.2f / 602.2b). When `target` is `none`, target-dependent reductions
evaluate to `0`; when `target` is `some o`, only target-dependent reductions
evaluate. -/
def costReductionAmount (g : Game) (p : PlayerId) (r : CostReduction)
    (target : Option GameObject := none) : Nat :=
  let isTargetCond : ConditionSelector → Bool
    | .targetDamaged | .targetTapped | .targetAttackingNontoken
    | .targetAttacking | .targetPowerAtMost _ => true
    | _ => false
  let isTargetNumber : NumberSelector → Bool
    | .targetPlusOneCounters => true
    | _ => false
  match r with
  | .none => 0
  | .when n cond =>
    if isTargetCond cond != target.isSome then 0
    else if g.boardConditionHolds p cond (target := target) then n else 0
  | .byAmount amount perUnit =>
    if isTargetNumber amount != target.isSome then 0
    else
      match g.boardNumber p amount (target := target) with
      | some k => k.toNat * perUnit
      | none => 0

/-- Whether this face should enter tapped given the controller's board. It is
checked before the permanent enters, so lands or planeswalkers entering at
the same time are not counted (rulings 808 / 809). -/
def entersTapped (g : Game) (p : PlayerId) (card : CardDef) : Bool :=
  card.staticAbilities.any (· == .fra .entersTappedChooseColor) ||
    match card.entersTappedRule with
    | .untapped | .unlessPayLife _ => false
    | .always => true
    | .unless cond => !g.boardConditionHolds p cond

/-- Okoye: attacking creature tokens you control have first strike. -/
def okoyeGrantsFirstStrike (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.status.attacking && o.printed.isToken &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any (fun
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
        eq.staticAbilities.any (fun
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
        eq.staticAbilities.any StaticAbility.equippedCantBeBlocked)

/-- Whether `o` can't be blocked, printed or granted until end of turn
(CR 509.1b / 611.2a), or while its power is at most a listed value. -/
def hasCantBeBlocked (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.cantBeBlocked) ||
  g.equippedHexproofUnblockableThisTurn o ||
  g.equippedCantBeBlockedNow o ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedIfPowerAtMost? with
      | some n => g.snapshotPower o <= n
      | none => false)) ||
  -- Tetsuko Umezawa, Fugitive: checked as blockers are declared, so a
  -- creature already blocked stays blocked (ruling 842).
  (o.isOnBattlefield && o.isCreature &&
    (g.snapshotPower o <= 1 || g.snapshotToughness o <= 1) &&
    match o.controller with
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any (fun
          | .smallCreaturesYouControlUnblockable => true
          | _ => false))
    | none => false)

/-- Whether `o` has lifelink, printed, granted until end of turn, or from a
lifelink counter (CR 702.15). -/
def hasLifelink (g : Game) (o : GameObject) : Bool :=
  g.hasKeyword o (·.lifelink) ||
  (o.isOnBattlefield &&
    o.staticAbilities.any (fun ab =>
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
  (g.currentKeywords o).menace ||
  (o.isOnBattlefield && o.status.plusOnePlusOne > 0 &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun src =>
        src.staticAbilities.any StaticAbility.creaturesWithPlusOneHaveMenace))

/-- Minimum number of creatures required to block `o`, or `0` if unrestricted.
Menace is 2; Troll of Khazad-dûm is 3. -/
def minBlockersRequired (g : Game) (o : GameObject) : Nat :=
  let fromStatic :=
    o.staticAbilities.foldl (fun acc ab =>
      match ab.cantBeBlockedExcept? with
      | some n => max acc n
      | none => acc) 0
  max fromStatic (if g.hasMenace o then 2 else 0)

/-- Maximum number of creatures that may block `o`, if a static caps it. -/
def maxBlockersAllowed (_g : Game) (o : GameObject) : Option Nat :=
  o.staticAbilities.foldl (fun acc ab =>
    match ab.cantBeBlockedByMoreThan? with
    | some n =>
      some (match acc with
        | some m => min m n
        | none => n)
    | none => acc) none

/-- True when `n` blockers is a legal number for `attacker` (CR 702.111b).
Zero is always legal (the attacker is unblocked). -/
def legalBlockerCount (g : Game) (attacker : GameObject) (n : Nat) : Bool :=
  let need := g.minBlockersRequired attacker
  let underMax :=
    match g.maxBlockersAllowed attacker with
    | none => true
    | some m => n ≤ m
  (n == 0 || need <= 1 || n >= need) && underMax

/-- Creatures with flying can't attack this player or block their creatures. -/
def leftoverFlyingRestriction (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
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
  blocker.status.blocking.isEmpty && !blocker.status.cantBlockUntilEot &&
  !blocker.printed.cantBlock &&
  g.mayDeclareAsBlocker blocker &&
  !g.enchantedCantAttackOrBlock blocker &&
  (!g.creaturesWithoutFlyingCantBlock || g.hasFlying blocker) &&
  attacker.status.attacking &&
  !g.hasCantBeBlocked attacker &&
  !islandwalkUnblockable &&
  !(attacker.staticAbilities.any StaticAbility.blocksTokens &&
    blocker.printed.isToken) &&
  !(attacker.staticAbilities.any (fun ab =>
      match ab.cantBeBlockedByPowerAtMost? with
      | some n => g.snapshotPower blocker <= n
      | none => false)) &&
  !(attacker.staticAbilities.any (fun ab =>
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
  src.staticAbilities.any (fun ab =>
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
      wt.source.id == id && wt.ability.sagaChapterNumber?.isSome)
  let stacked :=
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.sourceId == some id &&
          o.triggeredAbility.any (·.sagaChapterNumber?.isSome)
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
           src.staticAbilities.any (fun
             | .youAndOtherSubtypeHaveHexproofIfShield subtype =>
               -- “You and other Heroes”: the source itself is not included.
               src.id != o.id && g.hasSubtype o subtype
             | _ => false)))

/-- The player has hexproof from opponents (Captain America, Super-Soldier). -/
def playerHasHexproof (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun src =>
    src.status.shield > 0 &&
      src.staticAbilities.any (fun
        | .youAndOtherSubtypeHaveHexproofIfShield _ => true
        | _ => false))

/-- Protection from the source's colors or from its card type. -/
def frcProtectedFrom (g : Game) (o src : GameObject) : Bool :=
  let colorBlock := o.printed.protectionFromColors.any (src.printed.colors.contains ·)
  let typeMatch (em : GameObject) :=
    em.printed.protectionFromChosenCardType &&
      match em.status.chosenCardType with
      | some t => src.printed.types.any (fun ty => CardType.englishName ty == t)
      | none => false
  colorBlock || typeMatch o ||
    match o.controller with
    | some p => (g.permanentsOf p).any typeMatch
    | none => false

/-- Hexproof stops an opponent from targeting that player (CR 702.11c). -/
def playerCanBeTargetedBy (g : Game) (caster target : PlayerId) : Bool :=
  let typeBlock :=
    match (g.resolvingSpell.orElse (fun _ => g.proposedSpell.map (·.spellId))).bind g.findObject? with
    | none => false
    | some src =>
      (g.permanentsOf target).any (fun em =>
        em.printed.protectionFromChosenCardType &&
          match em.status.chosenCardType with
          | some t => src.printed.types.any (fun ty => CardType.englishName ty == t)
          | none => false)
  (caster == target || !g.playerHasHexproof target) &&
    !(g.player target).protectionFromEverything && !typeBlock

/-- True when damage that would be dealt by `src` is prevented (Old Fat
Spider chapter II). -/
def sourceDamagePrevented (g : Game) (src : GameObject) : Bool :=
  src.status.preventDamageGrantedBy.any g.grantorStillInPlay

/-- Whether `o` has deathtouch, printed or granted until end of turn (CR 702.2). -/
def hasDeathtouch (g : Game) (o : GameObject) : Bool :=
  hasPrintedOrEot o (·.deathtouch) || o.status.keywordCounters.deathtouch > 0 ||
    (g.fraGrantedKeywords o).deathtouch

/-- Whether `o` has indestructible (CR 702.12). An until-end-of-turn effect can
make it lose the keyword. -/
def leftoverIndestructible (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    o.staticAbilities.any (fun
      | .indestructibleIfArtifactCreatureOrPlan => true
      | _ => false) &&
    match o.controller with
    | none => false
    | some p =>
      (g.permanentsOf p).any (fun x =>
        (x.isCreature && x.printed.isArtifact) || g.hasSubtype x "Plan")

def hasIndestructible (g : Game) (o : GameObject) : Bool :=
  ((g.currentKeywords o).indestructible ||
    g.loreThresholdProtection o ||
    g.leftoverIndestructible o) &&
  !(o.isOnBattlefield && o.status.untilEotLosesIndestructible)

/-- Mana value of `o` (CR 202.3). `{X}` is the chosen value while the object
is on the stack and 0 otherwise (rulings 178 / 185 / 186). -/
def objectManaValue (_g : Game) (o : GameObject) : Nat :=
  let printed := o.printed.manaValue
  if o.zone != .stack then printed
  else printed + o.chosenX.getD 0

/-- The Reaver Cleaver: combat damage to a player or planeswalker makes Treasures. -/
def equippedCreatesCombatTreasures (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    g.battlefield.any (fun eq =>
      eq.attachedTo == some o.id &&
        eq.staticAbilities.any (fun
          | .equippedGetsTrampleAndCombatTreasures _ _ => true
          | _ => false))

/-- Whether `o` has trample, printed, granted, or from a lord (CR 702.19). -/
def hasTrample (g : Game) (o : GameObject) : Bool :=
  (g.currentKeywords o).trample ||
  (o.isOnBattlefield && g.battlefield.any (fun src => g.grantsTrampleTo src o)) ||
  g.equippedCreatesCombatTreasures o

/-- Keywords including those granted by static abilities and until-EOT effects.
Only trample (lords) and indestructible (until-EOT loss) differ from
`printedOrUntilEot`; overlaying the other keywords would restate identity. -/
def effectiveKeywords (g : Game) (o : GameObject) : Keywords :=
  { Keywords.merge o.printedOrUntilEot (g.fraGrantedKeywords o) with
    indestructible := g.hasIndestructible o
    trample := g.hasTrample o }

end Game
end Mtg.Engine
