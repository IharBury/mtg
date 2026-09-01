import Mtg.Engine.Game.SpellResolution

/-!
# Combat (CR 506–510)

Declaring attackers and blockers, combat-damage assignment checks and
defaults, dealing assigned combat damage (deathtouch, trample, lifelink,
CR 510.1c–d / 702.19b), and clearing combat (CR 511.3).
-/

namespace Mtg.Engine
namespace Game

def declareAttackers (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (defender : Option PlayerId := none) (each : Array (Option PlayerId) := #[]) :
    Except String Game := do
  if g.pending != .declareAttackers || g.priorityInstead g.activePlayer != p then
    throw "Not time to declare attackers"
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    let o := g.object! id
    if !g.canAttack o then
      throw s!"{o.name} cannot attack"
    let want :=
      match each[i]? with
      | some (some d) => some d
      | some none => defender
      | none => defender
    let dest ← g.resolveAttackDestination p want
    if g.hasFlying o && g.leftoverFlyingRestriction dest then
      throw s!"{o.name} can't attack {(g.player dest).name}"
    g := g.setObject { o with status := { o.status with
      attacking := true
      attackingWhom := some dest
      declaredAsAttackerThisTurn := true } }
    if !g.hasVigilance (g.object! id) then
      g := g.becomeTapped (g.object! id)
    g := g.logMsg
      s!"{g.player p |>.name} attacks {(g.player dest).name} with {o.name}"
  if ids.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not attack"
  g := g.putAttackTriggersOnStack p ids
  g := { g with pending := .none }
  g := g.promptTriggerTargetsIfNeeded
  if g.pending != .none then
    return g
  return g.receivePriority p

def declareBlockers (g : Game) (p : PlayerId) (assignments : Array (ObjectId × ObjectId)) :
    Except String Game := do
  if g.pending != .declareBlockers then
    throw "Not time to declare blockers"
  if p != g.currentBlockersPlayer then
    throw "Only the defending player declares blockers"
  let mut g := g
  for (blockerId, attackerId) in assignments do
    let b := g.object! blockerId
    let a := g.object! attackerId
    if !g.canBlock b a then
      throw s!"{b.name} cannot block {a.name}"
    g := g.setObject { b with status := { b.status with blocking := #[attackerId] } }
    let aNow := g.object! attackerId
    g := g.setObject { aNow with status := { aNow.status with blocked := true } }
    g := g.logMsg s!"{b.name} blocks {a.name}"
  -- CR 509.1c / 702.111: a menace (or “except by N or more”) creature that is
  -- blocked must be blocked by at least that many creatures.
  for o in g.battlefield do
    if o.status.attacking then
      let need := g.minBlockersRequired o
      if need > 1 then
        let n := (g.blockersOf o.id).size
        if n > 0 && n < need then
          let word := if need == 2 then "two" else toString need
          throw s!"{o.name} can't be blocked except by {word} or more creatures"
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  g := g.putBlockedTriggersOnStack assignments
  let rest := g.blockersQueue.extract 1 g.blockersQueue.size
  if rest.isEmpty then
    return { g with pending := .none, blockersQueue := #[] } |>.receivePriority g.activePlayer
  else
    return { g with pending := .declareBlockers, blockersQueue := rest }

/-- Sum of combat damage this assignment sends to creatures. -/
def creatureDamageTotal (asgn : CreatureCombatAssignment) : Int :=
  asgn.toCreatures.foldl (fun acc (_, n) => acc + n) 0

/-- A legal default assignment for `source` (CR 510.1c–d, 702.19).
Without trample, all damage goes to the first remaining recipient — one
legal division under 510.1c/d. With trample, lethal is assigned to each
blocker before leftover goes to the defending player. -/
def defaultCombatAssignment (g : Game) (source : GameObject) (forAttackers : Bool)
    (already : Array CreatureCombatAssignment) : CreatureCombatAssignment :=
  let dmg := max (g.power source) 0
  let defender := source.status.attackingWhom.getD g.defendingPlayer
  let playerDmg := if (g.player defender).lost then 0 else dmg
  if forAttackers then
    let blockers := g.blockersOf source.id
    if blockers.isEmpty then
      if source.status.blocked && !g.hasTrample source then
        { source := source.id }
      else
        { source := source.id, toPlayer := playerDmg }
    else if g.hasTrample source then
      Id.run do
        let mut remaining := dmg
        let mut toCreatures : Array (ObjectId × Int) := #[]
        let mut already := already
        for b in blockers do
          let need := g.lethalRemaining b already (fromDeathtouch := g.hasDeathtouch source)
          let amt := min remaining need
          toCreatures := toCreatures.push (b.id, amt)
          already := already.push { source := source.id, toCreatures := #[(b.id, amt)] }
          remaining := remaining - amt
        let toPlayer := if (g.player defender).lost then 0 else remaining
        return { source := source.id, toCreatures := toCreatures, toPlayer := toPlayer }
    else
      { source := source.id, toCreatures := #[(blockers[0]!.id, dmg)] }
  else
    let targets := g.creaturesBlockedBy source
    if targets.isEmpty then { source := source.id }
    else { source := source.id, toCreatures := #[(targets[0]!.id, dmg)] }

/-- Fill in a default for every assigning creature not listed in `listed`. -/
def completeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String (Array CreatureCombatAssignment) := do
  let mut acc : Array CreatureCombatAssignment := #[]
  let mut seen : Array ObjectId := #[]
  let assigning := g.creaturesAssigningCombatDamage forAttackers
  for a in listed do
    if seen.contains a.source then
      throw "Duplicate combat damage source"
    if !assigning.any (fun o => o.id == a.source) then
      throw "That creature does not assign combat damage now"
    seen := seen.push a.source
    acc := acc.push a
  for o in assigning do
    if !seen.contains o.id then
      let asgn := g.defaultCombatAssignment o forAttackers acc
      acc := acc.push asgn
      seen := seen.push o.id
  return acc

/-- Check one creature's assignment against CR 510.1a–d and trample (702.19b).
`batch` is the complete assignment for this half of 510.1, so lethal can
include damage from other creatures (CR 510.1e / 702.19b). -/
def checkCombatAssignment (g : Game) (asgn : CreatureCombatAssignment) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  let some src := g.findObject? asgn.source | throw "no such object"
  if !src.isOnBattlefield then
    throw s!"{src.name} is not on the battlefield"
  let defender := src.status.attackingWhom.getD g.defendingPlayer
  let dmg := max (g.power src) 0
  if asgn.toPlayer < 0 || asgn.toCreatures.any (fun (_, n) => n < 0) then
    throw "Combat damage amounts cannot be negative"
  let mut seenTargets : Array ObjectId := #[]
  for (tid, _) in asgn.toCreatures do
    if seenTargets.contains tid then
      throw "Duplicate combat damage recipient"
    seenTargets := seenTargets.push tid
  let recipients := g.legalCombatDamageRecipients src forAttackers
  for (tid, _) in asgn.toCreatures do
    if !recipients.any (fun r => r.id == tid) then
      if forAttackers then
        throw s!"{src.name} must assign combat damage to the creatures blocking it (CR 510.1c)"
      else
        throw s!"{src.name} must assign combat damage to the creatures it's blocking (CR 510.1d)"
  let toCreatures := creatureDamageTotal asgn
  if forAttackers then
    if !src.status.attacking then
      throw s!"{src.name} is not attacking"
    if recipients.isEmpty then
      if asgn.toCreatures.size != 0 then
        throw s!"{src.name} has no blocking creatures to assign combat damage to"
      if src.status.blocked && !g.hasTrample src then
        if asgn.toPlayer != 0 then
          throw s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if (g.player defender).lost then
        if asgn.toPlayer != 0 then
          throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
      else if asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
    else
      if (g.player defender).lost then
        if asgn.toPlayer != 0 then
          throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
        if toCreatures > dmg then
          throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
      else if toCreatures + asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
      if asgn.toPlayer > 0 then
        if !g.hasTrample src then
          throw s!"{src.name} cannot assign combat damage to the defending player"
        if recipients.any (fun b => g.lethalRemaining b batch > 0) then
          throw s!"{src.name} must assign lethal damage to each blocking creature before trampling (CR 702.19b)"
  else
    if src.status.blocking.isEmpty then
      throw s!"{src.name} is not blocking"
    if asgn.toPlayer != 0 then
      throw s!"{src.name} assigns combat damage to the creatures it's blocking (CR 510.1d)"
    if recipients.isEmpty then
      if toCreatures != 0 then
        throw s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
    else if toCreatures != dmg then
      throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"

/-- CR 510.1e: the total assignment is legal only if every creature complies. -/
def checkCombatAssignmentBatch (g : Game) (forAttackers : Bool)
    (batch : Array CreatureCombatAssignment) : Except String Unit := do
  for a in batch do
    let _ ← checkCombatAssignment g a forAttackers batch
  let expected := (g.creaturesAssigningCombatDamage forAttackers).map (·.id)
  if batch.size != expected.size || !expected.all (fun id => batch.any (·.source == id)) then
    throw "Every attacking or blocking creature must assign combat damage (CR 510.1)"

/-- Apply assigned combat damage simultaneously (CR 510.2). -/
def dealAssignedCombatDamage (g : Game) : Game :=
  Id.run do
    let mut g := g
    for asgn in g.assignedCombatDamage do
      let src := g.object! asgn.source
      let defn :=
        match src.status.attackingWhom with
        | some pid => pid
        | none => g.defendingPlayer
      let mut totalDealt : Int := 0
      let recipients :=
        if src.status.attacking then g.blockersOf src.id else g.creaturesBlockedBy src
      if src.status.attacking && src.status.blocked && recipients.isEmpty &&
          asgn.toPlayer == 0 then
        g := g.logMsg
          s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if !src.status.blocking.isEmpty && recipients.isEmpty then
        g := g.logMsg
          s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
      if g.sourceDamagePrevented src then
        g := g.logMsg s!"combat damage from {src.name} is prevented"
      else
        for (tid, amt) in asgn.toCreatures do
          if amt > 0 then
            let amt := g.replacedDamageAmount src amt (combat := true)
            let t := g.object! tid
            g := g.markDamageOn t amt
              s!"{src.name} deals {amt} combat damage to {t.name}"
              (deathtouch := g.hasDeathtouch src) (combat := true)
            totalDealt := totalDealt + amt
      if !g.sourceDamagePrevented src && asgn.toPlayer > 0 &&
          !(g.player defn).lost then
        let toPlayer := g.replacedDamageAmount src asgn.toPlayer (combat := true)
        let pl := g.player defn
        g := g.setPlayer { pl with life := pl.life - toPlayer }
        totalDealt := totalDealt + toPlayer
        if src.status.blocked then
          g := g.logMsg
            s!"{src.name} tramples for {toPlayer} to {pl.name} ({(g.player defn).life} life)"
        else
          g := g.logMsg
            s!"{src.name} deals {toPlayer} combat damage to {pl.name} ({(g.player defn).life} life)"
      if g.hasLifelink src && totalDealt > 0 then
        match src.controller with
        | some pid => g := g.gainLife pid totalDealt.toNat
        | none => pure ()
      if asgn.toPlayer > 0 && !(g.player defn).lost then
        match src.controller with
        | some pid =>
          g := { g with lastCombatDamagePlayer := some defn }
          g := g.putMatchingSourceTriggers pid src .dealsCombatDamageToPlayer
          g := g.putMatchingSourceTriggers pid src .dealsCombatDamageToPlayerOrBattle
          if src.isCreature then
            for o in g.permanentsOf pid do
              for ab in o.printed.triggeredAbilities do
                match ab with
                | .triggered _ _ opts =>
                  match ab.shared, opts.watchedSubtype with
                  | .createTokens .., some subtype =>
                    if o.id != src.id && g.hasSubtype src subtype then
                      g := g.queueTrigger pid o ab .dealsCombatDamageToPlayerOrBattle
                  | _, _ => pure ()
          if g.hasSubtype src "Army" then
            g := g.putControlledTriggers pid .armyYouControlCombatDamage
          for eq in g.battlefield do
            if eq.attachedTo == some src.id then
              match eq.controller with
              | some c =>
                g := g.putMatchingSourceTriggers c eq
                  .equippedDealsCombatDamageToPlayer
                  (some asgn.toPlayer)
              | none => pure ()
          if src.status.combatDamageCreatesTreasure then
            g := g.createTreasureTokens pid asgn.toPlayer.toNat
          g := g.putControlledTriggers defn .combatDamageToYou
          g := { g with lastLifeLost := some (defn, asgn.toPlayer.toNat) }
          g := g.livingPlayers.foldl (fun acc pl =>
            acc.putControlledTriggers pl.id .playerLosesLife) g
        | none => pure ()
    let pendingRegular :=
      g.combatHasFirstStrike && !g.firstStrikeDamageDone
    let assignedFs :=
      if pendingRegular then
        g.firstStrikeAssignedThisCombat ++ g.assignedCombatDamage.map (·.source)
      else g.firstStrikeAssignedThisCombat
    g := { g with
      assignedCombatDamage := #[]
      pending := .none
      firstStrikeDamageDone := g.firstStrikeDamageDone || g.combatHasFirstStrike
      pendingRegularCombatDamage := pendingRegular
      firstStrikeAssignedThisCombat := assignedFs }
    return g.receivePriority g.activePlayer

/-- Record a legal assignment batch and append it for later dealing. -/
def storeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  let batch ← g.completeCombatAssignments forAttackers listed
  let _ ← checkCombatAssignmentBatch g forAttackers batch
  return { g with assignedCombatDamage := g.assignedCombatDamage ++ batch }

/-- After attackers have assigned, the defending player assigns (CR 510.1d)
or damage is dealt if they have no division to announce. -/
def finishAttackerCombatAssignment (g : Game) : Game :=
  let defender := g.defendingPlayer
  if g.needsCombatDamageChoice false then
    { g with pending := .assignCombatDamage defender false }
      |>.logMsg s!"{(g.player defender).name} assigns combat damage (CR 510.1d)"
  else
    match g.storeCombatAssignments false #[] with
    | .ok g' => g'.dealAssignedCombatDamage
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Start CR 510.1: the active player assigns attacking creatures first. -/
def beginCombatDamageAssignment (g : Game) : Game :=
  let g := { g with assignedCombatDamage := #[], pending := .none }
  if g.needsCombatDamageChoice true then
    { g with pending := .assignCombatDamage g.activePlayer true }
      |>.logMsg s!"{(g.player g.activePlayer).name} assigns combat damage (CR 510.1c)"
  else
    match g.storeCombatAssignments true #[] with
    | .ok g' => g'.finishAttackerCombatAssignment
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- Assign and deal combat damage (CR 510.1–510.2). -/
def combatDamage (g : Game) : Game :=
  g.beginCombatDamageAssignment

/-- Announce how attacking or blocking creatures assign combat damage (CR 510.1). -/
def announceCombatDamage (g : Game) (p : PlayerId)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  match g.pending with
  | .assignCombatDamage q forAttackers =>
    if p != q then
      throw s!"Only {(g.player q).name} may assign combat damage (CR 510.1)"
    let g ← g.storeCombatAssignments forAttackers listed
    if forAttackers then
      return g.finishAttackerCombatAssignment
    else
      return g.dealAssignedCombatDamage
  | _ => throw "Not time to assign combat damage (CR 510.1)"

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := { g with
      firstStrikeDamageDone := false
      pendingRegularCombatDamage := false
      firstStrikeAssignedThisCombat := #[]
      blockersQueue := #[] }
    for o in g.battlefield do
      if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked then
        g := g.setObject { o with
          status := { o.status with
            attacking := false
            attackingWhom := none
            blocking := #[]
            blocked := false } }
    return g

end Game
end Mtg.Engine
