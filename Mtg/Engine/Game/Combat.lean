import Mtg.Engine.Game.SpellResolution

/-!
# Combat (CR 506–510)

Declaring attackers and blockers, combat-damage assignment checks and
defaults, dealing assigned combat damage (deathtouch, trample, lifelink,
CR 510.1c–d / 702.19b), and clearing combat (CR 511.3).
-/

namespace Mtg.Engine
namespace Game

/-- Whether `pw` is limited to one attacker each combat (Tomik, Orzhov
Lawmage grants this to planeswalkers its controller controls). -/
def planeswalkerAttackedByOneAtMost (g : Game) (pw : GameObject) : Bool :=
  match g.controllerOf pw with
  | some q =>
    (g.permanentsOf q).any (fun o =>
      (g.staticAbilities o).any (· == .fra .planeswalkersAttackedByOneAtMost))
  | none => false

def declareAttackers (g : Game) (p : PlayerId) (ids : Array ObjectId)
    (defender : Option PlayerId := none) (each : Array (Option PlayerId) := #[])
    (planeswalkers : Array (Option ObjectId) := #[]) :
    Except String Game := do
  if g.pending != .declareAttackers || g.priorityInstead g.activePlayer != p then
    throw "Not time to declare attackers"
  let g ← g.withBatchM (some (.turnBased .declareAttackers)) fun g => do
    let mut g := g
    let mut decls : Array (EventObject × AttackTarget) := #[]
    let mut steps : Array (ObjectId × PlayerId × Option GameObject) := #[]
    for i in [0:ids.size] do
      let id := ids[i]!
      let o := g.object! id
      if !g.canAttack o then
        throw s!"{g.name o} cannot attack"
      let want :=
        match each[i]? with
        | some (some d) => some d
        | some none => defender
        | none => defender
      let pw? ←
        match planeswalkers[i]? with
        | some (some pwId) =>
          match g.findObject? pwId with
          | some pw =>
            if !pw.isOnBattlefield || !g.isPlaneswalker pw then
              throw s!"{g.name pw} is not a planeswalker on the battlefield"
            else if !(g.livingOpponents p).any (fun pl => g.controlledBy pw pl.id) then
              throw s!"{g.name pw} isn't controlled by an opponent (CR 508.1b)"
            else pure (some pw)
          | none => throw "no such planeswalker"
        | _ => pure none
      if g.cantAttackJaces p then
        match pw? with
        | some pw =>
          if (g.name pw).startsWith "Jace" || g.hasSubtype pw .jace then
            throw s!"{g.name o} can't attack {g.name pw} this turn"
        | none => pure ()
      let dest ←
        match pw? with
        | some pw => pure ((g.controllerOf pw).getD pw.owner)
        | none => g.resolveAttackDestination p want
      if g.hasFlying o && g.leftoverFlyingRestriction dest then
        throw s!"{g.name o} can't attack {(g.player dest).name}"
      let target : AttackTarget :=
        match pw? with
        | some pw => .planeswalker pw.id
        | none => .player dest
      decls := decls.push ({ (g.snapshot o) with attacking := true, attackingTarget := some target }, target)
      steps := steps.push (id, dest, pw?)
    if !decls.isEmpty then
      g := g.record (GameEvent.attackersDeclared g.turnNumber p decls
        (cause := some (.turnBased .declareAttackers)))
    for (id, dest, pw?) in steps do
      let o := g.object! id
      if !g.hasVigilance o then
        g := g.becomeTapped o (cause := some (.turnBased .declareAttackers))
      g := g.logMsg
        (match pw? with
         | some pw => s!"{g.player p |>.name} attacks {g.name pw} with {g.name o}"
         | none => s!"{g.player p |>.name} attacks {(g.player dest).name} with {g.name o}")
    return g
  let mut g := g
  -- Tomik, Orzhov Lawmage (ruling 834): checked on the whole declaration.
  for pw in g.battlefield do
    if g.isPlaneswalker pw && g.planeswalkerAttackedByOneAtMost pw then
      let n := (g.battlefield.filter (fun a =>
        a.status.attacking && a.status.attackingPlaneswalker? == some pw.id)).size
      if n > 1 then
        throw s!"No more than one creature can attack {g.name pw} each combat"
  for o in g.permanentsOf p do
    if g.mustAttackIfAble o && !ids.contains o.id then
      throw s!"{g.name o} must attack if able"
  let tax := ids.foldl (fun acc id =>
    let o := g.object! id
    if o.status.attackingTarget.isSome then
      acc + g.attackTaxPerCreature (g.defendingPlayerOf o)
    else acc) 0
  if tax > 0 then
    if !(g.player p).manaPool.canPay (ManaCost.ofGeneric tax) then
      throw s!"{(g.player p).name} must pay {tax} to attack"
    g ← g.payCost p (ManaCost.ofGeneric tax)
    g := g.logMsg s!"{(g.player p).name} pays {tax} to attack"
  if ids.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not attack"
  g := g.change (.pending .none)
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
  let (g, rest) ← g.withBatchExcept (some (.turnBased .declareBlockers)) fun g => do
    let mut g := g
    let mut decls : Array (EventObject × ObjectId) := #[]
    for (blockerId, attackerId) in assignments do
      let b := g.object! blockerId
      let a := g.object! attackerId
      if !g.canBlock b a then
        throw s!"{b.name} cannot block {a.name}"
      decls := decls.push (g.snapshot b, attackerId)
    if !decls.isEmpty then
      g := g.record (GameEvent.blockersDeclared g.turnNumber p decls
        (cause := some (.turnBased .declareBlockers)))
    let mut blockedAttackers : Array ObjectId := #[]
    for (blockerId, attackerId) in assignments do
      let b := g.object! blockerId
      let a := g.object! attackerId
      if !blockedAttackers.contains attackerId then
        blockedAttackers := blockedAttackers.push attackerId
      g := g.logMsg s!"{b.name} blocks {a.name}"
    for attackerId in blockedAttackers do
      let a := g.object! attackerId
      let bs := (assignments.filter (·.2 == attackerId)).map (·.1)
      g := g.record (GameEvent.becameBlocked g.turnNumber (g.snapshot a) bs
        (cause := some (.turnBased .declareBlockers)))
    -- CR 509.1b / 702.111: a menace (or “except by N or more”) creature that is
    -- blocked must be blocked by at least that many creatures.
    for o in g.battlefield do
      if o.status.attacking then
        let need := g.minBlockersRequired o
        if need > 1 then
          let n := (g.blockersOf o.id).size
          if n > 0 && n < need then
            let word := if need == 2 then "two" else toString need
            throw s!"{o.name} can't be blocked except by {word} or more creatures"
    let rest := g.blockersQueue.extract 1 g.blockersQueue.size
    if rest.isEmpty then
      for o in g.battlefield do
        if o.status.attacking && !o.status.blocked then
          g := g.record (GameEvent.remainedUnblocked g.turnNumber (g.snapshot o)
            (cause := some (.turnBased .declareBlockers)))
    return (g, rest)
  let mut g := g
  if assignments.isEmpty then
    g := g.logMsg s!"{g.player p |>.name} does not block"
  if rest.isEmpty then
    return g.changes #[.pending .none, .blockersQueue #[]] |>.receivePriority g.activePlayer
  else
    return g.changes #[.pending .declareBlockers, .blockersQueue rest]

/-- Sum of combat damage this assignment sends to creatures. -/
def creatureDamageTotal (asgn : CreatureCombatAssignment) : Int :=
  asgn.toCreatures.foldl (fun acc (_, n) => acc + n) 0

/-- A legal default assignment for `source` (CR 510.1c–d, 702.19).
Without trample, all damage goes to the first remaining recipient — one
legal division under 510.1c/d. With trample, lethal is assigned to each
blocker before leftover goes to the defending player. -/
def defaultCombatAssignment (g : Game) (source : GameObject) (forAttackers : Bool)
    (already : Array CreatureCombatAssignment) : CreatureCombatAssignment :=
  let dmg := g.combatDamageAmount source
  let liveDest := g.hasLiveAttackDestination source
  let playerDmg := if !liveDest then 0 else dmg
  if forAttackers then
    let blockers := g.blockersOf source.id
    if blockers.isEmpty then
      if (source.status.blocked && !g.hasTrample source) || !liveDest then
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
        if liveDest then
          return { source := source.id, toCreatures := toCreatures, toPlayer := remaining }
        else
          let (b0, amt0) := toCreatures[0]!
          return {
            source := source.id
            toCreatures := toCreatures.set! 0 (b0, amt0 + remaining)
            toPlayer := 0
          }
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
  let defender := g.defendingPlayerOf src
  let dmg := g.combatDamageAmount src
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
  let liveDest := g.hasLiveAttackDestination src
  if forAttackers then
    if !src.status.attacking then
      throw s!"{src.name} is not attacking"
    if recipients.isEmpty then
      if asgn.toCreatures.size != 0 then
        throw s!"{src.name} has no blocking creatures to assign combat damage to"
      if src.status.blocked && !g.hasTrample src then
        if asgn.toPlayer != 0 then
          throw s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
      else if !liveDest then
        if asgn.toPlayer != 0 then
          if (g.player defender).lost then
            throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
          else
            throw s!"{src.name} has no remaining player, planeswalker, or battle in combat to assign damage to (CR 506.4c / 702.19f)"
      else if asgn.toPlayer != dmg then
        throw s!"{src.name} must assign combat damage equal to its power (CR 510.1a)"
    else
      if !liveDest then
        if asgn.toPlayer != 0 then
          if (g.player defender).lost then
            throw s!"combat damage isn't assigned to a player who has left the game (CR 800.4e)"
          else
            throw s!"{src.name} cannot assign combat damage to the defending player when the planeswalker it was attacking left combat (CR 702.19b / 702.19f)"
        if toCreatures != dmg then
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

private inductive CombatDamageStep where
  | checkEmpty (src : ObjectId) (toPlayer : Int)
  | toCreature (src : ObjectId) (target : ObjectId) (amount : Int)
  | toPlayerOrPw (src : ObjectId) (amount : Int)
  | lifelink (src : ObjectId)
deriving Inhabited

private def buildCombatDamageSteps (asgns : Array CreatureCombatAssignment) : Array CombatDamageStep :=
  Id.run do
    let mut steps : Array CombatDamageStep := #[]
    for asgn in asgns do
      steps := steps.push (.checkEmpty asgn.source asgn.toPlayer)
      for (tid, amt) in asgn.toCreatures do
        if amt > 0 then
          steps := steps.push (.toCreature asgn.source tid amt)
      if asgn.toPlayer > 0 then
        steps := steps.push (.toPlayerOrPw asgn.source asgn.toPlayer)
      steps := steps.push (.lifelink asgn.source)
    return steps

/-- Apply assigned combat damage simultaneously (CR 510.2). -/
def dealAssignedCombatDamage (g : Game) (_appliedSoFar : Array ReplacementId := #[])
    (startIdx : Nat := 0) : Game :=
  let fs := (g.combatHasFirstStrike || g.hasFirstStrikeAssignmentInCurrentStep) && !g.firstStrikeDamageDone
  let combatCause := some (EventCause.turnBased (.dealCombatDamage fs))
  let isOuterCall := g.currentBatch.isNone
  let steps := buildCombatDamageSteps g.assignedCombatDamage
  let g := g.withBatch combatCause fun g => Id.run do
    let mut g := g
    for k in [startIdx:steps.size] do
      match steps[k]! with
      | .checkEmpty srcId toPlayer =>
        let src := g.object! srcId
        let recipients :=
          if src.status.attacking then g.blockersOf src.id else g.creaturesBlockedBy src
        if src.status.attacking && src.status.blocked && recipients.isEmpty &&
            toPlayer == 0 then
          g := g.logMsg
            s!"{src.name} is blocked with no remaining blockers and assigns no combat damage (CR 510.1c)"
        else if !src.status.blocking.isEmpty && recipients.isEmpty then
          g := g.logMsg
            s!"{src.name} is not blocking any creatures and assigns no combat damage (CR 510.1d)"
      | .toCreature srcId tid amt =>
        let src := g.object! srcId
        let srcEvent := g.snapshot src
        let t := g.object! tid
        let rep := g.replaceDamage amt (src? := some src) (srcEvent? := some srcEvent)
          (recipientPerm? := some t) (combat := true) (cause := combatCause)
        if let some (chooser, choices) := rep.choice? then
          return g.promptChooseReplacement chooser choices (.dealAssignedCombatDamage #[] k)
        let dealtAmt := rep.amount
        g := g.markDamageOn t amt
          s!"{src.name} deals {dealtAmt} combat damage to {t.name}"
          (deathtouch := g.hasDeathtouch src) (combat := true)
          (source := some srcEvent) (sourceObj := some src)
          (replaced := some rep) (consumeOrder := true) (cause := rep.cause)
        if let .chooseReplacement .. := g.pending then
          return g.chainPendingReplacement (.dealAssignedCombatDamage #[] (k + 1))
      | .toPlayerOrPw srcId amt =>
        let src := g.object! srcId
        let srcEvent := g.snapshot src
        let defn := g.defendingPlayerOf src
        let pwTarget? := src.status.attackingPlaneswalker?
        if pwTarget?.isSome then
          -- CR 510.1c / 120.3c: damage to the attacked planeswalker removes loyalty.
          match pwTarget?.bind g.findObject? with
          | some pw =>
            if pw.isOnBattlefield then
              let rep := g.replaceDamage amt (src? := some src) (srcEvent? := some srcEvent)
                (recipientPerm? := some pw) (combat := true) (cause := combatCause)
              if let some (chooser, choices) := rep.choice? then
                return g.promptChooseReplacement chooser choices (.dealAssignedCombatDamage #[] k)
              let dealtAmt := rep.amount
              g := g.markDamageOn pw amt s!"{src.name} deals {dealtAmt} combat damage to {pw.name}"
                (deathtouch := g.hasDeathtouch src) (combat := true)
                (source := some srcEvent) (sourceObj := some src)
                (replaced := some rep) (consumeOrder := true) (cause := rep.cause)
              if let .chooseReplacement .. := g.pending then
                return g.chainPendingReplacement (.dealAssignedCombatDamage #[] (k + 1))
          | none => pure ()
        else if !(g.player defn).lost then
          let rep := g.replaceDamage amt (src? := some src) (srcEvent? := some srcEvent)
            (recipientPlayer? := some defn) (combat := true) (cause := combatCause)
          if let some (chooser, choices) := rep.choice? then
            return g.promptChooseReplacement chooser choices (.dealAssignedCombatDamage #[] k)
          g := g.consumeReplacementOrder rep.applied
          let pl := g.player defn
          if rep.prevented then
            if rep.preventedAmount > 0 then
              let prevCause :=
                g.resolveOptionalCause rep.cause (fallbackSrc := srcEvent.id)
                  (fallbackCtrl := (g.controllerOf src).orElse (fun _ => some defn))
              g := g.record (GameEvent.damagePrevented g.turnNumber srcEvent (.player defn)
                rep.preventedAmount prevCause)
            if g.protectionFromEverything defn then
              g := g.logMsg s!"combat damage to {pl.name} is prevented"
            else
              g := g.logMsg s!"combat damage from {src.name} is prevented"
          else
            let toPlayer := rep.amount
            let dealtCause := rep.cause.getD (.turnBased (.dealCombatDamage fs))
            if toPlayer > 0 then
              g := g.record (GameEvent.damagedPlayer g.turnNumber srcEvent defn toPlayer.toNat true
                (cause := dealtCause))
            if g.lifeLocked defn || g.lifeCantChange defn then
              g := g.logMsg s!"{pl.name}'s life total can't change"
            else
              if toPlayer > 0 then
                g := g.record (GameEvent.life g.turnNumber defn toPlayer.toNat false true true
                  (cause := dealtCause))
            if toPlayer > 0 && srcEvent.toxic > 0 then
              g := g.record (GameEvent.poisoned g.turnNumber defn srcEvent.toxic
                (cause := .turnBased (.dealCombatDamage fs)))
              g := g.logMsg s!"{pl.name} gets {srcEvent.toxic} poison counter(s) (toxic)"
            if !(g.lifeLocked defn || g.lifeCantChange defn) then
              if src.status.blocked then
                g := g.logMsg
                  s!"{g.name src} tramples for {toPlayer} to {pl.name} ({(g.player defn).life} life)"
              else
                g := g.logMsg
                  s!"{g.name src} deals {toPlayer} combat damage to {pl.name} ({(g.player defn).life} life)"
      | .lifelink srcId =>
        let src := g.object! srcId
        if g.hasLifelink src then
          let totalDealt : Nat :=
            match g.currentBatch with
            | none => 0
            | some (bid, _) =>
              g.events.foldl (fun acc e =>
                if e.batch != some bid then acc
                else
                  match e.change with
                  | .rules (.damage (.dealt pkts)) =>
                    pkts.foldl (fun s p =>
                      if p.combat && p.source.id == some srcId then s + p.amount else s) acc
                  | _ => acc) 0
          if totalDealt > 0 then
            match g.controllerOf src with
            | some pid =>
              g := g.gainLife pid totalDealt (cause := combatCause)
              if let .chooseReplacement .. := g.pending then
                return g.chainPendingReplacement (.dealAssignedCombatDamage #[] (k + 1))
            | none => pure ()
    g.change (.pending .none)
  if let .chooseReplacement .. := g.pending then
    if isOuterCall then
      let g := if fs then g.chainPendingReplacement .addExtraCombatDamageStep else g
      g.chainPendingReplacement (.receivePriority g.activePlayer)
    else g
  else if isOuterCall then
    let g :=
      if fs then
        g.record (GameEvent.extraStepAdded g.turnNumber .combatDamage .afterCurrent
          (cause := .gameRule .stepAdvance))
      else g
    g.receivePriority g.activePlayer
  else g

/-- Record a legal assignment batch and append it for later dealing. -/
def storeCombatAssignments (g : Game) (forAttackers : Bool)
    (listed : Array CreatureCombatAssignment) : Except String Game := do
  let batch ← g.completeCombatAssignments forAttackers listed
  let _ ← checkCombatAssignmentBatch g forAttackers batch
  let fs := g.combatHasFirstStrike && !g.firstStrikeDamageDone
  return g.record (GameEvent.combatDamageAssigned g.turnNumber forAttackers batch (firstStrike := fs))

/-- Prompt the next defending player in APNAP order who controls a multi-attacker
blocking creature, or finalize blocker assignments and deal combat damage once
all defending players have chosen (CR 510.1d / 802.5). -/
def continueBlockerCombatAssignment (g : Game) : Game :=
  let already := g.pendingBlockerAssignments.map (·.source)
  let assigning := g.creaturesAssigningCombatDamage false
  let nextP? := g.apnapOrder.find? (fun p =>
    p != g.activePlayer && g.stillInGame p &&
      assigning.any (fun o =>
        g.controlledBy o p && !already.contains o.id &&
          (g.legalCombatDamageRecipients o false).size ≥ 2 && g.combatDamageAmount o > 0))
  match nextP? with
  | some nextP =>
    g.change (.pending (.assignCombatDamage nextP false))
      |>.logMsg s!"{(g.player nextP).name} assigns combat damage (CR 510.1d)"
  | none =>
    let accum := g.pendingBlockerAssignments.filter (fun a =>
      assigning.any (·.id == a.source))
    let g := g.change (.pendingBlockerAssignments #[])
    match g.storeCombatAssignments false accum with
    | .ok g' => g'.dealAssignedCombatDamage
    | .error e => g.logMsg s!"Combat damage assignment failed: {e}"

/-- After attackers have assigned, each defending player in APNAP order assigns
blocking creatures (CR 510.1d / 802.5) or damage is dealt if none have a
division to announce. -/
def finishAttackerCombatAssignment (g : Game) : Game :=
  (g.change (.pendingBlockerAssignments #[])).continueBlockerCombatAssignment

/-- Start CR 510.1: the active player assigns attacking creatures first. -/
def beginCombatDamageAssignment (g : Game) : Game :=
  let g := g.changes #[.pending .none, .pendingBlockerAssignments #[]]
  if g.needsCombatDamageChoice true then
    g.change (.pending (.assignCombatDamage g.activePlayer true))
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
    if forAttackers then
      let g ← g.storeCombatAssignments true listed
      return g.finishAttackerCombatAssignment
    else
      let assigning := g.creaturesAssigningCombatDamage false
      let mine := assigning.filter (g.controlledBy · p)
      let mut seen : Array ObjectId := #[]
      let mut acc := g.pendingBlockerAssignments.filter (fun a =>
        !mine.any (·.id == a.source))
      for a in listed do
        if seen.contains a.source then
          throw "Duplicate combat damage source"
        if !mine.any (·.id == a.source) then
          if assigning.any (·.id == a.source) then
            throw "You do not control that blocking creature"
          else
            throw "That creature does not assign combat damage now"
        seen := seen.push a.source
        acc := acc.push a
      for o in mine do
        if !seen.contains o.id then
          let asgn := g.defaultCombatAssignment o false acc
          acc := acc.push asgn
          seen := seen.push o.id
      for a in acc do
        if mine.any (·.id == a.source) then
          let _ ← checkCombatAssignment g a false acc
      let g := g.change (.pendingBlockerAssignments acc)
      return g.continueBlockerCombatAssignment
  | _ => throw "Not time to assign combat damage (CR 510.1)"

def clearCombat (g : Game) : Game :=
  Id.run do
    let mut g := g.change (.blockersQueue #[])
    let cause := EventCause.turnBased .removeFromCombatAtEndOfCombat
    for o in g.battlefield do
      if o.status.attacking || !o.status.blocking.isEmpty || o.status.blocked then
        g := g.record (GameEvent.removedFromCombat g.turnNumber (g.snapshot o) (cause := cause))
    return g

end Game
end Mtg.Engine
