import Mtg.Engine.Game.SacrificeDiscard

/-!
# Damage, destruction, and life (CR 120 / 119)

Destroying permanents (CR 701.8), marking damage with replacement
effects (shield counters, prevention, multipliers), damage to players,
fights (CR 701.14), and life loss and gain (CR 119).
-/

namespace Mtg.Engine
namespace Game

/-- The resolving spell, or the source of the resolving ability, as the
default damage source when an effect deals damage without naming another
source (CR 609.7 / 113.7 / 120.2). -/
def resolvingDamageSource? (g : Game) : Option GameObject :=
  match g.resolvingSpell.bind g.findObject? with
  | some s => some s
  | none =>
  match (g.resolvingAbility.bind g.findObject?).bind (fun ab => ab.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.triggerSequenceRest.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.mayContext.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.triggerOr.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.chooseModesRest.bind (fun r => r.sourceId.bind g.findObject?) with
  | some s => some s
  | none =>
  match g.fraAfterLook.bind (fun (_, sid?, _) => sid?.bind g.findObject?) with
  | some s => some s
  | none => none

/-- The resolving damage source object, following a source that moved zones
before its ability resolved (CR 113.7a). -/
def resolvingMovedDamageSource? (g : Game) : Option GameObject :=
  match g.resolvingDamageSource? with
  | some s => some s
  | none =>
    let sid? :=
      (g.resolvingAbility.bind g.findObject?).bind (·.sourceId)
        |>.orElse (fun _ => g.triggerSequenceRest.bind (·.sourceId))
        |>.orElse (fun _ => g.mayContext.bind (·.sourceId))
        |>.orElse (fun _ => g.triggerOr.bind (·.sourceId))
        |>.orElse (fun _ => g.chooseModesRest.bind (·.sourceId))
        |>.orElse (fun _ => g.fraAfterLook.bind (fun (_, s, _) => s))
    sid?.bind (fun sid => g.findObject? (g.followMoved sid))

/-- Snapshot the resolving damage source as an `EventObject`, following a
source that moved zones before its ability resolved (CR 113.7a). -/
def resolvingDamageSourceEvent? (g : Game) : Option EventObject :=
  g.resolvingMovedDamageSource?.map g.snapshot

/-- Destroy a permanent (CR 701.8). Indestructible permanents aren't destroyed
(CR 701.8b / 702.12b). If it would die this turn under an exile replacement,
`move` sends it to exile instead of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Game :=
  if o.status.shield > 0 then
    let g := g.record (GameEvent.counters g.turnNumber o.controller o.asEvent .shield 1 true (cause := cause))
    g.logMsg s!"A shield counter is removed from {o.name} instead of destroying it"
  else if g.hasIndestructible o then
    g.logMsg s!"{o.name} is indestructible and isn't destroyed"
  else
    g.moveToOwnerGraveyard o s!"{o.name} is destroyed" (verb := some .destroy) (cause := cause)

/-- True when all damage that would be dealt to `o` is prevented. -/
def preventsAllDamageTo (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .preventAllDamageToThis => true
    | _ => false)

def markDamageOn (g : Game) (o : GameObject) (n : Int) (msg : String)
    (deathtouch := false) (combat := false) (unpreventable := false)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  if n > 0 && !unpreventable && g.preventsAllDamageTo o then
    g.logMsg s!"Damage that would be dealt to {o.name} is prevented"
  else
  let defaultCause :=
    cause.orElse (fun _ =>
      if n <= 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) => .oneShotEffect none src ctrl)
  g.withBatch defaultCause fun g =>
  let srcEvent : EventObject :=
    let base := (source.orElse (fun _ => g.resolvingDamageSourceEvent?)).getD default
    { base with keywords := { base.keywords with deathtouch := base.keywords.deathtouch || deathtouch } }
  let healsOther :=
    o.printed.staticAbilities.any (fun
      | .healOtherDamageWhenDealt => true
      | _ => false)
  let g :=
    if healsOther && n > 0 then
      g.record (GameEvent.damageMarkedCleared g.turnNumber #[o.id] (cause := cause))
    else g
  let o := g.findObject? o.id |>.getD o
  if n > 0 && o.status.shield > 0 && !unpreventable then
    let g := g.record (GameEvent.counters g.turnNumber o.controller o.asEvent .shield 1 true (cause := cause))
    g.logMsg s!"A shield counter is removed from {o.name} instead of damage"
  else if n > 0 && o.status.shield > 0 && unpreventable then
    let g := g.record (GameEvent.counters g.turnNumber o.controller o.asEvent .shield 1 true (cause := cause))
    let g := g.logMsg s!"A shield counter is removed from {o.name} (unpreventable damage)"
    let marked := g.object! o.id
    let happened := GameEvent.damaged g.turnNumber srcEvent marked.asEvent n.toNat combat (cause := cause)
    (g.record happened |>.record (GameEvent.damageMarked g.turnNumber marked.id n.toNat (cause := cause))).logMsg msg
  else
  -- CR 120.3c: damage dealt to a planeswalker removes that many loyalty counters.
  let happened := GameEvent.damaged g.turnNumber srcEvent o.asEvent n.toNat combat (cause := cause)
  let g := if n > 0 then g.record happened else g
  let g :=
    let g :=
      if n > 0 then
        g.record (GameEvent.damageMarked g.turnNumber o.id n.toNat (cause := cause))
      else g
    let g :=
      if o.printed.isPlaneswalker && n > 0 then
        g.record (GameEvent.counters g.turnNumber none o.asEvent .loyalty n.toNat true (cause := cause))
      else g
    g.logMsg msg
  g

/-- Extra noncombat damage from Hawkeye, Young Avenger. X is his power at
the time the damage would be dealt (MSH 305). -/
def hawkeyeNoncombatBonus (g : Game) (sourceController : PlayerId) : Int :=
  (g.permanentsOf sourceController).foldl (fun acc o =>
    if o.staticAbilities.any (fun
      | .noncombatDamagePlusSourcePower => true
      | _ => false) then
      acc + g.power o
    else acc) (0 : Int)

/-- Each attached Mjölnir doubles damage (two → ×4, three → ×8; MSH 237). -/
def mjolnirMultiplier (g : Game) (src : GameObject) : Nat :=
  let n :=
    (g.battlefield.filter (fun o =>
      o.attachedTo == some src.id &&
        o.staticAbilities.any (fun
          | .equippedDealsDoubleDamage => true
          | _ => false))).size
  if n == 0 then 1 else Nat.pow 2 n

/-- Apply Hawkeye then Mjölnir. Hawkeye adds only to noncombat damage dealt
to an opponent of the source's controller or a permanent an opponent
controls. If all damage is prevented, neither replacement applies
(MSH 177 / 178). Combat assignment happens first; this multiplies the
already-divided amounts (MSH 179). -/
def replacedDamageAmount (g : Game) (src : GameObject) (n : Int)
    (combat := false) (recipient : Option PlayerId := none) : Int :=
  let srcEvent := g.snapshot src
  let proposed :=
    match recipient with
    | some pid => GameEvent.damagedPlayer g.turnNumber srcEvent pid n.toNat combat
    | none => GameEvent.damaged g.turnNumber srcEvent src.asEvent n.toNat combat
  if !proposed.watches .wouldDealDamage || g.sourceDamagePrevented src then 0
  else
    let extra :=
      if combat || n ≤ 0 then (0 : Int)
      else
        match src.controller, recipient with
        | some p, some r => if r != p then g.hawkeyeNoncombatBonus p else 0
        | _, _ => (0 : Int)
    (n + extra) * Int.ofNat (g.mjolnirMultiplier src)

/-- Tomik, Izzet Sparkmage: noncombat damage a source deals to an opponent of
its controller, or a permanent one controls, is increased by 1 for each. -/
def tomikNoncombatBonus (g : Game) (src : GameObject) (recipient : PlayerId) : Int :=
  match src.controller with
  | some p =>
    if p == recipient then 0
    else Int.ofNat ((g.permanentsOf p).filter (·.staticAbilities.any
      (· == .fra .noncombatDamagePlusOne))).size
  | none => 0

/-- Increase `p`'s life total (CR 119.2). Gaining 0 life does nothing (CR 119.9). -/
def gainLife (g : Game) (p : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  let proposed := GameEvent.life g.turnNumber p n true (cause := cause)
  if n == 0 || !proposed.watches .wouldGainLife then g
  else if (g.livingOpponents p).any (fun opp =>
      (g.permanentsOf opp.id).any (·.printed.opponentsCantGainLife)) then
    g.logMsg s!"{(g.player p).name} can't gain life"
  else
    let pl := g.player p
    if pl.lifeLocked || pl.lifeCantChange then
      g.logMsg s!"{pl.name}'s life total can't change"
    else
      let before := pl.life
      let happened := GameEvent.life g.turnNumber p n true (cause := cause)
      (g.record happened).logMsg
        s!"{pl.name} gains {n} life ({before + (n : Int)} life)"

/-- Deal `n` damage to a creature and log the generic “is dealt” message. -/
def dealDamageToPermanent (g : Game) (o : GameObject) (n : Int)
    (source : Option EventObject := none)
    (cause : Option EventCause := none) : Game :=
  let srcEvent? := source.orElse (fun _ => g.resolvingDamageSourceEvent?)
  let prevented := g.preventsAllDamageTo o || o.status.shield > 0
  let defaultCause :=
    cause.orElse (fun _ =>
      if n <= 0 || g.preventsAllDamageTo o then none
      else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
        .oneShotEffect none
          (ctxSrc.orElse (fun _ => srcEvent?.bind (·.id)))
          (ctrl.orElse (fun _ => srcEvent?.bind (·.controller))))
  g.withBatch defaultCause fun g =>
  let g := g.markDamageOn o n s!"{o.name} is dealt {n} damage" (source := srcEvent?) (cause := cause)
  -- CR 702.15b: damage dealt by a source with lifelink.
  match srcEvent?.bind (fun src => if src.keywords.lifelink then src.controller else none) with
  | some c =>
    if n > 0 && !prevented then g.gainLife c n.toNat (cause := cause) else g
  | none => g

/-- Deal `n` damage from a named source (fight, dies trigger, blocked trigger). -/
def dealDamageFrom (g : Game) (sourceName : String) (o : GameObject) (n : Int)
    (deathtouch := false) (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  match source.orElse (fun _ => g.resolvingMovedDamageSource?) with
  | some src =>
    if g.frcProtectedFrom o src || g.sourceDamagePrevented src then
      g.logMsg s!"damage from {src.name} is prevented"
    else
      let n := g.replacedDamageAmount src n (recipient := o.controller)
      let n :=
        if n > 0 then
          match o.controller with
          | some c => n + g.tomikNoncombatBonus src c
          | none => n
        else n
      let prevented := g.preventsAllDamageTo o || o.status.shield > 0
      let defaultCause :=
        cause.orElse (fun _ =>
          if n <= 0 || g.preventsAllDamageTo o then none
          else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
            .oneShotEffect none
              (ctxSrc.orElse (fun _ => some src.id))
              (ctrl.orElse (fun _ => src.controller)))
      g.withBatch defaultCause fun g =>
      let g := g.changeStatus src.id (.dealtDamageThisTurn true)
      let g := g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}"
        (deathtouch || g.hasDeathtouch src) (source := some (g.snapshot src)) (cause := cause)
      -- CR 702.15b: damage dealt by a source with lifelink.
      match src.controller with
      | some c =>
        if n > 0 && !prevented && g.hasLifelink src then g.gainLife c n.toNat (cause := cause) else g
      | none => g
  | none =>
    g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}" deathtouch (cause := cause)

/-- Deal `n` damage to a player and log the resulting life total (CR 120). -/
def dealDamageToPlayer (g : Game) (pid : PlayerId) (n : Int)
    (preventable := true) (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  let source := source.orElse (fun _ => g.resolvingDamageSource?)
  let n : Int :=
    match source with
    | some src =>
      if g.sourceDamagePrevented src then (0 : Int)
      else
        let n := g.replacedDamageAmount src n (recipient := some pid)
        if n > 0 then n + g.tomikNoncombatBonus src pid else n
    | none => n
  let pl := g.player pid
  if n == 0 && source.isSome then
    g.logMsg s!"damage from the source is prevented"
  else if preventable && pl.protectionFromEverything then
    g.logMsg s!"damage to {pl.name} is prevented (protection from everything)"
  else
    let defaultCause :=
      cause.orElse (fun _ =>
        if n <= 0 then none
        else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
          .oneShotEffect none
            (ctxSrc.orElse (fun _ => source.map (·.id)))
            (ctrl.orElse (fun _ => source.bind (·.controller))))
    g.withBatch defaultCause fun g =>
    let srcEvent :=
      ((source.map g.snapshot).orElse (fun _ => g.resolvingDamageSourceEvent?)).getD default
    let happened := GameEvent.damagedPlayer g.turnNumber srcEvent pid n.toNat false (cause := cause)
    let g := if n > 0 then g.record happened else g
    let g :=
      if (pl.lifeLocked || pl.lifeCantChange) && n != 0 then
        g.logMsg s!"{pl.name}'s life total can't change"
      else if n > 0 then
        (g.record (GameEvent.life g.turnNumber pid n.toNat false true false (cause := cause))).logMsg
          s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"
      else
        g.logMsg s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"
    -- CR 702.15b: damage dealt by a source with lifelink.
    match source with
    | some src =>
      match src.controller with
      | some c => if n > 0 && g.hasLifelink src then g.gainLife c n.toNat (cause := cause) else g
      | none => g
    | none => g

/-- Deal `n` damage to each opponent of `controller` under a single shared
`.oneShotEffect` cause when resolving (CR 120 / 610.1). -/
def dealDamageToEachOpponent (g : Game) (controller : PlayerId) (n : Int)
    (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  let source := source.orElse (fun _ => g.resolvingDamageSource?)
  let defaultCause :=
    cause.orElse (fun _ =>
      if n <= 0 || (g.livingOpponents controller).isEmpty then none
      else g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
        .oneShotEffect none
          (ctxSrc.orElse (fun _ => source.map (·.id)))
          (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
  g.forEachOpponent controller (fun g pid =>
    g.dealDamageToPlayer pid n (source := source) (cause := cause))

/-- Deal this creature's power as damage to `dest` (one side of a fight). -/
def dealFightDamage (g : Game) (src dest : GameObject)
    (cause : Option EventCause := none) : Game :=
  g.dealDamageFrom src.name dest (g.power src).toNat (source := some src) (cause := cause)

/-- Both sides of a fight deal damage simultaneously-looking: `src` first,
then `dest` if both are still in play. -/
def fightCreatures (g : Game) (src dest : GameObject)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      g.currentResolvingContext?.map fun (ctxSrc, ctrl) =>
        .oneShotEffect none
          (ctxSrc.orElse (fun _ => some src.id))
          (ctrl.orElse (fun _ => src.controller)))
  g.withBatch defaultCause fun g =>
  let g := g.dealFightDamage src dest (cause := cause)
  match g.findObject? dest.id, g.findObject? src.id with
  | some dest, some src => g.dealFightDamage dest src (cause := cause)
  | _, _ => g

/-- Decrease `p`'s life total (CR 119.3). Losing 0 life does nothing
(CR 119.9). Loss of life is not damage (CR 119.3 / 120.3). -/
def loseLife (g : Game) (p : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    if pl.lifeLocked || pl.lifeCantChange then
      g.logMsg s!"{pl.name}'s life total can't change"
    else
      (g.record (GameEvent.life g.turnNumber p n false (cause := cause))).logMsg
        s!"{pl.name} loses {n} life ({pl.life - (n : Int)} life)"

/-- Each opponent of `controller` loses `n` life under one shared
`.oneShotEffect` cause when resolving (CR 119.3 / 610.1). -/
def loseLifeEachOpponent (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 || (g.livingOpponents controller).isEmpty then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
  g.forEachOpponent controller (fun g pid => g.loseLife pid n (cause := cause))

/-- Each opponent of `controller` loses `n` life and `controller` gains `n`
life under one shared `.oneShotEffect` cause when resolving (CR 119 / 610.1). -/
def eachOpponentLosesYouGain (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none src (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
  let g := g.forEachOpponent controller (fun g pid => g.loseLife pid n (cause := cause))
  g.gainLife controller n (cause := cause)

/-- Draw `cards`, then lose `life` (Night's Whisper, MSH draw-and-lose). -/
def drawThenLoseLife (g : Game) (p : PlayerId) (cards life : Nat) : Game :=
  let defaultCause :=
    g.currentResolvingContext?.map fun (src, ctrl) =>
      .oneShotEffect none src (ctrl.orElse (fun _ => some p))
  g.withBatch defaultCause fun g =>
  (g.draw p cards).loseLife p life

/-- If a shuffle is waiting for a `--norandom` result, leave it. Otherwise
run a stored draw or life-gain after-action. -/
def continueIfShuffled (g : Game) : Game :=
  match g.pendingRandom? with
  | some _ => g
  | none =>
    let after := g.afterRandom
    let g := g.change (.afterRandom .none)
    match after with
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | other => g.change (.afterRandom other)

/-- Deal `n` damage to an already-legal player or permanent target. -/
def dealDamageToTarget (g : Game) (t : Target) (n : Int)
    (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  -- The source is the resolving spell, or the source of the resolving
  -- ability (CR 609.7 / 113.7).
  let src := source.orElse (fun _ => g.resolvingDamageSource?)
  match t with
  | Target.player pid => g.dealDamageToPlayer pid n (source := src) (cause := cause)
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      match src with
      | some s => g.dealDamageFrom s.name o n (source := some s) (cause := cause)
      | none => g.dealDamageToPermanent o n (cause := cause)
    | none => g.logMsg "The target is no longer in play"
  | Target.card _ => g.logMsg "The target is no longer legal"

end Game
end Mtg.Engine
