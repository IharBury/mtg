import Mtg.Engine.Game.SacrificeDiscard

/-!
# Damage, destruction, and life (CR 120 / 119)

Destroying permanents (CR 701.7), marking damage with replacement
effects (shield counters, prevention, multipliers), damage to players,
fights (CR 701.12), and life loss and gain (CR 118).
-/

namespace Mtg.Engine
namespace Game

/-- Destroy a permanent (CR 701.7). Indestructible permanents aren't destroyed
(CR 702.12b / 701.7b). If it would die this turn under an exile replacement,
`move` sends it to exile instead of the graveyard (CR 614.1). -/
def destroyPermanent (g : Game) (o : GameObject) : Game :=
  if o.status.shield > 0 then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    g.logMsg s!"A shield counter is removed from {o.name} instead of destroying it"
  else if g.hasIndestructible o then
    g.logMsg s!"{o.name} is indestructible and isn't destroyed"
  else
    g.moveToOwnerGraveyard o s!"{o.name} is destroyed"

/-- Update `o`'s status in place. -/
def mapObjectStatus (g : Game) (o : GameObject) (f : Status → Status) : Game :=
  g.setObject { o with status := f o.status }

/-- Queue “a creature you control is dealt damage” triggers (She-Hulk). -/
def queueCreatureYouControlDealtDamage (g : Game) (o : GameObject) (n : Int) : Game :=
  if n <= 0 || !o.isCreature then g
  else
    match o.controller with
    | none => g
    | some p =>
      g.foldControlledPermanents p (excludeId := none) (fun g src =>
        g.putMatchingSourceTriggers p src .creatureYouControlDealtDamage (some n))

/-- True when all damage that would be dealt to `o` is prevented. -/
def preventsAllDamageTo (_g : Game) (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .preventAllDamageToThis => true
    | _ => false)

def markDamageOn (g : Game) (o : GameObject) (n : Int) (msg : String)
    (deathtouch := false) (combat := false) (unpreventable := false) : Game :=
  if n > 0 && !unpreventable && g.preventsAllDamageTo o then
    g.logMsg s!"Damage that would be dealt to {o.name} is prevented"
  else
  let healsOther :=
    o.printed.staticAbilities.any (fun
      | .healOtherDamageWhenDealt => true
      | _ => false)
  let o :=
    if healsOther && n > 0 then
      { o with status := { o.status with damage := 0 } }
    else o
  let g := if healsOther && n > 0 then g.setObject o else g
  if n > 0 && o.status.shield > 0 && !unpreventable then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    g.logMsg s!"A shield counter is removed from {o.name} instead of damage"
  else if n > 0 && o.status.shield > 0 && unpreventable then
    let g := g.setObject { o with status := { o.status with shield := o.status.shield - 1 } }
    let g := g.logMsg s!"A shield counter is removed from {o.name} (unpreventable damage)"
    let g := (g.mapObjectStatus (g.object! o.id) (fun s => s.addDamage n deathtouch)).logMsg msg
    g.queueCreatureYouControlDealtDamage (g.object! o.id) n
  else
  -- CR 120.3c: damage dealt to a planeswalker removes that many loyalty counters.
  let g := (g.mapObjectStatus o (fun s =>
    let s := s.addDamage n deathtouch
    if o.printed.isPlaneswalker && n > 0 then
      { s with loyaltyCounters := s.loyaltyCounters - n.toNat }
    else s)).logMsg msg
  let g :=
    if n > 0 then
      match o.controller with
      | some p =>
        let already := g.waitingTriggers.any (fun t =>
          t.source.id == o.id && t.event == .sourceDealtDamage)
        -- The amount dealt rides on last-known power (Hexhaven Invigorator);
        -- simultaneous damage adds up.
        let g :=
          if already then
            { g with waitingTriggers := g.waitingTriggers.map (fun t =>
                if t.source.id == o.id && t.event == .sourceDealtDamage then
                  { t with lastKnownPower := some ((t.lastKnownPower.getD 0) + n) }
                else t) }
          else g.putMatchingSourceTriggers p (g.object! o.id) .sourceDealtDamage (some n)
        let hasEnrage :=
          o.printed.triggeredAbilities.any (fun ab =>
            match ab.shared with
            | .watch .hulk => true
            | _ => false)
        if !already && hasEnrage && o.status.attacking then
          { g with enrageGrantsAdditionalCombat := g.enrageGrantsAdditionalCombat + 1 }
        else g
      | none => g
    else g
  let g := g.queueCreatureYouControlDealtDamage o n
  if n > 0 && !combat then
    match o.controller with
    | none => { g with lastNoncombatDamage := some (o.id, n.toNat) }
    | some p =>
      let g := { g with lastNoncombatDamage := some (o.id, n.toNat) }
      g.putMatchingSourceTriggers p o .sourceDealtNoncombatDamage
        (some n)
  else g

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
  if g.sourceDamagePrevented src then 0
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

/-- Deal `n` damage to a creature and log the generic “is dealt” message. -/
def dealDamageToPermanent (g : Game) (o : GameObject) (n : Int) : Game :=
  g.markDamageOn o n s!"{o.name} is dealt {n} damage"

/-- Increase `p`'s life total (CR 118.2). Gaining 0 life does nothing (CR 118.9). -/
def gainLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    let g := g.setLife p (pl.life + (n : Int))
      s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
    let g := g.modifyPlayer p (fun pl =>
      { pl with lifeGainedThisTurn := pl.lifeGainedThisTurn + n })
    g.putControlledTriggers p .youGainLife

/-- Deal `n` damage from a named source (fight, dies trigger, blocked trigger). -/
def dealDamageFrom (g : Game) (sourceName : String) (o : GameObject) (n : Int)
    (deathtouch := false) (source : Option GameObject := none) : Game :=
  match source with
  | some src =>
    if g.sourceDamagePrevented src then
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
      let g :=
        g.mapObjectStatus src (fun s => { s with dealtDamageThisTurn := true })
      let g := g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}"
        (deathtouch || g.hasDeathtouch src)
      -- CR 702.15b: damage dealt by a source with lifelink.
      match src.controller with
      | some c =>
        if n > 0 && !prevented && g.hasLifelink src then g.gainLife c n.toNat else g
      | none => g
  | none =>
    g.markDamageOn o n s!"{sourceName} deals {n} damage to {o.name}" deathtouch

/-- Deal `n` damage to a player and log the resulting life total (CR 120). -/
def dealDamageToPlayer (g : Game) (pid : PlayerId) (n : Int)
    (preventable := true) (source : Option GameObject := none) : Game :=
  let n :=
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
    let g := if n > 0 then g.modifyPlayer pid (fun pl => { pl with dealtNoncombatDamageThisTurn := true }) else g
    let g := g.setLife pid (pl.life - n) s!"{pl.name} is dealt {n} damage ({pl.life - n} life)"
    let g := g.afterLifeLost pid (pl.life - (g.player pid).life).toNat
    -- CR 702.15b: damage dealt by a source with lifelink.
    let g :=
      match source with
      | some src =>
        match src.controller with
        | some c => if n > 0 && g.hasLifelink src then g.gainLife c n.toNat else g
        | none => g
      | none => g
    let g :=
      match source with
      | some src =>
        match src.controller with
        | some c =>
          if n > 0 && g.hasSubtype src "Hero" then g.putControlledTriggersOncePerBatch c .heroesDealDamageToPlayer
          else g
        | none => g
      | none => g
    if n > 0 then
      -- Each other player sees an opponent dealt noncombat damage. “One or
      -- more opponents” triggers once per batch.
      g.livingPlayers.foldl (fun g q =>
        if q.id == pid then g
        else
          let g := g.putFraEventTriggers q.id .opponentDealtNoncombatDamage
          g.foldControlledPermanents q.id none fun g o =>
            if g.waitingTriggers.any (fun w =>
                w.source.id == o.id && w.event == .fra .opponentsDealtNoncombatDamage) then g
            else g.putMatchingSourceTriggers q.id o (.fra .opponentsDealtNoncombatDamage)) g
    else g

/-- Deal this creature's power as damage to `dest` (one side of a fight). -/
def dealFightDamage (g : Game) (src dest : GameObject) : Game :=
  g.dealDamageFrom src.name dest (g.power src).toNat (source := some src)

/-- Both sides of a fight deal damage simultaneously-looking: `src` first,
then `dest` if both are still in play. -/
def fightCreatures (g : Game) (src dest : GameObject) : Game :=
  let g := g.dealFightDamage src dest
  match g.findObject? dest.id, g.findObject? src.id with
  | some dest, some src => g.dealFightDamage dest src
  | _, _ => g

/-- Decrease `p`'s life total (CR 118.3a). Losing 0 life does nothing
(CR 118.9). Loss of life is not damage (CR 120.3). -/
def loseLife (g : Game) (p : PlayerId) (n : Nat) : Game :=
  if n == 0 then g
  else
    let pl := g.player p
    let g := g.setLife p (pl.life - (n : Int)) s!"{pl.name} loses {n} life ({pl.life - (n : Int)} life)"
    let lost := (pl.life - (g.player p).life).toNat
    g.afterLifeLost p lost

/-- Draw `cards`, then lose `life` (Night's Whisper, MSH draw-and-lose). -/
def drawThenLoseLife (g : Game) (p : PlayerId) (cards life : Nat) : Game :=
  (g.draw p cards).loseLife p life

/-- If a shuffle is waiting for a `--norandom` result, leave it. Otherwise
run a stored draw or life-gain after-action. -/
def continueIfShuffled (g : Game) : Game :=
  match g.pendingRandom? with
  | some _ => g
  | none =>
    let after := g.afterRandom
    let g := { g with afterRandom := .none }
    match after with
    | .draw p n => g.draw p n
    | .gainLife p n => g.gainLife p n
    | other => { g with afterRandom := other }

/-- Deal `n` damage to an already-legal player or permanent target. -/
def dealDamageToTarget (g : Game) (t : Target) (n : Int) : Game :=
  -- The source is the resolving spell, or the source of the resolving
  -- ability (CR 609.7 / 113.7).
  let src :=
    match g.resolvingSpell.bind g.findObject? with
    | some s => some s
    | none => (g.resolvingAbility.bind g.findObject?).bind (fun ab => ab.sourceId.bind g.findObject?)
  match t with
  | Target.player pid => g.dealDamageToPlayer pid n (source := src)
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      match src with
      | some s => g.dealDamageFrom s.name o n (source := some s)
      | none => g.dealDamageToPermanent o n
    | none => g.logMsg "The target is no longer in play"
  | Target.card _ => g.logMsg "The target is no longer legal"

end Game
end Mtg.Engine
