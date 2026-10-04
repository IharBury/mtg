import Mtg.Engine.Game.LibrarySearch

/-!
# Resolution target helpers (CR 608.2b)

Re-checking target legality as an effect resolves, `applyPermanentAction`
for shared actions on permanents, beginning scry, mill (CR 701.13), and
damage to each matching creature.
-/

namespace Mtg.Engine
namespace Game

/-- Log why a targeted ability failed to affect its announced target (CR 608.2b). -/
def illegalAbilityTarget (g : Game) : Target → Game
  | Target.player _ => g.logMsg "The target is no longer legal"
  | Target.permanent oid =>
    match g.findObject? oid with
    | some o =>
      if o.isOnBattlefield then g.logMsg "The target is no longer legal"
      else g.logMsg "The target is no longer in play"
    | none => g.logMsg "The target is no longer in play"
  | Target.card oid =>
    match g.findObject? oid with
    | some o =>
      match o.zone with
      | .graveyard _ => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer in the graveyard"
    | none => g.logMsg "The target is no longer in the graveyard"

/-- Apply `f` when the announced target is still in `legal` (CR 608.2b).
`missing` is logged when no target was announced; `none` leaves the game unchanged. -/
def withLegalTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → Target → Game) (missing : Option String := none) : Game :=
  match targets[0]? with
  | none =>
    match missing with
    | some msg => g.logMsg msg
    | none => g
  | some t =>
    if legal.contains t then f g t else g.illegalAbilityTarget t

/-- Apply `f` to a still-legal permanent target. -/
def withLegalPermanentTarget (g : Game) (legal : Array Target) (targets : Array Target)
    (f : Game → GameObject → Game) (missing : Option String := none) : Game :=
  g.withLegalTarget legal targets (fun g t =>
    match t with
    | Target.permanent oid =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer in play"
      | some o => f g o
    | Target.player _ | Target.card _ => g.logMsg "The target is no longer legal")
    missing

/-- Apply `f` when the announced target is still legal for `kind` (CR 608.2b). -/
def withLegalKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → Target → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalTarget (g.legalTargetsForKind controller kind sourceId) targets f missing

/-- Apply `f` to a still-legal permanent target of `kind`. -/
def withLegalKindPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → GameObject → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalPermanentTarget (g.legalTargetsForKind controller kind sourceId) targets f
    missing

/-- Apply `f` to a still-legal player target of `kind`. -/
def withLegalKindPlayer (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (f : Game → PlayerId → Game)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  g.withLegalKindTarget controller kind targets (fun g tgt =>
    match tgt with
    | Target.player pid => f g pid
    | Target.permanent _ | Target.card _ => g.logMsg "The target is no longer legal")
    sourceId missing

/-- Apply `f` when the announced trigger target is still legal (CR 608.2b). -/
def withLegalTriggerTarget (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → Target → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindTarget controller ab.targetKind targets f sourceId (some noneMsg)

/-- Apply `f` to a still-legal permanent target of a triggered ability. -/
def withLegalTriggerPermanent (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → GameObject → Game) (noneMsg : String := "The target is no longer legal") : Game :=
  g.withLegalKindPermanent controller ab.targetKind targets f sourceId (some noneMsg)

/-- Apply `f` to a still-legal player target of a triggered ability. -/
def withLegalTriggerPlayer (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target)
    (f : Game → PlayerId → Game) : Game :=
  g.withLegalTriggerTarget controller ab sourceId targets (fun g t =>
    match t with
    | Target.player pid => f g pid
    | _ => g.logMsg "The target is no longer legal")

/-- Deal `n` damage to a still-legal target of `kind`. -/
def applyDamageToKindTarget (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (n : Nat) (sourceId : Option ObjectId := none)
    (missing : Option String := none) : Game :=
  g.withLegalKindTarget controller kind targets (fun g t => g.dealDamageToTarget t n)
    sourceId missing

/-- Exile creature cards from `fromPlayer`'s graveyard and grant `controller`
permission to cast them, spending mana as though it were any type. -/
def exileCreaturesFromGraveyard (g : Game) (controller fromPlayer : PlayerId) : Game :=
  let ids :=
    (g.player fromPlayer).graveyard.filter (fun id =>
      match g.findObject? id with
      | some o => o.printed.isCreature
      | none => false)
  Id.run do
    let mut g := g
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        let name := o.name
        let (g', newId) := g.move id .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some {
            player := controller
            turnEndsRemaining := 0
            whileExiled := true
            anyMana := true } }
        g := g.logMsg
          s!"{name} is exiled. {(g.player controller).name} may cast it for as long as it remains exiled"
    return g

/-- Apply a shared permanent action (spells, activated abilities, and triggers). -/
def applyPermanentAction (g : Game) (o : GameObject) : PermanentAction → Game
  | .pump pw tw => g.pumpPermanent o pw tw
  | .pumpAndTrample pw tw => g.pumpAndGrantTrample o pw tw
  | .destroy => g.destroyPermanent o
  | .plusOne n => g.addPlusOnePlusOneTo o n
  | .plusOnePlusOneTrampleHexproof => g.grantPlusOnePlusOneTrampleHexproof o
  | .dealDamage n => g.dealDamageToPermanent o n
  | .dealDamageLoseIndestructibleExile n =>
    g.dealDamageLoseIndestructibleExileTo o n
  | .destroyThenNonflyersCantBlock =>
    let g := g.destroyPermanent o
    let g := { g with creaturesWithoutFlyingCantBlock := true }
    g.logMsg "Creatures without flying can't block this turn"
  | .cantBeBlocked => g.grantCantBeBlockedThisTurn o
  | .pumpAndLifelink pw tw =>
    let g := g.pumpPermanent o pw tw
    g.grantUntilEotLogged (g.object! o.id) Keyword.lifelink
  | .pumpAndExileIfDies pw tw =>
    let g := g.pumpPermanent o pw tw
    let o := g.object! o.id
    let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
    g.logMsg s!"If {o.name} would die this turn, exile it instead"
  | .grantKeywords k =>
    g.grantUntilEotLogged o k
  | .tap => g.becomeTapped o
  | .untap =>
    if g.hostCantBecomeUntapped o then
      g.logMsg s!"{o.name} can't become untapped"
    else if !o.status.tapped then
      g.logMsg s!"{o.name} is already untapped"
    else
      let g := g.mapObjectStatus o (fun s => { s with tapped := false })
      g.logMsg s!"{o.name} untaps"
  | .becomeArtifactIndestructible =>
    let g := g.mapObjectStatus o (fun s =>
      { s with
        additionalArtifactUntilEot := true
        untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.indestructible })
    g.logMsg
      s!"{o.name} becomes an artifact and gains indestructible until end of turn"
  | .pumpAndGrant pw tw k =>
    let g := g.pumpPermanent o pw tw
    g.grantUntilEotLogged (g.object! o.id) k
def applyOnPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (action : PermanentAction)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  match action with
  | .dealDamage n =>
    g.applyDamageToKindTarget controller kind targets n sourceId missing
  | _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.applyPermanentAction o action) sourceId missing

/-- Queue “whenever you scry” triggers for permanents `p` controls (CR 701.20). -/
def queueScryTriggers (g : Game) (p : PlayerId) (lookedAt : Nat) : Game :=
  g.foldControlledPermanents p none fun g o =>
    g.enqueueWaitingTriggers
      (o.waitingTriggersFor p .youScry (some (Int.ofNat lookedAt)))

/-- Start scrying `n` as a keyword action during resolution (CR 701.20).
Scry 0 is skipped and does not trigger “whenever you scry” (CR 701.20c). -/
def beginScry (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  let count := min n pl.library.size
  let g := if n == 0 then g else g.queueScryTriggers p count
  if count == 0 then
    g.logMsg s!"{pl.name} scries {n} (no cards to look at)"
  else
    { g with pending := .scry p count }.logMsg s!"{pl.name} scries {n}"

/-- Put the top `n` cards of `p`'s library into their graveyard (CR 701.13). -/
def mill (g : Game) (p : PlayerId) (n : Nat) : Game :=
  Id.run do
    let mut g := g
    for _ in [0:n] do
      let pl := g.player p
      if pl.library.isEmpty then
        return g.logMsg s!"{pl.name} mills nothing (empty library)"
      else
        let top := pl.library.back!
        let name := (g.object! top).name
        let (g', _) := g.move top (.graveyard p) none
        g := g'.logMsg s!"{pl.name} mills {name}"
    return g

/-- Mill `n`, then put matching milled cards from the graveyard into hand.
`maxPut` limits how many are returned (`none` means all matches). -/
def millThenPutFromGy (g : Game) (p : PlayerId) (n : Nat)
    (pred : GameObject → Bool) (maxPut : Option Nat := none) : Game :=
  let g := g.mill p n
  let gy := (g.player p).graveyard
  let take := gy.size.min n
  let milled := gy.extract (gy.size - take) gy.size
  Id.run do
    let mut g := g
    let mut left := maxPut.getD milled.size
    for id in milled do
      if left > 0 && pred (g.object! id) then
        let name := (g.object! id).name
        let (g', _) := g.move id (.hand p) none
        g := g'.logMsg s!"{(g.player p).name} puts {name} into their hand"
        left := left - 1
    return g

/-- Deal `n` damage to each creature matching `pred`. -/
def dealDamageToEachCreatureMatching (g : Game) (n : Nat)
    (pred : GameObject → Bool := fun _ => true) : Game :=
  g.foldBattlefield (fun o => o.isCreature && pred o)
    (fun g o => g.dealDamageToPermanent o n)

/-- Deal `n` damage to each non-Dragon creature. -/
def dealDamageToEachNonDragon (g : Game) (n : Nat) : Game :=
  g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o "Dragon")

end Game
end Mtg.Engine
