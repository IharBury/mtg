import Mtg.Engine.Game.Core

/-!
# Player designations

Enduring story (HOB storied), The Ring and the Ring-bearer, the city's
blessing (ascend, CR 702.131), and shadow counters.
-/

namespace Mtg.Engine
namespace Game

/-- Grant a lasting player designation if `p` now qualifies. The designation
is never removed. Not a triggered ability. -/
def grantDesignationIfNeeded (g : Game) (p : PlayerId)
    (already : Player → Bool) (qualifies : Game → PlayerId → Bool)
    (designation : PlayerDesignation) (msg : String) : Game :=
  if already (g.player p) then g
  else if qualifies g p then
    g.record (GameEvent.gainedDesignation g.turnNumber p designation
      (cause := some (.gameRule .staticAbility))) |>.logMsg s!"{(g.player p).name} {msg}"
  else g

/-- Grant an enduring story if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantEnduringStoryIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.enduringStory)
    (fun g p => g.controlsStoried p && g.storiedPermanentCount p ≥ 3)
    .enduringStory
    "has an enduring story"

/-- Whether `p` has an emblem named The Ring. -/
def hasTheRing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).theRingAbilities > 0

/-- Number of The Ring abilities `p`'s emblem currently has. -/
def theRingAbilityCount (g : Game) (p : PlayerId) : Nat :=
  (g.player p).theRingAbilities

/-- Whether `o` is `p`'s Ring-bearer (CR 701.54a / 701.54e). -/
def isRingBearer (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  o.isOnBattlefield && (g.player p).ringBearerId == some o.id && g.controlledBy o p

/-- Whether `o` is any player's Ring-bearer (CR 701.54a). -/
def isAnyRingBearer (g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && g.players.any (fun pl => g.isRingBearer pl.id o)

/-- Creatures `p` controls that can be chosen as Ring-bearer. -/
def ringBearerChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o => g.isCreature o)

/-- Clear `p`'s previous Ring-bearer if different, then mark `chosen` if present (CR 701.54a). -/
def setRingBearer (g : Game) (p : PlayerId) (chosen : Option ObjectId)
    (cause : Option EventCause := none) : Game :=
  let effCause := g.resolveOptionalCause (cause.orElse (fun _ => g.resolvingOneShotCause p)) (fallbackCtrl := some p)
  g.withBatchCore (some effCause) fun g =>
    let effCause := g.resolveOptionalCause (cause.orElse (fun _ => g.resolvingOneShotCause p)) (fallbackCtrl := some p)
    let g :=
      match (g.player p).ringBearerId with
      | some oldId =>
        if some oldId == chosen then g
        else
          match g.findObject? oldId with
          | some oldObj =>
            g.record (GameEvent.designation g.turnNumber (g.snapshot oldObj) .ringBearer false (cause := effCause))
          | none =>
            let snap := (g.lastKnownBefore? oldId).getD { id := some oldId }
            g.record (GameEvent.designation g.turnNumber snap .ringBearer false (cause := effCause))
      | none => g
    match chosen with
    | none => g
    | some id =>
      match g.findObject? id with
      | none => g
      | some o =>
        g.record (GameEvent.designation g.turnNumber (g.snapshot o) .ringBearer true (cause := effCause))

/-- Grant the city's blessing if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantCitysBlessingIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.citysBlessing)
    (fun g p => g.controlsAscend p && g.permanentCount p ≥ 10)
    .citysBlessing
    "has the city's blessing"

/-- Finish placing a shadow counter on `targetId` once `recordPutCounters` completes. -/
def finishShadowCounter (g : Game) (targetId : ObjectId) (before : Nat) : Game :=
  match g.findObject? targetId with
  | none => g
  | some cur =>
    if !cur.isOnBattlefield || cur.status.counterCount .shadow <= before then g
    else
      let g := g.createEffect (.additionalSubtype cur.id .wraith true)
      g.logMsg s!"{g.name cur} gets a shadow counter"

/-- Put a shadow counter on `o`. It has shadow and is a Wraith. -/
def putShadowCounter (g : Game) (o : GameObject) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.putShadowCounter o.id)
  else
    let before := o.status.counterCount .shadow
    let g := g.recordPutCounters o.id .shadow 1 (byPlayer := g.controllerOf o)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishShadowCounter o.id before)
    else
      g.finishShadowCounter o.id before

end Game
end Mtg.Engine
