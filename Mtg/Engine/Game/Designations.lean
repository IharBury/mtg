import Mtg.Engine.Game.Core

/-!
# Player designations

Enduring story (HOB storied), The Ring and the Ring-bearer, the city's
blessing (ascend, CR 702.131), and shadow counters.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `p` currently has an enduring story. -/
def hasEnduringStory (g : Game) (p : PlayerId) : Bool :=
  (g.player p).enduringStory

/-- A permanent counts once toward Storied even if it is legendary, an
artifact, and a Saga. -/
def countsTowardStoried (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield &&
    (o.isLegendary || o.printed.isArtifact || o.printed.hasSubtype "Saga")

/-- Number of legendary, Saga, and/or artifact permanents `p` controls. -/
def storiedPermanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).filter (g.countsTowardStoried) |>.size

/-- Whether `p` controls a permanent with storied. -/
def controlsStoried (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.storied)

/-- Grant a lasting player designation if `p` now qualifies. The designation
is never removed. Not a triggered ability. -/
def grantDesignationIfNeeded (g : Game) (p : PlayerId)
    (already : Player → Bool) (qualifies : Game → PlayerId → Bool)
    (set : Player → Player) (msg : String) : Game :=
  if already (g.player p) then g
  else if qualifies g p then
    g.modifyPlayer p set |>.logMsg s!"{(g.player p).name} {msg}"
  else g

/-- Grant an enduring story if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantEnduringStoryIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.enduringStory)
    (fun g p => g.controlsStoried p && g.storiedPermanentCount p ≥ 3)
    (fun pl => { pl with enduringStory := true })
    "has an enduring story"

/-- Grant an enduring story to every player who now qualifies. -/
def refreshEnduringStory (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantEnduringStoryIfNeeded pl.id) g

/-- Whether `p` has an emblem named The Ring. -/
def hasTheRing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).theRingAbilities > 0

/-- Number of The Ring abilities `p`'s emblem currently has. -/
def theRingAbilityCount (g : Game) (p : PlayerId) : Nat :=
  (g.player p).theRingAbilities

/-- Whether `o` is `p`'s Ring-bearer. -/
def isRingBearer (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  (g.player p).ringBearerId == some o.id && o.status.ringBearer

/-- Creatures `p` controls that can be chosen as Ring-bearer. -/
def ringBearerChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o => o.isCreature)

/-- Clear Ring-bearer marks, then mark `chosen` if present. -/
def setRingBearer (g : Game) (p : PlayerId) (chosen : Option ObjectId) : Game :=
  let g :=
    g.objects.foldl (fun acc o =>
      if o.status.ringBearer && o.controlledBy p then
        acc.setObject { o with status := { o.status with ringBearer := false } }
      else acc) g
  match chosen with
  | none =>
    g.modifyPlayer p (fun pl => { pl with ringBearerId := none })
  | some id =>
    match g.findObject? id with
    | none => g.modifyPlayer p (fun pl => { pl with ringBearerId := none })
    | some o =>
      let g := g.setObject { o with status := { o.status with ringBearer := true } }
      g.modifyPlayer p (fun pl => { pl with ringBearerId := some id })

/-- Whether `p` currently has the city's blessing. -/
def hasCitysBlessing (g : Game) (p : PlayerId) : Bool :=
  (g.player p).citysBlessing

/-- Number of permanents `p` currently controls (phased-out objects do not
count). -/
def permanentCount (g : Game) (p : PlayerId) : Nat :=
  (g.permanentsOf p).size

/-- Whether `p` controls a permanent with ascend, or a resolving spell with
ascend on the stack. -/
def controlsAscend (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o => o.printed.keywords.ascend) ||
    g.stack.any (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        o.controller == some p && o.printed.keywords.ascend &&
          o.triggeredAbility.isNone && o.abilityEffect.isNone
      | none => false)

/-- Grant the city's blessing if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantCitysBlessingIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.citysBlessing)
    (fun g p => g.controlsAscend p && g.permanentCount p ≥ 10)
    (fun pl => { pl with citysBlessing := true })
    "has the city's blessing"

/-- Grant the city's blessing to every player who now qualifies. -/
def refreshCitysBlessing (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantCitysBlessingIfNeeded pl.id) g

/-- Put a shadow counter on `o`. It has shadow and is a Wraith. -/
def putShadowCounter (g : Game) (o : GameObject) : Game :=
  let extra :=
    if o.status.additionalSubtypes.any (· == "Wraith") then o.status.additionalSubtypes
    else o.status.additionalSubtypes.push "Wraith"
  g.setObject { o with status := { o.status with
    shadow := o.status.shadow + 1
    additionalSubtypes := extra } }
    |>.logMsg s!"{o.name} gets a shadow counter"

end Game
end Mtg.Engine
