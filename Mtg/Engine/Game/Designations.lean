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
    (change : PlayerChange) (msg : String) : Game :=
  if already (g.player p) then g
  else if qualifies g p then
    g.changePlayer p change |>.logMsg s!"{(g.player p).name} {msg}"
  else g

/-- Grant an enduring story if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantEnduringStoryIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.enduringStory)
    (fun g p => g.controlsStoried p && g.storiedPermanentCount p ≥ 3)
    (.enduringStory true)
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
        acc.changeStatus o.id (.ringBearer false)
      else acc) g
  match chosen with
  | none =>
    g.changePlayer p (.ringBearerId none)
  | some id =>
    match g.findObject? id with
    | none => g.changePlayer p (.ringBearerId none)
    | some _ =>
      let g := g.changeStatus id (.ringBearer true)
      g.changePlayer p (.ringBearerId (some id))

/-- Grant the city's blessing if `p` now qualifies. The designation is on the
player and is never removed. Not a triggered ability. -/
def grantCitysBlessingIfNeeded (g : Game) (p : PlayerId) : Game :=
  g.grantDesignationIfNeeded p (·.citysBlessing)
    (fun g p => g.controlsAscend p && g.permanentCount p ≥ 10)
    (.citysBlessing true)
    "has the city's blessing"

/-- Grant the city's blessing to every player who now qualifies. -/
def refreshCitysBlessing (g : Game) : Game :=
  g.players.foldl (fun g pl => g.grantCitysBlessingIfNeeded pl.id) g

/-- Put a shadow counter on `o`. It has shadow and is a Wraith. -/
def putShadowCounter (g : Game) (o : GameObject) : Game :=
  let n := g.countersYouPut o 1
  let g := g.recordPutCounters o.id .shadow n (byPlayer := o.controller)
  let g := g.createEffect (.additionalSubtype o.id .wraith true)
  g.logMsg s!"{o.name} gets a shadow counter"

end Game
end Mtg.Engine
