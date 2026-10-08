import Mtg.Engine.Card.Counter
import Mtg.Engine.Game.Damage

/-!
# Pumps, grants, and counters (CR 613.4c / 122)

Until-end-of-turn pumps and keyword grants, +1/+1 counters and amass
(CR 701.47), finality counters, hand-size effects, improvise
(CR 702.126).
-/

namespace Mtg.Engine
namespace Game

/-- Until-end-of-turn +P/+T on `o` (CR 613.4c / 611.2a). `trample` also grants
trample until end of turn (e.g. Oliphaunt). -/
def pumpPermanent (g : Game) (o : GameObject) (p t : Int) (trample := false) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addPump p t
    if trample then s.grantUntilEot Keyword.trample else s)
  let gain := if trample then " and gains trample" else ""
  g.logMsg s!"{o.name} gets {signedStat p}/{signedStat t}{gain} until end of turn"

/-- Until-end-of-turn +P/+T on each creature `p` controls. -/
def pumpControlledCreatures (g : Game) (p : PlayerId) (pw tw : Int) : Game :=
  g.forEachControlledCreature p (fun g o => g.pumpPermanent o pw tw)

/-- Grant `kw` until end of turn to each creature `p` controls that matches `pred`. -/
def grantUntilEotToControlledCreatures (g : Game) (p : PlayerId) (kw : Keywords)
    (label : String) (pred : Game → GameObject → Bool := fun _ _ => true) : Game :=
  g.forEachControlledCreature p fun g o =>
    if pred g o then
      g.mapObjectStatus o (·.grantUntilEot kw)
        |>.logMsg s!"{o.name} gains {label} until end of turn"
    else g

/-- Grant each keyword in `kws` until end of turn, re-reading `o` after each. -/
def grantUntilEotKeywords (g : Game) (o : GameObject) (kws : List Keywords) : Game :=
  kws.foldl (fun g kw =>
    match g.findObject? o.id with
    | some o => g.mapObjectStatus o (·.grantUntilEot kw)
    | none => g) g

/-- Grant `k` until end of turn and log the standard “gains … until end of turn”. -/
def grantUntilEotLogged (g : Game) (o : GameObject) (k : Keywords) : Game :=
  g.mapObjectStatus o (·.grantUntilEot k)
    |>.logMsg s!"{o.name} gains {k} until end of turn"

/-- Set base P/T, optional creature types, and keywords until end of turn. -/
def setUntilEotForm (g : Game) (o : GameObject) (pt : Int × Int)
    (kws : Keywords) (msg : String)
    (types : Option (Array String) := none)
    (additionalCreature := false) (additionalArtifact := false)
    (pumpPerArtifact := false) : Game :=
  g.mapObjectStatus o (fun s =>
    { s with
      setBasePT := some pt
      replacedCreatureTypesUntilEot := types.orElse fun _ => s.replacedCreatureTypesUntilEot
      untilEotKeywords := Keywords.merge s.untilEotKeywords kws
      additionalCreatureUntilEot := additionalCreature || s.additionalCreatureUntilEot
      additionalArtifactUntilEot := additionalArtifact || s.additionalArtifactUntilEot
      pumpPerArtifactUntilEot := pumpPerArtifact || s.pumpPerArtifactUntilEot })
    |>.logMsg msg

/-- Put `n` finality counters on `o` (MSH). Multiple counters are redundant. -/
def addFinalityTo (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) : Game :=
  let n := g.countersYouPut o n (putter := byPlayer)
  let g := g.mapObjectStatus o (fun s => { s with finality := s.finality + n })
  g.logMsg s!"{o.name} gets a finality counter"

/-- Frozen in Ice, or a granted “can't become untapped”, blocks every untap.
Enchanted River's Grasp only skips the untap step. -/
def hostCantBecomeUntapped (g : Game) (o : GameObject) : Bool :=
  let frozen :=
    g.battlefield.any (fun aura =>
      aura.attachedTo == some o.id &&
        aura.staticAbilities.any (fun
          | .enchantedLosesAbilitiesCantUntap => true
          | _ => false))
  let granted :=
    o.status.cantUntapGrantedBy.any (fun sid =>
      match g.findObject? sid with
      | some src => src.isOnBattlefield
      | none => false)
  frozen || granted

/-- Enchanted River's Grasp: doesn't untap during its controller's untap step. -/
def hostSkipsUntapStep (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun aura =>
    aura.attachedTo == some o.id &&
      aura.staticAbilities.any (fun
        | .enchantedLosesAbilitiesDoesntUntap => true
        | _ => false))

/-- Timestamp-ordered maximum hand size (MSH 184 / 376). `10000` is "no maximum". -/
def grantsNoMaxHandSize (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .noMaximumHandSize => true
    | _ => false)

def grantsMaxHandSizeTen (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .maximumHandSize 10 => true
    | .maximumHandSize _ => false
    | _ => false)

def effectiveMaxHandSize (g : Game) (p : PlayerId) : Nat :=
  let effects :=
    ((g.permanentsOf p).filter (fun o =>
      grantsNoMaxHandSize o || grantsMaxHandSizeTen o)).qsort
      (fun a b => decide (a.timestamp < b.timestamp))
  effects.foldl (fun acc o =>
    if grantsMaxHandSizeTen o then 10
    else if grantsNoMaxHandSize o then 10000
    else acc) (g.player p).maxHandSize

/-- Reduce generic mana in `cost` by `n` (improvise taps artifacts for {1}). -/
def improviseReduce (cost : ManaCost) (n : Nat) : ManaCost :=
  cost.reduceGeneric n

/-- Whether `face` has improvise, including from a granting permanent. -/
def spellHasImprovise (g : Game) (face : CardDef) (caster : PlayerId) : Bool :=
  face.hasImprovise ||
    (!face.isCreature &&
      (g.permanentsOf caster).any (fun o => o.printed.grantsImproviseToNoncreature))

/-- Tap untapped artifacts you control for improvise. Each pays {1}. -/
def tapArtifactsForImprovise (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  let mut g := g
  let mut seen : Array ObjectId := #[]
  for id in ids do
    if seen.contains id then
      throw "An artifact cannot be tapped twice for the same improvise payment"
    seen := seen.push id
    let some o := g.findObject? id | throw "no such object"
    if !(o.isOnBattlefield && o.printed.isArtifact && o.controlledBy p) then
      throw s!"{o.name} is not an artifact you control"
    if o.status.tapped then
      throw s!"{o.name} is already tapped"
    g := g.becomeTapped o
  return g.logMsg s!"{(g.player p).name} taps {ids.size} artifact(s) for improvise"

/-- Equip worthy may attach only to a legendary non-Villain red or white
creature. Other attach effects ignore this restriction. -/
def isWorthyPermanent (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature && o.printed.isWorthy

/-- Put a +1/+1 counter on `id` when it is still a creature. -/
def addPlusOneIfStillCreature (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | some o =>
    if o.isOnBattlefield && o.isCreature then g.addPlusOnePlusOneTo o 1
    else g.logMsg "The target is no longer legal"
  | none => g.logMsg "The target is no longer legal"

/-- The Army `controller` controls with the latest timestamp, if any. -/
def newestArmy? (g : Game) (controller : PlayerId) : Option GameObject :=
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Army")
  armies.foldl (fun best o =>
    match best with
    | none => some o
    | some b => if o.timestamp ≥ b.timestamp then some o else some b) none

/-- Put-counter triggers for Goblin, Orc, and Army permanents (CR 122.1). -/
def queueGoblinOrcArmyCounterTriggers (g : Game) (o : GameObject) : Game :=
  match o.controller with
  | some p =>
    if g.hasSubtype o "Goblin" || g.hasSubtype o "Orc" || g.hasSubtype o "Army" then
      g.putControlledTriggers p .youPutCountersOnGoblinOrcArmy
    else g
  | none => g

/-- Put an indestructible counter on `o`. -/
def addIndestructibleCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) : Game :=
  let n := g.countersYouPut o n (putter := byPlayer)
  let g := g.mapObjectStatus o (fun s =>
    { s with indestructibleCounters := s.indestructibleCounters + n })
  let g := g.logMsg s!"{o.name} gets an indestructible counter"
  if n > 0 then g.queueGoblinOrcArmyCounterTriggers o else g

/-- Put a lifelink counter on `o`. -/
def addLifelinkCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) : Game :=
  let n := g.countersYouPut o n (putter := byPlayer)
  let g := g.mapObjectStatus o (fun s =>
    { s with lifelinkCounters := s.lifelinkCounters + n })
  let g := g.logMsg s!"{o.name} gets a lifelink counter"
  if n > 0 then g.queueGoblinOrcArmyCounterTriggers o else g

/-- Put a burden counter on `o`. The log includes the new total. -/
def addBurdenCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) : Game :=
  let n := g.countersYouPut o n (putter := byPlayer)
  let g := g.mapObjectStatus o (fun s => { s with burden := s.burden + n })
  let total := (g.object! o.id).status.burden
  let g := g.logMsg s!"{o.name} gets a burden counter ({total})"
  if n > 0 then g.queueGoblinOrcArmyCounterTriggers o else g

/-- Put `n` counters of `kind` on `o`. +1/+1 counters go through
`addPlusOnePlusOneTo` so their enters-with bonus and “you put a +1/+1
counter” triggers still apply. Burden counters keep the total in the log. -/
def addCounters (g : Game) (o : GameObject) (kind : CounterKind) (n : Nat := 1)
    (entersWith := false) (byPlayer : Option PlayerId := none) : Game :=
  match kind with
  | .plusOnePlusOne =>
    g.addPlusOnePlusOneTo o n (entersWith := entersWith) (byPlayer := byPlayer)
  | .burden => g.addBurdenCounter o n (byPlayer := byPlayer)
  | kind =>
    let n := g.countersYouPut o n (putter := byPlayer) (entersWith := entersWith)
    if n == 0 then g
    else
      let g := g.mapObjectStatus o (fun s => s.addCounters kind n)
      let g := g.logMsg s!"{o.name} gets {kind.countersPhrase n}"
      g.queueGoblinOrcArmyCounterTriggers o

/-- Put the amass counters and subtype on `armyId`. -/
def finishAmassOn (g : Game) (controller : PlayerId) (armyId : ObjectId)
    (subtype : String) (n : Nat) (attach : Option ObjectId := none) : Game :=
  match g.findObject? armyId with
  | none => g.logMsg "That Army is no longer on the battlefield"
  | some army =>
    if !army.isOnBattlefield || !army.controlledBy controller || !g.hasSubtype army "Army" then
      g.logMsg "That Army is no longer on the battlefield"
    else
      let g :=
        if g.hasSubtype army subtype then g
        else
          g.mapObjectStatus army (fun s =>
            { s with additionalSubtypes := s.additionalSubtypes.push subtype })
      let army := g.object! army.id
      let g := g.addPlusOnePlusOneTo army n
      let g := g.logMsg
        s!"{(g.player controller).name} amasses {subtype}s {n} ({army.name} is the amassed Army)"
      match attach with
      | none => g
      | some sid =>
        match g.findObject? sid with
        | some src =>
          if src.isOnBattlefield then g.attachSourceTo src (g.object! army.id) else g
        | none => g

/-- Amass `[subtype]` `n` (CR 701.43). If you control no Army, the token
enters as 0/0 and triggers see that power before counters are put on it. If
you control more than one Army, you choose which one. -/
def amass (g : Game) (controller : PlayerId) (subtype : String) (n : Nat)
    (attach : Option ObjectId := none) : Game :=
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Army")
  if armies.size > 1 then
    let ids := armies.map (fun (o : GameObject) => o.id)
    { g with pending := .fraChoice controller (.chooseCards ids 1 (.amassArmy subtype n attach)) }
      |>.logMsg s!"{(g.player controller).name} chooses an Army to amass"
  else
    let createdFresh := armies.isEmpty
    let (g, army) :=
      match armies[0]? with
      | none => g.createToken controller (armyToken subtype)
      | some army => (g, army)
    let g :=
      if createdFresh then
        let g := g.afterPermanentEnters (g.object! army.id)
        g.logMsg s!"the amassed Army entered as a 0/0 creature"
      else g
    g.finishAmassOn controller (g.object! army.id).id subtype n attach

/-- Amass Goblins `n` (CR 701.43). -/
def amassGoblins (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Goblin" n

/-- Amass Orcs `n` (CR 701.43). -/
def amassOrcs (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Orc" n

/-- Amass Zombies `n` (CR 701.43). -/
def amassZombies (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Zombie" n

/-- Damage plus until-EOT lose-indestructible and exile-if-dies (e.g. Smite). -/
def dealDamageLoseIndestructibleExileTo (g : Game) (o : GameObject) (n : Nat) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addDamage n
    { s with
      untilEotLosesIndestructible := true
      untilEotExileIfDies := true })
  g.logMsg
    s!"{o.name} is dealt {n} damage, loses indestructible until end of turn, and will be exiled if it would die this turn"

/-- Until-end-of-turn “can't be blocked” (CR 509.1b / 611.2a). -/
def grantCantBeBlockedThisTurn (g : Game) (o : GameObject) : Game :=
  let g := g.mapObjectStatus o (·.grantUntilEot Keyword.cantBeBlocked)
  g.logMsg s!"{o.name} can't be blocked this turn"

/-- Until-end-of-turn +P/+T and trample (e.g. Oliphaunt). -/
def pumpAndGrantTrample (g : Game) (o : GameObject) (p t : Int) : Game :=
  g.pumpPermanent o p t (trample := true)

end Game
end Mtg.Engine
