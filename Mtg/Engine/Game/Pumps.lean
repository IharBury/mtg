import Mtg.Engine.Card.Counter
import Mtg.Engine.Game.Damage

/-!
# Pumps, grants, and counters (CR 613.4c / 122)

Until-end-of-turn pumps and keyword grants, +1/+1 counters and amass
(CR 701.43), finality counters, hand-size effects, improvise
(CR 702.126).
-/

namespace Mtg.Engine
namespace Game

/-- Until-end-of-turn +P/+T on `o` (CR 613.4c / 611.2a). `trample` also grants
trample until end of turn (e.g. Oliphaunt). -/
def pumpPermanent (g : Game) (o : GameObject) (p t : Int) (trample := false) : Game :=
  let g := g.createEffect (.pump o.id p t)
  let g := if trample then g.createEffect (.keywordsUntilEot o.id Keyword.trample) else g
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
      (g.createEffect (.keywordsUntilEot o.id kw))
        |>.logMsg s!"{o.name} gains {label} until end of turn"
    else g

/-- Grant each keyword in `kws` until end of turn, re-reading `o` after each. -/
def grantUntilEotKeywords (g : Game) (o : GameObject) (kws : List Keywords) : Game :=
  kws.foldl (fun g kw =>
    if (g.findObject? o.id).isSome then g.createEffect (.keywordsUntilEot o.id kw)
    else g) g

/-- Grant `k` until end of turn and log the standard “gains … until end of turn”. -/
def grantUntilEotLogged (g : Game) (o : GameObject) (k : Keywords) : Game :=
  (g.createEffect (.keywordsUntilEot o.id k))
    |>.logMsg s!"{o.name} gains {k} until end of turn"

/-- Set base P/T, optional creature types, and keywords until end of turn. -/
def setUntilEotForm (g : Game) (o : GameObject) (pt : Int × Int)
    (kws : Keywords) (msg : String)
    (types : Option (Array CardSubtype) := none)
    (additionalCreature := false) (additionalArtifact := false)
    (pumpPerArtifact := false) : Game :=
  let g := g.createEffect (.setBasePTUntilEot o.id pt)
  let g :=
    match types with
    | some subs => g.createEffect (.replacedCreatureTypesUntilEot o.id subs)
    | none => g
  let g := if kws != Keywords.none then g.createEffect (.keywordsUntilEot o.id kws) else g
  let g := if additionalCreature then g.createEffect (.additionalCreature o.id true) else g
  let g := if additionalArtifact then g.createEffect (.additionalArtifactUntilEot o.id) else g
  let g := if pumpPerArtifact then g.createEffect (.pumpPerArtifactUntilEot o.id) else g
  g.logMsg msg

/-- Put `n` finality counters on `o` (MSH). Multiple counters are redundant. -/
def addFinalityTo (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none) (entersWith := false)
    (cause : Option EventCause := none) : Game :=
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .finality n (putter := byPlayer)
      (entersWith := entersWith) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .finality n entersWith byPlayer cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    let putter := byPlayer.orElse (fun _ => o.controller)
    let g :=
      if n' > 0 && !entersWith then g.record (GameEvent.counters g.turnNumber putter o.asEvent .finality n' (cause := cause'))
      else g
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

/-- Run the CR 616.1 replacement loop for untapping `o` (CR 122.1d: "If a
permanent with a stun counter on it would become untapped, instead remove a
stun counter from it"). Returns `(stunReplaced, cause')`. -/
def replaceUntap (g : Game) (o : GameObject)
    (cause : Option EventCause := none) : Bool × Option EventCause :=
  let untap := GameEvent.untapped g.turnNumber o.asEvent false (cause := cause)
  if !o.status.tapped || !untap.watches .wouldUntap then
    (false, cause)
  else
    let affected := o.controller.getD o.owner
    let specs : Array ReplacementSpec := Id.run do
      let mut s : Array ReplacementSpec := #[]
      if o.status.stun > 0 then
        s := s.push {
          id := { raw := 601, object := some o.id }
          source := some o.id
          controller := o.controller
          affectedPlayer := affected
          kind := .stunCounterUntap o.id
        }
      for (_, eff) in g.activeEffects do
        match eff with
        | .replacement spec _ =>
          match spec.kind with
          | .stunCounterUntap tid =>
            if tid == o.id && o.status.stun > 0 then
              s := s.push { spec with affectedPlayer := affected }
          | _ => pure ()
        | _ => pure ()
      return s
    let candidates := specs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
    match g.selectNextReplacement candidates #[] with
    | some chosen =>
      (true, g.wrapReplacedCause chosen.id cause o.controller)
    | none =>
      (false, cause)

/-- Timestamp-ordered maximum hand size (MSH 184 / 376). `none` is "no maximum". -/
def grantsNoMaxHandSize (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .noMaximumHandSize => true
    | _ => false)

def grantsMaxHandSizeTen (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .maximumHandSize 10 => true
    | .maximumHandSize _ => false
    | _ => false)

def effectiveMaxHandSize (g : Game) (p : PlayerId) : Option Nat :=
  let effects :=
    ((g.permanentsOf p).filter (fun o =>
      grantsNoMaxHandSize o || grantsMaxHandSizeTen o)).qsort
      (fun a b => decide (a.timestamp < b.timestamp))
  effects.foldl (fun acc o =>
    if grantsMaxHandSizeTen o then some 10
    else if grantsNoMaxHandSize o then none
    else acc) (g.player p).maxHandSize

/-- Reduce generic mana in `cost` by `n` (improvise taps artifacts for {1}). -/
def improviseReduce (cost : ManaCost) (n : Nat) : ManaCost :=
  cost.reduceGeneric n

/-- Whether `face` has improvise, including from a granting permanent. -/
def spellHasImprovise (g : Game) (face : CardDef) (caster : PlayerId) : Bool :=
  face.hasImprovise ||
    (!face.isCreature &&
      (g.permanentsOf caster).any (fun o => o.printed.grantsImproviseToNoncreature))

/-- Open a simultaneous rules-event batch on `g` for use across an `Except`
`do` block, returning the updated `Game` and a `closeBatch` continuation that
restores `currentBatch` and evaluates batch-level triggers once (CR 603.2c). -/
def openBatch (g : Game) (cause : Option EventCause := none) : Game × (Game → Game) :=
  match g.currentBatch with
  | some (batchId, prevCause?) =>
    let mergedCause? := prevCause?.orElse (fun _ => cause)
    ({ g with currentBatch := some (batchId, mergedCause?) }, id)
  | none =>
    let batchId : BatchId := ⟨g.nextBatchId⟩
    let startIdx := g.events.size
    ({ g with
        currentBatch := some (batchId, cause)
        nextBatchId := max g.nextBatchId (batchId.raw + 1)
        openBatchObjects := g.objects
        openBatchPlayers := g.players
        openBatchEffects := g.activeEffects
        openBatchPending := g.pending },
     fun g1 =>
       let keepOpen :=
         match g1.pending with
         | .chooseReplacement ..
         | .fraChoice _ (.chooseColor _)
         | .fraChoice _ (.entersCreatureType _)
         | .fraChoice _ (.entersOddEven _)
         | .fraChoice _ (.chooseCardName _) => true
         | _ => g1.pendingReplacement.isSome
       if keepOpen then
         g1.chainPendingReplacement (.closeBatch batchId startIdx)
       else
         g1.finishOpenBatch batchId startIdx)

/-- Tap untapped artifacts you control for improvise. Each pays {1}. -/
def tapArtifactsForImprovise (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  let cause := some (EventCause.costPayment .tap p (g.proposedSpell.map (·.spellId)))
  let (g0, closeBatch) := g.openBatch cause
  let mut g := g0
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
    g := g.becomeTapped o (cause := cause)
  g := closeBatch g
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
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o .army)
  armies.foldl (fun best o =>
    match best with
    | none => some o
    | some b => if o.timestamp ≥ b.timestamp then some o else some b) none

/-- Put an indestructible counter on `o`. -/
def addIndestructibleCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .indestructible n (putter := byPlayer) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .indestructible n false byPlayer cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    let putter := byPlayer.orElse (fun _ => o.controller)
    let g :=
      if n' > 0 then g.record (GameEvent.counters g.turnNumber putter o.asEvent .indestructible n' (cause := cause'))
      else g
    g.logMsg s!"{o.name} gets an indestructible counter"

/-- Put a lifelink counter on `o`. -/
def addLifelinkCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .lifelink n (putter := byPlayer) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .lifelink n false byPlayer cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    let putter := byPlayer.orElse (fun _ => o.controller)
    let g :=
      if n' > 0 then g.record (GameEvent.counters g.turnNumber putter o.asEvent .lifelink n' (cause := cause'))
      else g
    g.logMsg s!"{o.name} gets a lifelink counter"

/-- Put a burden counter on `o`. The log includes the new total. -/
def addBurdenCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .burden n (putter := byPlayer) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .burden n false byPlayer cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    let putter := byPlayer.orElse (fun _ => o.controller)
    let g :=
      if n' > 0 then g.record (GameEvent.counters g.turnNumber putter o.asEvent .burden n' (cause := cause'))
      else g
    let total := (g.object! o.id).status.burden
    g.logMsg s!"{o.name} gets a burden counter ({total})"

/-- Put `n` counters of `kind` on `o`. +1/+1 counters go through
`addPlusOnePlusOneTo` so their enters-with bonus and “you put a +1/+1
counter” triggers still apply. Burden counters keep the total in the log. -/
def addCounters (g : Game) (o : GameObject) (kind : CounterKind) (n : Nat := 1)
    (entersWith := false) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  match kind with
  | .plusOnePlusOne =>
    g.addPlusOnePlusOneTo o n (entersWith := entersWith) (byPlayer := byPlayer) (cause := cause)
  | .burden => g.addBurdenCounter o n (byPlayer := byPlayer) (cause := cause)
  | kind =>
    let (n', applied, cause', choice?, _) :=
      g.replaceCountersPutChoice o kind n (putter := byPlayer)
        (entersWith := entersWith) (cause := cause)
    match choice? with
    | some (chooser, choices) =>
      g.promptChooseReplacement chooser choices
        (.addCounters o.id kind n entersWith byPlayer cause)
    | none =>
      let g := g.consumeReplacementOrder applied
      if n' == 0 then g
      else
        let putter := byPlayer.orElse (fun _ => o.controller)
        let happened := GameEvent.counters g.turnNumber putter o.asEvent kind n' (cause := cause')
        (if entersWith then g else g.record happened).logMsg s!"{o.name} gets {kind.countersPhrase n'}"

/-- Put the amass counters and subtype on `armyId`. -/
def finishAmassOn (g : Game) (controller : PlayerId) (armyId : ObjectId)
    (subtype : CardSubtype) (n : Nat) (attach : Option ObjectId := none)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? armyId with
  | none => g.logMsg "That Army is no longer on the battlefield"
  | some army =>
    if !army.isOnBattlefield || !army.controlledBy controller || !g.hasSubtype army .army then
      g.logMsg "That Army is no longer on the battlefield"
    else
      let (g, cause) : Game × Option EventCause :=
        match cause with
        | some c => (g, some c)
        | none =>
          match g.currentResolvingContext? with
          | some (src, ctrl) =>
            let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) src
            (g, some c)
          | none => (g, none)
      let g :=
        if g.hasSubtype army subtype then g
        else g.createEffect (.additionalSubtype army.id subtype) (cause := cause)
      let army := g.object! army.id
      let g := g.addPlusOnePlusOneTo army n (cause := cause)
      let g := g.logMsg
        s!"{(g.player controller).name} amasses {subtype}s {n} ({army.name} is the amassed Army)"
      match attach with
      | none => g
      | some sid =>
        match g.findObject? sid with
        | some src =>
          if src.isOnBattlefield then g.attachSourceTo src (g.object! army.id) (cause := cause) else g
        | none => g

/-- Amass `[subtype]` `n` (CR 701.43). If you control no Army, the token
enters as 0/0 and triggers see that power before counters are put on it. If
you control more than one Army, you choose which one. -/
def amass (g : Game) (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
    (attach : Option ObjectId := none)
    (cause : Option EventCause := none) : Game :=
  let (g, cause) : Game × Option EventCause :=
    match cause with
    | some c => (g, some c)
    | none =>
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) src
        (g, some c)
      | none => (g, none)
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o .army)
  if armies.size > 1 then
    let ids := armies.map (fun (o : GameObject) => o.id)
    let g :=
      match cause with
      | some c => ids.foldl (fun (g : Game) id => g.change (.setLinkedExileCause id (some c))) g
      | none => g
    (g.change (.pending (.fraChoice controller (.chooseCards ids 1 (.amassArmy subtype n attach))))).logMsg
      s!"{(g.player controller).name} chooses an Army to amass"
  else
    let createdFresh := armies.isEmpty
    let (g, army) :=
      match armies[0]? with
      | none => g.createToken controller (armyToken subtype) (cause := cause)
      | some army => (g, army)
    let g :=
      if createdFresh then
        let g := g.afterPermanentEnters (g.object! army.id)
        g.logMsg s!"the amassed Army entered as a 0/0 creature"
      else g
    g.finishAmassOn controller (g.object! army.id).id subtype n attach (cause := cause)

/-- Amass Goblins `n` (CR 701.43). -/
def amassGoblins (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .goblin n (cause := cause)

/-- Amass Orcs `n` (CR 701.43). -/
def amassOrcs (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .orc n (cause := cause)

/-- Amass Zombies `n` (CR 701.43). -/
def amassZombies (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .zombie n (cause := cause)

/-- Damage plus until-EOT lose-indestructible and exile-if-dies (e.g. Smite).
Spells apply those three steps in order. This sets the same flags at once. -/
def dealDamageLoseIndestructibleExileTo (g : Game) (o : GameObject) (n : Nat)
    (source : EventObject) : Game :=
  let g := if n > 0 then g.record (GameEvent.damaged g.turnNumber source o.asEvent n) else g
  let g := g.record (GameEvent.damageMarked g.turnNumber o.id n)
  let g := g.createEffects #[.loseIndestructibleUntilEot o.id, .exileIfDiesUntilEot o.id]
  g.logMsg
    s!"{o.name} is dealt {n} damage, loses indestructible until end of turn, and will be exiled if it would die this turn"

/-- Until-end-of-turn “can't be blocked” (CR 509.1b / 611.2a). -/
def grantCantBeBlockedThisTurn (g : Game) (o : GameObject) : Game :=
  let g := g.createEffect (.keywordsUntilEot o.id Keyword.cantBeBlocked)
  g.logMsg s!"{o.name} can't be blocked this turn"

/-- Until-end-of-turn +P/+T and trample (e.g. Oliphaunt). -/
def pumpAndGrantTrample (g : Game) (o : GameObject) (p t : Int) : Game :=
  g.pumpPermanent o p t (trample := true)

end Game
end Mtg.Engine
