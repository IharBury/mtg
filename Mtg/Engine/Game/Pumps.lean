import Mtg.Engine.Card.Counter
import Mtg.Engine.Game.SacrificeDiscard

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
  if n == 0 then g
  else
  let putter :=
    if entersWith then byPlayer.orElse (fun _ => g.controllerOf o)
    else byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.addFinalityTo o.id n putter entersWith cause)
  else
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .finality n (putter := putter)
      (entersWith := entersWith) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addFinalityTo o.id n putter entersWith cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    if n' == 0 then g
    else
      let g :=
        if !entersWith then
          g.record (GameEvent.counters g.turnNumber putter (g.snapshot o) .finality n'
            (cause := g.resolveOptionalCause cause' (fallbackCtrl := putter)))
        else g
      g.logMsg s!"{g.name o} gets a finality counter"

/-- Frozen in Ice, or a granted “can't become untapped”, blocks every untap.
Enchanted River's Grasp only skips the untap step. -/
def hostCantBecomeUntapped (g : Game) (o : GameObject) : Bool :=
  let frozen :=
    g.battlefield.any (fun aura =>
      aura.attachedTo == some o.id &&
        (g.staticAbilities aura).any (fun
          | .enchantedLosesAbilitiesCantUntap => true
          | _ => false))
  let granted :=
    (g.cantUntapGrantedBy o).any (fun sid =>
      match g.findObject? sid with
      | some src => src.isOnBattlefield
      | none => false)
  frozen || granted

/-- Enchanted River's Grasp: doesn't untap during its controller's untap step. -/
def hostSkipsUntapStep (g : Game) (o : GameObject) : Bool :=
  g.battlefield.any (fun aura =>
    aura.attachedTo == some o.id &&
      (g.staticAbilities aura).any (fun
        | .enchantedLosesAbilitiesDoesntUntap => true
        | _ => false))

/-- Run one CR 616.1 replacement step for untapping `o` (CR 122.1d: "If a
permanent with a stun counter on it would become untapped, instead remove a
stun counter from it"). When multiple `.stunCounterUntap` effects apply, returns
`choice? = some (chooser, choices)` so the controller/affected player chooses. -/
def replaceUntap (g : Game) (o : GameObject)
    (cause : Option EventCause := none) :
    Bool × Array ReplacementId × Option EventCause × Option (PlayerId × Array ReplacementId) :=
  let untap := GameEvent.untapped g.turnNumber (g.snapshot o)
    (cause := g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)
      (defaultCause := .turnBased .untapAll))
  if !o.status.tapped || !untap.watches .wouldUntap then
    (false, #[], cause, none)
  else
    let ctrl := g.controllerOf o
    let affected := ctrl.getD o.owner
    let specs : Array ReplacementSpec := Id.run do
      let mut s : Array ReplacementSpec := #[]
      if o.status.stun > 0 then
        s := s.push {
          id := { kind := .stunCounterUntap, object := some o.id }
          source := some o.id
          controller := ctrl
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
    match g.selectNextReplacementStep candidates #[] g.replacementOrder with
    | .none =>
      (false, #[], cause, none)
    | .needChoice chooser choices _ =>
      (false, #[], cause, some (chooser, choices))
    | .chosen chosen _ =>
      (true, #[chosen.id],
        g.wrapReplacedCause chosen.id cause ctrl (defaultCause := .turnBased .untapAll),
        none)

/-- Untap `o` on the battlefield, running `replaceUntap` and pausing on
`Pending.chooseReplacement` (`PendingReplacement.untapPermanent`) if multiple
CR 616.1 untap replacements compete (CR 122.1d / 616.1). -/
def untapPermanent (g : Game) (o : GameObject)
    (duringUntapStep : Bool := false) (logUntap : Bool := true)
    (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.untapPermanent o.id duringUntapStep logUntap cause)
  else if !o.isOnBattlefield || !o.status.tapped || g.hostCantBecomeUntapped o then g
  else
    let defaultCause : EventCause :=
      if duringUntapStep then cause.getD (.turnBased .untapAll)
      else g.resolveOptionalCause cause (fallbackCtrl := g.controllerOf o)
        (defaultCause := .turnBased .untapAll)
    let untap := GameEvent.untapped g.turnNumber (g.snapshot o)
      (cause := defaultCause)
    if !untap.watches .wouldUntap then g
    else
      let (stunned, applied, cause', choice?) := g.replaceUntap o (cause := some defaultCause)
      match choice? with
      | some (chooser, choices) =>
        g.promptChooseReplacement chooser choices
          (.untapPermanent o.id duringUntapStep logUntap (some defaultCause))
      | none =>
        let g := g.consumeReplacementOrder applied
        if stunned then
          let g := g.record (GameEvent.counters g.turnNumber (g.controllerOf o) (g.snapshot o) .stun 1 true
            (cause := cause'.getD defaultCause))
          g.logMsg s!"A stun counter is removed from {g.name o} instead of untapping it (CR 122.1d)"
        else
          let g := g.record untap
          if logUntap then g.logMsg s!"{g.name o} untaps" else g

/-- Untap each permanent in `ids` sequentially inside an open or standalone
batch, pausing on `Pending.chooseReplacement` when stun-counter replacements tie. -/
def untapPermanentsLoop (g : Game) (ids : Array ObjectId)
    (cause : Option EventCause := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.untapPermanentsLoop ids cause)
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        g := g.untapPermanent o (cause := cause)
        if let .chooseReplacement .. := g.pending then
          let rem := ids.extract (i + 1) ids.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement (.untapPermanentsLoop rem cause)
          return g
    | none => pure ()
  return g

/-- Timestamp-ordered maximum hand size (CR 613.7a; MSH 184 / 376). `none` is "no maximum". -/
def effectiveMaxHandSize (g : Game) (p : PlayerId) : Option Nat :=
  let entries : Array ((Nat × Nat) × Option Nat) :=
    (g.permanentsOf p).foldl (fun acc o =>
      (g.evalLayer6 o).staticsWithTs.foldl (fun acc (ab, ts) =>
        match ab with
        | .noMaximumHandSize => acc.push (ts, none)
        | .maximumHandSize n => acc.push (ts, some n)
        | _ => acc) acc) #[]
  let sorted :=
    entries.qsort (fun a b =>
      decide (a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2)))
  sorted.foldl (fun _ (_, maxHs) => maxHs) (g.player p).maxHandSize

/-- Reduce generic mana in `cost` by `n` (improvise taps artifacts for {1}). -/
def improviseReduce (cost : ManaCost) (n : Nat) : ManaCost :=
  cost.reduceGeneric n

/-- Whether `face` has improvise, including from a granting permanent. -/
def spellHasImprovise (g : Game) (face : CardDef) (caster : PlayerId) : Bool :=
  face.hasImprovise ||
    (!face.isCreature &&
      (g.permanentsOf caster).any (fun o =>
        (g.baseCard o).grantsImproviseToNoncreature && g.retainsPrintedAbilities o))

/-- Tap untapped artifacts you control for improvise. Each pays {1}. -/
def tapArtifactsForImprovise (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  let cause := some (EventCause.costPayment .tap p (g.proposedSpell.map (·.spellId)))
  let g ← g.withBatchM cause fun g => do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for id in ids do
      if seen.contains id then
        throw "An artifact cannot be tapped twice for the same improvise payment"
      seen := seen.push id
      let some o := g.findObject? id | throw "no such object"
      if !(o.isOnBattlefield && g.isArtifact o && g.controlledBy o p) then
        throw s!"{g.name o} is not an artifact you control"
      if o.status.tapped then
        throw s!"{g.name o} is already tapped"
      g := g.becomeTapped o (cause := cause)
    return g
  return g.logMsg s!"{(g.player p).name} taps {ids.size} artifact(s) for improvise"

/-- Put a +1/+1 counter on `id` when it is still a creature. -/
def addPlusOneIfStillCreature (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | some o =>
    if o.isOnBattlefield && g.isCreature o then g.addPlusOnePlusOneTo o 1
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
  if n == 0 then g
  else
  let putter := byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.addCounters o.id .indestructible n false putter cause)
  else
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .indestructible n (putter := putter) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .indestructible n false putter cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    if n' == 0 then g
    else
      let g :=
        g.record (GameEvent.counters g.turnNumber putter (g.snapshot o) .indestructible n'
          (cause := g.resolveOptionalCause cause' (fallbackCtrl := putter)))
      g.logMsg s!"{g.name o} gets an indestructible counter"

/-- Put a lifelink counter on `o`. -/
def addLifelinkCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
  let putter := byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.addCounters o.id .lifelink n false putter cause)
  else
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .lifelink n (putter := putter) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .lifelink n false putter cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    if n' == 0 then g
    else
      let g :=
        g.record (GameEvent.counters g.turnNumber putter (g.snapshot o) .lifelink n'
          (cause := g.resolveOptionalCause cause' (fallbackCtrl := putter)))
      g.logMsg s!"{g.name o} gets a lifelink counter"

/-- Put a burden counter on `o`. The log includes the new total. -/
def addBurdenCounter (g : Game) (o : GameObject) (n : Nat := 1)
    (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
  let putter := byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.addCounters o.id .burden n false putter cause)
  else
  let (n', applied, cause', choice?, _) :=
    g.replaceCountersPutChoice o .burden n (putter := putter) (cause := cause)
  match choice? with
  | some (chooser, choices) =>
    g.promptChooseReplacement chooser choices
      (.addCounters o.id .burden n false putter cause)
  | none =>
    let g := g.consumeReplacementOrder applied
    if n' == 0 then g
    else
      let g :=
        g.record (GameEvent.counters g.turnNumber putter (g.snapshot o) .burden n'
          (cause := g.resolveOptionalCause cause' (fallbackCtrl := putter)))
      let total := (g.object! o.id).status.burden
      g.logMsg s!"{g.name o} gets a burden counter ({total})"

/-- Put `n` counters of `kind` on `o`. +1/+1 counters go through
`addPlusOnePlusOneTo` so their enters-with bonus and “you put a +1/+1
counter” triggers still apply. Burden counters keep the total in the log. -/
def addCounters (g : Game) (o : GameObject) (kind : CounterKind) (n : Nat := 1)
    (entersWith := false) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  if n == 0 then g
  else
  match kind with
  | .plusOnePlusOne =>
    g.addPlusOnePlusOneTo o n (entersWith := entersWith) (byPlayer := byPlayer) (cause := cause)
  | .burden => g.addBurdenCounter o n (byPlayer := byPlayer) (cause := cause)
  | kind =>
    let putter :=
      if entersWith then byPlayer.orElse (fun _ => g.controllerOf o)
      else byPlayer.orElse (fun _ => g.counterPutter (g.controllerOf o))
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.addCounters o.id kind n entersWith putter cause)
    else
      let (n', applied, cause', choice?, _) :=
        g.replaceCountersPutChoice o kind n (putter := putter)
          (entersWith := entersWith) (cause := cause)
      match choice? with
      | some (chooser, choices) =>
        g.promptChooseReplacement chooser choices
          (.addCounters o.id kind n entersWith putter cause)
      | none =>
        let g := g.consumeReplacementOrder applied
        if n' == 0 then g
        else
          let finalCause := g.resolveOptionalCause cause' (fallbackCtrl := putter)
          let happened := GameEvent.counters g.turnNumber putter (g.snapshot o) kind n'
            (cause := finalCause)
          let g := if entersWith then g else g.record happened
          let g :=
            if !entersWith && kind == .time then
              g.syncImpendingNotACreature o.id (cause := some finalCause)
            else g
          g.logMsg s!"{g.name o} gets {kind.countersPhrase n'}"

/-- Log and optionally attach `attach` once `finishAmassOn`'s counter placement finishes. -/
private def finishAmassOnPost (g : Game) (controller : PlayerId) (armyId : ObjectId)
    (subtype : CardSubtype) (n : Nat) (attach : Option ObjectId := none)
    (cause : Option EventCause := none) : Game :=
  let armyName := (g.findObject? armyId).map (·.name) |>.getD "Army"
  let g := g.logMsg
    s!"{(g.player controller).name} amasses {subtype}s {n} ({armyName} is the amassed Army)"
  match attach with
  | none => g
  | some sid =>
    match g.findObject? sid, g.findObject? armyId with
    | some src, some army =>
      if src.isOnBattlefield && army.isOnBattlefield then
        g.attachSourceTo src army (cause := cause)
      else g
    | _, _ => g

/-- Put the amass counters and subtype on `armyId`. -/
def finishAmassOn (g : Game) (controller : PlayerId) (armyId : ObjectId)
    (subtype : CardSubtype) (n : Nat) (attach : Option ObjectId := none)
    (stage : Nat := 0) (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishAmassOn controller armyId subtype n attach stage cause)
  else if stage != 0 then
    g.finishAmassOnPost controller armyId subtype n attach cause
  else
    match g.findObject? armyId with
    | none => g.logMsg "That Army is no longer on the battlefield"
    | some army =>
      if !army.isOnBattlefield || !g.controlledBy army controller || !g.hasSubtype army .army then
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
        if let .chooseReplacement .. := g.pending then
          g.chainPendingReplacement (.finishAmassOn controller armyId subtype n attach 1 cause)
        else
          g.finishAmassOnPost controller armyId subtype n attach cause

/-- Finish a freshly-created Army amass once `createToken` completes (synchronously
or after a `Pending.chooseReplacement` pause). -/
def finishFreshAmass (g : Game) (controller : PlayerId) (subtype : CardSubtype)
    (n : Nat) (attach : Option ObjectId) (cause : Option EventCause := none)
    (minId : Nat := 0) : Game :=
  let freshArmies :=
    (g.permanentsOf controller).filter (fun o =>
      o.printed.isToken && g.hasSubtype o .army && o.id.raw ≥ minId)
  if freshArmies.isEmpty then g
  else
    let g := freshArmies.foldl (fun acc o => acc.afterPermanentEnters o) g
    let g := g.logMsg s!"the amassed Army entered as a 0/0 creature"
    g.finishAmassOn controller freshArmies[0]!.id subtype n attach (cause := cause)

/-- Amass `subtype` `n`, choosing which Army when `controller` controls more
than one (CR 701.47). -/
def amass (g : Game) (controller : PlayerId) (subtype : CardSubtype) (n : Nat)
    (attach : Option ObjectId := none)
    (cause : Option EventCause := none) : Game :=
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.amass controller subtype n attach cause)
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
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o .army)
  if armies.size > 1 then
    let ids := armies.map (fun (o : GameObject) => o.id)
    let g :=
      match cause with
      | some c => g.change (.stashedCause (some c))
      | none => g
    (g.change (.pending (.fraChoice controller (.chooseCards ids 1 (.amassArmy subtype n attach))))).logMsg
      s!"{(g.player controller).name} chooses an Army to amass"
  else
    match armies[0]? with
    | some army =>
      g.finishAmassOn controller army.id subtype n attach (cause := cause)
    | none =>
      let minId := g.nextObjectId
      let (g, _) := g.createToken controller (armyToken subtype) (cause := cause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishFreshAmass controller subtype n attach cause minId)
      else
        g.finishFreshAmass controller subtype n attach (cause := cause) (minId := minId)

/-- Amass Goblins `n` (CR 701.47). -/
def amassGoblins (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .goblin n (cause := cause)

/-- Amass Orcs `n` (CR 701.47). -/
def amassOrcs (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .orc n (cause := cause)

/-- Amass Zombies `n` (CR 701.47). -/
def amassZombies (g : Game) (controller : PlayerId) (n : Nat)
    (cause : Option EventCause := none) : Game :=
  g.amass controller .zombie n (cause := cause)

/-- Finish the until-EOT lose-indestructible and exile-if-dies effects of
`dealDamageLoseIndestructibleExileTo` once `markDamageOn` finishes. -/
def finishDealDamageLoseIndestructibleExile (g : Game) (targetId : ObjectId)
    (targetName : String) (n : Nat) (cause : EventCause) : Game :=
  let name := (g.findObject? targetId).map g.name |>.getD targetName
  let g := g.createEffects #[.loseIndestructibleUntilEot targetId, .exileIfDiesUntilEot targetId]
    (cause := some cause)
  g.logMsg
    s!"{name} is dealt {n} damage, loses indestructible until end of turn, and will be exiled if it would die this turn"

/-- Damage plus until-EOT lose-indestructible and exile-if-dies (e.g. Smite).
Spells apply those three steps in order. This sets the same flags at once. -/
def dealDamageLoseIndestructibleExileTo (g : Game) (o : GameObject) (n : Nat)
    (source : EventObject) : Game :=
  let (g, cause) := g.allocDelayedCause source.controller source.id
  let srcObj := g.damageSourceObjFromSnapshot? (some source)
  let oName := g.name o
  let g := g.markDamageOn o (Int.ofNat n) s!"{oName} is dealt {n} damage"
    (source := some source) (sourceObj := srcObj) (cause := some cause)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishDealDamageLoseIndestructibleExile o.id oName n cause)
  else
    g.finishDealDamageLoseIndestructibleExile o.id oName n cause

/-- Until-end-of-turn “can't be blocked” (CR 509.1b / 611.2a). -/
def grantCantBeBlockedThisTurn (g : Game) (o : GameObject) : Game :=
  let g := g.createEffect (.keywordsUntilEot o.id Keyword.cantBeBlocked)
  g.logMsg s!"{o.name} can't be blocked this turn"

/-- Until-end-of-turn +P/+T and trample (e.g. Oliphaunt). -/
def pumpAndGrantTrample (g : Game) (o : GameObject) (p t : Int) : Game :=
  g.pumpPermanent o p t (trample := true)

end Game
end Mtg.Engine
