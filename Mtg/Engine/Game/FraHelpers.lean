import Mtg.Engine.Game.ModeledTriggers

/-!
# Reality Fracture resolution helpers

Shared helpers for resolving `Resolution.fra`: target legality, sources and
causes of resolving abilities, reflexive triggers, and searches.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `t` is still a legal target for the `i`th instance of “target”
of `kind` (CR 608.2b), accounting for `g.resolvingSkippedSlots` when optional
slots were skipped at announcement. -/
def targetLegalAt (g : Game) (controller : PlayerId) (kind : EffectTargetKind) (i : Nat)
    (t : Target) (sourceId : Option ObjectId) : Bool :=
  let slot :=
    if g.resolvingSkippedSlots.isEmpty || kind.spec.slots.isEmpty then i
    else Id.run do
      let mut s := 0
      let mut rem := i
      while s < kind.spec.slots.size do
        if g.resolvingSkippedSlots.contains s then
          s := s + 1
        else if rem == 0 then
          return s
        else
          rem := rem - 1
          s := s + 1
      return s
  (g.legalTargetsForAtomicKind controller (kind.slotKind slot) sourceId).contains t

/-- The permanent announced as the `i`th target, if it is still legal. -/
def legalPermanentAt? (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (i : Nat) (sourceId : Option ObjectId) : Option GameObject :=
  match targets[i]? with
  | some (Target.permanent id) =>
    if g.targetLegalAt controller kind i (Target.permanent id) sourceId then g.findObject? id
    else none
  | _ => none

/-- The source's name for damage logs. -/
def fraSourceName (g : Game) (sourceId : Option ObjectId) : String :=
  match g.resolvingSpell.bind g.findObject? with
  | some o => o.name
  | none =>
    match sourceId.bind g.findObject? with
    | some o => o.name
    | none => "The effect"

/-- Deal `n` damage to each opponent of `controller`, then `controller` gains
`n` life. -/
def drainOpponents (g : Game) (controller : PlayerId) (n : Nat)
    (source : Option GameObject := none)
    (cause : Option EventCause := none) : Game :=
  let defaultCause :=
    cause.orElse (fun _ =>
      if n == 0 then none
      else g.currentResolvingContext?.map fun (src, ctrl) =>
        .oneShotEffect none
          (src.orElse (fun _ => source.map (·.id)))
          (ctrl.orElse (fun _ => some controller)))
  g.withBatch defaultCause fun g =>
    let g := g.dealDamageToEachOpponent controller n (source := source) (cause := cause)
    g.gainLife controller n (cause := cause)

/-- Grant `k` to `o` until end of turn, logged. -/
def grantKeywordsUntilEot (g : Game) (o : GameObject) (k : Keywords) : Game :=
  if k == Keywords.none then g else g.grantUntilEotLogged o k

/-- The creature type `p` chooses for “choose a creature type”: the type most
common among creatures they control. -/
def chooseCreatureTypeFor (g : Game) (p : PlayerId) : CardSubtype :=
  let counts : Array (CardSubtype × Nat) :=
    (g.creaturesControlledBy p).foldl (fun acc o =>
      (g.subtypes o).foldl (fun acc t =>
        if !t.isCreatureType then acc
        else
          match acc.findIdx? (·.1 == t) with
          | some i => acc.modify i (fun (s, n) => (s, n + 1))
          | none => acc.push (t, 1)) acc) #[]
  (counts.foldl (fun best c =>
    match best with
    | none => some c
    | some b => if c.2 > b.2 then some c else best) none).map (·.1) |>.getD .human

/-- Cards in `p`'s hand that a “reveal your hand, you choose” effect may pick. -/
def revealedHandChoices (g : Game) (p : PlayerId) (permanentOnly : Bool) : Array ObjectId :=
  (g.player p).hand.filter (fun id =>
    match g.findObject? id with
    | some o =>
      !g.isLand o && (!permanentOnly || g.isPermanentCard o)
    | none => false)

/-- `victim` reveals their hand and `chooser` picks a card for them to discard. -/
def beginRevealDiscard (g : Game) (chooser victim : PlayerId) (permanentOnly : Bool) : Game :=
  let g := g.revealHand victim
  if (g.revealedHandChoices victim permanentOnly).isEmpty then
    let what := if permanentOnly then "nonland permanent card" else "nonland card"
    g.logMsg s!"{(g.player victim).name} has no {what} to discard"
  else
    g.beginFraChoice chooser (.discardFromRevealedHand victim permanentOnly)
      s!"{(g.player chooser).name} chooses a card from {(g.player victim).name}'s hand"

/-- Cards `p` owns outside the game. -/
def outsideCards (g : Game) (p : PlayerId) : Array GameObject :=
  g.objects.filter (fun o => o.zone == .outside p)

/-- Give `p`'s sideboard cards object identities outside the game, so an
effect can reveal or move them (CR 400.11b). -/
def materializeSideboard (g : Game) (p : PlayerId) : Game :=
  let side := (g.player p).sideboard
  let g := g.changePlayer p (.sideboard #[])
  side.foldl (fun g card => (g.allocObject card p (.outside p)).1) g

/-- Cards named Sphinx's Approach in `p`'s graveyard. -/
def sphinxsApproachesInGraveyard (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (·.name == "Sphinx's Approach"))

/-- Next player after `p` in turn order among `ps`, starting with the active
player (CR 101.4). -/
def apnapFrom (g : Game) : Array PlayerId := g.apnapOrder

/-- Put `id` from a graveyard onto the battlefield under `controller`'s
control with `plusOnes` +1/+1 counters, logging arrival only when synchronous
entry onto `.battlefield` succeeded (CR 800.4b / 616.1). -/
def returnCardToBattlefield (g : Game) (controller : PlayerId) (id : ObjectId)
    (plusOnes : Nat := 0) (tapped := false) : Game × ObjectId :=
  let name := (g.object! id).name
  let (g, newId) := g.putOntoBattlefield id controller (tapped := tapped)
    (extraEntersWith := if plusOnes > 0 then #[(.plusOnePlusOne, plusOnes)] else #[])
  let paused := match g.pending with | .chooseReplacement .. => true | _ => false
  let g :=
    if !paused && (g.findObject? newId).any (·.isOnBattlefield) then
      g.logMsg s!"{name} returns to the battlefield"
    else g
  (g, newId)

/-- Remove up to `n` counters from `o` (Mabel, Bitter Recluse). The controller
of the ability removes counters that help an opponent's permanent (loyalty,
then +1/+1, then other kinds) or hurt their own (stun, then minus-one counters). -/
def removeUpToCountersFrom (g : Game) (controller : PlayerId) (o : GameObject) (n : Nat) : Game :=
  let take (have_ left : Nat) : Nat × Nat := (Nat.min have_ left, left - Nat.min have_ left)
  let s := o.status
  let removals : Array (CounterKind × Nat) :=
    if g.controlledBy o controller then
      let (a, left) := take s.stun n
      let (b, _) := take s.minusOneMinusOne left
      #[(.stun, a), (.minusOneMinusOne, b)]
    else
      let (a, left) := take s.loyaltyCounters n
      let (b, left) := take s.plusOnePlusOne left
      let (c, left) := take s.shield left
      let (d, _) := take s.indestructibleCounters left
      #[(.loyalty, a), (.plusOnePlusOne, b), (.shield, c), (.indestructible, d)]
  let g := g.withBatch none fun g =>
    removals.foldl (fun g (k, amt) =>
      g.recordRemoveCounters o.id k amt (byPlayer := some controller)) g
  g.logMsg s!"Counters are removed from {g.name o}"

/-- The resolving activated or triggered ability's stack object. -/
def resolvingAbilityObject? (g : Game) : Option GameObject :=
  g.resolvingAbility.bind g.findObject?

/-- The object that caused the resolving triggered ability, if still at its
recorded `ObjectId` (CR 400.7). -/
def fraCause? (g : Game) : Option GameObject :=
  (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind g.findObject?

/-- The controller of the object that caused the resolving triggered ability,
as it last existed. -/
def fraCauseController? (g : Game) : Option PlayerId :=
  g.resolvingAbilityObject?.bind (·.fraCauseController)

/-- “For each opponent, up to one target creature or planeswalker that
player controls”: one optional instance per opponent. -/
def perOpponentKind (g : Game) (controller : PlayerId) (f : TargetFilter) : EffectTargetKind :=
  let fs := (g.livingOpponents controller).map (fun pl => { f with controller := .specific pl.id.idx })
  .multi fs ((List.range fs.size).toArray)

/-- Put `n` +1/+1 counters on each creature `p` controls. -/
def plusOneOnEachCreatureOf (g : Game) (p : PlayerId) (n : Nat := 1) : Game :=
  g.withBatch none fun g =>
    (g.creaturesControlledBy p).foldl (fun g o => g.addPlusOnePlusOneTo (g.object! o.id) n) g

/-- Pause-safe loop placing a loyalty counter on each planeswalker in `ids`. -/
def loyaltyOnPwsLoop (g : Game) (p : PlayerId) (ids : Array ObjectId) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.finishPostStep (.loyaltyOnPlaneswalkersLoop p ids))
  let mut g := g
  for i in [0:ids.size] do
    let id := ids[i]!
    if let some o := g.findObject? id then
      if o.isOnBattlefield && g.isPlaneswalker o then
        g := g.putCountersDeferredLog o.id .loyalty 1 (some p) .isPutOn
        if let .chooseReplacement .. := g.pending then
          let rem := ids.extract (i + 1) ids.size
          if !rem.isEmpty then
            g := g.chainPendingReplacement (.finishPostStep (.loyaltyOnPlaneswalkersLoop p rem))
          return g
  return g

/-- Put a loyalty counter on each planeswalker `p` controls. -/
def loyaltyOnEachPlaneswalkerOf (g : Game) (p : PlayerId) : Game :=
  let pws := (g.permanentsOf p).filter (g.isPlaneswalker ·) |>.map (·.id)
  if pws.isEmpty then g
  else
    g.withBatch none fun g =>
      g.loyaltyOnPwsLoop p pws

end Game
end Mtg.Engine
