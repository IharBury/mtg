import Mtg.Engine.Game.ModeledTriggers

/-!
# Reality Fracture resolution helpers

Shared helpers for resolving `Resolution.fra`: target legality, sources and
causes of resolving abilities, reflexive triggers, and searches.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `t` is still a legal target for the `i`th instance of “target”
of `kind` (CR 608.2b). -/
def targetLegalAt (g : Game) (controller : PlayerId) (kind : EffectTargetKind) (i : Nat)
    (t : Target) (sourceId : Option ObjectId) : Bool :=
  (g.legalTargetsForAtomicKind controller (kind.slotKind i) sourceId).contains t

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
    (source : Option GameObject := none) : Game :=
  let g := g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n (source := source))
  g.gainLife controller n

/-- Grant `k` to `o` until end of turn, logged. -/
def grantKeywordsUntilEot (g : Game) (o : GameObject) (k : Keywords) : Game :=
  if k == Keywords.none then g else g.grantUntilEotLogged o k

/-- The creature type `p` chooses for “choose a creature type”: the type most
common among creatures they control. -/
def chooseCreatureTypeFor (g : Game) (p : PlayerId) : String :=
  let counts : Array (String × Nat) :=
    (g.creaturesControlledBy p).foldl (fun acc o =>
      o.subtypes.foldl (fun acc t =>
        match acc.findIdx? (·.1 == t) with
        | some i => acc.modify i (fun (s, n) => (s, n + 1))
        | none => acc.push (t, 1)) acc) #[]
  (counts.foldl (fun best c =>
    match best with
    | none => some c
    | some b => if c.2 > b.2 then some c else best) none).map (·.1) |>.getD "Human"

/-- Create one token of `kind` for `controller` and return it. -/
def createOneKindToken (g : Game) (controller : PlayerId) (kind : TokenKind) :
    Game × GameObject :=
  g.createToken controller (tokenPrinted kind)

/-- Begin a `FraChoice` for `p`. -/
def beginFraChoice (g : Game) (p : PlayerId) (choice : FraChoice) (msg : String) : Game :=
  { g with pending := .fraChoice p choice }.logMsg msg

/-- Cards in `p`'s hand that a “reveal your hand, you choose” effect may pick. -/
def revealedHandChoices (g : Game) (p : PlayerId) (permanentOnly : Bool) : Array ObjectId :=
  (g.player p).hand.filter (fun id =>
    match g.findObject? id with
    | some o =>
      !o.printed.isLand && (!permanentOnly || o.printed.isPermanentCard)
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
  let g := g.modifyPlayer p (fun pl => { pl with sideboard := #[] })
  side.foldl (fun g card => (g.allocObject card p (.outside p)).1) g

/-- Cards named Sphinx's Approach in `p`'s graveyard. -/
def sphinxsApproachesInGraveyard (g : Game) (p : PlayerId) : Array ObjectId :=
  (g.player p).graveyard.filter (fun id =>
    (g.findObject? id).any (·.name == "Sphinx's Approach"))

/-- Next player after `p` in turn order among `ps`, starting with the active
player (CR 101.4). -/
def apnapFrom (g : Game) : Array PlayerId := g.apnapOrder

/-- Put `id` from a graveyard onto the battlefield under `controller`'s
control with `plusOnes` +1/+1 counters, and run its enters handling. -/
def returnCardToBattlefield (g : Game) (controller : PlayerId) (id : ObjectId)
    (plusOnes : Nat := 0) (tapped := false) : Game × ObjectId :=
  let name := (g.object! id).name
  let (g, newId) := g.putOntoBattlefield id controller (tapped := tapped)
  let g :=
    if plusOnes > 0 then
      g.mapObjectStatus (g.object! newId) (fun s => s.addPlusOnePlusOne plusOnes)
    else g
  let g := g.logMsg s!"{name} returns to the battlefield"
  (g, newId)


/-- `p` discards `id` from their hand (CR 701.9). -/
def discardFromHand (g : Game) (p : PlayerId) (id : ObjectId) (chooser : Option PlayerId := none) :
    Game :=
  let card := g.object! id
  let g :=
    match chooser with
    | some c => g.logMsg s!"{(g.player c).name} chooses {card.name}. {(g.player p).name} discards it"
    | none => g.logMsg s!"{(g.player p).name} discards {card.name}"
  let (g, _) := g.move id (.graveyard card.owner) none
  g.modifyPlayer p (fun pl => { pl with cardsDiscardedThisTurn := pl.cardsDiscardedThisTurn + 1 })

/-- `p` discards `id`, chosen at random (CR 701.9). -/
def discardFromHandRandomly (g : Game) (p : PlayerId) (id : ObjectId) : Game :=
  (g.logMsg s!"{(g.player p).name} discards a card at random").discardFromHand p id

/-- Remove up to `n` counters from `o` (Mabel, Bitter Recluse). The controller
of the ability removes counters that help an opponent's permanent (loyalty,
then +1/+1, then other kinds) or hurt their own (stun, then minus-one counters). -/
def removeUpToCountersFrom (g : Game) (controller : PlayerId) (o : GameObject) (n : Nat) : Game :=
  let take (have_ left : Nat) : Nat × Nat := (Nat.min have_ left, left - Nat.min have_ left)
  let s := o.status
  let s' :=
    if o.controlledBy controller then
      let (a, left) := take s.stun n
      let (b, _) := take s.minusOneMinusOne left
      { s with stun := s.stun - a, minusOneMinusOne := s.minusOneMinusOne - b }
    else
      let (a, left) := take s.loyaltyCounters n
      let (b, left) := take s.plusOnePlusOne left
      let (c, left) := take s.shield left
      let (d, _) := take s.indestructibleCounters left
      { s with loyaltyCounters := s.loyaltyCounters - a, plusOnePlusOne := s.plusOnePlusOne - b
               shield := s.shield - c, indestructibleCounters := s.indestructibleCounters - d }
  (g.setObject { o with status := s' }).logMsg s!"Counters are removed from {o.name}"

/-- The resolving activated or triggered ability's stack object. -/
def resolvingAbilityObject? (g : Game) : Option GameObject :=
  g.resolvingAbility.bind g.findObject?

/-- The object that caused the resolving triggered ability, where it is now. -/
def fraCause? (g : Game) : Option GameObject :=
  (g.resolvingAbilityObject?.bind (·.fraCauseId)).bind (fun id => g.findObject? (g.followMoved id))

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
  (g.creaturesControlledBy p).foldl (fun g o => g.addPlusOnePlusOneTo (g.object! o.id) n) g

/-- Put a loyalty counter on each planeswalker `p` controls. -/
def loyaltyOnEachPlaneswalkerOf (g : Game) (p : PlayerId) : Game :=
  let pws := (g.permanentsOf p).filter (·.printed.isPlaneswalker)
  if pws.isEmpty then g
  else
    let g := pws.foldl (fun g o =>
      let n := g.countersYouPut (g.object! o.id) 1 (putter := some p)
      (g.mapObjectStatus (g.object! o.id) (fun s =>
        { s with loyaltyCounters := s.loyaltyCounters + n })).logMsg
        s!"A loyalty counter is put on {o.name}") g
    g.queueLoyaltyPutTriggers p

end Game
end Mtg.Engine
