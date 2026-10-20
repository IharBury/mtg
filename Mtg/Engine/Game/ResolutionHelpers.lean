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
def exileCreaturesFromGraveyard (g : Game) (controller fromPlayer : PlayerId)
    (ty : CardType := .creature) : Game :=
  let ids :=
    (g.player fromPlayer).graveyard.filter (fun id =>
      match g.findObject? id with
      | some o => o.printed.hasType ty
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

/-- Put `o` on the top (`top`) or bottom of its owner's library. -/
def putOnOwnerLibrary (g : Game) (o : GameObject) (top : Bool) : Game :=
  let side := if top then "top" else "bottom"
  let name := o.name
  let owner := o.owner
  let (g, newId) := g.move o.id (.library owner) none
  let pl := g.player owner
  let without := stripId pl.library newId
  let library := if top then without ++ #[newId] else #[newId] ++ without
  (g.setPlayer { pl with library := library }).logMsg
    s!"{(g.player owner).name} puts {name} on the {side} of their library"

/-- Apply a shared permanent action (spells, activated abilities, and triggers). -/
def applyPermanentAction (g : Game) (o : GameObject) (action : PermanentAction) : Game :=
  let r : Resolution := action
  match r with
  | .pump (.fixed pw) (.fixed tw) _ => g.pumpPermanent o pw tw
  | .sequence [.pump (.fixed pw) (.fixed tw) _, .grant (.keywords _) _] =>
    g.pumpAndGrantTrample o pw tw
  | .destroy _ _ => g.destroyPermanent o
  | .putCounters (.ofKind .plusOnePlusOne n) _ => g.addPlusOnePlusOneTo o n
  | .dealDamage (.fixed n) _ _ => g.dealDamageToPermanent o n.toNat
  | .lose .indestructible _ =>
    let g := g.mapObjectStatus o (fun s => { s with untilEotLosesIndestructible := true })
    g.logMsg s!"{o.name} loses indestructible until end of turn"
  | .cant (.beBlocked _) => g.grantCantBeBlockedThisTurn o
  | .grant (.keywords k) _ =>
    g.grantUntilEotLogged o k
  | .putCounters (.ofKind .indestructible _) _ => g.addIndestructibleCounter o
  | .putCounters (.ofKind .doubleStrike _) _ =>
    let g := g.mapObjectStatus o (·.addCounters .doubleStrike 1)
    g.logMsg s!"{o.name} gets a double strike counter"
  | .putCounters (.ofKind .burden _) _ => g.addBurdenCounter o
  | .tap _ true => g.becomeTapped o
  | .untap _ =>
    if g.hostCantBecomeUntapped o then
      g.logMsg s!"{o.name} can't become untapped"
    else if !o.status.tapped then
      g.logMsg s!"{o.name} is already untapped"
    else if o.status.stun > 0 then
      let g := g.mapObjectStatus o (fun s => { s with stun := s.stun - 1 })
      g.logMsg s!"A stun counter is removed from {o.name} instead of untapping it (CR 122.1d)"
    else
      let g := g.mapObjectStatus o (fun s => { s with tapped := false })
      g.logMsg s!"{o.name} untaps"
  | .sequence [.becomeArtifact _, .grant (.keywords _) _] =>
    let g := g.mapObjectStatus o (fun s =>
      { s with
        additionalArtifactUntilEot := true
        untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.indestructible })
    g.logMsg
      s!"{o.name} becomes an artifact and gains indestructible until end of turn"
  | .becomePrepared _ true => g.becomePrepared o
  | .sequence [.tap _ true, .putCounters (.ofKind .stun _) _] =>
    -- Ruling 764: an already tapped creature still gets the stun counter.
    let g := if o.status.tapped then g else g.becomeTapped o
    let n := g.countersYouPut (g.object! o.id) 1
    let g := g.mapObjectStatus (g.object! o.id) (fun s => { s with stun := s.stun + n })
    g.logMsg s!"A stun counter is put on {o.name}"
  | .setBasePT (.fixed pw) (.fixed tw) _ =>
    let g := g.mapObjectStatus o (fun s => { s with setBasePT := some (pw, tw) })
    g.logMsg s!"{o.name} has base power and toughness {pw}/{tw} until end of turn"
  | .putOnLibrary .top _ => g.putOnOwnerLibrary o true
  | .putOnLibrary .bottom _ => g.putOnOwnerLibrary o false
  | .exile _ .forLater _ => (g.move o.id .exile none).1
  | .pump .double .double _ =>
    g.pumpPermanent o (g.power o) (g.toughness o)
  | _ => g

def applyOnPermanent (g : Game) (controller : PlayerId) (kind : EffectTargetKind)
    (targets : Array Target) (action : PermanentAction)
    (sourceId : Option ObjectId := none) (missing : Option String := none) : Game :=
  let r : Resolution := action
  match r with
  | .dealDamage (.fixed n) _ _ =>
    g.applyDamageToKindTarget controller kind targets n.toNat sourceId missing
  | _ =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.applyPermanentAction o action) sourceId missing

/-- Start surveilling `n` during resolution (CR 701.25): look at the top
`n` cards, put any number into the graveyard and the rest back on top in any
order. -/
def beginSurveil (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let pl := g.player p
  let count := min n pl.library.size
  let g := if n == 0 then g else g.queueScryOrSurveilTriggers p
  let g := if n == 0 then g else
    g.modifyPlayer p (fun pl => { pl with surveilledThisTurn := true })
  if count == 0 then
    g.logMsg s!"{pl.name} surveils {n} (no cards to look at)"
  else
    { g with pending := .surveil p count }.logMsg
      s!"{pl.name} surveils {n}"

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

/-- Deal `n` damage to each creature that is not `subtype`. -/
def dealDamageToEachNonDragon (g : Game) (n : Nat) (subtype : String := "Dragon") : Game :=
  g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o subtype)

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

/-- Reveal `p`'s hand (Cloak and Dagger; MSH 132 / 225). -/
def revealHand (g : Game) (p : PlayerId) : Game :=
  let names :=
    (g.player p).hand.foldl (fun acc id =>
      match g.findObject? id with
      | some o => if acc == "" then o.name else s!"{acc}, {o.name}"
      | none => acc) ""
  g.logMsg s!"{(g.player p).name} reveals their hand ({names})"

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
      ({ s with loyaltyCounters := s.loyaltyCounters - a, plusOnePlusOne := s.plusOnePlusOne - b
                shield := s.shield - c }).setCounter .indestructible (s.indestructibleCounters - d)
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
