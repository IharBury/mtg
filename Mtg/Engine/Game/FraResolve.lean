import Mtg.Engine.Game.ModeledTriggers

/-!
# Reality Fracture effect resolution

`applyFra` resolves `Resolution.fra` for spells, activated abilities, and
triggered abilities. Choices made while one resolves leave a
`Pending.fraChoice`; `FraChoices` finishes them.
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

def applyFra (g : Game) (controller : PlayerId) (effect : Effect) (r : FraResolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.findObject?).orElse (fun _ => sourceId.bind g.findObject?)
  match r with
  | .bounce =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if o.zone == .stack then
            if o.isCopy then
              (g.removeFromZoneList o.id .stack |>.ceaseToExist o.id).logMsg
                s!"The copy of {o.name} ceases to exist (CR 704.5e)"
            else g.returnToHand id o.owner
          else g
        | none => g
      | Target.player _ => g) sourceId illegal
  | .exile =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") sourceId illegal
  | .destroyDrawIfNotAttacking =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let wasAttacking := o.status.attacking
      let ctrl := o.controller.getD o.owner
      let g := g.destroyPermanent o
      if wasAttacking then g else g.draw ctrl 1) sourceId illegal
  | .loseLife n => g.loseLife controller n
  | .damageEachOpponentGainLife n => g.drainOpponents controller n src?
  | .damageEachPlayer n =>
    g.livingPlayers.foldl (fun g pl => g.dealDamageToPlayer pl.id n (source := src?)) g
  | .drawAndGainLife c l => (g.draw controller c).gainLife controller l
  | .damageThenPlusOneOnSecond n =>
    let g :=
      match g.legalPermanentAt? controller kind targets 0 sourceId with
      | some o => g.dealDamageFrom srcName o n (source := src?)
      | none => g.logMsg "The first target is no longer legal"
    match g.legalPermanentAt? controller kind targets 1 sourceId with
    | some o => g.addPlusOnePlusOneTo o 1
    | none => g
  | .returnFromGyToBattlefield plusOnes =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let (g, newId) := g.returnCardToBattlefield controller id plusOnes
        g.afterPermanentEnters (g.object! newId)
      | _ => g) sourceId illegal
  | .returnFromGyToHand =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o => g.returnToHand id o.owner
        | none => g
      | _ => g) sourceId illegal
  | .destroyAllNotChosenType =>
    let chosen := g.chooseCreatureTypeFor controller
    let g := g.logMsg s!"{(g.player controller).name} chooses {chosen}"
    let doomed := g.battlefield.filter (fun o => o.isCreature && !g.hasSubtype o chosen)
    doomed.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.destroyPermanent o
      | none => g) g
  | .searchPlaneswalkerToTop =>
    match g.findLibraryCard? controller (·.isPlaneswalker) with
    | none =>
      (g.logMsg s!"{(g.player controller).name} searches their library and finds no planeswalker card").shuffleLibrary controller
    | some id =>
      let name := (g.object! id).name
      let g := g.logMsg s!"{(g.player controller).name} reveals {name}"
      let g := g.shuffleLibrary controller
      let g := g.modifyPlayer controller (fun pl =>
        { pl with library := (pl.library.filter (· != id)).push id })
      g.logMsg s!"{(g.player controller).name} puts {name} on top of their library"
  | .plusOneOnEachTarget n =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent id =>
        if g.targetLegalAt controller kind 0 t sourceId then
          g.addPlusOnePlusOneTo (g.object! id) n
        else g.illegalAbilityTarget t
      | _ => g) g
  | .returnAllNonlandPermanentsFromGy =>
    let ids := (g.player controller).graveyard.filter (fun id =>
      (g.findObject? id).any (fun o =>
        o.printed.isPermanentCard && !o.printed.isLand && !o.printed.isAura))
    let (g, newIds) := ids.foldl (fun (acc : Game × Array ObjectId) id =>
      let (g, newId) := acc.1.returnCardToBattlefield controller id
      (g, acc.2.push newId)) (g, #[])
    newIds.foldl (fun g id =>
      match g.findObject? id with
      | some o => g.afterPermanentEnters o
      | none => g) g
  | .drawMilledThisTurn =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.draw controller (g.player pid).cardsMilledThisTurn) sourceId illegal
  | .exileAllCreaturesEmpower =>
    let creatures := g.battlefield.filter (·.isCreature)
    let g := creatures.foldl (fun g o =>
      let (g, _) := g.move o.id .exile none
      g.logMsg s!"{o.name} is exiled") g
    g.empowerJace controller creatures.size
  | .drawGreatestPowerLoseLife =>
    let n := (g.greatestPowerAmongCreatures controller).toNat
    let before := (g.player controller).cardsDrawnThisTurn
    let g := g.draw controller n
    let drawn := (g.player controller).cardsDrawnThisTurn - before
    g.loseLife controller drawn
  | .revealHandDiscardNonland permanentOnly =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      g.beginRevealDiscard controller pid permanentOnly) sourceId illegal
  | .damageThenRevealDiscardNonland n =>
    g.withLegalKindPlayer controller kind targets (fun g pid =>
      let g := g.dealDamageToPlayer pid n (source := src?)
      g.beginRevealDiscard controller pid false) sourceId illegal
  | .extrapolate =>
    let g := g.materializeSideboard controller
    let names := (g.outsideCards controller).foldl (fun acc o =>
      if acc.contains o.name then acc else acc.push o.name) (#[] : Array String)
    if names.size < 2 then
      g.logMsg s!"{(g.player controller).name} has no two cards with different names outside the game"
    else
      g.beginFraChoice controller .extrapolateReveal
        s!"{(g.player controller).name} may reveal two cards with different names from outside the game"
  | .sphinxsApproach =>
    let g := g.draw controller 2
    match g.resolvingSpell.bind g.findObject? with
    | some spell =>
      if spell.zone == .stack && !spell.isCopy &&
          (g.sphinxsApproachesInGraveyard controller).size ≥ 4 then
        g.beginFraChoice controller (.sphinxsApproach spell.id)
          s!"{(g.player controller).name} may exile Sphinx's Approach and four cards named Sphinx's Approach"
      else g
    | none => g
  | .cadetThenPlusOneOtherWizardTokens =>
    let (g, cadet) := g.createOneKindToken controller .cadet
    (g.permanentsOf controller).foldl (fun g o =>
      if o.id != cadet.id && o.printed.isToken && g.hasSubtype o "Wizard" then
        g.addPlusOnePlusOneTo o 1
      else g) g
  | .damageEachOppCreatureAndPlaneswalker n =>
    let victims := g.battlefield.filter (fun o =>
      (o.isCreature || o.printed.isPlaneswalker) && o.controller.isSome &&
        !o.controlledBy controller)
    victims.foldl (fun g o =>
      match g.findObject? o.id with
      | some o => g.dealDamageFrom srcName o n (source := src?)
      | none => g) g
  | .loseAbilitiesThenFight =>
    match g.legalPermanentAt? controller kind targets 0 sourceId with
    | none => g.logMsg "The first target is no longer legal. No damage is dealt"
    | some victim =>
      let g := g.mapObjectStatus victim (fun s => { s with losesAbilitiesUntilEot := true })
      let g := g.logMsg s!"{victim.name} loses all abilities until end of turn"
      match g.legalPermanentAt? controller kind targets 1 sourceId with
      | some striker =>
        g.dealDamageFrom striker.name (g.object! victim.id) (max (g.power striker) 0)
          (source := some striker)
      | none => g.logMsg "The second target is no longer legal. No damage is dealt"
  | .pumpGrantUntap p t k =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.pumpPermanent o p t
      let g := g.grantKeywordsUntilEot (g.object! o.id) k
      g.applyPermanentAction (g.object! o.id) .untap) sourceId illegal
  | .pumpGrantPlusOne p t k n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.pumpPermanent o p t
      let g := g.grantKeywordsUntilEot (g.object! o.id) k
      g.addPlusOnePlusOneTo (g.object! o.id) n) sourceId illegal
  | .plusOneThenGrant n k =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        let g := g.addPlusOnePlusOneTo o n
        g.grantKeywordsUntilEot (g.object! o.id) k) sourceId illegal
  | .clashOfElements =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      g.beginFraChoice o.owner (.topOrBottomDamage o.id 2)
        s!"{(g.player o.owner).name} may put {o.name} on top of their library") sourceId illegal
  | .entrustTheSpark =>
    if (g.permanentsOf controller).any (·.printed.isPlaneswalker) then
      g.beginFraChoice controller .maySacrificePlaneswalker
        s!"{(g.player controller).name} may sacrifice a planeswalker"
    else g.logMsg s!"{(g.player controller).name} controls no planeswalker to sacrifice"
  | .cadetsPlusOnePerThreeIfFromGy n =>
    let fromGy := (g.resolvingSpell.bind g.findObject?).any (·.castFromGraveyard)
    let counters := if fromGy then (g.player controller).graveyard.size / 3 else 0
    Id.run do
      let mut g := g
      for _ in [0:n] do
        let (g', tok) := g.createOneKindToken controller .cadet
        g := g'
        if counters > 0 then
          match g.findObject? tok.id with
          | some o => g := g.addPlusOnePlusOneTo o counters
          | none => pure ()
      return g
  | .cadetWithHaste =>
    let (g, tok) := g.createOneKindToken controller .cadet
    match g.findObject? tok.id with
    | some o => g.grantKeywordsUntilEot o Keyword.haste
    | none => g
  | .drawOneOrTwoIfNotFromHand =>
    let fromHand := (g.resolvingSpell.bind g.findObject?).any (·.castFromHand)
    g.draw controller (if fromHand then 1 else 2)
  | .destroyThenPlusOneEachOfPlayer =>
    let g :=
      match g.legalPermanentAt? controller kind targets 0 sourceId with
      | some o => g.destroyPermanent o
      | none => g.logMsg "The first target is no longer legal"
    match targets[1]? with
    | some (Target.player pid) =>
      if g.targetLegalAt controller kind 1 (Target.player pid) sourceId then
        (g.creaturesControlledBy pid).foldl (fun g o => g.addPlusOnePlusOneTo o 1) g
      else g.logMsg "The second target is no longer legal"
    | _ => g
  | .exileReturnBrieflyIfMvAtMost n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      -- Ruling: the mana value is that of the permanent as it last existed
      -- on the battlefield.
      let mv := g.objectManaValue o
      let (g, exiled) := g.move o.id .exile none
      let g := g.logMsg s!"{o.name} is exiled"
      if mv ≤ n && !o.printed.isToken then
        let (g, back) := g.putOntoBattlefield exiled controller (tapped := true)
        let g := g.logMsg s!"{o.name} returns to the battlefield tapped under {(g.player controller).name}'s control"
        let g := { g with delayedEndStepExiles := g.delayedEndStepExiles.push back }
        g.afterPermanentEnters (g.object! back)
      else g) sourceId illegal
  | .eachPlayerMayWheel n =>
    match g.apnapFrom.toList with
    | [] => g
    | p :: rest =>
      g.beginFraChoice p (.mayWheel n rest.toArray)
        s!"{(g.player p).name} may discard their hand and draw {n} cards"
  | .mountainsAddExtraRed =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with mountainExtraRedThisTurn := pl.mountainExtraRedThisTurn + 1 })
    g.logMsg s!"Until end of turn, whenever {(g.player controller).name} taps a Mountain for mana, they add an additional \{R}"
  | .searchLandToGraveyard =>
    g.resolveLibrarySearch controller (·.isLand) "land card" fun g id =>
      let name := (g.object! id).name
      let (g, _) := g.move id (.graveyard controller) none
      g.logMsg s!"{(g.player controller).name} puts {name} into their graveyard"
  | .counter =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id => g.counterStackSpell id
      | _ => g) sourceId illegal
  | .counterUnlessPays n =>
    g.withLegalKindTarget controller kind targets (fun g _ =>
      g.beginPayOrLetCounter targets n) sourceId illegal
  | .millThenDraw m d => (g.mill controller m).draw controller d
  | .destroy =>
    g.withLegalKindPermanent controller kind targets (fun g o => g.destroyPermanent o)
      sourceId illegal
  | .damageExileIfDies n =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.dealDamageFrom srcName (g.object! o.id) n (source := src?)) sourceId illegal
  | .millMayPutPermanentGainLife n life =>
    let before := (g.player controller).graveyard.size
    let g := g.mill controller n
    let gy := (g.player controller).graveyard
    let milled := gy.extract before gy.size
    let choices := milled.filter (fun id => (g.findObject? id).any (·.printed.isPermanentCard))
    if choices.isEmpty then g.gainLife controller life
    else
      g.beginFraChoice controller (.mayPutMilledPermanent choices life)
        s!"{(g.player controller).name} may put a permanent card milled this way into their hand"
  | .chooseTriggerModes _ => g

end Game
end Mtg.Engine
