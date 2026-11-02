import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture activated and loyalty abilities

Resolutions used by FRA activated abilities, loyalty abilities, and the
emblems and effects those create. `applyFra` delegates them here.
-/

namespace Mtg.Engine
namespace Game

/-- Keyword coded by `code` in `Resolution.chooseKeyword`. -/
def fraKeywordOfCode : Nat → Keywords
  | 0 => Keyword.trample
  | 1 => Keyword.hexproof
  | 2 => Keyword.haste
  | 3 => Keyword.deathtouch
  | _ => Keywords.none

/-- Name of the keyword coded by `code`. -/
def fraKeywordName : Nat → String
  | 0 => "trample"
  | 1 => "hexproof"
  | 2 => "haste"
  | 3 => "deathtouch"
  | _ => "nothing"

/-- Ask `p` which of `options` the permanent `id` gains until end of turn. -/
def beginChooseKeyword (g : Game) (p : PlayerId) (id : ObjectId) (options : Array Nat) : Game :=
  match g.findObject? id with
  | some o =>
    if !o.isOnBattlefield then g
    else
      let names := String.intercalate ", " (options.toList.map fraKeywordName)
      g.beginFraChoice p (.chooseKeyword id options)
        s!"{(g.player p).name} chooses {names} for {o.name}"
  | none => g

/-- Give `p` an emblem or effect object in the command zone (CR 114.1–114.5). -/
def createCommandObject (g : Game) (p : PlayerId) (card : CardDef)
    (untilTurnOf : Option PlayerId := none) : Game :=
  let (g, obj) := g.allocObject card p .command (some p)
  match untilTurnOf with
  | some q =>
    let effCause :=
      g.resolveOptionalCause none (fallbackCtrl := some p) (defaultCause := .gameRule .spellCast)
    g.createEffect (.fraEmblemUntilTurnOf obj.id q) (cause := some effCause)
  | none => g

/-- Each player in APNAP order who controls a creature. -/
def playersWithCreaturesApnap (g : Game) : Array PlayerId :=
  g.apnapOrder.filter (fun p => !(g.creaturesControlledBy p).isEmpty)

/-- Ask the next player in `players` to sacrifice a creature for Garruk,
Veiled Butcher, or sacrifice the chosen creatures and finish. -/
def continueSacrificeEach (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (chosen : Array ObjectId) : Game :=
  match (players.filter (fun p => !(g.creaturesControlledBy p).isEmpty)).toList with
  | p :: rest =>
    g.beginFraChoice p (.sacrificeCreatureEach controller rest.toArray chosen)
      s!"{(g.player p).name} sacrifices a creature"
  | [] =>
    let youSacrificed := chosen.any (fun id =>
      (g.findObject? id).any (fun o => o.isOnBattlefield && g.controlledBy o controller))
    let pairs := chosen.filterMap (fun id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then some ((g.controllerOf o).getD o.owner, id)
        else none
      | none => none)
    let preBf := g.battlefield
    g.withBatch none fun g =>
      g.sacrificePermanentsLoop pairs (preBattlefield := some preBf)
        (createBeastFor := if youSacrificed then some controller else none)

/-- Ask the next opponent in `players` to discard two cards for Garruk,
Veiled Butcher, or draw `draws` cards for `controller` and finish. -/
partial def continueDiscardTwo (g : Game) (controller : PlayerId) (players : Array PlayerId)
    (draws : Nat) : Game :=
  match players.toList with
  | [] => g.draw controller draws
  | p :: rest =>
    let hand := (g.player p).hand
    if hand.size ≤ 2 then
      let nonland := (hand.filter (fun id => !g.isLand (g.object! id))).size
      let nextDraws := if nonland < 2 then draws + 1 else draws
      let g := g.withBatch none fun g =>
        hand.foldl (fun g id => g.discardFromHand p id) g
      let g :=
        if hand.isEmpty then g.logMsg s!"{(g.player p).name} has no cards to discard" else g
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep 10 controller nextDraws (modes := rest.toArray.map (·.idx)))
      else
        g.continueDiscardTwo controller rest.toArray nextDraws
    else
      g.beginFraChoice p (.discardTwo controller rest.toArray draws)
        s!"{(g.player p).name} discards two cards"

/-- Creatures attacking `p` directly (not a planeswalker). -/
def creaturesAttackingPlayer (g : Game) (p : PlayerId) : Array GameObject :=
  g.battlefield.filter (fun o =>
    g.isCreature o && o.status.attacking && o.status.attackingTarget == some (.player p))

/-- Run Hawkeye's Trick Arrows modes starting at `targetIdx`, pausing on
`Pending.chooseReplacement` so mode 2's choice or later modes do not clobber it. -/
def runHawkeyeArrows (g : Game) (controller : PlayerId) (modes : Array Nat)
    (targets : Array Target) (targetIdx : Nat) (sourceId : Option ObjectId) : Game := Id.run do
  let src := sourceId.bind g.damageSourceById?
  let illegal := some "The target is no longer legal"
  let mut g := g
  let mut idx := targetIdx
  for k in [0:modes.size] do
    let m := modes[k]!
    let slice := targets.extract idx (idx + 1)
    match m with
    | 0 =>
      g := g.withLegalKindPermanent controller .creature slice (fun g o =>
        (g.createEffect (.cantBlockUntilEot o.id)).logMsg
          s!"{o.name} can't block this turn") sourceId illegal
      idx := idx + 1
    | 1 =>
      g := g.withLegalKindPlayer controller .player slice
        (fun g pid => g.dealDamageToPlayer pid 2 (source := src)) sourceId illegal
      idx := idx + 1
    | _ =>
      if (g.player controller).hand.isEmpty then
        g := g.draw controller 1
      else
        g := g.beginFraChoice controller .discardThenDraw
          s!"{(g.player controller).name} discards a card, then draws a card"
    if let .chooseReplacement .. := g.pending then
      let rem := modes.extract (k + 1) modes.size
      if !rem.isEmpty then
        g := g.chainPendingReplacement
          (.finishPostStep 12 controller idx (sourceId := sourceId)
            (targets := targets) (modes := rem))
      return g
  return g

/-- Run the library-reveal, put-onto-battlefield, and bottoming tail of
`.identityEcho` once the target permanent's exile completes. -/
def finishIdentityEchoAfterExile (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (oName : String) : Game :=
  let g := g.logMsg s!"{oName} is exiled"
  let lib := (g.player controller).library
  let (revealed, hit) := Id.run do
    let mut revealed : Array ObjectId := #[]
    for i in [0:lib.size] do
      let id := lib[lib.size - 1 - i]!
      let c := g.object! id
      if g.isCreature c || g.isPlaneswalker c then
        return (revealed, some id)
      revealed := revealed.push id
    return (revealed, none)
  let allRevealed := revealed ++ hit.toArray
  let (g, revealCause?) : Game × Option EventCause :=
    if !allRevealed.isEmpty then
      let (g, c) := g.allocDelayedCause (some controller) sourceId
      (g, some c)
    else (g, none)
  let g :=
    if allRevealed.isEmpty then g
    else g.record (GameEvent.revealed g.turnNumber controller allRevealed (cause := revealCause?))
  let g := allRevealed.foldl (fun g id =>
    g.logMsg s!"{(g.player controller).name} reveals {(g.object! id).name}") g
  match hit with
  | some id =>
    let (g, newId) := g.putOntoBattlefield id controller (cause := revealCause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement
        (.finishPostStep 11 controller 0 none (some id) (ids := revealed) (cause := revealCause?))
    else
      let g :=
        match g.findObject? newId with
        | some entered =>
          if entered.isOnBattlefield then
            let g := g.logMsg s!"{entered.name} enters the battlefield"
            g.afterPermanentEnters entered
          else g
        | none => g
      if revealed.isEmpty then g
      else
        g.requestOrderInto revealed (.library controller)
          s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order"
          (cause := revealCause?)
  | none =>
    let g := g.logMsg "No creature or planeswalker card is revealed"
    if revealed.isEmpty then g
    else
      g.requestOrderInto revealed (.library controller)
        s!"{(g.player controller).name} puts the rest on the bottom of their library in a random order"
        (cause := revealCause?)

/-- Resolve an FRA activated or loyalty ability resolution. -/
def applyFraAbility (g : Game) (controller : PlayerId) (effect : Effect) (r : Resolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  let kind := effect.targetKind
  let illegal := some "The target is no longer legal"
  let srcName := g.fraSourceName sourceId
  let src? := (g.resolvingSpell.bind g.damageSourceById?).orElse (fun _ => sourceId.bind g.damageSourceById?)
  let source? : Option GameObject :=
    sourceId.bind g.findObject?
  let onSource (f : Game → GameObject → Game) : Game :=
    match source? with
    | some o => if o.isOnBattlefield then f g o else g
    | none => g
  let chosenX := (g.resolvingAbility.bind g.chosenXOf?).getD 0
  match r with
  | .emrakulGrantMana =>
    match sourceId.bind (fun id => g.followMovedToZone? id (· == Zone.exile)) with
    | none => g
    | some card =>
      let perm : PlayPermission :=
        { player := controller, whileExiled := true }
      let g := (g.createEffect (.playPermission card.id perm)).logMsg
        s!"{(g.player controller).name} may cast {card.name} for as long as it remains exiled"
      g.withLegalKindPermanent controller kind targets (fun g land =>
        let g := g.createEffect (.colorlessGrantUntilCast land.id card.id)
        g.logMsg s!"{g.name land} gains \"\{T}: Add \{C}\{C}\" until {card.name} is cast from exile")
        sourceId illegal
  | .nextSpellCantBeCountered =>
    (g.createEffect (.nextSpellCantBeCounteredThisTurn controller)).logMsg
      s!"The next spell {(g.player controller).name} casts this turn can't be countered"
  | .identityEcho =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let oName := g.name o
      let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
      let (g, _) := g.move o.id .exile none (cause := some exileCause)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement
          (.finishPostStep 62 controller (sourceId := sourceId) (cardId := some o.id))
      else
        g.finishIdentityEchoAfterExile controller sourceId oName)
      sourceId illegal
  | .destroyDrawIfLegendaryEnchantment =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let legendaryEnchantment := g.isLegendary o && g.isEnchantment o
      let g := g.destroyPermanent o
      if legendaryEnchantment then g.draw controller 1 else g) sourceId illegal
  | .chooseKeyword options =>
    onSource (fun g o => g.beginChooseKeyword controller o.id options.toArray)
  | .graveyardCardToLibraryBottom =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        let card := g.object! id
        (g.moveIdsInOrder #[id] (.library card.owner)).logMsg
          s!"{card.name} is put on the bottom of {(g.player card.owner).name}'s library"
      | _ => g) sourceId illegal
  | .destroyAllCreatures =>
    let preBf := g.battlefield
    let doomed := (preBf.filter (g.isCreature ·)).map (·.id)
    g.withBatch none fun g =>
      g.destroyPermanentsLoop doomed (preBattlefield := some preBf)
  | .ownerShufflesIntoLibrary =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let owner := o.owner
      let oName := g.name o
      let (g, _) := g.move o.id (.library owner) none
        (verb := some .shuffleIntoLibrary) (libraryPosition := some .shuffledIn)
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep 63 owner (cardId := some o.id))
      else
        let g := g.logMsg s!"{(g.player owner).name} shuffles {oName} into their library"
        g.shuffleThen owner .none) sourceId illegal
  | .grantCombatDamageDrawTwo =>
    onSource (fun g o =>
      let ab := TriggeredAbility.fra .combatDamageToPlayer
        "Whenever this creature deals combat damage to a player, draw two cards." (.draw 2)
      (g.createEffect (.grantedTriggered o.id ab true)).logMsg
        s!"Until end of turn, whenever {g.name o} deals combat damage to a player, {(g.player controller).name} draws two cards")
  | .sourceGetsPowerPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (g.isArtifact ·)).size
    match source? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o n 0 else g
    | none => g
  | .pumpPerArtifact =>
    let n : Int := Int.ofNat ((g.permanentsOf controller).filter (g.isArtifact ·)).size
    g.withLegalKindPermanent controller kind targets (fun g o => g.pumpPermanent o n 0)
      sourceId illegal
  | .plusOneOnEachWithPlusOne =>
    g.withBatch none fun g =>
      let ids := ((g.creaturesControlledBy controller).filter (·.status.plusOnePlusOne > 0)).map (·.id)
      ids.foldl (fun g id =>
        match g.findObject? id with
        | some o => g.addPlusOnePlusOneTo o 1
        | none => g) g
  | .bounceEachTarget =>
    g.withBatch none fun g =>
      (List.range targets.size).foldl (fun g i =>
        match targets[i]! with
        | t@(Target.permanent id) =>
          if g.targetLegalAt controller kind i t sourceId then
            match g.findObject? id with
            | some o => g.returnToHand id o.owner
            | none => g
          else g.illegalAbilityTarget t
        | _ => g) g
  | .surveilReturnNoncreatureNonland =>
    let g := g.beginSurveil controller 1
    match g.pending with
    | .surveil .. => g.change (.surveilReturnNoncreatureNonland true)
    | _ => g
  | .addBlueNoncreatureOnly =>
    (g.addMana controller (.colored .blue) 1 (source := sourceId)
      (restriction := some (.fra .noncreatureSpell))).logMsg
      s!"{(g.player controller).name} adds \{U} (noncreature spells only)"
  | .tapAndStunX =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := if o.status.tapped then g else g.becomeTapped o
      if chosenX == 0 then g
      else
        (g.recordPutCounters o.id .stun chosenX (byPlayer := some controller)).logMsg
          s!"{chosenX} stun counter(s) are put on {g.name o}") sourceId illegal
  | .emblemDrawOnCast =>
    let emblem : CardDef := {
      name := "Chandra, Chill of Compliance Emblem", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra .youCastSpell
        "Whenever you cast a spell, draw a card." (.draw 1)] }
    (g.createCommandObject controller emblem).logMsg
      s!"{(g.player controller).name} gets an emblem with \"Whenever you cast a spell, draw a card.\""
  | .empowerJacePerIsland =>
    let n := ((g.permanentsOf controller).filter (fun o => g.hasSubtype o .island)).size
    g.empowerJace controller n
  | .attackersGetMinusFiveUntilYourTurn =>
    let effectCard : CardDef := {
      name := s!"{srcName} effect", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creatureAttacksYouOrYourPlaneswalker)
        "Whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn."
        (.causeGetsPump (-5) 0)] }
    (g.createCommandObject controller effectCard (untilTurnOf := some controller)).logMsg
      s!"Until {(g.player controller).name}'s next turn, whenever a creature attacks them or a planeswalker they control, it gets -5/-0 until end of turn"
  | .exileOpponentLibrariesButBottom =>
    g.withBatch none fun g =>
      g.forEachOpponent controller (fun g pid =>
        let lib := (g.player pid).library
        let g := (lib.extract 1 lib.size).foldl (fun g id => (g.move id .exile none).1) g
        g.logMsg s!"All but the bottom card of {(g.player pid).name}'s library are exiled")
  | .minusFourMinusOneUntilYourTurn =>
    if targets.isEmpty then g
    else
      g.withLegalKindPermanent controller kind targets (fun g o =>
        (g.createEffect (.untilTurnOfPump o.id controller (-4) (-1))).logMsg
          s!"{g.name o} gets -4/-1 until {(g.player controller).name}'s next turn") sourceId illegal
  | .eachPlayerSacrificesThenBeast =>
    g.continueSacrificeEach controller g.apnapOrder #[]
  | .eachOpponentDiscardsTwoDrawPerShort =>
    g.continueDiscardTwo controller (g.apnapOrder.filter (· != controller)) 0
  | .damageEachCreatureExceptYourTokens n =>
    let victims := g.battlefield.filter (fun o =>
      g.isCreature o && !(o.printed.isToken && g.controlledBy o controller))
    let (g, cause?) : Game × Option EventCause :=
      if n == 0 || victims.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none => (g, none)
    g.withBatch cause? fun g =>
      victims.foldl (fun g o =>
        match g.findObject? o.id with
        | some o => if o.isOnBattlefield then g.dealDamageFrom srcName o n (source := src?) (cause := cause?) else g
        | none => g) g
  | .emblemCreaturesGetTwoTwo =>
    let emblem : CardDef := {
      name := s!"{srcName} Emblem", types := #[]
      staticAbilities := #[.fra .emblemCreaturesGetTwoTwo] }
    (g.createCommandObject controller emblem).logMsg
      s!"{(g.player controller).name} gets an emblem with \"Creatures you control get +2/+2.\""
  | .untapTargets =>
    g.withBatch none fun g =>
      (List.range targets.size).foldl (fun g i =>
        match targets[i]! with
        | t@(Target.permanent id) =>
          if g.targetLegalAt controller kind i t sourceId then
            match g.findObject? id with
            | some o => g.applyPermanentAction o .untap
            | none => g
          else g.illegalAbilityTarget t
        | _ => g) g
  | .attackersGetTwoTwoTrampleUntilYourTurn =>
    let effectCard : CardDef := {
      name := s!"{srcName} effect", types := #[]
      triggeredAbilities := #[TriggeredAbility.fra (.fra .creaturesAttackYourOpponent)
        "Whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn."
        (.attackersOfPlayerGetTwoTwoTrample)] }
    (g.createCommandObject controller effectCard (untilTurnOf := some controller)).logMsg
      s!"Until {(g.player controller).name}'s next turn, creatures attacking their opponents get +2/+2 and gain trample"
  | .plusOnePerLand =>
    let n := ((g.permanentsOf controller).filter (g.isLand ·)).size
    g.withLegalKindPermanent controller kind targets (fun g o =>
      if n == 0 then g else g.addPlusOnePlusOneTo o n) sourceId illegal
  | .maySacrificeCreatureForBeast =>
    if (g.creaturesControlledBy controller).isEmpty then g
    else
      g.beginFraChoice controller (.maySacrificeThen #[.creature] .beastToken sourceId)
        s!"{(g.player controller).name} may sacrifice a creature"
  | .damageUpToOneAndPlayer n =>
    let (g, cause?) : Game × Option EventCause :=
      if n == 0 || targets.isEmpty then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none => (g, none)
    g.withBatch cause? fun g =>
      targets.foldl (fun g t =>
        match t with
        | Target.permanent id =>
          if g.targetLegalAt controller kind 0 t sourceId then
            g.dealDamageFrom srcName (g.object! id) n (source := src?) (cause := cause?)
          else g.illegalAbilityTarget t
        | Target.player pid =>
          if g.targetLegalAt controller kind 1 t sourceId then
            g.dealDamageToPlayer pid n (source := src?) (cause := cause?)
          else g.illegalAbilityTarget t
        | _ => g) g
  | .beastToken => g.createKindTokens controller .beast44trample 1
  | .putCauseCountersOnSource =>
    match g.resolvingAbilityObject?.bind (·.fraCauseStatus), source? with
    | some st, some o =>
      if !o.isOnBattlefield then g
      else
        g.withBatch none fun g =>
          let g := g.putCountersExceptPlusOne o.id st (byPlayer := g.controllerOf o)
          let g := if st.plusOnePlusOne > 0 then g.addPlusOnePlusOneTo (g.object! o.id) st.plusOnePlusOne else g
          g.logMsg s!"Counters are put on {g.name o}"
    | _, _ => g
  | .mayMoveSourceCountersToTarget =>
    match source? with
    | some src =>
      g.withLegalKindPermanent controller kind targets (fun g o =>
        if src.isOnBattlefield && src.status.hasCounters then
          g.beginFraChoice controller (.mayMoveAllCounters src.id o.id)
            s!"{(g.player controller).name} may move all counters from {g.name src} onto {g.name o}"
        else g) sourceId illegal
    | none => g
  | .mayPayThenProliferate pay times =>
    g.beginFraChoice controller (.mayPayThen pay (.proliferate times) sourceId)
      s!"{(g.player controller).name} may pay \{{pay}}"
  | .becomeArtifactCreatureUntilEot =>
    onSource (fun g o =>
      (g.createEffect (.additionalCreature o.id true)).logMsg
        s!"{o.name} becomes an artifact creature until end of turn")
  | .queueMshReflexive kind paid =>
    if kind == 2 then
      g.beginFraChoice controller (.hawkeyeModes paid #[] sourceId)
        s!"{(g.player controller).name} chooses up to {paid} Trick Arrows modes"
    else g.queueModeledReflexive controller sourceId kind paid
  | .mshReflexive kind paid =>
    g.resolveModeledReflexive controller sourceId kind paid targets g.resolvingDivision
  | .hawkeyeArrows modes =>
    g.runHawkeyeArrows controller modes.toArray targets 0 sourceId
  | .copySourceSpellXTimes =>
    match sourceId.bind g.findObject? with
    | some spell =>
      if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
      else
        let x := spell.chosenX.getD 0
        let (g, copies) := (List.range x).foldl (fun (acc : Game × Array ObjectId) _ =>
          let g := acc.1.copyStackSpell spell controller
          (g, acc.2.push ((g.stack.back?.map (·.objectId)).getD spell.id))) (g, #[])
        let targeted := ((g.stackEntry? spell.id).map (!·.targets.isEmpty)).getD false
        if copies.isEmpty || !targeted then g
        else
          g.beginFraChoice controller (.newTargetsForCopies copies)
            s!"{(g.player controller).name} may choose new targets for the copies"
    | none => g
  | .damageEqualSourcePower =>
    let src := sourceId.bind g.damageSourceById?
    let n :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none =>
        match sourceId.bind g.lastKnownBefore? with
        | some eo => (eo.power.getD 0).toNat
        | none => 0
    let srcName := (src.map g.name).getD "The creature"
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.dealDamageFrom srcName o n (source := src))
      sourceId (some "The target is no longer legal")
  | .returnSourceToHand =>
    match sourceId.bind (fun id => g.followMovedToZone? id (fun | .graveyard _ => true | _ => false)) with
    | some o =>
      if o.zone == .graveyard o.owner then g.returnToHand o.id o.owner
      else g.logMsg s!"{o.name} is no longer in the graveyard"
    | none => g.logMsg "The ability's source is no longer in the graveyard"
  | .sarumanExileCopyMayCast =>
    g.withLegalKindTarget controller kind targets (fun g t =>
      match t with
      | Target.card id =>
        match g.findObject? id with
        | some o =>
          if !(o.zone == .graveyard o.owner) ||
              !(g.isEnchantment o || g.isInstantOrSorcery o) then
            g.logMsg "The target is no longer legal"
          else
            let name := g.name o
            let (g, exId) := g.move id .exile none
            let g := g.logMsg s!"{name} is exiled"
            let card := g.object! exId
            let base := g.copiableValues card
            let copyId : ObjectId := ⟨g.nextObjectId⟩
            let copyTs := g.timestamp + 1
            let copyObj : GameObject := {
              id := copyId
              printed := base
              owner := controller
              controller := some controller
              zone := .exile
              timestamp := copyTs
              isCopy := true
            }
            let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot copyObj)
              (cause := g.resolveOptionalCause none (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
            g.beginFraChoice controller (.mayCastCopy copyId)
              s!"{(g.player controller).name} may cast the copy of {name} without paying its mana cost"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal") sourceId illegal
  | .zemoBoastCopies =>
    let exiled := (g.resolvingAbility.map g.boastExiledOf).getD #[]
    let (g, cause?) : Game × Option EventCause :=
      if exiled.any (fun id => (g.findObject? id).any (·.zone == .exile)) then
        let (g, c) := g.allocDelayedCause (some controller) sourceId
        (g, some c)
      else (g, none)
    let (g, copies) := g.withBatchReturn cause? fun g =>
      exiled.foldl (fun (acc : Game × Array ObjectId) id =>
        let (g, cs) := acc
        match g.findObject? id with
        | some card =>
          if card.zone != .exile then (g, cs)
          else
            let base := g.copiableValues card
            let copyId : ObjectId := ⟨g.nextObjectId⟩
            let copyTs := g.timestamp + 1
            let copyObj : GameObject := {
              id := copyId
              printed := { base with isToken := base.isPermanentCard }
              owner := controller
              controller := some controller
              zone := .exile
              timestamp := copyTs
              isCopy := true
            }
            let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot copyObj)
              (cause := g.resolveOptionalCause cause? (fallbackSrc := sourceId) (fallbackCtrl := some controller)))
            let g := g.createEffect (.playPermission copyId {
              player := controller,
              whileExiled := true, withoutManaCost := true, ignoreTiming := true })
              (cause := cause?)
            (g, cs.push copyId)
        | none => (g, cs)) (g, #[])
    if copies.isEmpty then g.logMsg "No exiled card is left to copy"
    else
      g.beginFraChoice controller (.castCopiesFree copies 1000 3)
        s!"{(g.player controller).name} may cast up to three of the copies without paying their mana costs"
  | .extort =>
    g.beginFraChoice controller (.mayPayExtort sourceId)
      s!"{(g.player controller).name} may pay \{W/B} (extort)"
  | .proliferate times =>
    if times == 0 then g
    else
      (g.change (.pending (.chooseProliferate controller times))).logMsg
        s!"{(g.player controller).name} proliferates {times} time(s)"
  | .causeGetsPump p t =>
    match g.fraCause? with
    | some o => if o.isOnBattlefield then g.pumpPermanent o p t else g
    | none => g
  | .attackersOfPlayerGetTwoTwoTrample =>
    match g.fraCauseController? with
    | some defender =>
      g.withBatch none fun g =>
        (g.creaturesAttackingPlayer defender).foldl (fun g o =>
          let g := g.pumpPermanent (g.object! o.id) 2 2
          g.grantKeywordsUntilEot (g.object! o.id) Keyword.trample) g
    | none => g
  | _ => g

end Game
end Mtg.Engine
