import Mtg.Engine.Game.CastExtras

/-!
# Saga chapter resolution (CR 714.2)

`applyChapterEffect` for chapter abilities and the intervening-if
recheck used when their triggers resolve (CR 603.4).
-/

namespace Mtg.Engine
namespace Game

/-- The source gains landfall: create a 1/1 green Elf. -/
def gainLandfallCreateElf (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | some src =>
    if !src.isOnBattlefield then g
    else
      let landfall : TriggeredAbility :=
        .onLandYouControlEntersCreateTokens TokenKind.elf 1
      let g := g.createEffect (.grantedTriggered src.id landfall false)
      g.logMsg s!"{src.name} gains landfall"
  | none => g

/-- Elves the controller controls get +P/+0 and vigilance until end of turn. -/
def elvesGetVigilance (g : Game) (controller : PlayerId) (power : Int) : Game :=
  g.forEachControlledCreature controller fun g o =>
    if g.hasSubtype o .elf then
      let g := g.pumpPermanent o power 0
      g.createEffect (.keywordsUntilEot o.id Keyword.vigilance)
        |>.logMsg s!"{o.name} gets {signedStat power}/+0 and gains vigilance until end of turn"
    else g

/-- The announced creature gains hexproof while the source remains. -/
def grantHexproofWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (kind : EffectTargetKind) : Game :=
  match sourceId with
  | none => g
  | some sid =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.createEffect (.hexproofWhileSource o.id sid)
      g.logMsg s!"{o.name} gains hexproof for as long as the Saga remains")
      sourceId (some "The target is no longer legal")

/-- Damage the announced creature would deal is prevented while the source remains. -/
def preventDamageWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (kind : EffectTargetKind) : Game :=
  match sourceId with
  | none => g
  | some sid =>
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let g := g.createEffect (.preventDamageWhileSource o.id sid)
      g.logMsg s!"damage that would be dealt by {o.name} is prevented while the Saga remains")
      sourceId none

/-- Finish or run sequential exile-to-hand moves for `returnLinkedExileToHand`,
deferring `linkedExile` removal and the hand-arrival log across
`Pending.chooseReplacement` and checking `followMovedToZone?`. -/
def returnLinkedExileToHandLoop (g : Game) (srcId : ObjectId) (ids : Array ObjectId)
    (pendingItem : Option (ObjectId × PlayerId × String) := none) : Game := Id.run do
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.returnLinkedExileToHandLoop srcId ids pendingItem)
  let mut g := g
  if let some (eid, owner, name) := pendingItem then
    if (g.followMovedToZone? eid (· != .exile)).isSome then
      g := g.pruneLinkedExileId srcId eid
    if (g.followMovedToZone? eid (· == .hand owner)).isSome then
      g := g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  for i in [0:ids.size] do
    let eid := ids[i]!
    match g.findObject? eid with
    | none => pure ()
    | some card =>
      let owner := card.owner
      let name := card.name
      let (g', _) := g.move eid (.hand owner) none
      g := g'
      if let .chooseReplacement .. := g.pending then
        let rem := ids.extract (i + 1) ids.size
        return g.chainPendingReplacement
          (.returnLinkedExileToHandLoop srcId rem (some (eid, owner, name)))
      if (g.followMovedToZone? eid (· != .exile)).isSome then
        g := g.pruneLinkedExileId srcId eid
      if (g.followMovedToZone? eid (· == .hand owner)).isSome then
        g := g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  return g

/-- A card the source exiled returns to its owner's hand (CR 607.2a / 714.4,
including LKI when the Saga left the battlefield before its chapter resolved). -/
def returnLinkedExileToHand (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId with
  | none => g.logMsg "The Saga is no longer in play"
  | some sid =>
    let allIds := g.allLinkedExilesOf sid
    match allIds.find? (fun eid => (g.findObject? eid).any (·.zone == .exile)) with
    | some eid => g.returnLinkedExileToHandLoop sid #[eid]
    | none =>
      if allIds.isEmpty then
        if (g.findObject? sid).isSome then g.logMsg "No card is exiled with this Saga"
        else g.logMsg "The Saga is no longer in play"
      else
        g.logMsg "The exiled card is no longer there"

/-- Whenever the controller attacks this turn, a creature they control
gets +1/+1 for each Plains they control. -/
def attackPumpPerPlains (g : Game) (controller : PlayerId) : Game :=
  let (g, cause) := g.allocDelayedCause (some controller)
  let src :=
    match g.currentResolvingContext? with
    | some (some sid, _) => g.damageSourceById? sid
    | _ => none
  g.registerDelayedTrigger { controller, source := src, kind := .attackPumpPerPlains, cause }
    |>.logMsg
      s!"Whenever {(g.player controller).name} attacks this turn, a creature they control gets +1/+1 for each Plains they control"

/-- Create the 6/6 Dragon token for `treasureThenDragon`, guarding CR 616.1
choices and prevented token creation. -/
def treasureThenDragonCreateDragon (g : Game) (controller : PlayerId) : Game :=
  let g := g.change (.recentTokenIds #[])
  let (g, _) := g.createToken controller dragonToken (recordRecent := true)
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep .logAndEnterRecentTokens)
  else
    g.recentTokenIds.foldl (fun g tid =>
      match g.findObject? tid with
      | some entered =>
        if entered.isOnBattlefield then
          (g.logMsg s!"{entered.name} enters the battlefield").afterPermanentEnters entered
        else g
      | none => g) g

/-- Finish `treasureThenDragon` once the Treasure token creation completes. -/
def treasureThenDragonAfterCreate (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g
  | some src =>
    if !src.isOnBattlefield then g
    else if g.countSubtype controller .treasure < 4 then g
    else
      let name := src.name
      let g := g.sacrificeToGraveyard src s!"{name} is sacrificed"
      if let .chooseReplacement .. := g.pending then
        g.chainPendingReplacement (.finishPostStep (.treasureThenDragonCreateDragon controller))
      else
        g.treasureThenDragonCreateDragon controller

/-- Create a Treasure. Then if the controller has four or more, sacrifice
the source and create a 6/6 red Dragon with flying. -/
def treasureThenDragon (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  let g := g.createTreasureTokens controller 1
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep (.treasureThenDragonAfterCreate controller sourceId))
  else
    g.treasureThenDragonAfterCreate controller sourceId

/-- Gain control of the announced creatures while the source remains
(CR 608.2b / 611.2b / 613.7). -/
def gainControlWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target)
    (maxTotalMv : Option Nat := none) : Game :=
  g.withSourceStillOnBattlefield sourceId (fun g src =>
    let legalIds : Array ObjectId := Id.run do
      let mut ids : Array ObjectId := #[]
      for t in targets do
        if let Target.permanent id := t then
          if !ids.contains id then
            if let some o := g.findObject? id then
              let mvOk := maxTotalMv.all (g.objectManaValue o ≤ ·)
              if o.isOnBattlefield && g.isCreature o &&
                  g.canBeTargetedBy controller o sourceId && mvOk then
                ids := ids.push id
      return ids
    let totalMv := legalIds.foldl (fun acc id =>
      match g.findObject? id with
      | some o => acc + g.objectManaValue o
      | none => acc) 0
    if !targets.isEmpty && (legalIds.isEmpty || !maxTotalMv.all (totalMv ≤ ·)) then
      g.logMsg "The target is no longer legal"
    else
      g.withBatch none fun g =>
        legalIds.foldl (fun (g : Game) id =>
          match g.findObject? id with
          | some o =>
            if (g.player controller).lost then
              g.logMsg s!"{o.name} does not change control (CR 800.4b)"
            else
              g.createEffect (.controlWhileSource o.id controller src.id)
                |>.logMsg s!"{(g.player controller).name} gains control of {o.name}"
          | none => g) g)
    "The Super Hero Civil War has left the battlefield. You won't gain control."

/-- Resolve a printed Saga chapter (CR 714.2 / 608). -/
def applyChapterEffect (g : Game) (controller : PlayerId) (e : Effect)
    (sourceId : Option ObjectId) (targets : Array Target) : Game :=
  match e.asChapter? with
  | none => g.applyEffect controller e targets
  | some ch =>
  match ch with
  | .dealDamageToOppCreature n =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g o =>
      g.dealDamageToPermanent o n (source := sourceId.bind g.damageSourceEventById?))
      sourceId (some "The target is no longer legal")
  | .destroyOppArtifact =>
    g.withLegalKindPermanent controller .oppArtifact targets (fun g o =>
      g.destroyPermanent o) sourceId (some "The target is no longer legal")
  | .addMana mana =>
    g.addMana controller mana 1 (source := sourceId)
      |>.logMsg s!"{(g.player controller).name} adds {mana}"
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
  | .gainLandfallCreateElf =>
    g.gainLandfallCreateElf sourceId
  | .elvesGetVigilance p =>
    g.elvesGetVigilance controller p
  | .opponentDiscardsNonland =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.discardNonlandFrom controller pid)
      sourceId (some "The target is no longer legal")
  | .amass n =>
    g.amassGoblins controller n
  | .opponentLosesYouGain n =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid =>
        let (g, cause?) : Game × Option EventCause :=
          if n == 0 then (g, none)
          else
            match g.currentResolvingContext? with
            | some (src, ctrl) =>
              let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
              (g, some c)
            | none => (g, none)
        g.loseLife pid n (cause := cause?) |>.gainLife controller n (cause := cause?))
      sourceId (some "The target is no longer legal")
  | .grantHexproofWhileRemains =>
    g.grantHexproofWhileSource controller sourceId targets .creatureYouControl
  | .preventDamageWhileRemains =>
    g.preventDamageWhileSource controller sourceId targets .creature
  | .draw n =>
    g.draw controller n
  | .searchBasicPlainsExileGainLife max life =>
    g.resolveSearchBasicPlainsExile controller sourceId max life
  | .returnLinkedExileToHand =>
    g.returnLinkedExileToHand sourceId
  | .grantAttackPumpPerPlainsThisTurn =>
    g.attackPumpPerPlains controller
  | .blinkUntilEndStep =>
    g.withLegalKindPermanent controller .creatureOrLandYouControl targets
      (fun g o => g.exileUntilNextEndStep o) sourceId none
  | .treasureThenDragonIfFour =>
    g.treasureThenDragon controller sourceId
  | .recruit =>
    g.beginRecruit controller
  | .returnCreatureFromGyMvAtMost n =>
    g.withLegalKindTarget controller (.creatureCardInYourGraveyardMvAtMost n) targets
      (fun g t =>
        match t with
        | Target.card oid =>
          match g.findObject? oid with
          | none => g.logMsg "The target is no longer in the graveyard"
          | some o =>
            let name := o.name
            let (g, newId) := g.putOntoBattlefield oid controller
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep (.returnedToBattlefield oid false))
            else
              let entered := g.object! newId
              if entered.isOnBattlefield then
                (g.logMsg s!"{name} returns to the battlefield").afterPermanentEnters entered
              else g
        | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .plusOneUpToOne =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.addPlusOnePlusOneTo o 1) sourceId none
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost n =>
    g.gainControlWhileSource controller sourceId targets (maxTotalMv := some n)
  | .dealDamageToEachNonSubtypeAndOpponents n subtype =>
    let src? := sourceId.bind g.damageSourceById?
    let srcSnap? := sourceId.bind g.damageSourceEventById?
    let (g, cause?) : Game × Option EventCause :=
      if n == 0 then (g, none)
      else
        match g.currentResolvingContext? with
        | some (src, ctrl) =>
          let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
          (g, some c)
        | none => (g, none)
    let g :=
      g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o subtype)
        (source := srcSnap?) (cause := cause?)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.dealDamageToEachOpponent controller n sourceId cause?))
    else
      g.dealDamageToEachOpponent controller n (source := src?) (cause := cause?)
  | .dealXDamageToTargetOpponentGreatestArtifactMv =>
    let x := g.greatestManaValueAmong controller (g.isArtifact ·)
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.dealDamageToPlayer pid x (source := sourceId.bind g.damageSourceById?))
      sourceId (some "The target is no longer legal")
  | .spell s =>
    g.applyEffect controller {
      targeting := s.targeting
      allowsZeroTargets := s.allowsZeroTargets
      phrase := s.phrase
      resolution := Resolution.ofSpell s.resolution } targets

/-- Intervening “if” conditions rechecked on resolution (CR 608.2a).
“While you control” attack triggers are not rechecked. -/
def interveningStillHolds (g : Game) (controller : PlayerId)
    (ab : TriggeredAbility) : Bool :=
  let lifeOk :=
    match ab.timing.gainedLifeAtLeast with
    | none => true
    | some n => g.loggedLifeGained controller ≥ n
  let beginCombatFerocious :=
    match ab with
    | .triggered .yourBeginCombat _ opts =>
      match opts.youControlCreatureWithPower with
      | some n => g.greatestPowerAmongCreatures controller ≥ n
      | none => true
    | _ => true
  lifeOk && beginCombatFerocious

/-- All CR 603.4 / 608.2a intervening-“if” conditions rechecked on trigger
resolution before pushing `resolutionFinish`. Non-intervening trigger-time
conditions (such as “while you control” attack ferocious and CR 702.186 `∞`
`.step .harnessedFlicker`) are not rechecked here. -/
def triggerInterveningHolds (g : Game) (controller : PlayerId)
    (ab : TriggeredAbility) (sourceId : Option ObjectId)
    (targets : Array Target := #[]) (lastKnownPower : Option Int := none)
    (fraCauseId : Option ObjectId := none)
    (fraCauseStatus : Option Status := none) : Bool :=
  let src := sourceId.bind g.damageSourceById?
  let cause := fraCauseId.bind g.damageSourceById?
  let hulklingOk :=
    match ab.shared with
    | .watch .hulklingCompare =>
      match sourceId with
      | none => false
      | some sid =>
        let srcPT? : Option (Int × Int) :=
          match g.findObject? sid with
          | some s =>
            if s.isOnBattlefield then some (g.power s, g.toughness s)
            else
              match g.lastKnownPowerOf? sid, g.lastKnownToughnessOf? sid with
              | some hp, some ht => some (hp, ht)
              | _, _ => none
          | none =>
            match g.lastKnownPowerOf? sid, g.lastKnownToughnessOf? sid with
            | some hp, some ht => some (hp, ht)
            | _, _ => none
        let cid? :=
          match targets[0]? with
          | some (Target.permanent id) | some (Target.card id) => some id
          | _ => fraCauseId
        let causePT? : Option (Int × Int) :=
          match cid? with
          | none => none
          | some cid =>
            if cid == sid then none
            else
              match g.findObject? cid with
              | some other =>
                if other.isOnBattlefield then some (g.power other, g.toughness other)
                else
                  match g.lastKnownPowerOf? cid, g.lastKnownToughnessOf? cid with
                  | some op, some ot => some (op, ot)
                  | _, _ => some (g.power other, g.toughness other)
              | none =>
                match g.lastKnownPowerOf? cid, g.lastKnownToughnessOf? cid with
                | some op, some ot => some (op, ot)
                | _, _ => none
        match causePT?, srcPT? with
        | some (op, ot), some (hp, ht) => op > hp || ot > ht
        | _, _ => false
    | _ => true
  let sharedInterveningOk :=
    match ab.shared with
    | .beginCombatIfDrawnTwoPump => g.loggedDraws controller ≥ 2
    | .thisAttack .equippedDrain =>
      g.attachedEquipmentAtResolution sourceId lastKnownPower > 0
    | .thisAttack .ifArtifactEnteredDraw =>
      g.loggedArtifactEntered controller
    | .resource .drawIfAnotherHeroDamage =>
      (g.permanentsOf controller).any (fun o => g.hasSubtype o .hero && some o.id != sourceId)
    | .step .drawToTen => (g.player controller).hand.size < 10
    | .protectionEverything => src.any (fun s => g.wasCast s.id)
    | .copySelfNonlegendary =>
      match sourceId.bind g.findObject? with
      | some o => !o.printed.isToken
      | none => (sourceId.bind g.lastKnownBefore?).any (!·.token)
    | .drawIfAttackedOrEnteredSubtype st =>
      g.loggedAttackedWithSubtype controller st || g.loggedSubtypeEntered controller st
    | _ =>
      match ab.effect.resolution with
      | .frc .gingerbrute => (g.player controller).isMonarch
      | .frc .obAngel => g.loggedLifeGained controller > 0
      | _ => true
  g.interveningStillHolds controller ab &&
    hulklingOk &&
    sharedInterveningOk &&
    g.fraInterveningHolds controller ab src cause &&
    g.fraConditionHolds controller ab.opts.fraCondition src fraCauseStatus

end Game
end Mtg.Engine
