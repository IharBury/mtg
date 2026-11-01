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

/-- A card the source exiled returns to its owner's hand. -/
def returnLinkedExileToHand (g : Game) (sourceId : Option ObjectId) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The Saga is no longer in play"
  | some src =>
    match src.linkedExile[0]? with
    | none => g.logMsg "No card is exiled with this Saga"
    | some eid =>
      match g.findObject? eid with
      | none => g.logMsg "The exiled card is no longer there"
      | some card =>
        let owner := card.owner
        let name := card.name
        let (g, _) := g.move eid (.hand owner) none
        let srcNow := g.object! src.id
        let g := g.changeObject src.id (.linkedExile (srcNow.linkedExile.filter (· != eid)))
        g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"

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
    g.chainPendingReplacement (.finishPostStep 32 controller)
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
        g.chainPendingReplacement (.finishPostStep 31 controller)
      else
        g.treasureThenDragonCreateDragon controller

/-- Create a Treasure. Then if the controller has four or more, sacrifice
the source and create a 6/6 red Dragon with flying. -/
def treasureThenDragon (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  let g := g.createTreasureTokens controller 1
  if let .chooseReplacement .. := g.pending then
    g.chainPendingReplacement (.finishPostStep 30 controller 0 sourceId)
  else
    g.treasureThenDragonAfterCreate controller sourceId

/-- Gain control of the announced creatures while the source remains. -/
def gainControlWhileSource (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (targets : Array Target) : Game :=
  g.withSourceStillOnBattlefield sourceId (fun g src =>
    targets.foldl (fun (g : Game) (t : Target) =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield then
            let g :=
              if (g.player controller).lost then
                g.logMsg s!"{o.name} does not change control (CR 800.4b)"
              else
                g.createEffect (.controlWhileSource o.id controller src.id)
            g.logMsg s!"{(g.player controller).name} gains control of {o.name}"
          else g
        | none => g
      | _ => g) g)
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
            let g := g.logMsg s!"{name} returns to the battlefield"
            if let .chooseReplacement .. := g.pending then
              g.chainPendingReplacement (.finishPostStep 20 controller 0 none (some oid) (shuffle := false))
            else
              g.afterPermanentEnters (g.object! newId)
        | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .plusOneUpToOne =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.addPlusOnePlusOneTo o 1) sourceId none
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost _n =>
    g.gainControlWhileSource controller sourceId targets
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
      g.chainPendingReplacement (.finishPostStep 33 controller n sourceId (cause := cause?))
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

end Game
end Mtg.Engine
