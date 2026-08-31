import Mtg.Engine.Game.CastExtras

/-!
# Saga chapter resolution (CR 714.3)

`applyChapterEffect` for chapter abilities and the intervening-if
recheck used when their triggers resolve (CR 603.4).
-/

namespace Mtg.Engine
namespace Game

/-- Resolve a printed Saga chapter (CR 714.3 / 608). -/
def applyChapterEffect (g : Game) (controller : PlayerId) (e : Effect)
    (sourceId : Option ObjectId) (targets : Array Target) : Game :=
  match e.asChapter? with
  | none => g.applyEffect controller e targets
  | some ch =>
  match ch with
  | .dealDamageToOppCreature n =>
    g.withLegalKindPermanent controller .oppCreature targets (fun g o =>
      g.dealDamageToPermanent o n) sourceId (some "The target is no longer legal")
  | .destroyOppArtifact =>
    g.withLegalKindPermanent controller .oppArtifact targets (fun g o =>
      g.destroyPermanent o) sourceId (some "The target is no longer legal")
  | .addMana mana =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add mana })
      |>.logMsg s!"{(g.player controller).name} adds {mana}"
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
  | .gainLandfallCreateElf =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.isOnBattlefield then g
      else
        let landfall : TriggeredAbility :=
          .onLandYouControlEntersCreateTokens TokenKind.elf 1
        let g := g.mapObjectStatus src (fun s =>
          { s with grantedTriggeredAbilities :=
            s.grantedTriggeredAbilities.push landfall })
        g.logMsg s!"{src.name} gains landfall"
    | none => g
  | .elvesGetVigilance p =>
    g.forEachControlledCreature controller fun g o =>
      if g.hasSubtype o "Elf" then
        let g := g.pumpPermanent o p 0
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.vigilance)
          |>.logMsg s!"{o.name} gets {signedStat p}/+0 and gains vigilance until end of turn"
      else g
  | .opponentDiscardsNonland =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.discardNonlandFrom controller pid)
      sourceId (some "The target is no longer legal")
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .opponentLosesYouGain n =>
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.loseLife pid n |>.gainLife controller n)
      sourceId (some "The target is no longer legal")
  | .grantHexproofWhileRemains =>
    match sourceId with
    | none => g
    | some sid =>
      g.withLegalKindPermanent controller .creatureYouControl targets (fun g o =>
        let g := g.mapObjectStatus o (fun s =>
          { s with hexproofGrantedBy := s.hexproofGrantedBy.push sid })
        g.logMsg s!"{o.name} gains hexproof for as long as the Saga remains")
        sourceId (some "The target is no longer legal")
  | .preventDamageWhileRemains =>
    match sourceId with
    | none => g
    | some sid =>
      g.withLegalKindPermanent controller .creature targets (fun g o =>
        let g := g.mapObjectStatus o (fun s =>
          { s with preventDamageGrantedBy := s.preventDamageGrantedBy.push sid })
        g.logMsg s!"damage that would be dealt by {o.name} is prevented while the Saga remains")
        sourceId none
  | .draw n =>
    g.draw controller n
  | .searchBasicPlainsExileGainLife max life =>
    g.resolveSearchBasicPlainsExile controller sourceId max life
  | .returnLinkedExileToHand =>
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
          let src := g.object! src.id
          let g := g.setObject { src with
            linkedExile := src.linkedExile.filter (· != eid) }
          g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"
  | .grantAttackPumpPerPlainsThisTurn =>
    g.modifyPlayer controller (fun pl =>
      { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn + 1 })
      |>.logMsg
        s!"Whenever {(g.player controller).name} attacks this turn, a creature they control gets +1/+1 for each Plains they control"
  | .blinkUntilEndStep =>
    g.withLegalKindPermanent controller .creatureOrLandYouControl targets
      (fun g o => g.exileUntilNextEndStep o) sourceId none
  | .treasureThenDragonIfFour =>
    let g := g.createTreasureTokens controller 1
    match sourceId.bind g.findObject? with
    | none => g
    | some src =>
      if !src.isOnBattlefield then g
      else if g.countSubtype controller "Treasure" < 4 then g
      else
        let name := src.name
        let g := g.sacrificeToGraveyard src s!"{name} is sacrificed"
        let (g, tok) := g.createToken controller dragonToken
        g.logMsg s!"{tok.name} enters the battlefield" |>.afterPermanentEnters (g.object! tok.id)
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
            g.logMsg s!"{name} returns to the battlefield"
              |>.afterPermanentEnters (g.object! newId)
        | _ => g.logMsg "The target is no longer legal")
      sourceId (some "The target is no longer legal")
  | .plusOneUpToOne =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      g.addPlusOnePlusOneTo o 1) sourceId none
  | .gainControlOfUpToTwoCreaturesTotalMvAtMost _n =>
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
                  g.setObject { o with
                    controller := some controller
                    controlChanged := true
                    controlUntilSourceLeaves := some src.id }
              g.logMsg s!"{(g.player controller).name} gains control of {o.name}"
            else g
          | none => g
        | _ => g) g)
      "The Super Hero Civil War has left the battlefield. You won't gain control."
  | .dealDamageToEachNonSubtypeAndOpponents n subtype =>
    let g :=
      g.dealDamageToEachCreatureMatching n (fun o => !g.hasSubtype o subtype)
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .dealXDamageToTargetOpponentGreatestArtifactMv =>
    let x := g.greatestManaValueAmong controller (·.printed.isArtifact)
    g.withLegalKindPlayer controller .opponent targets
      (fun g pid => g.dealDamageToPlayer pid x)
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
    | some n => (g.player controller).lifeGainedThisTurn ≥ n
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
