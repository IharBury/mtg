import Mtg.Engine.Game.CastExtras

/-!
# Saga chapter helpers (CR 714.3)

Helpers for chapter abilities and the intervening-if recheck used when
triggered abilities resolve (CR 603.4).
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
      let g := g.mapObjectStatus src (fun s =>
        { s with grantedTriggeredAbilities :=
          s.grantedTriggeredAbilities.push landfall })
      g.logMsg s!"{src.name} gains landfall"
  | none => g

/-- Elves the controller controls get +P/+0 and vigilance until end of turn. -/
def elvesGetVigilance (g : Game) (controller : PlayerId) (power : Int) : Game :=
  g.forEachControlledCreature controller fun g o =>
    if g.hasSubtype o "Elf" then
      let g := g.pumpPermanent o power 0
      g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.vigilance)
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
      let g := g.mapObjectStatus o (fun s =>
        { s with hexproofGrantedBy := s.hexproofGrantedBy.push sid })
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
      let g := g.mapObjectStatus o (fun s =>
        { s with preventDamageGrantedBy := s.preventDamageGrantedBy.push sid })
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
        let src := g.object! src.id
        let g := g.setObject { src with exileLinks :=
          { src.exileLinks with linkedExile := src.linkedExile.filter (· != eid) } }
        g.logMsg s!"{name} is put into {(g.player owner).name}'s hand"

/-- Whenever the controller attacks this turn, a creature they control
gets +1/+1 for each Plains they control. -/
def attackPumpPerPlains (g : Game) (controller : PlayerId) : Game :=
  g.modifyPlayer controller (fun pl =>
    { pl with attackPumpPerPlainsThisTurn := pl.attackPumpPerPlainsThisTurn + 1 })
    |>.logMsg
      s!"Whenever {(g.player controller).name} attacks this turn, a creature they control gets +1/+1 for each Plains they control"

/-- Create a Treasure. Then if the controller has four or more, sacrifice
the source and create a 6/6 red Dragon with flying. -/
def treasureThenDragon (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
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
                g.setObject { o with
                  controller := some controller
                  controlChanged := true
                  controlUntilSourceLeaves := some src.id }
            g.logMsg s!"{(g.player controller).name} gains control of {o.name}"
          else g
        | none => g
      | _ => g) g)
    "The Super Hero Civil War has left the battlefield. You won't gain control."

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
