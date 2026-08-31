import Mtg.Engine.Game.Decisions

/-!
# Applying player actions

`Game.apply` dispatching an `Action`, hand and actor queries, and
resolution helpers that return owned creatures or destroy the rest.
-/

namespace Mtg.Engine
namespace Game

def apply (g : Game) (p : PlayerId) : Action → Except String Game
  | .pass => g.pass p
  | .playLand id => g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .cast id =>
    match g.pending with
    | .mayCastFromLooked .. => g.chooseCastFromLooked p (some id)
    | .mayPutLandFromHand _ => g.putLandFromHandTapped p id
    | .mayPutArtifactFromHand .. => g.choosePutArtifactFromHand p id
    | _ => g.castSpell p id
  | .castAdventure id => g.castSpell p id true
  | .chooseMode idx =>
    match g.pending with
    | .chooseFoodOrTreasure _ => g.chooseFoodOrTreasure p idx
    | .chooseTapOrUntap _ tid => g.chooseTapOrUntap p idx tid
    | _ => g.announceMode p idx
  | .chooseX n => g.announceX p n
  | .target t => g.announceTarget p t
  | .targets ts => g.announceTargets p ts
  | .divideDamage as => g.announceDividedDamage p as
  | .activate id idx => g.activateAbility p id idx
  | .pay => g.pay p
  | .sacrifice id => g.sacrificeForActivation p id
  | .chooseAdditionalCost payGeneric => g.announceAdditionalCost p payGeneric
  | .declareAttackers ids defender each => g.declareAttackers p ids defender each
  | .declareBlockers as => g.declareBlockers p as
  | .assignCombatDamage asgns => g.announceCombatDamage p asgns
  | .keep => g.keepOpeningHand p
  | .keepLegend id => g.keepLegend p id
  | .stackTriggers ids => g.stackTriggers p ids
  | .takeMulligan => g.takeMulligan p
  | .putOnBottom ids => g.putCardsOnBottom p ids
  | .scry top bottom => g.finishScry p top bottom
  | .discard id => g.discardForDraw p id
  | .decline => g.decline p
  | .haveVillainConnive => g.haveVillainConnive p
  | .payGeneric => g.payGeneric p
  | .chooseTop => g.chooseLibrarySide p true
  | .chooseBottom => g.chooseLibrarySide p false
  | .choosePermanents ids => g.choosePermanents p ids
  | .announceKicker kick => g.announceKicker p kick
  | .announceGift to => g.announceGift p to
  | .announceTeamwork pay => g.announceTeamwork p pay
  | .chooseRingBearer id => g.announceRingBearer p id
  | .concede => return g.concede p
  | .supplyOrder ids => g.supplyOrder ids
  | .supplyIndex i => g.supplyIndex i

def handObjects (g : Game) (p : PlayerId) : Array GameObject :=
  (g.player p).hand.filterMap (fun id => g.findObject? id)

/-- Who must act next? -/
def actor (g : Game) : Option PlayerId :=
  if g.over then none
  else
    let who (p : PlayerId) : Option PlayerId :=
      if (g.player p).lost then some (g.nextLiving p) else some p
    match g.pending with
    | .declareAttackers => who g.activePlayer
    | .declareBlockers => who g.currentBlockersPlayer
    | .activateManaAbilities caster => who caster
    | .chooseMode p => who p
    | .chooseX p => who p
    | .chooseTargets p => who p
    | .sacrificePermanent p _ => who p
    | .sacrificeCreature p => who p
    | .declareMulligan p => who p
    | .putOnBottom p _ => who p
    | .scry p _ => who p
    | .mayDiscardDraw p _ => who p
    | .chooseAdditionalCost p => who p
    | .chooseSacrificeCreature p _ _ => who p
    | .chooseDiscardCard p _ => who p
    | .assignCombatDamage p _ => who p
    | .chooseLegend p _ _ => who p
    | .chooseTriggerToStack p => who p
    | .mayPayGeneric p _ => who p
    | .chooseLibraryPlacement p _ => who p
    | .mayAttachEquipment p _ => who p
    | .tapHumans p => who p
    | .payOrLetCounter p _ _ => who p
    | .payWard p _ _ => who p
    | .recruitDiscard p => who p
    | .chooseKicker p => who p
    | .chooseGift p => who p
    | .chooseTeamwork p => who p
    | .chooseTeamworkCreatures p _ => who p
    | .chooseRingBearer p => who p
    | .maySacrificeAnotherBolg p _ => who p
    | .mayCastFromLooked p _ _ => who p
    | .mayPutLandFromHand p => who p
    | .chooseFoodOrTreasure p => who p
    | .chooseTapOrUntap p _ => who p
    | .maySacArtifactOrDiscard p => who p
    | .mayPutArtifactFromHand p _ => who p
    | .mayHaveVillainConnive p _ _ => who p
    | .resolveRandom req =>
      match req with
      | .shuffleLibrary p => some p
      | .orderInto _ dest =>
        match dest with
        | .library p | .hand p | .graveyard p => some p
        | _ =>
          if g.players.isEmpty then none else some g.startingPlayer
      | .chooseObject _ | .chooseIndex _ =>
        if g.players.isEmpty then none else some g.startingPlayer
    | .none =>
      if g.playersReceivePriority then some g.priority else none

/-- Return owned creatures to hand and schedule that many Bird Soldiers
for the next upkeep (The Eagles Are Coming!). Tokens returned this way
are counted; they later cease in hand (CR 704.5d). -/
def returnOwnedCreaturesScheduleBirds (g : Game) (p : PlayerId)
    (ids : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    let mut n : Nat := 0
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        if o.isOnBattlefield && o.isCreature && o.owner == p then
          let name := o.name
          let owner := o.owner
          let (g', _) := g.move o.id (.hand owner) none
          g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
          n := n + 1
    if n > 0 then
      g := g.modifyPlayer p (fun pl =>
        { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n })
      g := g.logMsg
        s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
    return g

/-- Choose up to two creatures (they are not targets) and destroy the rest
(Mount Doom). Shroud and hexproof do not stop the choice. -/
def chooseCreaturesDestroyRest (g : Game) (keep : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if o.isCreature && !keep.contains o.id then
        g := g.destroyPermanent o
    return g.logMsg "Chosen creatures are kept; the rest are destroyed"

/-- Two different players each draw a card (Gleaming Splendor). The same
player cannot be chosen twice. -/
def twoPlayersEachDraw (g : Game) (a b : PlayerId) : Except String Game := do
  if a == b then
    throw "Two target players must be different"
  let g := g.draw a 1
  return g.draw b 1

end Game
end Mtg.Engine
