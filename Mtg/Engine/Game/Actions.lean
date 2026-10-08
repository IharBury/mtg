import Mtg.Engine.Game.FraChoices

/-!
# Applying player actions

`Game.apply` dispatching an `Action`, hand and actor queries, and
resolution helpers that return owned creatures or destroy the rest.
-/

namespace Mtg.Engine
namespace Game

def applyAction (g : Game) (p : PlayerId) : Action → Except String Game
  | .pass => g.pass p
  | .playLand id => g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .activateManaAbility id idx mana costIds => g.activateManaAbility p id idx mana costIds
  | .cast id =>
    match g.pending with
    | .mayCastFromLooked .. => g.chooseCastFromLooked p (some id)
    | .mayPutLandFromHand _ => g.putLandFromHandTapped p id
    | .mayPutArtifactFromHand .. => g.choosePutArtifactFromHand p id
    | .mayCastExiledElseDamage .. => g.castExiledAsAbilityResolves p id
    | .fraChoice _ (.castCopiesFree ..) => g.castFreeCopy p id
    | .fraChoice _ (.mayCastFromGraveyard _) => g.answerFraChoice p (.objects #[id])
    | _ => g.castSpell p id
  | .castAdventure id => g.castSpell p id true
  | .castWithSneak id attackerId => g.castSpell p id (sneakAttacker := some attackerId)
  | .chooseMode idx =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p (.mode idx)
    | .chooseFoodOrTreasure _ => g.chooseFoodOrTreasure p idx
    | .chooseTapOrUntap _ tid => g.chooseTapOrUntap p idx tid
    | .chooseLibraryPlacement _ _ =>
      if g.spellOr.isEmpty then g.announceMode p idx else g.chooseSpellOr p idx
    | _ => g.announceMode p idx
  | .chooseX n => g.announceX p n
  | .target t => g.announceTarget p t
  | .targets ts =>
    match g.pending with
    | .chooseProliferate .. => g.finishProliferate p ts
    | _ => g.announceTargets p ts
  | .divideDamage as => g.announceDividedDamage p as
  | .activate id idx => g.activateAbility p id idx
  | .pay => g.pay p
  | .sacrifice id => g.sacrificeForActivation p id
  | .chooseAdditionalCost payGeneric => g.announceAdditionalCost p payGeneric
  | .declareAttackers ids defender each pws => g.declareAttackers p ids defender each pws
  | .declareBlockers as => g.declareBlockers p as
  | .assignCombatDamage asgns => g.announceCombatDamage p asgns
  | .keep => g.keepOpeningHand p
  | .keepLegend id => g.keepLegend p id
  | .stackTriggers ids => g.stackTriggers p ids
  | .takeMulligan => g.takeMulligan p
  | .putOnBottom ids => g.putCardsOnBottom p ids
  | .scry top bottom => g.finishScry p top bottom
  | .surveil top graveyard => g.finishSurveil p top graveyard
  | .discard id => g.discardForDraw p id
  | .decline =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .decline
    | _ => g.decline p
  | .accept =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .accept
    | _ => throw "Nothing to accept now"
  | .haveVillainConnive => g.haveVillainConnive p
  | .payGeneric =>
    match g.pending with
    | .fraChoice _ (.mayPayThen ..) => g.answerFraChoice p .accept
    | _ => g.payGeneric p
  | .chooseTop =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .accept
    | _ => g.chooseLibrarySide p true
  | .chooseBottom =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .decline
    | _ => g.chooseLibrarySide p false
  | .choosePermanents ids =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p (.objects ids)
    | .activateManaAbilities _ => g.convoke p ids
    | _ => g.choosePermanents p ids
  | .announceKicker kick => g.announceKicker p kick
  | .announceGift to => g.announceGift p to
  | .announceTeamwork pay => g.announceTeamwork p pay
  | .chooseRingBearer id => g.announceRingBearer p id
  | .concede => return g.concede p
  | .supplyOrder ids => g.supplyOrder ids
  | .supplyIndex i => g.supplyIndex i
  | .chooseName name => g.answerFraChoice p (.name name)


/-- Apply an action, then process entering for tokens it created (CR 603.6a)
and put the resulting triggered abilities on the stack. -/
def apply (g : Game) (p : PlayerId) (a : Action) : Except String Game := do
  let g ← g.applyAction p a
  let g :=
    if g.pendingTokenEnters.isEmpty then g
    else
      let g := g.flushTokenEnters
      if g.pending == .none && !g.waitingTriggers.isEmpty && !g.over then
        g.receivePriority g.priority
      else g
  return g.flushUnlessPays

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
    | .discardForAdditionalCost p => who p
    | .sacrificeCreature p => who p
    | .declareMulligan p => who p
    | .putOnBottom p _ => who p
    | .scry p _ => who p
    | .surveil p _ => who p
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
    | .maySacArtifactOrDiscard p _ => who p
    | .mayPutArtifactFromHand p _ => who p
    | .mayHaveVillainConnive p _ _ => who p
    | .chooseProliferate p _ => who p
    | .fraChoice p _ => who p
    | .mayCastExiledElseDamage p _ _ => who p
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
