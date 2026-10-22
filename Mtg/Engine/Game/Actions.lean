import Mtg.Engine.Game.FraChoices

/-!
# Applying player actions

`Game.apply` dispatching an `Action`, hand and actor queries, and
resolution helpers that return owned creatures or destroy the rest.
-/

namespace Mtg.Engine
namespace Game

private def applyCastAction (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game :=
  match g.pending with
  | .mayCastFromLooked .. => g.chooseCastFromLooked p (some id)
  | .mayPutLandFromHand _ => g.putLandFromHandTapped p id
  | .mayPutArtifactFromHand .. => do
    let g ← g.choosePutArtifactFromHand p id
    return g.resumeSequenceThenPriority
  | .mayCastExiledElseDamage .. => g.castExiledAsAbilityResolves p id
  | .fraChoice _ (.castCopiesFree ..) => g.castFreeCopy p id
  | .fraChoice _ (.mayCastFromGraveyard _) => g.answerFraChoice p (.objects #[id])
  | .fraChoice _ (.mayCastCards _ _ _) => g.answerFraChoice p (.objects #[id])
  | _ => g.castSpell p id

private def applyActionPart1 (g : Game) (p : PlayerId) (a : @& Action) : Except String Game :=
  match a with
  | .keep => g.keepOpeningHand p
  | .takeMulligan => g.takeMulligan p
  | .arrayObjectAction ids _ true supplyRandom false =>
    if supplyRandom then g.supplyOrder ids else g.putCardsOnBottom p ids
  | .arrayObjectAction top rest _ surveil true =>
    if surveil then g.finishSurveil p top rest else g.finishScry p top rest
  | .decline =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .decline
    | _ => g.decline p
  | .accept =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .accept
    | .mayResolve _ => g.acceptMay p
    | _ => throw "Nothing to accept now"
  | .haveVillainConnive => g.haveVillainConnive p
  | .payGeneric =>
    match g.pending with
    | .fraChoice _ (.mayPayThen ..) => g.answerFraChoice p .accept
    | _ => g.payGeneric p
  | .chooseLibrarySide top =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p (if top then .accept else .decline)
    | _ => g.chooseLibrarySide p top
  | .arrayObjectAction ids _ false stackTriggers false =>
    if stackTriggers then g.stackTriggers p ids
    else
      match g.pending with
      | .fraChoice .. => g.answerFraChoice p (.objects ids)
      | .activateManaAbilities _ => g.convoke p ids
      | _ => g.choosePermanents p ids
  | .announceOptionalCost pay teamwork =>
    if teamwork then g.announceTeamwork p pay else g.announceKicker p pay
  | .optionalDesignation to _ false => g.announceGift p to
  | .optionalDesignation _ id true => g.announceRingBearer p id
  | .booleanOrConcede _ _ _ true => return g.concede p
  | .chooseName name => g.answerFraChoice p (.name name)
  | _ => throw "Unrecognized action"

def applyAction (g : Game) (p : PlayerId) (a : @& Action) : Except String Game :=
  match a with
  | .pass => g.pass p
  | .playLandOrKeepLegend id keepLegend =>
    if keepLegend then g.keepLegend p id else g.playLand p id
  | .tapForMana id m => g.tapForMana p id m
  | .activateManaAbility id idx mana costIds => g.activateManaAbility p id idx mana costIds
  | .cast id => applyCastAction g p id
  | .castAdventure id => g.castSpell p id true
  | .activateOrSneak id _ attackerId true => g.castSpell p id (sneakAttacker := some attackerId)
  | .chooseNat idx true _ =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p (.mode idx)
    | .chooseTriggerOr _ => g.chooseTriggerOr p idx
    | .chooseLibraryPlacement _ _ =>
      if g.spellOr.isEmpty then g.announceMode p idx else g.chooseSpellOr p idx
    | _ => g.announceMode p idx
  | .chooseNumber n supplyRandom =>
    if supplyRandom then g.supplyIndex n else g.announceX p n
  | .target t => g.announceTarget p t
  | .targets ts =>
    match g.pending with
    | .chooseProliferate .. => g.finishProliferate p ts
    | _ => g.announceTargets p ts
  | .divideDamage as => g.announceDividedDamage p as
  | .activateOrSneak id idx _ false => g.activateAbility p id idx
  | .pay => g.pay p
  | .objectAction id _ true discard => do
    let g ← if discard then g.discardForDraw p id else g.sacrificeForActivation p id
    return if g.mayThenResume then g.acceptMayThen else g
  | .chooseAdditionalCost payGeneric => g.announceAdditionalCost p payGeneric
  | .declareAttackers ids defender each pws => g.declareAttackers p ids defender each pws
  | .declareBlockers as => g.declareBlockers p as
  | .assignCombatDamage asgns => g.announceCombatDamage p asgns
  | a => applyActionPart1 g p a


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
    | .turnCombat (.playerBooleanStep p _ _) | .putOnBottom p _
    | .chooseLegend p _ _ | .cast p _ | .resolve p _ | .fraChoice p _ => who p
    | .resolveRandom req =>
      match req with
      | .shuffleLibrary p => some p
      | .orderInto _ dest =>
        match dest with
        | .library p | .hand p | .graveyard p => some p
        | _ =>
          if g.players.isEmpty then none else some g.startingPlayer
      | .chooseObject _ | .chooseIndex _ | _ =>
        if g.players.isEmpty then none else some g.startingPlayer
    | .none =>
      if g.playersReceivePriority then some g.priority else none
    | _ => none

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
