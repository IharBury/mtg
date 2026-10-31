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
    | .mayPutArtifactFromHand .. => do
      let g ← g.choosePutArtifactFromHand p id
      return g.resumeSequenceThenPriority
    | .mayCastExiledElseDamage .. => g.castExiledAsAbilityResolves p id
    | .fraChoice _ (.castCopiesFree ..) => g.castFreeCopy p id
    | .fraChoice _ (.mayCastFromGraveyard _) => g.answerFraChoice p (.objects #[id])
    | .fraChoice _ (.mayCastCards _ _ _) => g.answerFraChoice p (.objects #[id])
    | _ => g.castSpell p id
  | .castAdventure id => g.castSpell p id true
  | .castWithSneak id attackerId => g.castSpell p id (sneakAttacker := some attackerId)
  | .chooseMode idx =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p (.mode idx)
    | .chooseReplacement _ choices =>
      if choices.any (fun c => match c.kind with | .asEntersChooseOdd _ => true | _ => false) then
        if idx > 1 then throw "Choose even (0) or odd (1)"
        else
          let wantOdd := idx == 1
          match choices.find? (fun c => c.kind == .asEntersChooseOdd wantOdd) with
          | some id => g.chooseReplacement p id
          | none => throw "No such choice"
      else
        match choices[idx]? with
        | some id => g.chooseReplacement p id
        | none => throw "No such choice"
    | .chooseTriggerOr _ => g.chooseTriggerOr p idx
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
  | .sacrifice id => do
    let g ← g.sacrificeForActivation p id
    return if g.mayThenResume then g.acceptMayThen else g
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
  | .discard id => do
    let g ← g.discardForDraw p id
    return if g.mayThenResume then g.acceptMayThen else g
  | .decline =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .decline
    | .chooseReplacement _ choices =>
      match choices.find? (fun c =>
          match c.kind with
          | .entersTappedDeclinePayLife | .entersTappedDeclineBehold | .declineEntersAsCopy => true
          | _ => false) with
      | some id => g.chooseReplacement p id
      | none => g.decline p
    | _ => g.decline p
  | .accept =>
    match g.pending with
    | .fraChoice .. => g.answerFraChoice p .accept
    | .chooseReplacement _ choices =>
      match choices.find? (fun c =>
          match c.kind with
          | .entersUntappedPayLife _ | .entersUntappedBehold _ _ | .entersAsCopyCreatureUntilEot _ => true
          | _ => false) with
      | some id => g.chooseReplacement p id
      | none => throw "Nothing to accept now"
    | .mayResolve _ => g.acceptMay p
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
    | .chooseReplacement _ choices =>
      match ids with
      | #[tid] =>
        match choices.find? (fun c =>
            match c.kind with
            | .entersAsCopyCreatureUntilEot cid => cid == tid
            | .entersUntappedBehold bid _ => bid == tid
            | _ => false) with
        | some id => g.chooseReplacement p id
        | none => g.choosePermanents p ids
      | _ => g.choosePermanents p ids
    | .activateManaAbilities _ => g.convoke p ids
    | _ => g.choosePermanents p ids
  | .announceKicker kick => g.announceKicker p kick
  | .announceGift to => g.announceGift p to
  | .announceTeamwork pay => g.announceTeamwork p pay
  | .chooseRingBearer id => g.announceRingBearer p id
  | .concede => return g.concede p
  | .supplyOrder ids => g.supplyOrder ids
  | .supplyIndex i => g.supplyIndex i
  | .chooseName name =>
    match g.pending with
    | .chooseReplacement _ choices =>
      match choices.find? (fun c =>
          c.kind == .asEntersChooseCreatureTypePrompt ||
            c.kind == .asEntersChooseCardNamePrompt) with
      | some promptId =>
        match promptId.kind with
        | .asEntersChooseCreatureTypePrompt => do
          let some sub := (CardSubtype.ofOracle? name).filter CardSubtype.isCreatureType
            | throw s!"{name} is not a creature type"
          g.chooseReplacement p { promptId with kind := .asEntersChooseCreatureType sub }
        | _ =>
          g.chooseReplacement p { promptId with kind := .asEntersChooseCardName name }
      | none => g.answerFraChoice p (.name name)
    | _ => g.answerFraChoice p (.name name)
  | .chooseReplacement id => g.chooseReplacement p id


/-- Apply an action, then put any resulting triggered abilities on the stack. -/
def apply (g : Game) (p : PlayerId) (a : Action) : Except String Game := do
  let beforeWaiting := g.waitingTriggers.size
  let g ← g.applyAction p a
  let g :=
    if g.pending == .none && g.pendingReplacement.isSome && !g.over then
      match g.pendingReplacement with
      | some cont =>
        let g := g.change (.pendingReplacement none)
        g.resumePendingReplacement cont
      | none => g
    else g
  let g :=
    if g.pending == .none && g.waitingTriggers.size > beforeWaiting && !g.over then
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
    | .scry p .. => who p
    | .surveil p .. => who p
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
    | .mayResolve p => who p
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
    | .chooseTriggerOr p => who p
    | .maySacArtifactOrDiscard p _ => who p
    | .mayPutArtifactFromHand p _ => who p
    | .mayHaveVillainConnive p _ _ => who p
    | .chooseProliferate p _ => who p
    | .fraChoice p _ => who p
    | .chooseReplacement p _ => who p
    | .mayCastExiledElseDamage p .. => who p
    | .resolveRandom req =>
      match req with
      | .shuffleLibrary p => some p
      | .orderInto _ dest _ =>
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
    let (g, cause) := g.allocDelayedCause (some p)
    let mut g := g
    let mut n : Nat := 0
    for id in ids do
      match g.findObject? id with
      | none => pure ()
      | some o =>
        if o.isOnBattlefield && g.isCreature o && o.owner == p then
          let name := g.name o
          let owner := o.owner
          let (g', _) := g.move o.id (.hand owner) none (cause := some cause)
          g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
          n := n + 1
    if n > 0 then
      g := g.registerDelayedTrigger { controller := p, kind := .eaglesBirds n, cause }
      g := g.logMsg
        s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
    return g

/-- Choose up to two creatures (they are not targets) and destroy the rest
(Mount Doom). Shroud and hexproof do not stop the choice. -/
def chooseCreaturesDestroyRest (g : Game) (keep : Array ObjectId) : Game :=
  Id.run do
    let mut g := g
    for o in g.battlefield do
      if g.isCreature o && !keep.contains o.id then
        g := g.destroyPermanent o
    return g.logMsg "Chosen creatures are kept; the rest are destroyed"

/-- Two different players each draw a card (Gleaming Splendor). The same
player cannot be chosen twice. -/
def twoPlayersEachDraw (g : Game) (a b : PlayerId) : Except String Game := do
  if a == b then
    throw "Two target players must be different"
  let (g, cause?) : Game × Option EventCause :=
    match g.currentResolvingContext? with
    | some (src, ctrl) =>
      let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some a)) src
      (g, some c)
    | none => (g, none)
  let g := g.draw a 1 (cause := cause?)
  return g.draw b 1 (cause := cause?)

end Game
end Mtg.Engine
