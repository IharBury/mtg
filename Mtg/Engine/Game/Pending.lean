import Mtg.Engine.Game.Stack

/-!
# Pending decisions

Decisions the game is waiting on: `RandomRequest` / `AfterRandom` for
randomness supplied from outside the engine (shuffles, coin flips),
`WardCost` / `WardObligation` (CR 702.21), and the `Pending` prompt a
player must answer before the game continues.
-/

namespace Mtg.Engine

/-- A random event the engine would otherwise resolve with `Rng`.
`--norandom` leaves it pending so a host (the demo) can supply the result. -/
inductive RandomRequest where
  | randomRequestKind (player : PlayerId := ⟨0⟩) (n : Nat := 0) (ids : Array ObjectId := #[])
      (dest : Zone := .battlefield) (alt : Bool := false) (isObjects : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace RandomRequest
@[match_pattern] abbrev playerOrIndexRandom (player : PlayerId := ⟨0⟩) (n : Nat := 0) (isIndex : Bool := false) : RandomRequest :=
  .randomRequestKind player n #[] .battlefield isIndex false
@[match_pattern] abbrev objectsRandom (ids : Array ObjectId) (dest : Zone := .battlefield) (chooseOne : Bool := false) : RandomRequest :=
  .randomRequestKind ⟨0⟩ 0 ids dest chooseOne true
@[match_pattern] abbrev shuffleLibrary (player : PlayerId) : RandomRequest :=
  .playerOrIndexRandom player 0 false
@[match_pattern] abbrev chooseIndex (n : Nat) : RandomRequest :=
  .playerOrIndexRandom ⟨0⟩ n true
@[match_pattern] abbrev orderInto (ids : Array ObjectId) (dest : Zone) : RandomRequest :=
  .objectsRandom ids dest false
@[match_pattern] abbrev chooseObject (ids : Array ObjectId) : RandomRequest :=
  .objectsRandom ids .battlefield true
end RandomRequest

/-- Work that still belongs to an effect after a `--norandom` result is
applied. The RNG path runs the same work immediately. -/
inductive AfterRandom where
  | afterRandomKind (p : PlayerId := ⟨0⟩) (n : Nat := 0) (id : ObjectId := ⟨0⟩)
      (subtype : String := "") (rest : Array PlayerId := #[]) (ids : Array ObjectId := #[])
      (alt1 : Bool := false) (alt2 : Bool := false) (beholdOrPlusOne : Bool := false)
      (stepFlag : Bool := false) (arrayFlag : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace AfterRandom

@[match_pattern] abbrev none : AfterRandom :=
  .afterRandomKind ⟨0⟩ 0 ⟨0⟩ "" #[] #[] false false false false false
@[match_pattern] abbrev stepOrTargetAfter (p : PlayerId := ⟨0⟩) (n : Nat := 0) (id : ObjectId := ⟨0⟩)
    (subtype : String := "") (alt : Bool := false)
    (opening : Bool := false) (beholdOrPlusOne : Bool := false) : AfterRandom :=
  .afterRandomKind p n id subtype #[] #[] alt opening beholdOrPlusOne true false
@[match_pattern] abbrev arrayAfter (p : PlayerId) (rest : Array PlayerId := #[]) (ids : Array ObjectId := #[])
    (putOnTop : Bool := false) (isCards : Bool := false) : AfterRandom :=
  .afterRandomKind p 0 ⟨0⟩ "" rest ids putOnTop isCards false false true
@[match_pattern] abbrev playerAmount (p : PlayerId) (n : Nat) (gainLife : Bool := false) : AfterRandom :=
  .stepOrTargetAfter p n ⟨0⟩ "" gainLife false false
@[match_pattern] abbrev openingStep (idx : Nat) (setStarting : Bool := false) : AfterRandom :=
  .stepOrTargetAfter ⟨0⟩ idx ⟨0⟩ "" setStarting true false
@[match_pattern] abbrev beholdUntap (p : PlayerId) (landId : ObjectId) (subtype : String) : AfterRandom :=
  .stepOrTargetAfter p 0 landId subtype false false true
@[match_pattern] abbrev plusOne (id : ObjectId) : AfterRandom :=
  .stepOrTargetAfter ⟨0⟩ 0 id "" true false true
@[match_pattern] abbrev mulliganQueue (drawn : PlayerId) (rest : Array PlayerId) : AfterRandom :=
  .arrayAfter drawn rest #[] false false
@[match_pattern] abbrev playerCards (p : PlayerId) (ids : Array ObjectId) (putOnTop : Bool := false) : AfterRandom :=
  .arrayAfter p #[] ids putOnTop true
@[match_pattern] abbrev draw (p : PlayerId) (n : Nat) : AfterRandom := .playerAmount p n false
@[match_pattern] abbrev gainLife (p : PlayerId) (n : Nat) : AfterRandom := .playerAmount p n true
@[match_pattern] abbrev openingShuffles (next : Nat) : AfterRandom := .openingStep next false
@[match_pattern] abbrev setStartingPlayer (i : Nat) : AfterRandom := .openingStep i true
@[match_pattern] abbrev revealRandomCreatureThenBottom (controller : PlayerId) (revealed : Array ObjectId) : AfterRandom :=
  .playerCards controller revealed false
@[match_pattern] abbrev putOnTop (p : PlayerId) (ids : Array ObjectId) : AfterRandom := .playerCards p ids true

end AfterRandom

/-- Payment a player may make to stop ward from countering their spell
(CR 702.21). -/
inductive WardCost where
  | wardCostKind (n : Nat := 0) (paid : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false)
      (nonMana : Bool := false) (sacPerms : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace WardCost

@[match_pattern] abbrev manaOrDiscard (n : Nat) (orDiscard : Bool := false) : WardCost :=
  .wardCostKind n 0 orDiscard false false false
@[match_pattern] abbrev nonManaWard (sacrificeLegendary : Bool := false) (fivePoison : Bool := false) : WardCost :=
  .wardCostKind 0 0 sacrificeLegendary fivePoison true false
@[match_pattern] abbrev sacrificePermanents (left paid : Nat) : WardCost :=
  .wardCostKind left paid false false false true
@[match_pattern] abbrev genericMana (n : Nat) : WardCost := .manaOrDiscard n false
@[match_pattern] abbrev discardOrPay (n : Nat) : WardCost := .manaOrDiscard n true
@[match_pattern] abbrev discardEnchantmentInstantOrSorcery : WardCost := .nonManaWard false false
@[match_pattern] abbrev sacrificeLegendary : WardCost := .nonManaWard true false
@[match_pattern] abbrev fivePoison : WardCost := .nonManaWard false true
@[match_pattern] abbrev discardCard : WardCost := .nonManaWard true true

end WardCost

/-- A queued ward obligation waiting to be announced. -/
structure WardObligation where
  player : PlayerId
  spellId : ObjectId
  cost : WardCost
deriving DecidableEq, Repr, Inhabited, BEq

/-- Where cards found by a library search go (CR 701.19). -/
inductive SearchDest where
  | searchDestKind (sourceId : Option ObjectId := none) (subtype : String := "")
      (alt1 : Bool := false) (alt2 : Bool := false)
      (zoneDestFlag : Bool := false) (fromHandOrLibrary : Bool := false) (paramDest : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace SearchDest

@[match_pattern] abbrev simpleSearchDest (alt1 : Bool := false) (alt2 : Bool := false)
    (zoneDestFlag : Bool := false) (fromHandOrLibrary : Bool := false) : SearchDest :=
  .searchDestKind none "" alt1 alt2 zoneDestFlag fromHandOrLibrary false
@[match_pattern] abbrev paramSearchDest (sourceId : Option ObjectId := none) (subtype : String := "") (beholdUntap : Bool := false) : SearchDest :=
  .searchDestKind sourceId subtype beholdUntap false false false true
@[match_pattern] abbrev battlefield (tapped : Bool) : SearchDest :=
  .simpleSearchDest tapped false false false
@[match_pattern] abbrev zoneDest (graveyard : Bool := false) (topAfterShuffle : Bool := false) : SearchDest :=
  .simpleSearchDest graveyard topAfterShuffle true false
@[match_pattern] abbrev battlefieldFromHandOrLibrary : SearchDest :=
  .simpleSearchDest false false false true
@[match_pattern] abbrev exileLinked (sourceId : Option ObjectId) : SearchDest :=
  .paramSearchDest sourceId "" false
@[match_pattern] abbrev battlefieldTappedBeholdUntap (subtype : String) : SearchDest :=
  .paramSearchDest none subtype true
@[match_pattern] abbrev hand : SearchDest := .zoneDest false false
@[match_pattern] abbrev graveyard : SearchDest := .zoneDest true false
@[match_pattern] abbrev topAfterShuffle : SearchDest := .zoneDest false true
@[match_pattern] abbrev battlefieldTappedThenHand : SearchDest := .zoneDest true true

end SearchDest

/-- What to do with cards chosen from a looked-at, milled, or battlefield set. -/
inductive CardChoice where
  | cardChoiceKind (n : Nat := 0) (subtype : String := "") (attach : Option ObjectId := none)
      (alt : Bool := false) (creatures : Bool := false) (paramKind : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace CardChoice

@[match_pattern] abbrev booleanCardChoice (alt : Bool := false) (creatures : Bool := false) : CardChoice :=
  .cardChoiceKind 0 "" none alt creatures false
@[match_pattern] abbrev paramCardChoice (n : Nat) (subtype : String := "") (attach : Option ObjectId := none) (amass : Bool := false) : CardChoice :=
  .cardChoiceKind n subtype attach amass false true
@[match_pattern] abbrev toHand (mustOne : Bool) : CardChoice := .booleanCardChoice mustOne false
@[match_pattern] abbrev creaturesChoice (keepDestroyRest : Bool := false) : CardChoice := .booleanCardChoice keepDestroyRest true
@[match_pattern] abbrev landsTappedGainLife (life : Nat) : CardChoice := .paramCardChoice life "" none false
@[match_pattern] abbrev amassArmy (subtype : String) (n : Nat) (attach : Option ObjectId) : CardChoice :=
  .paramCardChoice n subtype attach true
@[match_pattern] abbrev creaturesToBattlefield : CardChoice := .creaturesChoice false
@[match_pattern] abbrev keepDestroyRest : CardChoice := .creaturesChoice true

end CardChoice

/-- Library, search, reveal, and draw choices made while an effect resolves (CR 401 / CR 701.19). -/
inductive LibraryChoice where
  | drawOrObjectLibraryChoice (ids : Array ObjectId := #[]) (id : ObjectId := ⟨0⟩)
      (player : PlayerId := ⟨0⟩) (n : Nat := 0) (discard : Nat := 0) (rest : Array PlayerId := #[])
      (sourceId : Option ObjectId := none)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (isArray : Bool := false) (isObjOrArray : Bool := false)
  | arrayOrSearchLibraryChoice (ids1 : Array ObjectId) (ids2 : Array ObjectId := #[]) (x : Nat := 0)
      (controller : PlayerId := ⟨0⟩) (dest : SearchDest := .hand)
      (after : Option Resolution := none) (kind : String := "")
      (purpose : CardChoice := .creaturesToBattlefield)
      (alt1 : Bool := false) (alt2 : Bool := false)
      (alt3 : Bool := false) (visionOrRiddles : Bool := false) (isSearchOrChoose : Bool := false)
deriving Repr, Inhabited, BEq

namespace LibraryChoice

@[match_pattern] abbrev drawOrExileLibraryChoice (n : Nat := 0) (discard : Nat := 0) (rest : Array PlayerId := #[])
    (sourceId : Option ObjectId := none) (alt1 : Bool := false) (alt2 : Bool := false)
    (exileOrReveal : Bool := false) : LibraryChoice :=
  .drawOrObjectLibraryChoice #[] ⟨0⟩ ⟨0⟩ n discard rest sourceId alt1 alt2 exileOrReveal false false
@[match_pattern] abbrev objectOrArrayLibraryChoice (ids : Array ObjectId := #[]) (id : ObjectId := ⟨0⟩)
    (player : PlayerId := ⟨0⟩) (damage : Nat := 0) (connive : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (isArray : Bool := false) : LibraryChoice :=
  .drawOrObjectLibraryChoice ids id player damage 0 #[] connive alt1 alt2 alt3 isArray true
@[match_pattern] abbrev multiArrayLibraryChoice (ids1 : Array ObjectId) (ids2 : Array ObjectId := #[]) (x : Nat := 0)
    (controller : PlayerId := ⟨0⟩) (alt1 : Bool := false) (alt2 : Bool := false)
    (alt3 : Bool := false) (visionOrRiddles : Bool := false) : LibraryChoice :=
  .arrayOrSearchLibraryChoice ids1 ids2 x controller .hand none "" .creaturesToBattlefield alt1 alt2 alt3 visionOrRiddles false
@[match_pattern] abbrev searchOrChooseLibrary (ids : Array ObjectId) (count : Nat) (dest : SearchDest := .hand)
    (after : Option Resolution := none) (kind : String := "")
    (purpose : CardChoice := .creaturesToBattlefield) (optional : Bool := false) (isChoose : Bool := false) : LibraryChoice :=
  .arrayOrSearchLibraryChoice ids #[] count ⟨0⟩ dest after kind purpose optional isChoose false false true
@[match_pattern] abbrev mayDrawOrWheel (n : Nat) (discard : Nat := 0) (rest : Array PlayerId := #[])
    (eachOppDraws : Bool := false) (wheel : Bool := false) : LibraryChoice :=
  .drawOrExileLibraryChoice n discard rest none eachOppDraws wheel false
@[match_pattern] abbrev mayExileTopOrReveal (sourceId : Option ObjectId := none) (extrapolate : Bool := false) : LibraryChoice :=
  .drawOrExileLibraryChoice 0 0 #[] sourceId extrapolate false true
@[match_pattern] abbrev objectLibraryChoice (id : ObjectId) (player : PlayerId := ⟨0⟩) (damage : Nat := 0)
    (connive : Option ObjectId := none) (trickster : Bool := false) (damageChoice : Bool := false) : LibraryChoice :=
  .objectOrArrayLibraryChoice #[] id player damage connive trickster damageChoice false false
@[match_pattern] abbrev cardArrayChoice (ids : Array ObjectId) (permanentId : ObjectId := ⟨0⟩)
    (revealer : PlayerId := ⟨0⟩) (alt : Bool := false) (arrange : Bool := false) (extrapolate : Bool := false) : LibraryChoice :=
  .objectOrArrayLibraryChoice ids permanentId revealer 0 none alt arrange extrapolate true
@[match_pattern] abbrev revealSelect (looked eligible : Array ObjectId) (flag : Bool := false)
    (putCreatures : Bool := false) (nickFury : Bool := false) : LibraryChoice :=
  .multiArrayLibraryChoice looked eligible 0 ⟨0⟩ flag putCreatures nickFury false
@[match_pattern] abbrev twoArrayOrVisionChoice (ids1 : Array ObjectId) (ids2 : Array ObjectId := #[])
    (x : Nat := 0) (controller : PlayerId := ⟨0⟩) (shuffle : Bool := false)
    (visionPick : Bool := false) (riddles : Bool := false) : LibraryChoice :=
  .multiArrayLibraryChoice ids1 ids2 x controller shuffle visionPick riddles true
@[match_pattern] abbrev searchChoice (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) (optional : Bool := false) : LibraryChoice :=
  .searchOrChooseLibrary eligible count dest after kind .creaturesToBattlefield optional false
@[match_pattern] abbrev chooseCards (ids : Array ObjectId) (max : Nat) (purpose : CardChoice) : LibraryChoice :=
  .searchOrChooseLibrary ids max .hand none "" purpose false true
@[match_pattern] abbrev mayWheel (n : Nat) (rest : Array PlayerId) : LibraryChoice := .mayDrawOrWheel n 0 rest false true
@[match_pattern] abbrev mayDrawChoice (draw : Nat) (discard : Nat := 0) (eachOppDraws : Bool := false) : LibraryChoice :=
  .mayDrawOrWheel draw discard #[] eachOppDraws false
@[match_pattern] abbrev mayDrawThenDiscard (draw discard : Nat) : LibraryChoice := .mayDrawOrWheel draw discard #[] false false
@[match_pattern] abbrev mayDrawThenEachOpponentDraws (n : Nat) : LibraryChoice := .mayDrawOrWheel n 0 #[] true false
@[match_pattern] abbrev topOrBottomDamage (id : ObjectId) (damage : Nat) : LibraryChoice :=
  .objectLibraryChoice id ⟨0⟩ damage none false true
@[match_pattern] abbrev palantirOrTrickster (player : PlayerId) (id : ObjectId) (connive : Option ObjectId := none) (trickster : Bool := false) : LibraryChoice :=
  .objectLibraryChoice id player 0 connive trickster false
@[match_pattern] abbrev palantirMayDraw (controller : PlayerId) (sourceId : ObjectId) : LibraryChoice :=
  .objectLibraryChoice sourceId controller 0 none false false
@[match_pattern] abbrev tricksterLibrary (caster : PlayerId) (creatureId : ObjectId) (connive : Option ObjectId) : LibraryChoice :=
  .objectLibraryChoice creatureId caster 0 connive true false
@[match_pattern] abbrev extrapolateReveal : LibraryChoice := .mayExileTopOrReveal none true
@[match_pattern] abbrev daredevilMayExile (sourceId : Option ObjectId) : LibraryChoice := .mayExileTopOrReveal sourceId false
@[match_pattern] abbrev extrapolatePick (revealer : PlayerId) (ids : Array ObjectId) : LibraryChoice :=
  .cardArrayChoice ids ⟨0⟩ revealer false false true
@[match_pattern] abbrev battlefieldCardListChoice (ids : Array ObjectId) (permanentId : ObjectId := ⟨0⟩) (transform : Bool := false) : LibraryChoice :=
  .cardArrayChoice ids permanentId ⟨0⟩ transform false false
@[match_pattern] abbrev mayBeginOnBattlefield (ids : Array ObjectId) : LibraryChoice :=
  .cardArrayChoice ids ⟨0⟩ ⟨0⟩ false false false
@[match_pattern] abbrev nickFuryMayTransform (permanentId : ObjectId) (rest : Array ObjectId) : LibraryChoice :=
  .cardArrayChoice rest permanentId ⟨0⟩ true false false
@[match_pattern] abbrev arrangeCards (ids : Array ObjectId) (splitPiles : Bool := false) : LibraryChoice :=
  .cardArrayChoice ids ⟨0⟩ ⟨0⟩ splitPiles true false
@[match_pattern] abbrev orderLibraryBottom (ids : Array ObjectId) : LibraryChoice := .cardArrayChoice ids ⟨0⟩ ⟨0⟩ false true false
@[match_pattern] abbrev riddlesSplit (looked : Array ObjectId) : LibraryChoice := .cardArrayChoice looked ⟨0⟩ ⟨0⟩ true true false
@[match_pattern] abbrev mayRevealToHand (looked eligible : Array ObjectId) (anyOrder : Bool) : LibraryChoice :=
  .revealSelect looked eligible anyOrder false false
@[match_pattern] abbrev revealPutCreatures (looked creatures : Array ObjectId) (anyNumber : Bool) : LibraryChoice :=
  .revealSelect looked creatures anyNumber true false
@[match_pattern] abbrev nickFuryPut (looked eligible : Array ObjectId) : LibraryChoice :=
  .revealSelect looked eligible false false true
@[match_pattern] abbrev searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) : LibraryChoice :=
  .searchChoice eligible count dest after kind false
@[match_pattern] abbrev maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) : LibraryChoice :=
  .searchChoice eligible count dest after kind true
@[match_pattern] abbrev visionQuestZones (libIds gyIds : Array ObjectId) (x : Nat) : LibraryChoice :=
  .twoArrayOrVisionChoice libIds gyIds x ⟨0⟩ false false false
@[match_pattern] abbrev visionQuestPick (ids : Array ObjectId) (x : Nat) (shuffle : Bool) : LibraryChoice :=
  .twoArrayOrVisionChoice ids #[] x ⟨0⟩ shuffle true false
@[match_pattern] abbrev riddlesChoosePile (controller : PlayerId) (faceUp faceDown : Array ObjectId) : LibraryChoice :=
  .twoArrayOrVisionChoice faceUp faceDown 0 controller false false true

end LibraryChoice

/-- Hand, discard, graveyard, and exile cast choices made while an effect resolves (CR 402 / CR 404 / CR 406). -/
inductive HandGraveyardChoice where
  | handOrCardListChoice (ids : Array ObjectId := #[]) (rest : Array PlayerId := #[])
      (victim : PlayerId := ⟨0⟩) (id : ObjectId := ⟨0⟩) (id2 : ObjectId := ⟨0⟩)
      (n : Nat := 0) (m : Nat := 0) (sourceId : Option ObjectId := none)
      (optVictim : Option PlayerId := none)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (singleOrPair : Bool := false) (discardAct : Bool := false) (isCardList : Bool := false)
  | mayDiscardThen (next : Resolution) (sourceId : Option ObjectId)
deriving Repr, Inhabited, BEq

namespace HandGraveyardChoice

@[match_pattern] abbrev handOrDiscardObjectChoice (victim : PlayerId := ⟨0⟩) (id : ObjectId := ⟨0⟩) (id2 : ObjectId := ⟨0⟩)
    (n : Nat := 0) (sourceId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (singleOrPair : Bool := false) (discardAct : Bool := false) : HandGraveyardChoice :=
  .handOrCardListChoice #[] #[] victim id id2 n 0 sourceId none alt1 alt2 alt3 singleOrPair discardAct false
@[match_pattern] abbrev cardListHandGyChoice (ids : Array ObjectId := #[]) (rest : Array PlayerId := #[])
    (n : Nat := 0) (m : Nat := 0) (cardId : ObjectId := ⟨0⟩)
    (victim : Option PlayerId := none) (controller : PlayerId := ⟨0⟩)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (castEligible : Bool := false) (hitOrMulti : Bool := false) : HandGraveyardChoice :=
  .handOrCardListChoice ids rest controller cardId ⟨0⟩ n m none victim alt1 alt2 alt3 castEligible hitOrMulti true
@[match_pattern] abbrev revealedHandChoice (victim : PlayerId) (permanentOnly : Bool := false)
    (exile : Bool := false) (sourceId : Option ObjectId := none) : HandGraveyardChoice :=
  .handOrDiscardObjectChoice victim ⟨0⟩ ⟨0⟩ 0 sourceId permanentOnly exile false false false
@[match_pattern] abbrev singleOrPairObjectChoice (id : ObjectId) (sourceId : ObjectId := ⟨0⟩)
    (castCopy : Bool := false) (moonstone : Bool := false) (zemo : Bool := false) : HandGraveyardChoice :=
  .handOrDiscardObjectChoice ⟨0⟩ id sourceId 0 none castCopy moonstone zemo true false
@[match_pattern] abbrev discardActionChoice (n : Nat := 0) (sourceId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (withSource : Bool := false) : HandGraveyardChoice :=
  .handOrDiscardObjectChoice ⟨0⟩ ⟨0⟩ ⟨0⟩ n sourceId alt1 alt2 withSource false true
@[match_pattern] abbrev countedCardsChoice (ids : Array ObjectId) (n : Nat) (m : Nat := 0)
    (castFromExileOrMilled : Bool := false) (copiesOrMilled : Bool := false) : HandGraveyardChoice :=
  .cardListHandGyChoice ids #[] n m ⟨0⟩ none ⟨0⟩ castFromExileOrMilled copiesOrMilled false false false
@[match_pattern] abbrev mayCastEligible (eligible : Array ObjectId) (withoutPaying : Bool := false)
    (exileInsteadOrFromHand : Bool := false) (zoneCards : Bool := false) : HandGraveyardChoice :=
  .cardListHandGyChoice eligible #[] 0 0 ⟨0⟩ none ⟨0⟩ withoutPaying exileInsteadOrFromHand zoneCards true false
@[match_pattern] abbrev hitOrMultiDiscardChoice (cardId : ObjectId := ⟨0⟩) (others : Array ObjectId := #[])
    (rest : Array PlayerId := #[]) (draws : Nat := 0) (victim : Option PlayerId := none)
    (controller : PlayerId := ⟨0⟩) (discardTwo : Bool := false) : HandGraveyardChoice :=
  .cardListHandGyChoice others rest draws 0 cardId victim controller discardTwo false false false true
@[match_pattern] abbrev discardFromRevealedHand (target : PlayerId) (permanentOnly : Bool) : HandGraveyardChoice :=
  .revealedHandChoice target permanentOnly false none
@[match_pattern] abbrev exileFromRevealedHand (victim : PlayerId) (sourceId : Option ObjectId) : HandGraveyardChoice :=
  .revealedHandChoice victim false true sourceId
@[match_pattern] abbrev singleCardChoice (id : ObjectId) (castCopy : Bool := false) (moonstone : Bool := false) : HandGraveyardChoice :=
  .singleOrPairObjectChoice id ⟨0⟩ castCopy moonstone false
@[match_pattern] abbrev mayExileOrCastCopy (id : ObjectId) (castCopy : Bool := false) : HandGraveyardChoice :=
  .singleOrPairObjectChoice id ⟨0⟩ castCopy false false
@[match_pattern] abbrev sphinxsApproach (spellId : ObjectId) : HandGraveyardChoice := .mayExileOrCastCopy spellId false
@[match_pattern] abbrev mayCastCopy (copyId : ObjectId) : HandGraveyardChoice := .mayExileOrCastCopy copyId true
@[match_pattern] abbrev moonstoneMayExile (cardId : ObjectId) : HandGraveyardChoice := .singleOrPairObjectChoice cardId ⟨0⟩ false true false
@[match_pattern] abbrev zemoBoastExile (abilityId sourceId : ObjectId) : HandGraveyardChoice :=
  .singleOrPairObjectChoice abilityId sourceId false false true
@[match_pattern] abbrev discardWithSource (id : Option ObjectId) (entireHand : Bool := false) : HandGraveyardChoice :=
  .discardActionChoice 0 id entireHand false true
@[match_pattern] abbrev discardThen (causeId : Option ObjectId) : HandGraveyardChoice := .discardWithSource causeId false
@[match_pattern] abbrev mayDiscardHandBalin (sourceId : Option ObjectId) : HandGraveyardChoice := .discardWithSource sourceId true
@[match_pattern] abbrev discardDrawOrStun (n : Nat := 0) (sourceId : Option ObjectId := none) (handDrawFixed : Bool := false) (stun : Bool := false) : HandGraveyardChoice :=
  .discardActionChoice n sourceId handDrawFixed stun false
@[match_pattern] abbrev discardThenDraw : HandGraveyardChoice := .discardActionChoice 0 none false false false
@[match_pattern] abbrev mayDiscardHandDrawFixed (n : Nat) : HandGraveyardChoice := .discardActionChoice n none true false false
@[match_pattern] abbrev discardThenStun (n : Nat) (sourceId : Option ObjectId) : HandGraveyardChoice :=
  .discardActionChoice n sourceId false true false
@[match_pattern] abbrev castCopiesFree (ids : Array ObjectId) (budget : Nat) (castsLeft : Nat) : HandGraveyardChoice :=
  .countedCardsChoice ids budget castsLeft false true
@[match_pattern] abbrev mayDiscardOrCastUpTo (ids : Array ObjectId) (n : Nat) (castFromExile : Bool := false) : HandGraveyardChoice :=
  .countedCardsChoice ids n 0 castFromExile false
@[match_pattern] abbrev mayDiscardThese (n : Nat) (ids : Array ObjectId) : HandGraveyardChoice := .countedCardsChoice ids n 0 false false
@[match_pattern] abbrev mayCastUpToFromExile (eligible : Array ObjectId) (left : Nat) : HandGraveyardChoice :=
  .countedCardsChoice eligible left 0 true false
@[match_pattern] abbrev mayTakeMilled (ids : Array ObjectId) (lifeAfter : Nat) : HandGraveyardChoice :=
  .countedCardsChoice ids lifeAfter 0 true true
@[match_pattern] abbrev mayCastZoneCards (eligible : Array ObjectId) (fromHand : Bool := false) : HandGraveyardChoice :=
  .mayCastEligible eligible false fromHand true
@[match_pattern] abbrev mayCastFromGraveyard (eligible : Array ObjectId) : HandGraveyardChoice := .mayCastZoneCards eligible false
@[match_pattern] abbrev mayCastInstantSorceryFromHand (eligible : Array ObjectId) : HandGraveyardChoice := .mayCastZoneCards eligible true
@[match_pattern] abbrev mayCastCards (eligible : Array ObjectId) (withoutPaying exileInstead : Bool) : HandGraveyardChoice :=
  .mayCastEligible eligible withoutPaying exileInstead false
@[match_pattern] abbrev discardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat) : HandGraveyardChoice :=
  .hitOrMultiDiscardChoice ⟨0⟩ #[] rest draws none controller true
@[match_pattern] abbrev mayCastHit (cardId : ObjectId) (others : Array ObjectId) (victim : Option PlayerId := none) : HandGraveyardChoice :=
  .hitOrMultiDiscardChoice cardId others #[] 0 victim ⟨0⟩ false
@[match_pattern] abbrev mayCastCascade (cardId : ObjectId) (others : Array ObjectId) : HandGraveyardChoice :=
  .mayCastHit cardId others none
@[match_pattern] abbrev mayCastGrima (cardId : ObjectId) (others : Array ObjectId) (victim : PlayerId) : HandGraveyardChoice :=
  .mayCastHit cardId others (some victim)

end HandGraveyardChoice

/-- Battlefield, sacrifice, counter, and permanent choices made while an effect resolves (CR 403 / CR 701.17). -/
inductive BattlefieldChoice where
  | mayOrTokenBattlefieldChoice (next : Resolution := .unrecognized) (sourceId : Option ObjectId := none)
      (kind : ObjectSelector := .source) (tokenKind : TokenKind := .treasure) (n : Nat := 0)
      (types : Array String := #[]) (alt : Bool := false) (isTokenOrType : Bool := false)
  | objectOrArrayBattlefieldChoice (rest : Array PlayerId := #[]) (ids : Array ObjectId := #[])
      (exiled : Array ObjectId := #[]) (chosen : Array ObjectId := #[])
      (controller : PlayerId := ⟨0⟩) (id : ObjectId := ⟨0⟩) (otherId : ObjectId := ⟨0⟩)
      (sourceId : Option ObjectId := none) (optExiled : Option ObjectId := none)
      (power : Nat := 0) (p : Int := 0) (t : Int := 0) (target : Target := .player ⟨0⟩)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (objChoice : Bool := false) (intChoice : Bool := false) (isPlayerOrObjects : Bool := false)
deriving Repr, Inhabited, BEq

namespace BattlefieldChoice

@[match_pattern] abbrev mayPermanentCostThen (next : Resolution) (sourceId : Option ObjectId) (kind : ObjectSelector := .source) (tapSource : Bool := false) : BattlefieldChoice :=
  .mayOrTokenBattlefieldChoice next sourceId kind .treasure 0 #[] tapSource false
@[match_pattern] abbrev tokenOrTypeBattlefieldChoice (kind : TokenKind := .treasure) (n : Nat := 0)
    (types : Array String := #[]) (isPalisade : Bool := false) : BattlefieldChoice :=
  .mayOrTokenBattlefieldChoice .unrecognized none .source kind n types isPalisade true
@[match_pattern] abbrev objectOrIntBattlefieldChoice (id : ObjectId := ⟨0⟩) (otherId : ObjectId := ⟨0⟩)
    (sourceId : Option ObjectId := none) (exiled : Option ObjectId := none)
    (power : Nat := 0) (p : Int := 0) (t : Int := 0) (target : Target := .player ⟨0⟩)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (objChoice : Bool := false) (intChoice : Bool := false) : BattlefieldChoice :=
  .objectOrArrayBattlefieldChoice #[] #[] #[] #[] ⟨0⟩ id otherId sourceId exiled power p t target alt1 alt2 alt3 objChoice intChoice false
@[match_pattern] abbrev playerOrObjectsBattlefieldChoice (rest : Array PlayerId := #[]) (ids : Array ObjectId := #[])
    (exiled : Array ObjectId := #[]) (chosen : Array ObjectId := #[])
    (controller : PlayerId := ⟨0⟩) (creatureId : ObjectId := ⟨0⟩) (n : Nat := 0)
    (sourceId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (fromObjects : Bool := false) : BattlefieldChoice :=
  .objectOrArrayBattlefieldChoice rest ids exiled chosen controller creatureId ⟨0⟩ sourceId none n 0 0 (.player ⟨0⟩) alt1 alt2 alt3 fromObjects false true
@[match_pattern] abbrev optionalSourceChoice (sourceId : Option ObjectId := none)
    (exiled : Option ObjectId := none) (oddEven : Bool := false) (widow : Bool := false) : BattlefieldChoice :=
  .objectOrIntBattlefieldChoice ⟨0⟩ ⟨0⟩ sourceId exiled 0 0 0 (.player ⟨0⟩) oddEven widow false false false
@[match_pattern] abbrev objectBattlefieldChoice (id : ObjectId) (otherId : ObjectId := ⟨0⟩)
    (power : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false) (moveOrCrew : Bool := false) : BattlefieldChoice :=
  .objectOrIntBattlefieldChoice id otherId none none power 0 0 (.player ⟨0⟩) alt1 alt2 moveOrCrew true false
@[match_pattern] abbrev intBattlefieldChoice (p : Int) (t : Int := 0) (objectId : ObjectId := ⟨0⟩)
    (target : Target := .player ⟨0⟩) (sourceId : Option ObjectId := none) (sheHulk : Bool := false) : BattlefieldChoice :=
  .objectOrIntBattlefieldChoice objectId ⟨0⟩ sourceId none 0 p t target sheHulk false false false true
@[match_pattern] abbrev playerBattlefieldChoice (rest : Array PlayerId) (ids : Array ObjectId := #[])
    (exiled : Array ObjectId := #[]) (chosen : Array ObjectId := #[]) (controller : PlayerId := ⟨0⟩)
    (creatureId : ObjectId := ⟨0⟩) (sourceId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (worldsOrBlackGate : Bool := false) : BattlefieldChoice :=
  .playerOrObjectsBattlefieldChoice rest ids exiled chosen controller creatureId 0 sourceId alt1 alt2 worldsOrBlackGate false
@[match_pattern] abbrev chooseFromObjects (ids : Array ObjectId) (n : Nat := 0) (hostId : ObjectId := ⟨0⟩)
    (removeOrHero : Bool := false) (sacThese : Bool := false) (attachOrHero : Bool := false) : BattlefieldChoice :=
  .playerOrObjectsBattlefieldChoice #[] ids #[] #[] ⟨0⟩ hostId n none removeOrHero sacThese attachOrHero true
@[match_pattern] abbrev mayCreateTokens (kind : TokenKind) (n : Nat) : BattlefieldChoice :=
  .tokenOrTypeBattlefieldChoice kind n #[] false
@[match_pattern] abbrev palisadeCreatureType (types : Array String) : BattlefieldChoice :=
  .tokenOrTypeBattlefieldChoice .treasure 0 types true
@[match_pattern] abbrev planeswalkerOrOddEven (sourceId : Option ObjectId := none) (oddEven : Bool := false) : BattlefieldChoice :=
  .optionalSourceChoice sourceId none oddEven false
@[match_pattern] abbrev maySacrificePlaneswalker : BattlefieldChoice := .optionalSourceChoice none none false false
@[match_pattern] abbrev oddOrEvenDestroy (sourceId : Option ObjectId) : BattlefieldChoice := .optionalSourceChoice sourceId none true false
@[match_pattern] abbrev widowMayCounter (sourceId : Option ObjectId) (exiled : Option ObjectId) : BattlefieldChoice :=
  .optionalSourceChoice sourceId exiled false true
@[match_pattern] abbrev maySacrificeThen (kind : ObjectSelector) (next : Resolution) (sourceId : Option ObjectId) : BattlefieldChoice :=
  .mayPermanentCostThen next sourceId kind false
@[match_pattern] abbrev mayTapSourceThen (next : Resolution) (sourceId : ObjectId) : BattlefieldChoice :=
  .mayPermanentCostThen next (some sourceId) .source true
@[match_pattern] abbrev mayObjectAction (id : ObjectId) (ultronOrDrawTreasure : Bool := false) (sacAnother : Bool := false) : BattlefieldChoice :=
  .objectBattlefieldChoice id ⟨0⟩ 0 ultronOrDrawTreasure sacAnother false
@[match_pattern] abbrev mayMovePlusOne (sourceId : ObjectId) : BattlefieldChoice := .objectBattlefieldChoice sourceId ⟨0⟩ 0 false false false
@[match_pattern] abbrev ultronMayPay (artifactId : ObjectId) : BattlefieldChoice := .objectBattlefieldChoice artifactId ⟨0⟩ 0 true false false
@[match_pattern] abbrev maySacrificeAnother (sourceId : ObjectId) (forDrawTreasure : Bool := false) : BattlefieldChoice :=
  .objectBattlefieldChoice sourceId ⟨0⟩ 0 forDrawTreasure true false
@[match_pattern] abbrev maySacrificeAnotherCreatureForPower (sourceId : ObjectId) : BattlefieldChoice :=
  .maySacrificeAnother sourceId false
@[match_pattern] abbrev maySacrificeAnotherForDrawTreasure (sourceId : ObjectId) : BattlefieldChoice :=
  .maySacrificeAnother sourceId true
@[match_pattern] abbrev mayMoveAllCounters (fromId toId : ObjectId) : BattlefieldChoice :=
  .objectBattlefieldChoice fromId toId 0 false false true
@[match_pattern] abbrev crew (abilityId vehicleId : ObjectId) (power : Nat) : BattlefieldChoice :=
  .objectBattlefieldChoice abilityId vehicleId power true false true
@[match_pattern] abbrev multiPlayerSacrifice (rest : Array PlayerId) (ids : Array ObjectId) (controller : PlayerId := ⟨0⟩) (nontokenOnly : Bool := false) (damager : Bool := false) : BattlefieldChoice :=
  .playerBattlefieldChoice rest ids #[] #[] controller ⟨0⟩ none nontokenOnly damager false
@[match_pattern] abbrev sacrificeCreatureEach (controller : PlayerId) (rest : Array PlayerId) (chosen : Array ObjectId) : BattlefieldChoice :=
  .playerBattlefieldChoice rest chosen #[] #[] controller ⟨0⟩ none false false false
@[match_pattern] abbrev sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId) : BattlefieldChoice :=
  .playerBattlefieldChoice rest chosen #[] #[] ⟨0⟩ ⟨0⟩ none true false false
@[match_pattern] abbrev sacrificeDamager (ids : Array ObjectId) (rest : Array PlayerId) (controller : PlayerId) : BattlefieldChoice :=
  .playerBattlefieldChoice rest ids #[] #[] controller ⟨0⟩ none false true false
@[match_pattern] abbrev worldsPutCreatures (eligible : Array ObjectId) (rest : Array PlayerId) (exiled chosen : Array ObjectId) (sourceId : Option ObjectId) : BattlefieldChoice :=
  .playerBattlefieldChoice rest eligible exiled chosen ⟨0⟩ ⟨0⟩ sourceId false false true
@[match_pattern] abbrev blackGatePlayer (creatureId : ObjectId) (players : Array PlayerId) : BattlefieldChoice :=
  .playerBattlefieldChoice players #[] #[] #[] ⟨0⟩ creatureId none true false true
@[match_pattern] abbrev chooseCreatureFrom (ids : Array ObjectId) (removeCounter : Bool := false) : BattlefieldChoice :=
  .chooseFromObjects ids 0 ⟨0⟩ removeCounter false false
@[match_pattern] abbrev sacrificeLeastPower (ids : Array ObjectId) : BattlefieldChoice := .chooseCreatureFrom ids false
@[match_pattern] abbrev hydeRemoveCounter (ids : Array ObjectId) : BattlefieldChoice := .chooseCreatureFrom ids true
@[match_pattern] abbrev maySacrificeThese (n : Nat) (ids : Array ObjectId) : BattlefieldChoice :=
  .chooseFromObjects ids n ⟨0⟩ false true false
@[match_pattern] abbrev attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId) : BattlefieldChoice :=
  .chooseFromObjects eligible 0 hostId false false true
@[match_pattern] abbrev mayPutHeroFromHandOrDraw (ids : Array ObjectId) : BattlefieldChoice :=
  .chooseFromObjects ids 0 ⟨0⟩ true false true
@[match_pattern] abbrev mayBecomeBasePT (objectId : ObjectId) (p t : Int) : BattlefieldChoice :=
  .intBattlefieldChoice p t objectId (.player ⟨0⟩) none false
@[match_pattern] abbrev sheHulkMayDamage (amount : Int) (target : Target) (sourceId : Option ObjectId) : BattlefieldChoice :=
  .intBattlefieldChoice amount 0 ⟨0⟩ target sourceId true

end BattlefieldChoice

/-- Cost, mode, enters, and target choices made while an effect resolves (CR 118 / CR 601.2 / CR 614.12 / CR 700.2). -/
inductive CostModeChoice where
  | mayPayOrPicksChoice (next : Resolution := .unrecognized) (sourceId : Option ObjectId := none)
      (objId : ObjectId := ⟨0⟩) (mana : Option Nat := none) (symbols : Array ManaSymbol := #[])
      (picks : Array CostPick := #[]) (pick : CostPick := default)
      (maxTimes : Nat := 0) (kind : Nat := 0)
      (alt1 : Bool := false) (alt2 : Bool := false) (isPicks : Bool := false)
  | modeOrTypeChoice (objectId : ObjectId := ⟨0⟩) (nats : Array Nat := #[]) (remaining : Nat := 0)
      (sourceId : Option ObjectId := none) (copies : Array ObjectId := #[])
      (types : Array String := #[]) (use : FraManaUse := .notSpellsFromHand)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
      (isObjOrSpecial : Bool := false) (isTypeOrMana : Bool := false)
deriving Repr, Inhabited, BEq

namespace CostModeChoice

@[match_pattern] abbrev mayPayOrResolveChoice (next : Resolution := .unrecognized) (sourceId : Option ObjectId := none)
    (objId : ObjectId := ⟨0⟩) (mana : Option Nat := none) (symbols : Array ManaSymbol := #[])
    (maxTimes : Nat := 0) (kind : Nat := 0) (reflexive : Bool := false) (isSymbols : Bool := false) : CostModeChoice :=
  .mayPayOrPicksChoice next sourceId objId mana symbols #[] default maxTimes kind reflexive isSymbols false
@[match_pattern] abbrev picksCostChoice (sourceId : ObjectId) (picks : Array CostPick := #[])
    (pick : CostPick := default) (next : Resolution := .unrecognized)
    (paid : Bool := false) (isSinglePick : Bool := false) : CostModeChoice :=
  .mayPayOrPicksChoice next none sourceId none #[] picks pick 0 0 paid isSinglePick true
@[match_pattern] abbrev modeOrEntersChoice (objectId : ObjectId := ⟨0⟩) (nats : Array Nat := #[]) (remaining : Nat := 0)
    (sourceId : Option ObjectId := none) (copies : Array ObjectId := #[])
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
    (isObjOrSpecial : Bool := false) : CostModeChoice :=
  .modeOrTypeChoice objectId nats remaining sourceId copies #[] .notSpellsFromHand alt1 alt2 alt3 alt4 isObjOrSpecial false
@[match_pattern] abbrev typeOrManaColorChoice (types : Array String := #[]) (left : Nat := 0)
    (use : FraManaUse := .notSpellsFromHand) (isManaColors : Bool := false) : CostModeChoice :=
  .modeOrTypeChoice ⟨0⟩ #[] left none #[] types use isManaColors false false false false true
@[match_pattern] abbrev mayResolveOrPayThen (next : Resolution) (sourceId : Option ObjectId) (mana : Option Nat := none) : CostModeChoice :=
  .mayPayOrResolveChoice next sourceId ⟨0⟩ mana #[] 0 0 false false
@[match_pattern] abbrev mayPaySymbolsChoice (symbols : Array ManaSymbol) (next : Resolution := .unrecognized)
    (sourceId : ObjectId := ⟨0⟩) (optSourceId : Option ObjectId := none)
    (maxTimes : Nat := 0) (kind : Nat := 0) (reflexive : Bool := false) : CostModeChoice :=
  .mayPayOrResolveChoice next optSourceId sourceId none symbols maxTimes kind reflexive true
@[match_pattern] abbrev modeOrCopyTargetsChoice (objectId : ObjectId := ⟨0⟩) (nats : Array Nat := #[])
    (remaining : Nat := 0) (sourceId : Option ObjectId := none) (copies : Array ObjectId := #[])
    (alt1 : Bool := false) (alt2 : Bool := false) (multi : Bool := false) (copyTargets : Bool := false) : CostModeChoice :=
  .modeOrEntersChoice objectId nats remaining sourceId copies alt1 alt2 multi copyTargets false
@[match_pattern] abbrev objectOrSpecialModeChoice (objectId : ObjectId := ⟨0⟩) (n : Nat := 0)
    (sourceId : Option ObjectId := none) (alt1 : Bool := false) (alt2 : Bool := false)
    (natChoice : Bool := false) (special : Bool := false) : CostModeChoice :=
  .modeOrEntersChoice objectId #[] n sourceId #[] alt1 alt2 natChoice special true
@[match_pattern] abbrev costPicks (sourceId : ObjectId) (picks : Array CostPick) (paid : Bool) : CostModeChoice :=
  .picksCostChoice sourceId picks default .unrecognized paid false
@[match_pattern] abbrev mayPayPickThen (pick : CostPick) (next : Resolution) (sourceId : ObjectId) : CostModeChoice :=
  .picksCostChoice sourceId #[] pick next false true
@[match_pattern] abbrev chooseCreatureType (types : Array String) : CostModeChoice :=
  .typeOrManaColorChoice types 0 .notSpellsFromHand false
@[match_pattern] abbrev addManaColors (left : Nat) (use : FraManaUse) : CostModeChoice :=
  .typeOrManaColorChoice #[] left use true
@[match_pattern] abbrev mayThen (next : Resolution) (sourceId : Option ObjectId) : CostModeChoice :=
  .mayResolveOrPayThen next sourceId none
@[match_pattern] abbrev mayPayThen (n : Nat) (next : Resolution) (sourceId : Option ObjectId) : CostModeChoice :=
  .mayResolveOrPayThen next sourceId (some n)
@[match_pattern] abbrev chooseAvailableOption (objectId : ObjectId) (available : Array Nat)
    (gollum : Bool := false) (keywordOrVision : Bool := false) : CostModeChoice :=
  .modeOrCopyTargetsChoice objectId available 0 none #[] gollum keywordOrVision false false
@[match_pattern] abbrev allianceMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available false false
@[match_pattern] abbrev gollumMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available true false
@[match_pattern] abbrev chooseKeyword (objectId : ObjectId) (options : Array Nat) : CostModeChoice :=
  .chooseAvailableOption objectId options false true
@[match_pattern] abbrev visionMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available true true
@[match_pattern] abbrev multiModesChoice (remaining : Nat) (chosen : Array Nat) (sourceId : Option ObjectId := none) (objectId : ObjectId := ⟨0⟩) (hawkeye : Bool := false) : CostModeChoice :=
  .modeOrCopyTargetsChoice objectId chosen remaining sourceId #[] hawkeye false true false
@[match_pattern] abbrev triggerModes (objectId : ObjectId) (remaining : Nat) (chosen : Array Nat) : CostModeChoice :=
  .multiModesChoice remaining chosen none objectId false
@[match_pattern] abbrev hawkeyeModes (left : Nat) (chosen : Array Nat) (sourceId : Option ObjectId) : CostModeChoice :=
  .multiModesChoice left chosen sourceId ⟨0⟩ true
@[match_pattern] abbrev newTargetsForCopies (copies : Array ObjectId) : CostModeChoice :=
  .modeOrCopyTargetsChoice ⟨0⟩ #[] 0 none copies false false false true
@[match_pattern] abbrev asEntersChoice (objectId : ObjectId) (cardName : Bool := false) (creatureTypeOrOddEven : Bool := false) : CostModeChoice :=
  .objectOrSpecialModeChoice objectId 0 none cardName creatureTypeOrOddEven false false
@[match_pattern] abbrev chooseColor (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId false false
@[match_pattern] abbrev chooseCardName (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId true false
@[match_pattern] abbrev entersCreatureType (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId false true
@[match_pattern] abbrev entersOddEven (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId true true
@[match_pattern] abbrev objectNatChoice (id : ObjectId) (n : Nat) (changeTarget : Bool := false) : CostModeChoice :=
  .objectOrSpecialModeChoice id n none changeTarget false true false
@[match_pattern] abbrev payLifeOrEnterTapped (objectId : ObjectId) (life : Nat) : CostModeChoice :=
  .objectNatChoice objectId life false
@[match_pattern] abbrev mayChangeSpellTarget (spellId : ObjectId) (index : Nat) : CostModeChoice :=
  .objectNatChoice spellId index true
@[match_pattern] abbrev specialCostOrMode (sourceId : Option ObjectId := none) (objectId : ObjectId := ⟨0⟩) (hyde : Bool := false) (kingpin : Bool := false) : CostModeChoice :=
  .objectOrSpecialModeChoice objectId 0 sourceId hyde kingpin false true
@[match_pattern] abbrev mayPayExtort (sourceId : Option ObjectId) : CostModeChoice :=
  .specialCostOrMode sourceId ⟨0⟩ false false
@[match_pattern] abbrev hydeMode (sourceId : ObjectId) : CostModeChoice :=
  .specialCostOrMode none sourceId true false
@[match_pattern] abbrev kingpinMayPay2Life : CostModeChoice :=
  .specialCostOrMode none ⟨0⟩ false true
@[match_pattern] abbrev mayPaySymbolsThen (symbols : Array ManaSymbol) (next : Resolution) (sourceId : ObjectId) : CostModeChoice :=
  .mayPaySymbolsChoice symbols next sourceId none 0 0 false
@[match_pattern] abbrev mayPayManaForReflexive (cost : Array ManaSymbol) (maxTimes : Nat) (kind : Nat) (sourceId : Option ObjectId) : CostModeChoice :=
  .mayPaySymbolsChoice cost .unrecognized ⟨0⟩ sourceId maxTimes kind true

end CostModeChoice

/-- A choice made while an effect resolves (CR 608 / CR 701). The player answers
with `Action.choosePermanents` (cards or permanents), `Action.accept`, or
`Action.decline`. -/
inductive FraChoice where
  /-- Unified resolution choice (CR 608 / CR 701): hand/graveyard, library, battlefield, or cost/mode. -/
  | fraChoiceKind (val : HandGraveyardChoice ⊕ LibraryChoice ⊕ BattlefieldChoice ⊕ CostModeChoice := .inl default)
deriving Repr, Inhabited, BEq

namespace FraChoice

@[match_pattern] abbrev handGraveyard (c : HandGraveyardChoice) : FraChoice :=
  .fraChoiceKind (.inl c)
@[match_pattern] abbrev library (c : LibraryChoice) : FraChoice :=
  .fraChoiceKind (.inr (.inl c))
@[match_pattern] abbrev battlefield (c : BattlefieldChoice) : FraChoice :=
  .fraChoiceKind (.inr (.inr (.inl c)))
@[match_pattern] abbrev costMode (c : CostModeChoice) : FraChoice :=
  .fraChoiceKind (.inr (.inr (.inr c)))

-- LibraryChoice aliases
@[match_pattern] abbrev mayWheel (n : Nat) (rest : Array PlayerId) : FraChoice := .library (.mayWheel n rest)
@[match_pattern] abbrev topOrBottomDamage (id : ObjectId) (damage : Nat) : FraChoice := .library (.topOrBottomDamage id damage)
@[match_pattern] abbrev extrapolateReveal : FraChoice := .library .extrapolateReveal
@[match_pattern] abbrev extrapolatePick (revealer : PlayerId) (ids : Array ObjectId) : FraChoice := .library (.extrapolatePick revealer ids)
@[match_pattern] abbrev mayDrawThenDiscard (draw discard : Nat) : FraChoice := .library (.mayDrawThenDiscard draw discard)
@[match_pattern] abbrev revealSelect (looked eligible : Array ObjectId) (flag : Bool) (putCreatures : Bool := false) : FraChoice :=
  .library (.revealSelect looked eligible flag putCreatures false)
@[match_pattern] abbrev mayRevealToHand (looked eligible : Array ObjectId) (anyOrder : Bool) : FraChoice := .library (.mayRevealToHand looked eligible anyOrder)
@[match_pattern] abbrev nickFuryPut (looked eligible : Array ObjectId) : FraChoice := .library (.nickFuryPut looked eligible)
@[match_pattern] abbrev nickFuryMayTransform (permanentId : ObjectId) (rest : Array ObjectId) : FraChoice := .library (.nickFuryMayTransform permanentId rest)
@[match_pattern] abbrev arrangeCards (ids : Array ObjectId) (splitPiles : Bool := false) : FraChoice := .library (.arrangeCards ids splitPiles)
@[match_pattern] abbrev orderLibraryBottom (ids : Array ObjectId) : FraChoice := .library (.orderLibraryBottom ids)
@[match_pattern] abbrev searchChoice (eligible : Array ObjectId) (count : Nat) (dest : SearchDest) (after : Option Resolution) (kind : String) (optional : Bool := false) : FraChoice :=
  .library (.searchChoice eligible count dest after kind optional)
@[match_pattern] abbrev searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest) (after : Option Resolution) (kind : String) : FraChoice :=
  .library (.searchLibrary eligible count dest after kind)
@[match_pattern] abbrev maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest) (after : Option Resolution) (kind : String) : FraChoice :=
  .library (.maySearchLibrary eligible count dest after kind)
@[match_pattern] abbrev palantirMayDraw (controller : PlayerId) (sourceId : ObjectId) : FraChoice := .library (.palantirMayDraw controller sourceId)
@[match_pattern] abbrev tricksterLibrary (caster : PlayerId) (creatureId : ObjectId) (connive : Option ObjectId) : FraChoice :=
  .library (.tricksterLibrary caster creatureId connive)
@[match_pattern] abbrev mayDrawThenEachOpponentDraws (n : Nat) : FraChoice := .library (.mayDrawThenEachOpponentDraws n)
@[match_pattern] abbrev visionQuestZones (libIds gyIds : Array ObjectId) (x : Nat) : FraChoice := .library (.visionQuestZones libIds gyIds x)
@[match_pattern] abbrev visionQuestPick (ids : Array ObjectId) (x : Nat) (shuffle : Bool) : FraChoice := .library (.visionQuestPick ids x shuffle)
@[match_pattern] abbrev daredevilMayExile (sourceId : Option ObjectId) : FraChoice := .library (.daredevilMayExile sourceId)
@[match_pattern] abbrev riddlesSplit (looked : Array ObjectId) : FraChoice := .library (.riddlesSplit looked)
@[match_pattern] abbrev riddlesChoosePile (controller : PlayerId) (faceUp faceDown : Array ObjectId) : FraChoice :=
  .library (.riddlesChoosePile controller faceUp faceDown)
@[match_pattern] abbrev revealPutCreatures (looked creatures : Array ObjectId) (anyNumber : Bool) : FraChoice :=
  .library (.revealPutCreatures looked creatures anyNumber)
@[match_pattern] abbrev chooseCards (ids : Array ObjectId) (max : Nat) (purpose : CardChoice) : FraChoice :=
  .library (.chooseCards ids max purpose)
@[match_pattern] abbrev mayBeginOnBattlefield (ids : Array ObjectId) : FraChoice := .library (.mayBeginOnBattlefield ids)

-- HandGraveyardChoice aliases
@[match_pattern] abbrev discardFromRevealedHand (target : PlayerId) (permanentOnly : Bool) : FraChoice :=
  .handGraveyard (.discardFromRevealedHand target permanentOnly)
@[match_pattern] abbrev mayExileOrCastCopy (id : ObjectId) (castCopy : Bool := false) : FraChoice :=
  .handGraveyard (.mayExileOrCastCopy id castCopy)
@[match_pattern] abbrev sphinxsApproach (spellId : ObjectId) : FraChoice := .handGraveyard (.sphinxsApproach spellId)
@[match_pattern] abbrev mayDiscardThen (next : Resolution) (sourceId : Option ObjectId) : FraChoice := .handGraveyard (.mayDiscardThen next sourceId)
@[match_pattern] abbrev discardWithSource (id : Option ObjectId) (entireHand : Bool := false) : FraChoice :=
  .handGraveyard (.discardWithSource id entireHand)
@[match_pattern] abbrev discardThen (causeId : Option ObjectId) : FraChoice :=
  .handGraveyard (.discardThen causeId)
@[match_pattern] abbrev discardThenStun (n : Nat) (sourceId : Option ObjectId) : FraChoice := .handGraveyard (.discardThenStun n sourceId)
@[match_pattern] abbrev exileFromRevealedHand (victim : PlayerId) (sourceId : Option ObjectId) : FraChoice :=
  .handGraveyard (.exileFromRevealedHand victim sourceId)
@[match_pattern] abbrev castCopiesFree (ids : Array ObjectId) (budget : Nat) (castsLeft : Nat) : FraChoice :=
  .handGraveyard (.castCopiesFree ids budget castsLeft)
@[match_pattern] abbrev discardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat) : FraChoice :=
  .handGraveyard (.discardTwo controller rest draws)
@[match_pattern] abbrev mayDiscardOrCastUpTo (ids : Array ObjectId) (n : Nat) (castFromExile : Bool := false) : FraChoice :=
  .handGraveyard (.mayDiscardOrCastUpTo ids n castFromExile)
@[match_pattern] abbrev mayDiscardThese (n : Nat) (ids : Array ObjectId) : FraChoice := .handGraveyard (.mayDiscardThese n ids)
@[match_pattern] abbrev mayCastZoneCards (eligible : Array ObjectId) (fromHand : Bool := false) : FraChoice :=
  .handGraveyard (.mayCastZoneCards eligible fromHand)
@[match_pattern] abbrev mayCastFromGraveyard (eligible : Array ObjectId) : FraChoice := .handGraveyard (.mayCastFromGraveyard eligible)
@[match_pattern] abbrev mayCastCards (eligible : Array ObjectId) (withoutPaying exileInstead : Bool) : FraChoice :=
  .handGraveyard (.mayCastCards eligible withoutPaying exileInstead)
@[match_pattern] abbrev discardThenDraw : FraChoice := .handGraveyard .discardThenDraw
@[match_pattern] abbrev zemoBoastExile (abilityId sourceId : ObjectId) : FraChoice := .handGraveyard (.zemoBoastExile abilityId sourceId)
@[match_pattern] abbrev mayCastCascade (cardId : ObjectId) (others : Array ObjectId) : FraChoice := .handGraveyard (.mayCastCascade cardId others)
@[match_pattern] abbrev mayCastGrima (cardId : ObjectId) (others : Array ObjectId) (victim : PlayerId) : FraChoice :=
  .handGraveyard (.mayCastGrima cardId others victim)
@[match_pattern] abbrev mayCastCopy (copyId : ObjectId) : FraChoice := .handGraveyard (.mayCastCopy copyId)
@[match_pattern] abbrev mayDiscardHandBalin (sourceId : Option ObjectId) : FraChoice := .handGraveyard (.mayDiscardHandBalin sourceId)
@[match_pattern] abbrev mayDiscardHandDrawFixed (n : Nat) : FraChoice := .handGraveyard (.mayDiscardHandDrawFixed n)
@[match_pattern] abbrev mayCastInstantSorceryFromHand (eligible : Array ObjectId) : FraChoice :=
  .handGraveyard (.mayCastInstantSorceryFromHand eligible)
@[match_pattern] abbrev mayCastUpToFromExile (eligible : Array ObjectId) (left : Nat) : FraChoice :=
  .handGraveyard (.mayCastUpToFromExile eligible left)
@[match_pattern] abbrev moonstoneMayExile (cardId : ObjectId) : FraChoice := .handGraveyard (.moonstoneMayExile cardId)
@[match_pattern] abbrev mayTakeMilled (ids : Array ObjectId) (lifeAfter : Nat) : FraChoice := .handGraveyard (.mayTakeMilled ids lifeAfter)

-- BattlefieldChoice aliases
@[match_pattern] abbrev maySacrificePlaneswalker : FraChoice := .battlefield .maySacrificePlaneswalker
@[match_pattern] abbrev maySacrificeThen (kind : ObjectSelector) (next : Resolution) (sourceId : Option ObjectId) : FraChoice :=
  .battlefield (.maySacrificeThen kind next sourceId)
@[match_pattern] abbrev mayObjectAction (id : ObjectId) (ultronPay : Bool := false) : FraChoice :=
  .battlefield (.mayObjectAction id ultronPay)
@[match_pattern] abbrev mayMovePlusOne (sourceId : ObjectId) : FraChoice := .battlefield (.mayMovePlusOne sourceId)
@[match_pattern] abbrev sacrificeCreatureEach (controller : PlayerId) (rest : Array PlayerId) (chosen : Array ObjectId) : FraChoice :=
  .battlefield (.sacrificeCreatureEach controller rest chosen)
@[match_pattern] abbrev mayMoveAllCounters (fromId toId : ObjectId) : FraChoice := .battlefield (.mayMoveAllCounters fromId toId)
@[match_pattern] abbrev crew (abilityId vehicleId : ObjectId) (power : Nat) : FraChoice := .battlefield (.crew abilityId vehicleId power)
@[match_pattern] abbrev maySacrificeAnother (sourceId : ObjectId) (forDrawTreasure : Bool := false) : FraChoice :=
  .battlefield (.maySacrificeAnother sourceId forDrawTreasure)
@[match_pattern] abbrev maySacrificeAnotherCreatureForPower (sourceId : ObjectId) : FraChoice :=
  .battlefield (.maySacrificeAnotherCreatureForPower sourceId)
@[match_pattern] abbrev maySacrificeAnotherForDrawTreasure (sourceId : ObjectId) : FraChoice :=
  .battlefield (.maySacrificeAnotherForDrawTreasure sourceId)
@[match_pattern] abbrev maySacrificeThese (n : Nat) (ids : Array ObjectId) : FraChoice := .battlefield (.maySacrificeThese n ids)
@[match_pattern] abbrev attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId) : FraChoice :=
  .battlefield (.attachAnyEquipment hostId eligible)
@[match_pattern] abbrev chooseCreatureFrom (ids : Array ObjectId) (removeCounter : Bool := false) : FraChoice :=
  .battlefield (.chooseCreatureFrom ids removeCounter)
@[match_pattern] abbrev sacrificeLeastPower (ids : Array ObjectId) : FraChoice := .battlefield (.sacrificeLeastPower ids)
@[match_pattern] abbrev sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId) : FraChoice :=
  .battlefield (.sacrificeNontokenEach rest chosen)
@[match_pattern] abbrev mayCreateTokens (kind : TokenKind) (n : Nat) : FraChoice := .battlefield (.mayCreateTokens kind n)
@[match_pattern] abbrev mayBecomeBasePT (objectId : ObjectId) (p t : Int) : FraChoice := .battlefield (.mayBecomeBasePT objectId p t)
@[match_pattern] abbrev mayTapSourceThen (next : Resolution) (sourceId : ObjectId) : FraChoice := .battlefield (.mayTapSourceThen next sourceId)
@[match_pattern] abbrev sacrificeDamager (ids : Array ObjectId) (rest : Array PlayerId) (controller : PlayerId) : FraChoice :=
  .battlefield (.sacrificeDamager ids rest controller)
@[match_pattern] abbrev hydeRemoveCounter (ids : Array ObjectId) : FraChoice := .battlefield (.hydeRemoveCounter ids)
@[match_pattern] abbrev sheHulkMayDamage (amount : Int) (target : Target) (sourceId : Option ObjectId) : FraChoice :=
  .battlefield (.sheHulkMayDamage amount target sourceId)
@[match_pattern] abbrev widowMayCounter (sourceId : Option ObjectId) (exiled : Option ObjectId) : FraChoice :=
  .battlefield (.widowMayCounter sourceId exiled)
@[match_pattern] abbrev ultronMayPay (artifactId : ObjectId) : FraChoice := .battlefield (.ultronMayPay artifactId)
@[match_pattern] abbrev mayPutHeroFromHandOrDraw (ids : Array ObjectId) : FraChoice := .battlefield (.mayPutHeroFromHandOrDraw ids)
@[match_pattern] abbrev oddOrEvenDestroy (sourceId : Option ObjectId) : FraChoice := .battlefield (.oddOrEvenDestroy sourceId)
@[match_pattern] abbrev palisadeCreatureType (types : Array String) : FraChoice := .battlefield (.palisadeCreatureType types)
@[match_pattern] abbrev worldsPutCreatures (eligible : Array ObjectId) (rest : Array PlayerId) (exiled chosen : Array ObjectId) (sourceId : Option ObjectId) : FraChoice :=
  .battlefield (.worldsPutCreatures eligible rest exiled chosen sourceId)
@[match_pattern] abbrev blackGatePlayer (creatureId : ObjectId) (players : Array PlayerId) : FraChoice :=
  .battlefield (.blackGatePlayer creatureId players)

-- CostModeChoice aliases
@[match_pattern] abbrev mayThen (next : Resolution) (sourceId : Option ObjectId) : FraChoice := .costMode (.mayThen next sourceId)
@[match_pattern] abbrev mayPayThen (n : Nat) (next : Resolution) (sourceId : Option ObjectId) : FraChoice := .costMode (.mayPayThen n next sourceId)
@[match_pattern] abbrev chooseAvailableOption (objectId : ObjectId) (available : Array Nat) (gollum : Bool := false) (keywordOrVision : Bool := false) : FraChoice :=
  .costMode (.chooseAvailableOption objectId available gollum keywordOrVision)
@[match_pattern] abbrev allianceMode (sourceId : ObjectId) (available : Array Nat) : FraChoice := .costMode (.allianceMode sourceId available)
@[match_pattern] abbrev gollumMode (sourceId : ObjectId) (available : Array Nat) : FraChoice := .costMode (.gollumMode sourceId available)
@[match_pattern] abbrev triggerModes (objectId : ObjectId) (remaining : Nat) (chosen : Array Nat) : FraChoice :=
  .costMode (.triggerModes objectId remaining chosen)
@[match_pattern] abbrev chooseKeyword (objectId : ObjectId) (options : Array Nat) : FraChoice := .costMode (.chooseKeyword objectId options)
@[match_pattern] abbrev asEntersChoice (objectId : ObjectId) (cardName : Bool := false) (creatureTypeOrOddEven : Bool := false) : FraChoice :=
  .costMode (.asEntersChoice objectId cardName creatureTypeOrOddEven)
@[match_pattern] abbrev chooseColor (objectId : ObjectId) : FraChoice := .costMode (.chooseColor objectId)
@[match_pattern] abbrev chooseCardName (objectId : ObjectId) : FraChoice := .costMode (.chooseCardName objectId)
@[match_pattern] abbrev costPicks (sourceId : ObjectId) (picks : Array CostPick) (paid : Bool) : FraChoice :=
  .costMode (.costPicks sourceId picks paid)
@[match_pattern] abbrev mayPayPickThen (pick : CostPick) (next : Resolution) (sourceId : ObjectId) : FraChoice :=
  .costMode (.mayPayPickThen pick next sourceId)
@[match_pattern] abbrev chooseCreatureType (types : Array String) : FraChoice := .costMode (.chooseCreatureType types)
@[match_pattern] abbrev mayPaySymbolsThen (symbols : Array ManaSymbol) (next : Resolution) (sourceId : ObjectId) : FraChoice :=
  .costMode (.mayPaySymbolsThen symbols next sourceId)
@[match_pattern] abbrev addManaColors (left : Nat) (use : FraManaUse) : FraChoice := .costMode (.addManaColors left use)
@[match_pattern] abbrev objectNatChoice (id : ObjectId) (n : Nat) (changeTarget : Bool := false) : FraChoice :=
  .costMode (.objectNatChoice id n changeTarget)
@[match_pattern] abbrev payLifeOrEnterTapped (objectId : ObjectId) (life : Nat) : FraChoice := .costMode (.payLifeOrEnterTapped objectId life)
@[match_pattern] abbrev mayPayExtort (sourceId : Option ObjectId) : FraChoice := .costMode (.mayPayExtort sourceId)
@[match_pattern] abbrev mayPayManaForReflexive (cost : Array ManaSymbol) (maxTimes : Nat) (kind : Nat) (sourceId : Option ObjectId) : FraChoice :=
  .costMode (.mayPayManaForReflexive cost maxTimes kind sourceId)
@[match_pattern] abbrev hawkeyeModes (left : Nat) (chosen : Array Nat) (sourceId : Option ObjectId) : FraChoice :=
  .costMode (.hawkeyeModes left chosen sourceId)
@[match_pattern] abbrev hydeMode (sourceId : ObjectId) : FraChoice := .costMode (.hydeMode sourceId)
@[match_pattern] abbrev visionMode (sourceId : ObjectId) (available : Array Nat) : FraChoice := .costMode (.visionMode sourceId available)
@[match_pattern] abbrev kingpinMayPay2Life : FraChoice := .costMode .kingpinMayPay2Life
@[match_pattern] abbrev mayChangeSpellTarget (spellId : ObjectId) (index : Nat) : FraChoice := .costMode (.mayChangeSpellTarget spellId index)
@[match_pattern] abbrev newTargetsForCopies (copies : Array ObjectId) : FraChoice := .costMode (.newTargetsForCopies copies)
@[match_pattern] abbrev entersCreatureType (objectId : ObjectId) : FraChoice := .costMode (.entersCreatureType objectId)
@[match_pattern] abbrev entersOddEven (objectId : ObjectId) : FraChoice := .costMode (.entersOddEven objectId)

end FraChoice

/-- Turn-based, combat, mulligan, state-based action, and trigger-stacking choices (CR 103 / CR 508–510 / CR 603.3b / CR 704.5j). -/
inductive TurnCombatPending where
  | turnCombatPendingKind (player : PlayerId := ⟨0⟩) (count : Nat := 0) (name : String := "") (ids : Array ObjectId := #[])
      (alt1 : Bool := false) (alt2 : Bool := false) (playerStep : Bool := false) (bottom : Bool := false) (legend : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace TurnCombatPending

@[match_pattern] abbrev stepOrBottomPending (player : PlayerId := ⟨0⟩) (count : Nat := 0)
    (alt1 : Bool := false) (alt2 : Bool := false) (playerStep : Bool := false) (bottom : Bool := false) : TurnCombatPending :=
  .turnCombatPendingKind player count "" #[] alt1 alt2 playerStep bottom false
/-- This player chooses which of these legendary permanents with the same
name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
@[match_pattern] abbrev chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId) : TurnCombatPending :=
  .turnCombatPendingKind player 0 name ids false false false false true
@[match_pattern] abbrev declareCombatStep (blockers : Bool := false) : TurnCombatPending :=
  .stepOrBottomPending ⟨0⟩ 0 blockers false false false
@[match_pattern] abbrev playerBooleanStep (player : PlayerId) (flag : Bool := false) (combatDamage : Bool := false) : TurnCombatPending :=
  .stepOrBottomPending player 0 flag combatDamage true false
@[match_pattern] abbrev putOnBottom (player : PlayerId) (count : Nat) : TurnCombatPending :=
  .stepOrBottomPending player count false false false true
@[match_pattern] abbrev declareAttackers : TurnCombatPending := .declareCombatStep false
@[match_pattern] abbrev declareBlockers : TurnCombatPending := .declareCombatStep true
@[match_pattern] abbrev playerStepChoice (player : PlayerId) (triggerOrder : Bool := false) : TurnCombatPending :=
  .playerBooleanStep player triggerOrder false
@[match_pattern] abbrev declareMulligan (player : PlayerId) : TurnCombatPending := .playerBooleanStep player false false
@[match_pattern] abbrev chooseTriggerToStack (player : PlayerId) : TurnCombatPending := .playerBooleanStep player true false
@[match_pattern] abbrev assignCombatDamage (player : PlayerId) (forAttackers : Bool) : TurnCombatPending :=
  .playerBooleanStep player forAttackers true

end TurnCombatPending

/-- Spell casting and ability activation announcement steps (CR 601.2 / CR 602.2 / CR 702). -/
inductive CastPending where
  | castPendingKind (sourceId : ObjectId := ⟨0⟩) (need : Nat := 0) (alt1 : Bool := false)
      (alt2 : Bool := false) (additional : Bool := false) (teamwork : Bool := false) (costObjects : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace CastPending

@[match_pattern] abbrev castStep (alt1 : Bool := false) (alt2 : Bool := false) (additional : Bool := false) (teamwork : Bool := false) : CastPending :=
  .castPendingKind ⟨0⟩ 0 alt1 alt2 additional teamwork false
@[match_pattern] abbrev costObjectsStep (sourceId : ObjectId := ⟨0⟩) (need : Nat := 0) (teamworkCreatures : Bool := false) : CastPending :=
  .castPendingKind sourceId need teamworkCreatures false false false true
@[match_pattern] abbrev announceStep (mode : Bool := false) (chooseX : Bool := false) : CastPending :=
  .castStep mode chooseX false false
@[match_pattern] abbrev activateManaAbilities : CastPending := .castStep false false false false
@[match_pattern] abbrev chooseMode : CastPending := .castStep true false false false
@[match_pattern] abbrev chooseX : CastPending := .castStep false true false false
@[match_pattern] abbrev chooseTargets : CastPending := .castStep true true false false
@[match_pattern] abbrev additionalStep (chooseCost : Bool := false) (kicker : Bool := false) : CastPending :=
  .castStep chooseCost kicker true false
@[match_pattern] abbrev discardForAdditionalCost : CastPending := .castStep false false true false
@[match_pattern] abbrev chooseAdditionalCost : CastPending := .castStep true false true false
@[match_pattern] abbrev chooseKicker : CastPending := .castStep false true true false
@[match_pattern] abbrev chooseGift : CastPending := .castStep true true true false
@[match_pattern] abbrev chooseTeamwork : CastPending := .castStep false false false true
@[match_pattern] abbrev sacrificePermanent (sourceId : ObjectId) : CastPending := .costObjectsStep sourceId 0 false
@[match_pattern] abbrev chooseTeamworkCreatures (need : Nat) : CastPending := .costObjectsStep ⟨0⟩ need true

end CastPending

/-- Resolution, keyword action, and trigger choices (CR 608 / CR 701). -/
inductive ResolvePending where
  | resolvePendingKind (n : Nat := 0) (id : ObjectId := ⟨0⟩) (villainId : ObjectId := ⟨0⟩)
      (ids : Array ObjectId := #[]) (remaining : Array PlayerId := #[])
      (cost : WardCost := .genericMana 0) (maxMv : Int := 0)
      (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
      (natChoice : Bool := false) (objectChoice : Bool := false) (payOrExile : Bool := false)
      (sacCreature : Bool := false) (discardCard : Bool := false) (ward : Bool := false) (looked : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ResolvePending

@[match_pattern] abbrev resolveChoiceKind (n : Nat := 0) (id : ObjectId := ⟨0⟩) (villainId : ObjectId := ⟨0⟩)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (natChoice : Bool := false) (objectChoice : Bool := false) (payOrExile : Bool := false) : ResolvePending :=
  .resolvePendingKind n id villainId #[] #[] (.genericMana 0) 0 alt1 alt2 alt3 natChoice objectChoice payOrExile false false false false
/-- This player must sacrifice a creature they control. `chosen` are
already-selected sacrifices; `remaining` are later players in APNAP order. -/
@[match_pattern] abbrev chooseSacrificeCreature (chosen : Array ObjectId) (remaining : Array PlayerId) : ResolvePending :=
  .resolvePendingKind 0 ⟨0⟩ ⟨0⟩ chosen remaining (.genericMana 0) 0 false false false false false false true false false false
/-- This player must discard a card. `remaining` are later opponents. -/
@[match_pattern] abbrev chooseDiscardCard (remaining : Array PlayerId) : ResolvePending :=
  .resolvePendingKind 0 ⟨0⟩ ⟨0⟩ #[] remaining (.genericMana 0) 0 false false false false false false false true false false
/-- Pay this ward cost or let the targeting spell or ability be countered
(CR 702.21). -/
@[match_pattern] abbrev payWard (spellId : ObjectId) (cost : WardCost) : ResolvePending :=
  .resolvePendingKind 0 spellId ⟨0⟩ #[] #[] cost 0 false false false false false false false false true false
/-- You may cast one of these looked-at library cards without paying its
mana cost as the ability resolves (Cosmic Cube; MSH 356). `maxMv` is the
greatest power among attacking creatures you control. -/
@[match_pattern] abbrev mayCastFromLooked (ids : Array ObjectId) (maxMv : Int) : ResolvePending :=
  .resolvePendingKind 0 ⟨0⟩ ⟨0⟩ ids #[] (.genericMana 0) maxMv false false false false false false false false false true
@[match_pattern] abbrev resolvePrompt (alt1 : Bool := false) (alt2 : Bool := false) (ringOrLand : Bool := false) : ResolvePending :=
  .resolveChoiceKind 0 ⟨0⟩ ⟨0⟩ alt1 alt2 ringOrLand false false false
@[match_pattern] abbrev natResolveChoice (n : Nat) (alt : Bool := false) (costDraw : Bool := false) (payOrProlif : Bool := false) : ResolvePending :=
  .resolveChoiceKind n ⟨0⟩ ⟨0⟩ alt costDraw payOrProlif true false false
@[match_pattern] abbrev objectResolveChoice (id : ObjectId) (villainId : ObjectId := ⟨0⟩) (alt : Bool := false) (equipOrArt : Bool := false) (connive : Bool := false) : ResolvePending :=
  .resolveChoiceKind 0 id villainId alt equipOrArt connive false true false
@[match_pattern] abbrev payOrExileChoice (n : Nat) (id : ObjectId) (castExiled : Bool := false) : ResolvePending :=
  .resolveChoiceKind n id ⟨0⟩ castExiled false false false false true

@[match_pattern] abbrev sacrificeCreature : ResolvePending := .resolvePrompt false false false
@[match_pattern] abbrev mayResolve : ResolvePending := .resolvePrompt true false false
@[match_pattern] abbrev tapHumans : ResolvePending := .resolvePrompt false true false
@[match_pattern] abbrev recruitDiscard : ResolvePending := .resolvePrompt true true false
@[match_pattern] abbrev ringOrLandPrompt (putLand : Bool := false) (triggerOr : Bool := false) : ResolvePending :=
  .resolvePrompt putLand triggerOr true
@[match_pattern] abbrev chooseRingBearer : ResolvePending := .resolvePrompt false false true
@[match_pattern] abbrev mayPutLandFromHand : ResolvePending := .resolvePrompt true false true
@[match_pattern] abbrev chooseTriggerOr : ResolvePending := .resolvePrompt false true true
@[match_pattern] abbrev lookLibrary (count : Nat) (surveil : Bool := false) : ResolvePending :=
  .natResolveChoice count surveil false false
@[match_pattern] abbrev scry (count : Nat) : ResolvePending := .natResolveChoice count false false false
@[match_pattern] abbrev surveil (count : Nat) : ResolvePending := .natResolveChoice count true false false
@[match_pattern] abbrev mayCostDraw (drawCount : Nat) (sacArtifact : Bool := false) : ResolvePending :=
  .natResolveChoice drawCount sacArtifact true false
@[match_pattern] abbrev mayDiscardDraw (drawCount : Nat) : ResolvePending := .natResolveChoice drawCount false true false
@[match_pattern] abbrev maySacArtifactOrDiscard (draw : Nat) : ResolvePending := .natResolveChoice draw true true false
@[match_pattern] abbrev payOrProliferate (n : Nat) (proliferate : Bool := false) : ResolvePending :=
  .natResolveChoice n proliferate false true
@[match_pattern] abbrev mayPayGeneric (n : Nat) : ResolvePending := .natResolveChoice n false false true
@[match_pattern] abbrev chooseProliferate (remaining : Nat) : ResolvePending := .natResolveChoice remaining true false true
@[match_pattern] abbrev objectChoice (id : ObjectId) (bolgSacrifice : Bool := false) : ResolvePending :=
  .objectResolveChoice id ⟨0⟩ bolgSacrifice false false
@[match_pattern] abbrev chooseLibraryPlacement (id : ObjectId) : ResolvePending := .objectResolveChoice id ⟨0⟩ false false false
@[match_pattern] abbrev maySacrificeAnotherBolg (bolgId : ObjectId) : ResolvePending := .objectResolveChoice bolgId ⟨0⟩ true false false
@[match_pattern] abbrev mayEquipmentOrArtifact (hostId : ObjectId) (fromHand : Bool := false) : ResolvePending :=
  .objectResolveChoice hostId ⟨0⟩ fromHand true false
@[match_pattern] abbrev mayAttachEquipment (hostId : ObjectId) : ResolvePending := .objectResolveChoice hostId ⟨0⟩ false true false
@[match_pattern] abbrev mayPutArtifactFromHand (hostId : ObjectId) : ResolvePending := .objectResolveChoice hostId ⟨0⟩ true true false
@[match_pattern] abbrev mayHaveVillainConnive (sourceId : ObjectId) (villainId : ObjectId) : ResolvePending :=
  .objectResolveChoice sourceId villainId false false true
@[match_pattern] abbrev payOrLetCounter (n : Nat) (spellId : ObjectId) : ResolvePending := .payOrExileChoice n spellId false
@[match_pattern] abbrev mayCastExiledElseDamage (cardId : ObjectId) (damage : Nat) : ResolvePending :=
  .payOrExileChoice damage cardId true

end ResolvePending

/-- Choice that must be made before priority proceeds. -/
inductive Pending where
  /-- Unified pending choice (CR 103 / 508–510 / 601 / 608): `none`, `turnCombat`, `cast`, `resolve`, `fraChoice`, or `resolveRandom`. -/
  | pendingKind (val : Option (TurnCombatPending ⊕ (PlayerId × CastPending) ⊕ (PlayerId × ResolvePending) ⊕ (PlayerId × FraChoice) ⊕ RandomRequest) := Option.none)
deriving Repr, Inhabited, BEq

namespace Pending

@[match_pattern] abbrev none : Pending :=
  .pendingKind Option.none
@[match_pattern] abbrev turnCombat (step : TurnCombatPending) : Pending :=
  .pendingKind (some (.inl step))
@[match_pattern] abbrev cast (player : PlayerId) (step : CastPending) : Pending :=
  .pendingKind (some (.inr (.inl (player, step))))
@[match_pattern] abbrev resolve (player : PlayerId) (choice : ResolvePending) : Pending :=
  .pendingKind (some (.inr (.inr (.inl (player, choice)))))
@[match_pattern] abbrev fraChoice (player : PlayerId) (choice : FraChoice) : Pending :=
  .pendingKind (some (.inr (.inr (.inr (.inl (player, choice))))))
@[match_pattern] abbrev resolveRandom (req : RandomRequest) : Pending :=
  .pendingKind (some (.inr (.inr (.inr (.inr req)))))

-- TurnCombatPending aliases
@[match_pattern] abbrev declareAttackers : Pending := .turnCombat .declareAttackers
@[match_pattern] abbrev declareBlockers : Pending := .turnCombat .declareBlockers
@[match_pattern] abbrev declareMulligan (player : PlayerId) : Pending := .turnCombat (.declareMulligan player)
@[match_pattern] abbrev putOnBottom (player : PlayerId) (count : Nat) : Pending := .turnCombat (.putOnBottom player count)
@[match_pattern] abbrev assignCombatDamage (player : PlayerId) (forAttackers : Bool) : Pending := .turnCombat (.assignCombatDamage player forAttackers)
@[match_pattern] abbrev chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId) : Pending := .turnCombat (.chooseLegend player name ids)
@[match_pattern] abbrev chooseTriggerToStack (player : PlayerId) : Pending := .turnCombat (.chooseTriggerToStack player)

-- CastPending aliases
@[match_pattern] abbrev activateManaAbilities (caster : PlayerId) : Pending := .cast caster .activateManaAbilities
@[match_pattern] abbrev chooseMode (caster : PlayerId) : Pending := .cast caster .chooseMode
@[match_pattern] abbrev chooseX (caster : PlayerId) : Pending := .cast caster .chooseX
@[match_pattern] abbrev chooseTargets (caster : PlayerId) : Pending := .cast caster .chooseTargets
@[match_pattern] abbrev sacrificePermanent (player : PlayerId) (sourceId : ObjectId) : Pending := .cast player (.sacrificePermanent sourceId)
@[match_pattern] abbrev discardForAdditionalCost (player : PlayerId) : Pending := .cast player .discardForAdditionalCost
@[match_pattern] abbrev chooseAdditionalCost (player : PlayerId) : Pending := .cast player .chooseAdditionalCost
@[match_pattern] abbrev chooseKicker (player : PlayerId) : Pending := .cast player .chooseKicker
@[match_pattern] abbrev chooseGift (player : PlayerId) : Pending := .cast player .chooseGift
@[match_pattern] abbrev chooseTeamwork (player : PlayerId) : Pending := .cast player .chooseTeamwork
@[match_pattern] abbrev chooseTeamworkCreatures (player : PlayerId) (need : Nat) : Pending := .cast player (.chooseTeamworkCreatures need)

-- ResolvePending aliases
@[match_pattern] abbrev sacrificeCreature (player : PlayerId) : Pending := .resolve player .sacrificeCreature
@[match_pattern] abbrev lookLibrary (player : PlayerId) (count : Nat) (surveil : Bool := false) : Pending :=
  .resolve player (.lookLibrary count surveil)
@[match_pattern] abbrev scry (player : PlayerId) (count : Nat) : Pending := .resolve player (.scry count)
@[match_pattern] abbrev surveil (player : PlayerId) (count : Nat) : Pending := .resolve player (.surveil count)
@[match_pattern] abbrev mayCostDraw (player : PlayerId) (drawCount : Nat) (sacArtifact : Bool := false) : Pending :=
  .resolve player (.mayCostDraw drawCount sacArtifact)
@[match_pattern] abbrev mayDiscardDraw (player : PlayerId) (drawCount : Nat) : Pending := .resolve player (.mayDiscardDraw drawCount)
@[match_pattern] abbrev chooseSacrificeCreature (player : PlayerId) (chosen : Array ObjectId) (remaining : Array PlayerId) : Pending :=
  .resolve player (.chooseSacrificeCreature chosen remaining)
@[match_pattern] abbrev chooseDiscardCard (player : PlayerId) (remaining : Array PlayerId) : Pending := .resolve player (.chooseDiscardCard remaining)
@[match_pattern] abbrev mayPayGeneric (player : PlayerId) (n : Nat) : Pending := .resolve player (.mayPayGeneric n)
@[match_pattern] abbrev chooseLibraryPlacement (player : PlayerId) (id : ObjectId) : Pending := .resolve player (.chooseLibraryPlacement id)
@[match_pattern] abbrev mayAttachEquipment (player : PlayerId) (hostId : ObjectId) : Pending := .resolve player (.mayAttachEquipment hostId)
@[match_pattern] abbrev mayResolve (player : PlayerId) : Pending := .resolve player .mayResolve
@[match_pattern] abbrev tapHumans (player : PlayerId) : Pending := .resolve player .tapHumans
@[match_pattern] abbrev payOrLetCounter (player : PlayerId) (n : Nat) (spellId : ObjectId) : Pending := .resolve player (.payOrLetCounter n spellId)
@[match_pattern] abbrev payWard (player : PlayerId) (spellId : ObjectId) (cost : WardCost) : Pending := .resolve player (.payWard spellId cost)
@[match_pattern] abbrev recruitDiscard (player : PlayerId) : Pending := .resolve player .recruitDiscard
@[match_pattern] abbrev chooseRingBearer (player : PlayerId) : Pending := .resolve player .chooseRingBearer
@[match_pattern] abbrev maySacrificeAnotherBolg (player : PlayerId) (bolgId : ObjectId) : Pending := .resolve player (.maySacrificeAnotherBolg bolgId)
@[match_pattern] abbrev mayCastFromLooked (player : PlayerId) (ids : Array ObjectId) (maxMv : Int) : Pending :=
  .resolve player (.mayCastFromLooked ids maxMv)
@[match_pattern] abbrev mayPutLandFromHand (player : PlayerId) : Pending := .resolve player .mayPutLandFromHand
@[match_pattern] abbrev chooseTriggerOr (player : PlayerId) : Pending := .resolve player .chooseTriggerOr
@[match_pattern] abbrev maySacArtifactOrDiscard (player : PlayerId) (draw : Nat) : Pending := .resolve player (.maySacArtifactOrDiscard draw)
@[match_pattern] abbrev mayPutArtifactFromHand (player : PlayerId) (hostId : ObjectId) : Pending := .resolve player (.mayPutArtifactFromHand hostId)
@[match_pattern] abbrev mayHaveVillainConnive (player : PlayerId) (sourceId : ObjectId) (villainId : ObjectId) : Pending :=
  .resolve player (.mayHaveVillainConnive sourceId villainId)
@[match_pattern] abbrev mayCastExiledElseDamage (player : PlayerId) (cardId : ObjectId) (damage : Nat) : Pending :=
  .resolve player (.mayCastExiledElseDamage cardId damage)
@[match_pattern] abbrev chooseProliferate (player : PlayerId) (remaining : Nat) : Pending := .resolve player (.chooseProliferate remaining)

end Pending

end Mtg.Engine
