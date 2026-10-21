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
  /-- Shuffle this player's library. The result is a permutation
  (index 0 = bottom). An empty result keeps the current order. -/
  | shuffleLibrary (player : PlayerId)
  /-- Put these cards into `dest` in the supplied order (index 0 = first
  / bottom). An empty result keeps their current relative order. -/
  | orderInto (ids : Array ObjectId) (dest : Zone)
  /-- Choose one of these objects at random. -/
  | chooseObject (ids : Array ObjectId)
  /-- Choose a natural number `0 ≤ i < n` (a coin toss is `n = 2`). -/
  | chooseIndex (n : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Work that still belongs to an effect after a `--norandom` result is
applied. The RNG path runs the same work immediately. -/
inductive AfterRandom where
  | none
  /-- Draw `n` cards for `p` (`!gainLife`) or have `p` gain `n` life (`gainLife`). -/
  | playerAmount (p : PlayerId) (n : Nat) (gainLife : Bool := false)
  /-- Continue CR 103.3 opening shuffles (`!setStarting`) or set starting player to seat `idx` then run opening shuffles (`setStarting`). -/
  | openingStep (idx : Nat) (setStarting : Bool := false)
  /-- After this player's library is ordered, draw a new opening hand and
  continue simultaneous mulligans for `rest`. -/
  | mulliganQueue (drawn : PlayerId) (rest : Array PlayerId)
  /-- Put the chosen creature from `ids` onto the battlefield then bottom the rest (`!putOnTop`, Getaway Barrel), or put `ids` on top of `p`'s library after shuffling (`putOnTop`). -/
  | playerCards (p : PlayerId) (ids : Array ObjectId) (putOnTop : Bool := false)
  /-- Behold `subtype`; if you do, untap `landId` (Elven Passage). -/
  | beholdUntap (p : PlayerId) (landId : ObjectId) (subtype : String)
  /-- Put a +1/+1 counter on this creature after the shuffle (Restorative Technique). -/
  | plusOne (id : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

namespace AfterRandom

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
  /-- Ward `{n}` (`!orDiscard`) or Ward — discard a card or pay `{n}` (`orDiscard`). -/
  | manaOrDiscard (n : Nat) (orDiscard : Bool := false)
  /-- Non-mana ward cost: discard an enchantment/instant/sorcery (`!sacrificeLegendary && !fivePoison`), sacrifice a legendary artifact/creature (`sacrificeLegendary && !fivePoison`), get five poison counters (`!sacrificeLegendary && fivePoison`), or discard a card (`sacrificeLegendary && fivePoison`). -/
  | nonManaWard (sacrificeLegendary : Bool := false) (fivePoison : Bool := false)
  /-- Ward — sacrifice `left` more permanents; `paid` were already
  sacrificed, so the cost can no longer be declined. -/
  | sacrificePermanents (left paid : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

namespace WardCost

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
  | battlefield (tapped : Bool)
  /-- Put into hand (`!graveyard && !topAfterShuffle`), graveyard (`graveyard && !topAfterShuffle`), on top of library after shuffling (`!graveyard && topAfterShuffle`), or first onto battlefield tapped and second into hand (`graveyard && topAfterShuffle`, Troop of Ponies). -/
  | zoneDest (graveyard : Bool := false) (topAfterShuffle : Bool := false)
  /-- Exiled, linked to the source. -/
  | exileLinked (sourceId : Option ObjectId)
  /-- Onto the battlefield tapped; you may behold a `subtype`, and if you do,
  untap it (Elven Passage). -/
  | battlefieldTappedBeholdUntap (subtype : String)
  /-- Onto the battlefield from the hand or library; shuffle only if the
  library was searched (Last Light of Durin's Day). -/
  | battlefieldFromHandOrLibrary
deriving DecidableEq, Repr, Inhabited, BEq

namespace SearchDest

@[match_pattern] abbrev hand : SearchDest := .zoneDest false false
@[match_pattern] abbrev graveyard : SearchDest := .zoneDest true false
@[match_pattern] abbrev topAfterShuffle : SearchDest := .zoneDest false true
@[match_pattern] abbrev battlefieldTappedThenHand : SearchDest := .zoneDest true true

end SearchDest

/-- What to do with cards chosen from a looked-at, milled, or battlefield set. -/
inductive CardChoice where
  /-- Put the chosen cards into your hand. `mustOne` requires exactly one
  when any card can be chosen. -/
  | toHand (mustOne : Bool)
  /-- Put the chosen creature cards onto the battlefield (`!keepDestroyRest`), or keep the chosen creatures and destroy every other creature (`keepDestroyRest`). -/
  | creaturesChoice (keepDestroyRest : Bool := false)
  /-- Put the chosen lands onto the battlefield tapped, then shuffle and
  gain `life` life. -/
  | landsTappedGainLife (life : Nat)
  /-- Amass `subtype` `n` onto the chosen Army. `attach` is an Equipment to
  attach afterward (Goblin Plate Mail). -/
  | amassArmy (subtype : String) (n : Nat) (attach : Option ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

namespace CardChoice

@[match_pattern] abbrev creaturesToBattlefield : CardChoice := .creaturesChoice false
@[match_pattern] abbrev keepDestroyRest : CardChoice := .creaturesChoice true

end CardChoice

/-- Library, search, reveal, and draw choices made while an effect resolves (CR 401 / CR 701.19). -/
inductive LibraryChoice where
  /-- Optional draw or wheel choice: draw `n` then discard `discard` (`!wheel && !eachOppDraws`), draw `n` then each opponent draws (`!wheel && eachOppDraws`), or wheel hand for `n` with `rest` (`wheel`). -/
  | mayDrawOrWheel (n : Nat) (discard : Nat := 0) (rest : Array PlayerId := #[]) (eachOppDraws : Bool := false) (wheel : Bool := false)
  /-- Single-object library choice: top/bottom with `damage` (`damageChoice = true`), Palantír draw (`!damageChoice && !trickster`), or Trickster's Stratagem (`!damageChoice && trickster`). -/
  | objectLibraryChoice (id : ObjectId) (player : PlayerId := ⟨0⟩) (damage : Nat := 0) (connive : Option ObjectId := none) (trickster : Bool := false) (damageChoice : Bool := false)
  /-- Reveal two cards with different names from outside the game (`extrapolate = true`), or exile the top card of your library (`extrapolate = false`, Daredevil). -/
  | mayExileTopOrReveal (sourceId : Option ObjectId := none) (extrapolate : Bool := false)
  /-- Card-array library choice: begin on battlefield (`false, false, false`), Nick Fury transform (`true, false, false`), order bottom (`false, true, false`), Riddles split (`true, true, false`), or extrapolate pick (`extrapolate = true`). -/
  | cardArrayChoice (ids : Array ObjectId) (permanentId : ObjectId := ⟨0⟩) (revealer : PlayerId := ⟨0⟩) (alt : Bool := false) (arrange : Bool := false) (extrapolate : Bool := false)
  /-- Reveal one of `eligible` from `looked` to hand (`!putCreatures && !nickFury`, `flag = anyOrder`), put creature cards from `eligible` onto the battlefield (`putCreatures`, `flag = anyNumber`), or put one of `eligible` onto the battlefield then bottom the rest (`nickFury`, Nick Fury). -/
  | revealSelect (looked eligible : Array ObjectId) (flag : Bool := false) (putCreatures : Bool := false) (nickFury : Bool := false)
  /-- Search (`!optional`) or optional "you may search" (`optional`, Old Thrush): choose up to `count` of `eligible` (or none, CR 701.19b), send them to `dest`, shuffle, then do `after`. -/
  | searchChoice (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) (optional : Bool := false)
  /-- Vision Quest zones (`!visionPick && !riddles`), Vision Quest pick (`visionPick`), or Riddles choose pile (`riddles`). -/
  | twoArrayOrVisionChoice (ids1 : Array ObjectId) (ids2 : Array ObjectId := #[]) (x : Nat := 0) (controller : PlayerId := ⟨0⟩) (shuffle : Bool := false) (visionPick : Bool := false) (riddles : Bool := false)
  /-- Choose up to `max` of `ids`. `purpose` says what the chosen cards do. -/
  | chooseCards (ids : Array ObjectId) (max : Nat) (purpose : CardChoice)
deriving Repr, Inhabited, BEq

namespace LibraryChoice

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
  /-- Choose a card from `victim`'s revealed hand to discard (`!exile`, nonland permanent if `permanentOnly`) or exile linked to `sourceId` (`exile`, Null Summoner). -/
  | revealedHandChoice (victim : PlayerId) (permanentOnly : Bool := false) (exile : Bool := false) (sourceId : Option ObjectId := none)
  /-- Single-object or boast-exile choice: Sphinx's Approach (`false, false, false`), cast copy (`true, false, false`), Moonstone exile (`false, true, false`), or Zemo boast exile (`zemo = true`). -/
  | singleOrPairObjectChoice (id : ObjectId) (sourceId : ObjectId := ⟨0⟩) (castCopy : Bool := false) (moonstone : Bool := false) (zemo : Bool := false)
  /-- You may discard a card; if you do, do `next`. -/
  | mayDiscardThen (next : Resolution) (sourceId : Option ObjectId)
  /-- Discard action choice: discard then draw (`false, false, false`), discard hand draw `n` (`true, false, false`), discard `n` then stun (`false, true, false`), discard with cause (`false, false, true`), or Balin discard hand (`true, false, true`). -/
  | discardActionChoice (n : Nat := 0) (sourceId : Option ObjectId := none) (alt1 : Bool := false) (alt2 : Bool := false) (withSource : Bool := false)
  /-- Counted card-list choice: discard `n` of `ids` (`false, false`), cast up to `n` from exile (`true, false`), cast copies free with budget `n` and `m` left (`false, true`), or take milled card then gain `n` life (`true, true`). -/
  | countedCardsChoice (ids : Array ObjectId) (n : Nat) (m : Nat := 0) (castFromExileOrMilled : Bool := false) (copiesOrMilled : Bool := false)
  /-- Cast one of `eligible` (`zoneCards = false`: `withoutPaying`, `exileInstead = exileInsteadOrFromHand`; `zoneCards = true`: from graveyard paying cost if `!exileInsteadOrFromHand`, or from hand free if `exileInsteadOrFromHand`). -/
  | mayCastEligible (eligible : Array ObjectId) (withoutPaying : Bool := false) (exileInsteadOrFromHand : Bool := false) (zoneCards : Bool := false)
  /-- Cascade/Gríma hit cast (`!discardTwo`) or opponent discard-two choice (`discardTwo = true`). -/
  | hitOrMultiDiscardChoice (cardId : ObjectId := ⟨0⟩) (others : Array ObjectId := #[]) (rest : Array PlayerId := #[]) (draws : Nat := 0) (victim : Option PlayerId := none) (controller : PlayerId := ⟨0⟩) (discardTwo : Bool := false)
deriving Repr, Inhabited, BEq

namespace HandGraveyardChoice

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
  /-- Sacrifice planeswalker (`false, false`), odd/even destroy (`true, false`), or Black Widow counter/exile (`widow = true`). -/
  | optionalSourceChoice (sourceId : Option ObjectId := none) (exiled : Option ObjectId := none) (oddEven : Bool := false) (widow : Bool := false)
  /-- You may sacrifice a permanent of `kind` (`!tapSource`) or tap the untapped source (`tapSource`); if you do, do `next`. -/
  | mayPermanentCostThen (next : Resolution) (sourceId : Option ObjectId) (kind : ObjectSelector := .source) (tapSource : Bool := false)
  /-- Single/pair object battlefield choice: remove +1/+1 (`false, false, false`), Ultron pay (`true, false, false`), sacrifice another (`_, true, false`), move all counters (`false, false, true`), or crew (`true, false, true`). -/
  | objectBattlefieldChoice (id : ObjectId) (otherId : ObjectId := ⟨0⟩) (power : Nat := 0) (alt1 : Bool := false) (alt2 : Bool := false) (moveOrCrew : Bool := false)
  /-- Multi-player or player-choice battlefield step: sacrifice each (`!worldsOrBlackGate`), Worlds Within Worlds (`false, false, true`), or Black Gate player (`true, false, true`). -/
  | playerBattlefieldChoice (rest : Array PlayerId) (ids : Array ObjectId := #[]) (exiled : Array ObjectId := #[]) (chosen : Array ObjectId := #[]) (controller : PlayerId := ⟨0⟩) (creatureId : ObjectId := ⟨0⟩) (sourceId : Option ObjectId := none) (alt1 : Bool := false) (alt2 : Bool := false) (worldsOrBlackGate : Bool := false)
  /-- Choose from `ids`: least-power sacrifice (`false, false, false`), remove counter (`true, false, false`), sacrifice `n` (`false, true, false`), attach Equipment to `hostId` (`false, false, true`), or put Hero from hand (`true, false, true`). -/
  | chooseFromObjects (ids : Array ObjectId) (n : Nat := 0) (hostId : ObjectId := ⟨0⟩) (removeOrHero : Bool := false) (sacThese : Bool := false) (attachOrHero : Bool := false)
  /-- You may create `n` tokens of `kind`. -/
  | mayCreateTokens (kind : TokenKind) (n : Nat)
  /-- Become base `p`/`t` until end of turn (`!sheHulk`) or She-Hulk deal `p` damage to `target` (`sheHulk = true`). -/
  | intBattlefieldChoice (p : Int) (t : Int := 0) (objectId : ObjectId := ⟨0⟩) (target : Target := .player ⟨0⟩) (sourceId : Option ObjectId := none) (sheHulk : Bool := false)
  /-- Choose one creature type among `types`, then return every creature that
  isn't that type (Raise the Palisade). -/
  | palisadeCreatureType (types : Array String)
deriving Repr, Inhabited, BEq

namespace BattlefieldChoice

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
  /-- You may do `next` (`mana = none`) or pay `{n}` to do `next` (`mana = some n`). -/
  | mayResolveOrPayThen (next : Resolution) (sourceId : Option ObjectId) (mana : Option Nat := none)
  /-- Mode or copy-target choice: available option (`!multi && !copyTargets`), multi-modes (`multi`), or new targets for copies (`copyTargets`). -/
  | modeOrCopyTargetsChoice (objectId : ObjectId := ⟨0⟩) (nats : Array Nat := #[]) (remaining : Nat := 0) (sourceId : Option ObjectId := none) (copies : Array ObjectId := #[]) (alt1 : Bool := false) (alt2 : Bool := false) (multi : Bool := false) (copyTargets : Bool := false)
  /-- As-enters (`!natChoice && !special`), object-nat (`natChoice`), or special cost/mode (`special`) choice. -/
  | objectOrSpecialModeChoice (objectId : ObjectId := ⟨0⟩) (n : Nat := 0) (sourceId : Option ObjectId := none) (alt1 : Bool := false) (alt2 : Bool := false) (natChoice : Bool := false) (special : Bool := false)
  /-- Choose what to pay `picks[0]` of the proposed activation's cost with,
  then the rest (CR 601.2h). `paid` is true once one has been paid, after
  which the activation can no longer be cancelled. -/
  | costPicks (sourceId : ObjectId) (picks : Array CostPick) (paid : Bool)
  /-- You may pay `pick` (sacrifice, discard, …) as an ability of `sourceId`
  resolves; when you do, do `next`. -/
  | mayPayPickThen (pick : CostPick) (next : Resolution) (sourceId : ObjectId)
  /-- Choose a creature type you control. `types` are offered by index
  (Orcrist). Answered with `Action.chooseMode` or `Action.chooseName`. -/
  | chooseCreatureType (types : Array String)
  /-- You may pay `symbols` to do `next` (`!reflexive`, Silvan Reveler) or up to `maxTimes` times for reflexive ability `kind` (`reflexive = true`). -/
  | mayPaySymbolsChoice (symbols : Array ManaSymbol) (next : Resolution := .unrecognized) (sourceId : ObjectId := ⟨0⟩) (optSourceId : Option ObjectId := none) (maxTimes : Nat := 0) (kind : Nat := 0) (reflexive : Bool := false)
  /-- Choose the color of each of `left` more mana to add, spendable only as
  `use` allows. Answered with `Action.chooseMode` (white, blue, black, red,
  green by index). -/
  | addManaColors (left : Nat) (use : FraManaUse)
deriving Repr, Inhabited, BEq

namespace CostModeChoice

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
  /-- Hand, discard, graveyard, or exile cast choice (CR 402 / CR 404 / CR 406). -/
  | handGraveyard (c : HandGraveyardChoice)
  /-- Library, search, reveal, or draw choice (CR 401 / CR 701.19). -/
  | library (c : LibraryChoice)
  /-- Battlefield, sacrifice, counter, or permanent choice (CR 403 / CR 701.17). -/
  | battlefield (c : BattlefieldChoice)
  /-- Cost, mode, enters, or target choice (CR 118 / CR 601.2 / CR 614.12 / CR 700.2). -/
  | costMode (c : CostModeChoice)
deriving Repr, Inhabited, BEq

namespace FraChoice

-- LibraryChoice aliases
@[match_pattern] abbrev mayWheel (n : Nat) (rest : Array PlayerId) : FraChoice := .library (.mayWheel n rest)
@[match_pattern] abbrev topOrBottomDamage (id : ObjectId) (damage : Nat) : FraChoice := .library (.topOrBottomDamage id damage)
@[match_pattern] abbrev extrapolateReveal : FraChoice := .library .extrapolateReveal
@[match_pattern] abbrev extrapolatePick (revealer : PlayerId) (ids : Array ObjectId) : FraChoice := .library (.extrapolatePick revealer ids)
@[match_pattern] abbrev mayDrawThenDiscard (draw discard : Nat) : FraChoice := .library (.mayDrawThenDiscard draw discard)
@[match_pattern] abbrev revealSelect (looked eligible : Array ObjectId) (flag : Bool) (putCreatures : Bool := false) : FraChoice :=
  .library (.revealSelect looked eligible flag putCreatures)
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
  /-- Declare attackers (`!blockers`, CR 508.1) or blockers (`blockers`, CR 509.1). -/
  | declareCombatStep (blockers : Bool := false)
  /-- Player boolean step: declare mulligan (`false, false`, CR 103.5), order waiting triggers (`true, false`, CR 603.3b), or assign combat damage (`combatDamage = true`, for attackers if `flag`, CR 510.1c–d). -/
  | playerBooleanStep (player : PlayerId) (flag : Bool := false) (combatDamage : Bool := false)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player chooses which of these legendary permanents with the same
  name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
  | chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

namespace TurnCombatPending

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
  /-- Core announcement (`!additional && !teamwork`), additional/optional cost (`additional`), or teamwork (`teamwork`) step. -/
  | castStep (alt1 : Bool := false) (alt2 : Bool := false) (additional : Bool := false) (teamwork : Bool := false)
  /-- Sacrifice permanent for cost (`!teamworkCreatures`) or choose `need` creatures for teamwork (`teamworkCreatures`, CR 702.194). -/
  | costObjectsStep (sourceId : ObjectId := ⟨0⟩) (need : Nat := 0) (teamworkCreatures : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

namespace CastPending

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
  /-- Resolution prompt: sacrifice creature (`false, false, false`), resolve `mayEffect` (`true, false, false`), tap Humans (`false, true, false`), recruit discard (`true, true, false`), Ring-bearer (`false, false, true`), put land from hand (`true, false, true`), or `TriggerResolution.or` (`false, true, true`). -/
  | resolvePrompt (alt1 : Bool := false) (alt2 : Bool := false) (ringOrLand : Bool := false)
  /-- Numeric resolution choice: scry/surveil (`false, false`), discard/sacrifice draw (`true, false`), or pay generic / proliferate (`false, true`). -/
  | natResolveChoice (n : Nat) (alt : Bool := false) (costDraw : Bool := false) (payOrProlif : Bool := false)
  /-- This player must sacrifice a creature they control. `chosen` are
  already-selected sacrifices; `remaining` are later players in APNAP order. -/
  | chooseSacrificeCreature (chosen : Array ObjectId) (remaining : Array PlayerId)
  /-- This player must discard a card. `remaining` are later opponents. -/
  | chooseDiscardCard (remaining : Array PlayerId)
  /-- Single/pair object resolution choice: library placement / Bolg sacrifice (`false, false`), attach Equipment / put artifact (`true, false`), or Villain connive (`connive = true`). -/
  | objectResolveChoice (id : ObjectId) (villainId : ObjectId := ⟨0⟩) (alt : Bool := false) (equipOrArt : Bool := false) (connive : Bool := false)
  /-- Pay `{n}` or let `id` be countered (`!castExiled`), or cast exiled `id` else deal `n` damage to each opponent (`castExiled`, Chandra). -/
  | payOrExileChoice (n : Nat) (id : ObjectId) (castExiled : Bool := false)
  /-- Pay this ward cost or let the targeting spell or ability be countered
  (CR 702.21). -/
  | payWard (spellId : ObjectId) (cost : WardCost)
  /-- You may cast one of these looked-at library cards without paying its
  mana cost as the ability resolves (Cosmic Cube; MSH 356). `maxMv` is the
  greatest power among attacking creatures you control. -/
  | mayCastFromLooked (ids : Array ObjectId) (maxMv : Int)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ResolvePending

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
  | none
  /-- Turn-based, combat, mulligan, state-based action, or trigger-stacking choice (CR 103 / CR 508–510 / CR 603.3b / CR 704.5j). -/
  | turnCombat (step : TurnCombatPending)
  /-- Spell casting or ability activation announcement step (CR 601.2 / CR 602.2 / CR 702). -/
  | cast (player : PlayerId) (step : CastPending)
  /-- Resolution, keyword action, or trigger choice (CR 608 / CR 701). -/
  | resolve (player : PlayerId) (choice : ResolvePending)
  /-- A Reality Fracture choice made while an effect resolves. -/
  | fraChoice (player : PlayerId) (choice : FraChoice)
  /-- A random event must be resolved by supplying its result (`--norandom`). -/
  | resolveRandom (req : RandomRequest)
deriving Repr, Inhabited, BEq

namespace Pending

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
