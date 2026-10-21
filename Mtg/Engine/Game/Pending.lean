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
  /-- The player may discard their hand and draw `n`; `rest` choose after. -/
  | mayWheel (n : Nat) (rest : Array PlayerId)
  /-- The owner of `id` puts it on top (accept) or on the bottom (decline) of
  their library; on top, they are dealt `damage`. -/
  | topOrBottomDamage (id : ObjectId) (damage : Nat)
  /-- You may reveal two cards with different names from outside the game. -/
  | extrapolateReveal
  /-- Choose one of `ids` for `revealer` to put into their hand. -/
  | extrapolatePick (revealer : PlayerId) (ids : Array ObjectId)
  /-- You may draw `draw` cards; if you do, discard `discard` cards. -/
  | mayDrawThenDiscard (draw discard : Nat)
  /-- Reveal one of `eligible` from `looked` to hand (`!putCreatures`, `flag = anyOrder`), or put creature cards from `eligible` onto the battlefield (`putCreatures`, `flag = anyNumber`). -/
  | revealSelect (looked eligible : Array ObjectId) (flag : Bool) (putCreatures : Bool := false)
  /-- You may put one of `eligible` onto the battlefield (Nick Fury). The rest
  of `looked` go on the bottom in a random order. -/
  | nickFuryPut (looked eligible : Array ObjectId)
  /-- You may transform the double-faced card just put onto the battlefield,
  then the other looked-at cards go on the bottom in a random order. -/
  | nickFuryMayTransform (permanentId : ObjectId) (rest : Array ObjectId)
  /-- Put `ids` on the bottom of your library (`!splitPiles`), or separate `ids` into face-up and face-down piles (`splitPiles`, Riddles in the Dark). -/
  | arrangeCards (ids : Array ObjectId) (splitPiles : Bool := false)
  /-- Search (`!optional`) or optional "you may search" (`optional`, Old Thrush): choose up to `count` of `eligible` (or none, CR 701.19b), send them to `dest`, shuffle, then do `after`. -/
  | searchChoice (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) (optional : Bool := false)
  /-- Palantír of Orthanc: this opponent may have `controller` draw a card.
  Declining mills X cards and this player loses life equal to their mana values. -/
  | palantirMayDraw (controller : PlayerId) (sourceId : ObjectId)
  /-- The owner puts `creatureId` second from the top (accept / choose top)
  or on the bottom (decline / choose bottom), then `caster` connives
  `connive` (Trickster's Stratagem). -/
  | tricksterLibrary (caster : PlayerId) (creatureId : ObjectId)
      (connive : Option ObjectId)
  /-- You may draw `n` cards. If you do, each opponent draws a card (Armor Wars). -/
  | mayDrawThenEachOpponentDraws (n : Nat)
  /-- Search the library as well as the graveyard (accept), or only the
  graveyard (decline), for Vision Quest. -/
  | visionQuestZones (libIds gyIds : Array ObjectId) (x : Nat)
  /-- Put one of these artifact creatures onto the battlefield with `x`
  +1/+1 counters. Shuffle afterward when `shuffle` is true. -/
  | visionQuestPick (ids : Array ObjectId) (x : Nat) (shuffle : Bool)
  /-- You may exile the top card of your library (Daredevil). -/
  | daredevilMayExile (sourceId : Option ObjectId)
  /-- An opponent chooses the face-up pile (accept) or the face-down pile
  (decline) for `controller`'s hand. -/
  | riddlesChoosePile (controller : PlayerId) (faceUp faceDown : Array ObjectId)
  /-- Choose up to `max` of `ids`. `purpose` says what the chosen cards do. -/
  | chooseCards (ids : Array ObjectId) (max : Nat) (purpose : CardChoice)
  /-- You may begin the game with the first of these cards on the battlefield
  (Quicksilver). The rest are asked next. -/
  | mayBeginOnBattlefield (ids : Array ObjectId)
deriving Repr, Inhabited, BEq

namespace LibraryChoice

@[match_pattern] abbrev mayRevealToHand (looked eligible : Array ObjectId) (anyOrder : Bool) : LibraryChoice :=
  .revealSelect looked eligible anyOrder false
@[match_pattern] abbrev revealPutCreatures (looked creatures : Array ObjectId) (anyNumber : Bool) : LibraryChoice :=
  .revealSelect looked creatures anyNumber true
@[match_pattern] abbrev orderLibraryBottom (ids : Array ObjectId) : LibraryChoice := .arrangeCards ids false
@[match_pattern] abbrev riddlesSplit (looked : Array ObjectId) : LibraryChoice := .arrangeCards looked true
@[match_pattern] abbrev searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) : LibraryChoice :=
  .searchChoice eligible count dest after kind false
@[match_pattern] abbrev maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option Resolution) (kind : String) : LibraryChoice :=
  .searchChoice eligible count dest after kind true

end LibraryChoice

/-- Hand, discard, graveyard, and exile cast choices made while an effect resolves (CR 402 / CR 404 / CR 406). -/
inductive HandGraveyardChoice where
  /-- Choose a card from `target`'s revealed hand for them to discard: a
  nonland permanent card if `permanentOnly`, else a nonland card. -/
  | discardFromRevealedHand (target : PlayerId) (permanentOnly : Bool)
  /-- You may exile `id` and four other cards named Sphinx's Approach (`!castCopy`), or cast this copy of an exiled card without paying its mana cost (`castCopy`, Saruman of Many Colors). -/
  | mayExileOrCastCopy (id : ObjectId) (castCopy : Bool := false)
  /-- You may discard a card; if you do, do `next`. -/
  | mayDiscardThen (next : Resolution) (sourceId : Option ObjectId)
  /-- Discard a card then draw and put +1/+1 counters on `id` (`!entireHand`), or optionally discard your hand to draw that many cards (`entireHand`, Balin). -/
  | discardWithSource (id : Option ObjectId) (entireHand : Bool := false)
  /-- Discard `n` cards, then tap and stun up to as many target creatures as
  nonland cards were discarded (Seasoned Cryomancer). -/
  | discardThenStun (n : Nat) (sourceId : Option ObjectId)
  /-- Choose a nonland card from `victim`'s revealed hand to exile, linked to
  `sourceId` (Null Summoner). -/
  | exileFromRevealedHand (victim : PlayerId) (sourceId : Option ObjectId)
  /-- Cast up to `castsLeft` of the copies `ids` with total mana value at
  most `budget` without paying their mana costs (Uldaros Theorix, Baron
  Helmut Zemo). -/
  | castCopiesFree (ids : Array ObjectId) (budget : Nat) (castsLeft : Nat)
  /-- The choosing opponent discards two cards; `controller` draws a card for
  each opponent who didn't discard two nonland cards. -/
  | discardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat)
  /-- You may discard `n` of `ids` (`!castFromExile`), or cast up to `n` more of these exiled cards without paying their mana costs (`castFromExile`, Doom Reigns Supreme). -/
  | mayDiscardOrCastUpTo (ids : Array ObjectId) (n : Nat) (castFromExile : Bool := false)
  /-- You may cast one of `eligible` from your graveyard paying its cost (`!fromHand`, Bilbo), or cast an instant/sorcery from `eligible` in hand without paying its mana cost (`fromHand`, Gandalf / Glamdring). -/
  | mayCastZoneCards (eligible : Array ObjectId) (fromHand : Bool := false)
  /-- You may cast one of these cards. `withoutPaying` skips the mana cost.
  An instant or sorcery is exiled instead of going to the graveyard when
  `exileInstead` is set. -/
  | mayCastCards (eligible : Array ObjectId) (withoutPaying exileInstead : Bool)
  /-- Discard a card, then draw a card. -/
  | discardThenDraw
  /-- Choose the black cards to exile from your graveyard to pay the boast
  ability `abilityId` of `sourceId`. Declining cancels the activation. -/
  | zemoBoastExile (abilityId sourceId : ObjectId)
  /-- Cascade: you may cast `cardId` without paying its mana cost; `others`
  and an uncast `cardId` go on the bottom in a random order (CR 702.85a). -/
  | mayCastCascade (cardId : ObjectId) (others : Array ObjectId)
  /-- Gríma: you may cast `cardId` without paying its mana cost. `others`,
  and `cardId` if it isn't cast, go on the bottom of `victim`'s library
  in a random order. -/
  | mayCastGrima (cardId : ObjectId) (others : Array ObjectId) (victim : PlayerId)
  /-- You may discard your hand. If you do, draw `n` cards (Sauron). -/
  | mayDiscardHandDrawFixed (n : Nat)
  /-- You may exile the discarded card and play it until the end of your next
  turn (Moonstone). -/
  | moonstoneMayExile (cardId : ObjectId)
  /-- You may put one of these milled cards into your hand, then gain `lifeAfter`
  life (Rapid Rescue, Rick Jones). Declining still gains the life. -/
  | mayTakeMilled (ids : Array ObjectId) (lifeAfter : Nat)
deriving Repr, Inhabited, BEq

namespace HandGraveyardChoice

@[match_pattern] abbrev sphinxsApproach (spellId : ObjectId) : HandGraveyardChoice := .mayExileOrCastCopy spellId false
@[match_pattern] abbrev mayCastCopy (copyId : ObjectId) : HandGraveyardChoice := .mayExileOrCastCopy copyId true
@[match_pattern] abbrev discardThen (causeId : Option ObjectId) : HandGraveyardChoice := .discardWithSource causeId false
@[match_pattern] abbrev mayDiscardHandBalin (sourceId : Option ObjectId) : HandGraveyardChoice := .discardWithSource sourceId true
@[match_pattern] abbrev mayDiscardThese (n : Nat) (ids : Array ObjectId) : HandGraveyardChoice := .mayDiscardOrCastUpTo ids n false
@[match_pattern] abbrev mayCastUpToFromExile (eligible : Array ObjectId) (left : Nat) : HandGraveyardChoice :=
  .mayDiscardOrCastUpTo eligible left true
@[match_pattern] abbrev mayCastFromGraveyard (eligible : Array ObjectId) : HandGraveyardChoice := .mayCastZoneCards eligible false
@[match_pattern] abbrev mayCastInstantSorceryFromHand (eligible : Array ObjectId) : HandGraveyardChoice := .mayCastZoneCards eligible true

end HandGraveyardChoice

/-- Battlefield, sacrifice, counter, and permanent choices made while an effect resolves (CR 403 / CR 701.17). -/
inductive BattlefieldChoice where
  /-- You may sacrifice a planeswalker to search for one (Entrust the Spark). -/
  | maySacrificePlaneswalker
  /-- You may sacrifice a permanent of `kind` (land, creature or planeswalker);
  if you do, do `next`. -/
  | maySacrificeThen (kind : ObjectSelector) (next : Resolution)
    (sourceId : Option ObjectId)
  /-- You may remove a +1/+1 counter from `id` (`!ultronPay`, Guiding Hydra), or pay {2} to copy the nontoken artifact `id` that entered (`ultronPay`, Ultron). -/
  | mayObjectAction (id : ObjectId) (ultronPay : Bool := false)
  /-- Each player sacrifices a creature of their choice; `controller` creates
  a 4/4 Beast if they sacrificed one (Garruk, Veiled Butcher). `chosen` are
  sacrificed together once everyone has chosen. -/
  | sacrificeCreatureEach (controller : PlayerId) (rest : Array PlayerId)
    (chosen : Array ObjectId)
  /-- You may move all counters from `fromId` onto `toId` (The Ozolith). -/
  | mayMoveAllCounters (fromId toId : ObjectId)
  /-- Tap untapped creatures with total power `power` or more to pay the crew
  cost of `vehicleId`'s ability `abilityId` (CR 702.122). Declining cancels
  the activation. -/
  | crew (abilityId vehicleId : ObjectId) (power : Nat)
  /-- You may sacrifice another creature for +1/+1 counters equal to its power (`!forDrawTreasure`, Rhovanion Rampager), or sacrifice another creature/artifact to draw a card and create a Treasure (`forDrawTreasure`, The Sackville-Bagginses). -/
  | maySacrificeAnother (sourceId : ObjectId) (forDrawTreasure : Bool := false)
  /-- You may sacrifice `n` of `ids`. Declining pays nothing. -/
  | maySacrificeThese (n : Nat) (ids : Array ObjectId)
  /-- Choose any number of Equipment to attach to `hostId`. Declining
  attaches none (Thorin, Mountain-king). -/
  | attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId)
  /-- Choose one of the tied least-power creatures to sacrifice (`!removeCounter`), or remove one counter from one of these creatures then draw (`removeCounter`, Mister Hyde). -/
  | chooseCreatureFrom (ids : Array ObjectId) (removeCounter : Bool := false)
  /-- Each player in turn sacrifices a nontoken creature of their choice;
  `chosen` are sacrificed together at the end (The Serpent Society). -/
  | sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId)
  /-- You may create `n` tokens of `kind`. -/
  | mayCreateTokens (kind : TokenKind) (n : Nat)
  /-- You may have `objectId`'s base power and toughness become `p`/`t`
  until end of turn. -/
  | mayBecomeBasePT (objectId : ObjectId) (p t : Int)
  /-- You may tap the untapped source; if you do, do `next`. -/
  | mayTapSourceThen (next : Resolution) (sourceId : ObjectId)
  /-- Sacrifice one creature that dealt combat damage to `controller`. The
  other opponents in `rest` choose next, then the Ring tempts `controller`
  (Witch-king of Angmar). -/
  | sacrificeDamager (ids : Array ObjectId) (rest : Array PlayerId)
    (controller : PlayerId)
  /-- You may have The Sensational She-Hulk deal `amount` damage to `target`.
  Accepting is the once-each-turn action (MSH 448). -/
  | sheHulkMayDamage (amount : Int) (target : Target) (sourceId : Option ObjectId)
  /-- You may put a +1/+1 counter on Black Widow. If you don't, you may cast
  `exiled` until end of turn. -/
  | widowMayCounter (sourceId : Option ObjectId) (exiled : Option ObjectId)
  /-- You may put one of these Hero cards from your hand onto the battlefield.
  If you don't, draw a card (Origin of the Avengers). -/
  | mayPutHeroFromHandOrDraw (ids : Array ObjectId)
  /-- Choose even (mode 0) or odd (mode 1), then destroy each other creature
  whose mana value has that quality (Thanos). -/
  | oddOrEvenDestroy (sourceId : Option ObjectId)
  /-- Choose one creature type among `types`, then return every creature that
  isn't that type (Raise the Palisade). -/
  | palisadeCreatureType (types : Array String)
  /-- `eligible` are this player's creature cards in hand. `rest` choose next.
  `exiled` return to their owners' hands after `chosen` enter (Worlds Within
  Worlds). -/
  | worldsPutCreatures (eligible : Array ObjectId) (rest : Array PlayerId)
      (exiled chosen : Array ObjectId) (sourceId : Option ObjectId)
  /-- Choose a player tied for most life. The creature can't be blocked by
  that player's creatures this turn (The Black Gate). -/
  | blackGatePlayer (creatureId : ObjectId) (players : Array PlayerId)
deriving Repr, Inhabited, BEq

namespace BattlefieldChoice

@[match_pattern] abbrev mayMovePlusOne (sourceId : ObjectId) : BattlefieldChoice := .mayObjectAction sourceId false
@[match_pattern] abbrev ultronMayPay (artifactId : ObjectId) : BattlefieldChoice := .mayObjectAction artifactId true
@[match_pattern] abbrev maySacrificeAnotherCreatureForPower (sourceId : ObjectId) : BattlefieldChoice :=
  .maySacrificeAnother sourceId false
@[match_pattern] abbrev maySacrificeAnotherForDrawTreasure (sourceId : ObjectId) : BattlefieldChoice :=
  .maySacrificeAnother sourceId true
@[match_pattern] abbrev sacrificeLeastPower (ids : Array ObjectId) : BattlefieldChoice := .chooseCreatureFrom ids false
@[match_pattern] abbrev hydeRemoveCounter (ids : Array ObjectId) : BattlefieldChoice := .chooseCreatureFrom ids true

end BattlefieldChoice

/-- Cost, mode, enters, and target choices made while an effect resolves (CR 118 / CR 601.2 / CR 614.12 / CR 700.2). -/
inductive CostModeChoice where
  /-- You may do `next` (accept or decline). -/
  | mayThen (next : Resolution) (sourceId : Option ObjectId)
  /-- You may pay `{n}`; if you do, do `next`. -/
  | mayPayThen (n : Nat) (next : Resolution) (sourceId : Option ObjectId)
  /-- Choose an available mode or keyword option for `objectId`: Alliance mode (`!gollum && !keywordOrVision`), Gollum mode (`gollum && !keywordOrVision`), keyword option (`!gollum && keywordOrVision`), or Vision mode (`gollum && keywordOrVision`). -/
  | chooseAvailableOption (objectId : ObjectId) (available : Array Nat)
      (gollum : Bool := false) (keywordOrVision : Bool := false)
  /-- Choose `remaining` more modes for the triggered ability `objectId`
  from `CardDef.fraTriggerModes` of its source. -/
  | triggerModes (objectId : ObjectId) (remaining : Nat) (chosen : Array Nat)
  /-- As `objectId` enters (CR 614.12), choose a color (`!cardName && !creatureTypeOrOddEven`), card name (`cardName && !creatureTypeOrOddEven`), creature type (`!cardName && creatureTypeOrOddEven`), or odd/even (`cardName && creatureTypeOrOddEven`). -/
  | asEntersChoice (objectId : ObjectId) (cardName : Bool := false) (creatureTypeOrOddEven : Bool := false)
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
  /-- You may pay `symbols`. If you do, do `next` (Silvan Reveler). -/
  | mayPaySymbolsThen (symbols : Array ManaSymbol) (next : Resolution) (sourceId : ObjectId)
  /-- Choose the color of each of `left` more mana to add, spendable only as
  `use` allows. Answered with `Action.chooseMode` (white, blue, black, red,
  green by index). -/
  | addManaColors (left : Nat) (use : FraManaUse)
  /-- Pay `n` life or `id` enters tapped (`!changeTarget`), or optionally change target slot `n` of spell `id` (`changeTarget`, Speedball). -/
  | objectNatChoice (id : ObjectId) (n : Nat) (changeTarget : Bool := false)
  /-- Extort: you may pay {W/B}; if you do, drain each opponent for 1. -/
  | mayPayExtort (sourceId : Option ObjectId)
  /-- You may pay `cost` up to `maxTimes` times (accept pays once; a mode
  index pays that many times); when you do, the reflexive ability `kind`
  triggers. -/
  | mayPayManaForReflexive (cost : Array ManaSymbol) (maxTimes : Nat) (kind : Nat)
    (sourceId : Option ObjectId)
  /-- Choose up to `left` more different modes of Hawkeye's Trick Arrows
  (0 Net, 1 Explosive, 2 Boomerang); decline to stop. -/
  | hawkeyeModes (left : Nat) (chosen : Array Nat) (sourceId : Option ObjectId)
  /-- Mister Hyde: choose mode 0 (+1/+1 counter) or 1 (remove a counter
  and draw). -/
  | hydeMode (sourceId : ObjectId)
  /-- You may pay 2 life so creatures you control assign combat damage equal
  to their toughness (The Kingpin of Crime). -/
  | kingpinMayPay2Life
  /-- Choose a new target for the first of `copies`, or decline to keep its
  target; then the rest. -/
  | newTargetsForCopies (copies : Array ObjectId)
deriving Repr, Inhabited, BEq

namespace CostModeChoice

@[match_pattern] abbrev allianceMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available false false
@[match_pattern] abbrev gollumMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available true false
@[match_pattern] abbrev chooseKeyword (objectId : ObjectId) (options : Array Nat) : CostModeChoice :=
  .chooseAvailableOption objectId options false true
@[match_pattern] abbrev visionMode (sourceId : ObjectId) (available : Array Nat) : CostModeChoice :=
  .chooseAvailableOption sourceId available true true
@[match_pattern] abbrev chooseColor (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId false false
@[match_pattern] abbrev chooseCardName (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId true false
@[match_pattern] abbrev entersCreatureType (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId false true
@[match_pattern] abbrev entersOddEven (objectId : ObjectId) : CostModeChoice := .asEntersChoice objectId true true
@[match_pattern] abbrev payLifeOrEnterTapped (objectId : ObjectId) (life : Nat) : CostModeChoice :=
  .objectNatChoice objectId life false
@[match_pattern] abbrev mayChangeSpellTarget (spellId : ObjectId) (index : Nat) : CostModeChoice :=
  .objectNatChoice spellId index true

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
  /-- This player declares whether they will take a mulligan (`!triggerOrder`, CR 103.5) or chooses the order of their waiting triggered abilities (`triggerOrder`, CR 603.3b). -/
  | playerStepChoice (player : PlayerId) (triggerOrder : Bool := false)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- The player announces how attacking (`forAttackers`) or blocking creatures
  assign combat damage (CR 510.1c–d). -/
  | assignCombatDamage (player : PlayerId) (forAttackers : Bool)
  /-- This player chooses which of these legendary permanents with the same
  name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
  | chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

namespace TurnCombatPending

@[match_pattern] abbrev declareAttackers : TurnCombatPending := .declareCombatStep false
@[match_pattern] abbrev declareBlockers : TurnCombatPending := .declareCombatStep true
@[match_pattern] abbrev declareMulligan (player : PlayerId) : TurnCombatPending := .playerStepChoice player false
@[match_pattern] abbrev chooseTriggerToStack (player : PlayerId) : TurnCombatPending := .playerStepChoice player true

end TurnCombatPending

/-- Spell casting and ability activation announcement steps (CR 601.2 / CR 602.2 / CR 702). -/
inductive CastPending where
  /-- Core spell/ability announcement step: activate mana abilities (`!mode && !chooseX`, CR 601.2g), choose a mode (`mode && !chooseX`, CR 601.2b), announce `{X}` (`!mode && chooseX`, CR 107.3a / 601.2b), or announce targets (`mode && chooseX`, CR 601.2c). -/
  | announceStep (mode : Bool := false) (chooseX : Bool := false)
  /-- After `pay`, choose an artifact or creature to sacrifice
  (another, when paying an activated ability). -/
  | sacrificePermanent (sourceId : ObjectId)
  /-- Additional or optional cost step: discard for additional cost (`!chooseCost && !kicker`), choose additional cost (`chooseCost && !kicker`), choose kicker (`!chooseCost && kicker`, CR 702.32), or choose gift (`chooseCost && kicker`, CR 702.185). -/
  | additionalStep (chooseCost : Bool := false) (kicker : Bool := false)
  /-- Announce whether to pay the optional teamwork cost (CR 702.194 / 601.2b). -/
  | chooseTeamwork
  /-- Choose creatures to tap for a teamwork cost (CR 702.194). -/
  | chooseTeamworkCreatures (need : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

namespace CastPending

@[match_pattern] abbrev activateManaAbilities : CastPending := .announceStep false false
@[match_pattern] abbrev chooseMode : CastPending := .announceStep true false
@[match_pattern] abbrev chooseX : CastPending := .announceStep false true
@[match_pattern] abbrev chooseTargets : CastPending := .announceStep true true
@[match_pattern] abbrev discardForAdditionalCost : CastPending := .additionalStep false false
@[match_pattern] abbrev chooseAdditionalCost : CastPending := .additionalStep true false
@[match_pattern] abbrev chooseKicker : CastPending := .additionalStep false true
@[match_pattern] abbrev chooseGift : CastPending := .additionalStep true true

end CastPending

/-- Resolution, keyword action, and trigger choices (CR 608 / CR 701). -/
inductive ResolvePending where
  /-- Resolution prompt: sacrifice a creature (`!mayResolve && !tapHumans`), resolve `mayEffect` (`mayResolve && !tapHumans`), tap any number of untapped Humans (`!mayResolve && tapHumans`), or discard a card for recruit (`mayResolve && tapHumans`). -/
  | resolvePrompt (mayResolve : Bool := false) (tapHumans : Bool := false)
  /-- This player is looking at the top `count` cards of their library to scry (`!surveil`, CR 701.20) or surveil (`surveil`, CR 701.25). -/
  | lookLibrary (count : Nat) (surveil : Bool := false)
  /-- This player may discard a card (`!sacArtifact`) or sacrifice an artifact / discard a card (`sacArtifact`); if they do, they draw `drawCount` (CR 701.9). -/
  | mayCostDraw (drawCount : Nat) (sacArtifact : Bool := false)
  /-- This player must sacrifice a creature they control. `chosen` are
  already-selected sacrifices; `remaining` are later players in APNAP order. -/
  | chooseSacrificeCreature (chosen : Array ObjectId) (remaining : Array PlayerId)
  /-- This player must discard a card. `remaining` are later opponents. -/
  | chooseDiscardCard (remaining : Array PlayerId)
  /-- You may pay `{n}` generic mana to draw (`!proliferate`), or choose permanents/players to proliferate `n` more times (`proliferate`, CR 701.34). -/
  | payOrProliferate (n : Nat) (proliferate : Bool := false)
  /-- Choose library top/bottom or `SpellResolution.or` side for `id` (`!bolgSacrifice`), or optionally sacrifice another creature to Bolg (`bolgId = id`, `bolgSacrifice`). -/
  | objectChoice (id : ObjectId) (bolgSacrifice : Bool := false)
  /-- You may attach an Equipment you control (`!fromHand`) or put an artifact card from your hand onto the battlefield (`fromHand`) for `hostId`. -/
  | mayEquipmentOrArtifact (hostId : ObjectId) (fromHand : Bool := false)
  /-- Pay `{n}` or let `id` be countered (`!castExiled`), or cast exiled `id` else deal `n` damage to each opponent (`castExiled`, Chandra). -/
  | payOrExileChoice (n : Nat) (id : ObjectId) (castExiled : Bool := false)
  /-- Pay this ward cost or let the targeting spell or ability be countered
  (CR 702.21). -/
  | payWard (spellId : ObjectId) (cost : WardCost)
  /-- Choose a creature you control as your Ring-bearer (`!putLand`), or optionally put a land from hand onto the battlefield tapped (`putLand`). -/
  | ringOrLandPrompt (putLand : Bool := false)
  /-- You may cast one of these looked-at library cards without paying its
  mana cost as the ability resolves (Cosmic Cube; MSH 356). `maxMv` is the
  greatest power among attacking creatures you control. -/
  | mayCastFromLooked (ids : Array ObjectId) (maxMv : Int)
  /-- The controller chooses one alternative of a `TriggerResolution.or`. -/
  | chooseTriggerOr
  /-- You may have this entering Villain connive (Baron Strucker; MSH 422). -/
  | mayHaveVillainConnive (sourceId : ObjectId) (villainId : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

namespace ResolvePending

@[match_pattern] abbrev sacrificeCreature : ResolvePending := .resolvePrompt false false
@[match_pattern] abbrev mayResolve : ResolvePending := .resolvePrompt true false
@[match_pattern] abbrev tapHumans : ResolvePending := .resolvePrompt false true
@[match_pattern] abbrev recruitDiscard : ResolvePending := .resolvePrompt true true
@[match_pattern] abbrev scry (count : Nat) : ResolvePending := .lookLibrary count false
@[match_pattern] abbrev surveil (count : Nat) : ResolvePending := .lookLibrary count true
@[match_pattern] abbrev mayDiscardDraw (drawCount : Nat) : ResolvePending := .mayCostDraw drawCount false
@[match_pattern] abbrev maySacArtifactOrDiscard (draw : Nat) : ResolvePending := .mayCostDraw draw true
@[match_pattern] abbrev mayPayGeneric (n : Nat) : ResolvePending := .payOrProliferate n false
@[match_pattern] abbrev chooseProliferate (remaining : Nat) : ResolvePending := .payOrProliferate remaining true
@[match_pattern] abbrev chooseLibraryPlacement (id : ObjectId) : ResolvePending := .objectChoice id false
@[match_pattern] abbrev maySacrificeAnotherBolg (bolgId : ObjectId) : ResolvePending := .objectChoice bolgId true
@[match_pattern] abbrev mayAttachEquipment (hostId : ObjectId) : ResolvePending := .mayEquipmentOrArtifact hostId false
@[match_pattern] abbrev mayPutArtifactFromHand (hostId : ObjectId) : ResolvePending := .mayEquipmentOrArtifact hostId true
@[match_pattern] abbrev payOrLetCounter (n : Nat) (spellId : ObjectId) : ResolvePending := .payOrExileChoice n spellId false
@[match_pattern] abbrev mayCastExiledElseDamage (cardId : ObjectId) (damage : Nat) : ResolvePending :=
  .payOrExileChoice damage cardId true
@[match_pattern] abbrev chooseRingBearer : ResolvePending := .ringOrLandPrompt false
@[match_pattern] abbrev mayPutLandFromHand : ResolvePending := .ringOrLandPrompt true

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
