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
  /-- Draw `n` cards for `p`. -/
  | draw (p : PlayerId) (n : Nat)
  /-- `p` gains `n` life. -/
  | gainLife (p : PlayerId) (n : Nat)
  /-- Continue CR 103.3 opening shuffles from this seat index. -/
  | openingShuffles (next : Nat)
  /-- After this player's library is ordered, draw a new opening hand and
  continue simultaneous mulligans for `rest`. -/
  | mulliganQueue (drawn : PlayerId) (rest : Array PlayerId)
  /-- Seat `i` takes the first turn; then opening shuffles. -/
  | setStartingPlayer (i : Nat)
  /-- Put the chosen creature from `revealed` onto the battlefield, then the
  other revealed cards on the bottom of `controller`'s library in a random
  order (Getaway Barrel). -/
  | revealRandomCreatureThenBottom (controller : PlayerId) (revealed : Array ObjectId)
  /-- Put these cards on top of `p`'s library after shuffling. -/
  | putOnTop (p : PlayerId) (ids : Array ObjectId)
  /-- Behold `subtype`; if you do, untap `landId` (Elven Passage). -/
  | beholdUntap (p : PlayerId) (landId : ObjectId) (subtype : String)
  /-- Put a +1/+1 counter on this creature after the shuffle (Restorative Technique). -/
  | plusOne (id : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Payment a player may make to stop ward from countering their spell
(CR 702.21). -/
inductive WardCost where
  /-- Ward `{n}`. -/
  | genericMana (n : Nat)
  /-- Ward — discard an enchantment, instant, or sorcery card. -/
  | discardEnchantmentInstantOrSorcery
  /-- Ward — sacrifice a legendary artifact or legendary creature. -/
  | sacrificeLegendary
  /-- Ward — discard a card or pay `{n}`. -/
  | discardOrPay (n : Nat)
  /-- Ward — get five poison counters. -/
  | fivePoison
  /-- Ward — discard a card. -/
  | discardCard
  /-- Ward — sacrifice `left` more permanents; `paid` were already
  sacrificed, so the cost can no longer be declined. -/
  | sacrificePermanents (left paid : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- A queued ward obligation waiting to be announced. -/
structure WardObligation where
  player : PlayerId
  spellId : ObjectId
  cost : WardCost
deriving DecidableEq, Repr, Inhabited, BEq

/-- What happens after a Reality Fracture choice is made. Each one is also a
`Resolution` step, run through the same interpreter. -/
inductive FraNext where
  | searchBasicLandTapped
  | searchLandsTapped (n : Nat)
  | searchEnchantmentToHand
  | tappedHeartwoods (n : Nat)
  | eachOpponentSacrificesCreature
  | drawThenCountersPerDiscard
  | eyeOfJaceCheck
  | reflexiveDamageAnyTarget (n : Nat)
  | reflexiveDestroyPerOpponent
  | reflexiveReturnLandTapped
  | beastToken
  | proliferate (times : Nat)
  | mshReflexive (kind paid : Nat)
  | gainLife (n : Nat)
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnSourceToHand
deriving DecidableEq, Repr, Inhabited, BEq

def FraNext.toResolution : FraNext → Resolution
  | .searchBasicLandTapped => .searchLibrary (.put .basicLand .tapped)
  | .searchLandsTapped n => .searchLibrary (.put (.landsUpTo n) .tapped)
  | .searchEnchantmentToHand => .searchLibrary (.returnToHand .enchantmentCard)
  | .tappedHeartwoods n => .createTokens .heartwood (.fixed n) true
  | .eachOpponentSacrificesCreature => .sacrifice .eachOpponentsCreature
  | .drawThenCountersPerDiscard => .putCounters .plusOnePerDiscardAfterDraw .cause
  | .eyeOfJaceCheck => .sacrifice .source .eyeOfJaceIfSevenInGy
  | .reflexiveDamageAnyTarget n => .queueReflexive (.dealDamage (.fixed n) .target)
  | .reflexiveDestroyPerOpponent => .queueReflexive (.destroy (.target .eachPermanent))
  | .reflexiveReturnLandTapped => .queueReflexive (.put .landCard .tapped)
  | .beastToken => .createTokens .beast44trample (.fixed 1) false
  | .proliferate n => .proliferate (.fixed n)
  | .mshReflexive k paid => .queueReflexive (.mshReflexive k paid)
  | .gainLife n => .gainLife n
  | .returnSourceToHand => .returnToHand .source

/-- Where cards found by a library search go (CR 701.19). -/
inductive SearchDest where
  | battlefield (tapped : Bool)
  | hand
  | graveyard
  /-- On top of the library after shuffling. -/
  | topAfterShuffle
  /-- Exiled, linked to the source. -/
  | exileLinked (sourceId : Option ObjectId)
  /-- The first chosen card onto the battlefield tapped, the second into the
  hand (Troop of Ponies). -/
  | battlefieldTappedThenHand
  /-- Onto the battlefield tapped; you may behold a `subtype`, and if you do,
  untap it (Elven Passage). -/
  | battlefieldTappedBeholdUntap (subtype : String)
  /-- Onto the battlefield from the hand or library; shuffle only if the
  library was searched (Last Light of Durin's Day). -/
  | battlefieldFromHandOrLibrary
deriving DecidableEq, Repr, Inhabited, BEq

/-- What a “you may sacrifice …” choice accepts. -/
inductive FraSacrifice where
  | land
  | creatureOrPlaneswalker
  | creature
deriving DecidableEq, Repr, Inhabited, BEq

/-- Part of an activation cost that needs the player to choose what to pay
with (CR 601.2h / 602.2b). -/
inductive CostPick where
  /-- Sacrifice another permanent of this subtype, or another creature when
  the subtype is `Creature`. -/
  | sacrificeAnotherSubtype (subtype : String)
  | sacrificeArtifact
  | sacrificeLegendaryArtifact
  | sacrificeArtifactOrCreature
  | sacrificeAnotherArtifact
  | sacrificeAnotherCreatureOrPlaneswalker
  | sacrificeArtifactOrLand
  | sacrificeEquipmentAttachedToSource
  /-- Sacrifice an artifact, or discard a nonland card. -/
  | sacrificeArtifactOrDiscardNonland
  | discardACard
  /-- Discard a nonland card. -/
  | discardNonland
  | discardLegendaryCard
  /-- Discard a legendary card with the same name as a legendary permanent
  you control. -/
  | discardLegendarySameName
  | exileAnotherCreatureCardFromGraveyard
  | tapUntappedCreature
  | tapTwoUntappedArtifacts
deriving DecidableEq, Repr, Inhabited, BEq

/-- How many objects `pick` takes. -/
def CostPick.count : CostPick → Nat
  | .tapTwoUntappedArtifacts => 2
  | _ => 1

/-- The cost phrase of `pick`, for prompts and logs. -/
def CostPick.phrase : CostPick → String
  | .sacrificeAnotherSubtype t => s!"sacrifice another {t.toLower}"
  | .sacrificeArtifact => "sacrifice an artifact"
  | .sacrificeLegendaryArtifact => "sacrifice a legendary artifact"
  | .sacrificeArtifactOrCreature => "sacrifice an artifact or creature"
  | .sacrificeAnotherArtifact => "sacrifice another artifact"
  | .sacrificeAnotherCreatureOrPlaneswalker => "sacrifice another creature or planeswalker"
  | .sacrificeArtifactOrLand => "sacrifice an artifact or land"
  | .sacrificeEquipmentAttachedToSource => "sacrifice an Equipment attached to the source"
  | .sacrificeArtifactOrDiscardNonland => "sacrifice an artifact or discard a nonland card"
  | .discardACard => "discard a card"
  | .discardNonland => "discard a nonland card"
  | .discardLegendaryCard => "discard a legendary card"
  | .discardLegendarySameName =>
    "discard a legendary card with the same name as a legendary permanent you control"
  | .exileAnotherCreatureCardFromGraveyard => "exile another creature card from your graveyard"
  | .tapUntappedCreature => "tap an untapped creature you control"
  | .tapTwoUntappedArtifacts => "tap two untapped artifacts you control"

/-- Parts of `ab`'s cost the player chooses what to pay with (CR 601.2h). -/
def costPicksOf (ab : ActivatedAbility) : Array CostPick :=
  let c := ab.cost
  let fra : Array CostPick :=
    match c.fra with
    | .exileAnotherCreatureCardFromGraveyard => #[.exileAnotherCreatureCardFromGraveyard]
    | .sacrificeAnotherArtifact => #[.sacrificeAnotherArtifact]
    | .sacrificeAnotherCreatureOrPlaneswalker => #[.sacrificeAnotherCreatureOrPlaneswalker]
    | .sacrificeArtifactOrLand => #[.sacrificeArtifactOrLand]
    | .discardLegendaryCard => #[.discardLegendaryCard]
    | .tapTwoUntappedArtifacts => #[.tapTwoUntappedArtifacts]
    | _ => #[]
  (if c.discardACard then #[CostPick.discardACard] else #[]) ++
  (if c.discardLegendarySameName then #[CostPick.discardLegendarySameName] else #[]) ++
  (if c.sacrificeLegendaryArtifact then #[CostPick.sacrificeLegendaryArtifact] else #[]) ++
  (if c.sacrificeArtifact then #[CostPick.sacrificeArtifact] else #[]) ++
  (if c.sacrificeArtifactOrCreature then #[CostPick.sacrificeArtifactOrCreature] else #[]) ++
  (if c.sacrificeArtifactOrDiscardNonland then
    #[CostPick.sacrificeArtifactOrDiscardNonland] else #[]) ++
  (if c.sacrificeEquipmentAttachedToSource then
    #[CostPick.sacrificeEquipmentAttachedToSource] else #[]) ++
  (if c.tapAnUntappedCreatureYouControl then #[CostPick.tapUntappedCreature] else #[]) ++
  (match c.sacrificeAnotherSubtype with
   | some t => #[CostPick.sacrificeAnotherSubtype t]
   | none => #[]) ++ fra

/-- What to do with cards chosen from a looked-at, milled, or battlefield set. -/
inductive CardChoice where
  /-- Put the chosen cards into your hand. `mustOne` requires exactly one
  when any card can be chosen. -/
  | toHand (mustOne : Bool)
  /-- Put the chosen creature cards onto the battlefield. -/
  | creaturesToBattlefield
  /-- Put the chosen lands onto the battlefield tapped, then shuffle and
  gain `life` life. -/
  | landsTappedGainLife (life : Nat)
  /-- The chosen creatures are kept. Every other creature is destroyed. -/
  | keepDestroyRest
  /-- Amass `subtype` `n` onto the chosen Army. `attach` is an Equipment to
  attach afterward (Goblin Plate Mail). -/
  | amassArmy (subtype : String) (n : Nat) (attach : Option ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

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
  /-- You may reveal one of `eligible` from among the looked-at `looked` and
  put it into your hand. The rest go on the bottom at random, or in an order
  you choose when `anyOrder` is true (Avengers Tower). -/
  | mayRevealToHand (looked eligible : Array ObjectId) (anyOrder : Bool)
  /-- You may put one of `eligible` onto the battlefield (Nick Fury). The rest
  of `looked` go on the bottom in a random order. -/
  | nickFuryPut (looked eligible : Array ObjectId)
  /-- You may transform the double-faced card just put onto the battlefield,
  then the other looked-at cards go on the bottom in a random order. -/
  | nickFuryMayTransform (permanentId : ObjectId) (rest : Array ObjectId)
  /-- Put these cards on the bottom of your library. The first card is the
  bottom. Every card must be included. -/
  | orderLibraryBottom (ids : Array ObjectId)
  /-- Search: choose up to `count` of `eligible` (or none, CR 701.19b), send
  them to `dest`, shuffle, then do `after`. `kind` is the logged card phrase. -/
  | searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option FraNext) (kind : String)
  /-- You may search (Old Thrush). Declining does not shuffle. Accepting
  continues as `searchLibrary`. -/
  | maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option FraNext) (kind : String)
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
  /-- Separate `looked` into a face-up pile (the chosen cards) and a face-down
  pile (Riddles in the Dark). An empty pile is legal. -/
  | riddlesSplit (looked : Array ObjectId)
  /-- An opponent chooses the face-up pile (accept) or the face-down pile
  (decline) for `controller`'s hand. -/
  | riddlesChoosePile (controller : PlayerId) (faceUp faceDown : Array ObjectId)
  /-- Put creature cards from `creatures` onto the battlefield. At most one
  when `anyNumber` is false (Earth's Mightiest Heroes). The rest of `looked`
  go to the graveyard. -/
  | revealPutCreatures (looked creatures : Array ObjectId) (anyNumber : Bool)
  /-- Choose up to `max` of `ids`. `purpose` says what the chosen cards do. -/
  | chooseCards (ids : Array ObjectId) (max : Nat) (purpose : CardChoice)
  /-- You may begin the game with the first of these cards on the battlefield
  (Quicksilver). The rest are asked next. -/
  | mayBeginOnBattlefield (ids : Array ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Hand, discard, graveyard, and exile cast choices made while an effect resolves (CR 402 / CR 404 / CR 406). -/
inductive HandGraveyardChoice where
  /-- Choose a card from `target`'s revealed hand for them to discard: a
  nonland permanent card if `permanentOnly`, else a nonland card. -/
  | discardFromRevealedHand (target : PlayerId) (permanentOnly : Bool)
  /-- You may exile `spellId` and four other cards named Sphinx's Approach. -/
  | sphinxsApproach (spellId : ObjectId)
  /-- You may discard a card; if you do, do `next`. -/
  | mayDiscardThen (next : FraNext) (sourceId : Option ObjectId)
  /-- Discard a card (required while you have one), then do `next`. -/
  | discardThen (next : FraNext) (sourceId : Option ObjectId)
    (causeId : Option ObjectId)
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
  /-- You may discard `n` of `ids`. Declining pays nothing. -/
  | mayDiscardThese (n : Nat) (ids : Array ObjectId)
  /-- You may cast one of these artifact, instant, or sorcery cards from your
  graveyard, paying its cost (Bilbo, Thief in the Night). An instant or
  sorcery cast this way is exiled instead of going to the graveyard. -/
  | mayCastFromGraveyard (eligible : Array ObjectId)
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
  /-- You may cast this copy of an exiled card without paying its mana cost.
  Declining makes the copy cease to exist (Saruman of Many Colors). -/
  | mayCastCopy (copyId : ObjectId)
  /-- You may discard your hand. If you do, draw that many cards. With an
  enduring story, `sourceId` deals that much damage to each opponent (Balin). -/
  | mayDiscardHandBalin (sourceId : Option ObjectId)
  /-- You may discard your hand. If you do, draw `n` cards (Sauron). -/
  | mayDiscardHandDrawFixed (n : Nat)
  /-- You may cast one of these instant or sorcery cards from your hand
  without paying its mana cost (Gandalf, Party Guest; Glamdring). -/
  | mayCastInstantSorceryFromHand (eligible : Array ObjectId)
  /-- You may cast up to `left` more of these exiled cards without paying
  their mana costs (Doom Reigns Supreme). -/
  | mayCastUpToFromExile (eligible : Array ObjectId) (left : Nat)
  /-- You may exile the discarded card and play it until the end of your next
  turn (Moonstone). -/
  | moonstoneMayExile (cardId : ObjectId)
  /-- You may put one of these milled cards into your hand, then gain `lifeAfter`
  life (Rapid Rescue, Rick Jones). Declining still gains the life. -/
  | mayTakeMilled (ids : Array ObjectId) (lifeAfter : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Battlefield, sacrifice, counter, and permanent choices made while an effect resolves (CR 403 / CR 701.17). -/
inductive BattlefieldChoice where
  /-- You may sacrifice a planeswalker to search for one (Entrust the Spark). -/
  | maySacrificePlaneswalker
  /-- You may sacrifice a permanent of `kind` (land, creature or planeswalker);
  if you do, do `next`. -/
  | maySacrificeThen (kind : FraSacrifice) (next : FraNext)
    (sourceId : Option ObjectId)
  /-- You may remove a +1/+1 counter from `sourceId` (Guiding Hydra). -/
  | mayMovePlusOne (sourceId : ObjectId)
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
  /-- You may sacrifice another creature. If you do, the source gets +1/+1
  counters equal to that creature's power (Rhovanion Rampager). -/
  | maySacrificeAnotherCreatureForPower (sourceId : ObjectId)
  /-- You may sacrifice another creature or artifact. If you do, draw a card
  and create a Treasure (The Sackville-Bagginses). -/
  | maySacrificeAnotherForDrawTreasure (sourceId : ObjectId)
  /-- You may sacrifice `n` of `ids`. Declining pays nothing. -/
  | maySacrificeThese (n : Nat) (ids : Array ObjectId)
  /-- Choose any number of Equipment to attach to `hostId`. Declining
  attaches none (Thorin, Mountain-king). -/
  | attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId)
  /-- Choose one of the tied least-power creatures to sacrifice. -/
  | sacrificeLeastPower (ids : Array ObjectId)
  /-- Each player in turn sacrifices a nontoken creature of their choice;
  `chosen` are sacrificed together at the end (The Serpent Society). -/
  | sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId)
  /-- You may create `n` tokens of `kind`. -/
  | mayCreateTokens (kind : TokenKind) (n : Nat)
  /-- You may have `objectId`'s base power and toughness become `p`/`t`
  until end of turn. -/
  | mayBecomeBasePT (objectId : ObjectId) (p t : Int)
  /-- You may tap the untapped source; if you do, do `next`. -/
  | mayTapSourceThen (next : FraNext) (sourceId : ObjectId)
  /-- Sacrifice one creature that dealt combat damage to `controller`. The
  other opponents in `rest` choose next, then the Ring tempts `controller`
  (Witch-king of Angmar). -/
  | sacrificeDamager (ids : Array ObjectId) (rest : Array PlayerId)
    (controller : PlayerId)
  /-- Remove one counter from one of these creatures, then draw (Mister Hyde). -/
  | hydeRemoveCounter (ids : Array ObjectId)
  /-- You may have The Sensational She-Hulk deal `amount` damage to `target`.
  Accepting is the once-each-turn action (MSH 448). -/
  | sheHulkMayDamage (amount : Int) (target : Target) (sourceId : Option ObjectId)
  /-- You may put a +1/+1 counter on Black Widow. If you don't, you may cast
  `exiled` until end of turn. -/
  | widowMayCounter (sourceId : Option ObjectId) (exiled : Option ObjectId)
  /-- You may pay {2} to copy the nontoken artifact that entered (Ultron). -/
  | ultronMayPay (artifactId : ObjectId)
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
deriving DecidableEq, Repr, Inhabited, BEq

/-- Cost, mode, enters, and target choices made while an effect resolves (CR 118 / CR 601.2 / CR 614.12 / CR 700.2). -/
inductive CostModeChoice where
  /-- You may do `next` (accept or decline). -/
  | mayThen (next : FraNext) (sourceId : Option ObjectId)
  /-- You may pay `{n}`; if you do, do `next`. -/
  | mayPayThen (n : Nat) (next : FraNext) (sourceId : Option ObjectId)
  /-- Choose an Alliance mode of `sourceId` that hasn't been chosen this turn.
  Answered with `Action.chooseMode` (0 add {G}{G}{G}, 1 +1/+1 counters,
  2 scry 2 then draw). -/
  | allianceMode (sourceId : ObjectId) (available : Array Nat)
  /-- Choose a Gollum mode that hasn't been chosen. Answered with
  `Action.chooseMode` (0 +1/+1, 1 each opponent loses 2 and you gain 2,
  2 draw). -/
  | gollumMode (sourceId : ObjectId) (available : Array Nat)
  /-- Choose `remaining` more modes for the triggered ability `objectId`
  from `CardDef.fraTriggerModes` of its source. -/
  | triggerModes (objectId : ObjectId) (remaining : Nat) (chosen : Array Nat)
  /-- `objectId` gains your choice of the keywords coded in `options`
  (0 trample, 1 hexproof, 2 haste, 3 deathtouch) until end of turn. Answered
  with the index of an option. -/
  | chooseKeyword (objectId : ObjectId) (options : Array Nat)
  /-- Choose a color for `objectId` as it enters (white, blue, black, red,
  green by index). -/
  | chooseColor (objectId : ObjectId)
  /-- Choose a nonland card name for `objectId` as it enters (Meddling
  Mage). Answered with `Action.chooseName`. -/
  | chooseCardName (objectId : ObjectId)
  /-- Choose what to pay `picks[0]` of the proposed activation's cost with,
  then the rest (CR 601.2h). `paid` is true once one has been paid, after
  which the activation can no longer be cancelled. -/
  | costPicks (sourceId : ObjectId) (picks : Array CostPick) (paid : Bool)
  /-- You may pay `pick` (sacrifice, discard, …) as an ability of `sourceId`
  resolves; when you do, do `next`. -/
  | mayPayPickThen (pick : CostPick) (next : FraNext) (sourceId : ObjectId)
  /-- Choose a creature type you control. `types` are offered by index
  (Orcrist). Answered with `Action.chooseMode` or `Action.chooseName`. -/
  | chooseCreatureType (types : Array String)
  /-- You may pay `symbols`. If you do, do `next` (Silvan Reveler). -/
  | mayPaySymbolsThen (symbols : Array ManaSymbol) (next : FraNext) (sourceId : ObjectId)
  /-- Choose the color of each of `left` more mana to add, spendable only as
  `use` allows. Answered with `Action.chooseMode` (white, blue, black, red,
  green by index). -/
  | addManaColors (left : Nat) (use : FraManaUse)
  /-- As `objectId` enters, pay `life` life (accept), or it enters tapped
  (decline). -/
  | payLifeOrEnterTapped (objectId : ObjectId) (life : Nat)
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
  /-- Choose a Vision mode that hasn't been chosen this turn.
  0 double strike, 1 indestructible, 2 draw. -/
  | visionMode (sourceId : ObjectId) (available : Array Nat)
  /-- You may pay 2 life so creatures you control assign combat damage equal
  to their toughness (The Kingpin of Crime). -/
  | kingpinMayPay2Life
  /-- You may choose a new target for one slot of `spellId`, or decline to
  keep it. `index` walks the spell's targets (Speedball). -/
  | mayChangeSpellTarget (spellId : ObjectId) (index : Nat)
  /-- Choose a new target for the first of `copies`, or decline to keep its
  target; then the rest. -/
  | newTargetsForCopies (copies : Array ObjectId)
  /-- As this permanent enters, choose a creature type (An Unexpected Party). -/
  | entersCreatureType (objectId : ObjectId)
  /-- As this permanent enters, choose even (0) or odd (1) (Gollum, Riddle Master). -/
  | entersOddEven (objectId : ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

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
deriving DecidableEq, Repr, Inhabited, BEq

namespace FraChoice

-- LibraryChoice aliases
@[match_pattern] abbrev mayWheel (n : Nat) (rest : Array PlayerId) : FraChoice := .library (.mayWheel n rest)
@[match_pattern] abbrev topOrBottomDamage (id : ObjectId) (damage : Nat) : FraChoice := .library (.topOrBottomDamage id damage)
@[match_pattern] abbrev extrapolateReveal : FraChoice := .library .extrapolateReveal
@[match_pattern] abbrev extrapolatePick (revealer : PlayerId) (ids : Array ObjectId) : FraChoice := .library (.extrapolatePick revealer ids)
@[match_pattern] abbrev mayDrawThenDiscard (draw discard : Nat) : FraChoice := .library (.mayDrawThenDiscard draw discard)
@[match_pattern] abbrev mayRevealToHand (looked eligible : Array ObjectId) (anyOrder : Bool) : FraChoice := .library (.mayRevealToHand looked eligible anyOrder)
@[match_pattern] abbrev nickFuryPut (looked eligible : Array ObjectId) : FraChoice := .library (.nickFuryPut looked eligible)
@[match_pattern] abbrev nickFuryMayTransform (permanentId : ObjectId) (rest : Array ObjectId) : FraChoice := .library (.nickFuryMayTransform permanentId rest)
@[match_pattern] abbrev orderLibraryBottom (ids : Array ObjectId) : FraChoice := .library (.orderLibraryBottom ids)
@[match_pattern] abbrev searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest) (after : Option FraNext) (kind : String) : FraChoice :=
  .library (.searchLibrary eligible count dest after kind)
@[match_pattern] abbrev maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest) (after : Option FraNext) (kind : String) : FraChoice :=
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
@[match_pattern] abbrev sphinxsApproach (spellId : ObjectId) : FraChoice := .handGraveyard (.sphinxsApproach spellId)
@[match_pattern] abbrev mayDiscardThen (next : FraNext) (sourceId : Option ObjectId) : FraChoice := .handGraveyard (.mayDiscardThen next sourceId)
@[match_pattern] abbrev discardThen (next : FraNext) (sourceId : Option ObjectId) (causeId : Option ObjectId) : FraChoice :=
  .handGraveyard (.discardThen next sourceId causeId)
@[match_pattern] abbrev discardThenStun (n : Nat) (sourceId : Option ObjectId) : FraChoice := .handGraveyard (.discardThenStun n sourceId)
@[match_pattern] abbrev exileFromRevealedHand (victim : PlayerId) (sourceId : Option ObjectId) : FraChoice :=
  .handGraveyard (.exileFromRevealedHand victim sourceId)
@[match_pattern] abbrev castCopiesFree (ids : Array ObjectId) (budget : Nat) (castsLeft : Nat) : FraChoice :=
  .handGraveyard (.castCopiesFree ids budget castsLeft)
@[match_pattern] abbrev discardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat) : FraChoice :=
  .handGraveyard (.discardTwo controller rest draws)
@[match_pattern] abbrev mayDiscardThese (n : Nat) (ids : Array ObjectId) : FraChoice := .handGraveyard (.mayDiscardThese n ids)
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
@[match_pattern] abbrev maySacrificeThen (kind : FraSacrifice) (next : FraNext) (sourceId : Option ObjectId) : FraChoice :=
  .battlefield (.maySacrificeThen kind next sourceId)
@[match_pattern] abbrev mayMovePlusOne (sourceId : ObjectId) : FraChoice := .battlefield (.mayMovePlusOne sourceId)
@[match_pattern] abbrev sacrificeCreatureEach (controller : PlayerId) (rest : Array PlayerId) (chosen : Array ObjectId) : FraChoice :=
  .battlefield (.sacrificeCreatureEach controller rest chosen)
@[match_pattern] abbrev mayMoveAllCounters (fromId toId : ObjectId) : FraChoice := .battlefield (.mayMoveAllCounters fromId toId)
@[match_pattern] abbrev crew (abilityId vehicleId : ObjectId) (power : Nat) : FraChoice := .battlefield (.crew abilityId vehicleId power)
@[match_pattern] abbrev maySacrificeAnotherCreatureForPower (sourceId : ObjectId) : FraChoice :=
  .battlefield (.maySacrificeAnotherCreatureForPower sourceId)
@[match_pattern] abbrev maySacrificeAnotherForDrawTreasure (sourceId : ObjectId) : FraChoice :=
  .battlefield (.maySacrificeAnotherForDrawTreasure sourceId)
@[match_pattern] abbrev maySacrificeThese (n : Nat) (ids : Array ObjectId) : FraChoice := .battlefield (.maySacrificeThese n ids)
@[match_pattern] abbrev attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId) : FraChoice :=
  .battlefield (.attachAnyEquipment hostId eligible)
@[match_pattern] abbrev sacrificeLeastPower (ids : Array ObjectId) : FraChoice := .battlefield (.sacrificeLeastPower ids)
@[match_pattern] abbrev sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId) : FraChoice :=
  .battlefield (.sacrificeNontokenEach rest chosen)
@[match_pattern] abbrev mayCreateTokens (kind : TokenKind) (n : Nat) : FraChoice := .battlefield (.mayCreateTokens kind n)
@[match_pattern] abbrev mayBecomeBasePT (objectId : ObjectId) (p t : Int) : FraChoice := .battlefield (.mayBecomeBasePT objectId p t)
@[match_pattern] abbrev mayTapSourceThen (next : FraNext) (sourceId : ObjectId) : FraChoice := .battlefield (.mayTapSourceThen next sourceId)
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
@[match_pattern] abbrev mayThen (next : FraNext) (sourceId : Option ObjectId) : FraChoice := .costMode (.mayThen next sourceId)
@[match_pattern] abbrev mayPayThen (n : Nat) (next : FraNext) (sourceId : Option ObjectId) : FraChoice := .costMode (.mayPayThen n next sourceId)
@[match_pattern] abbrev allianceMode (sourceId : ObjectId) (available : Array Nat) : FraChoice := .costMode (.allianceMode sourceId available)
@[match_pattern] abbrev gollumMode (sourceId : ObjectId) (available : Array Nat) : FraChoice := .costMode (.gollumMode sourceId available)
@[match_pattern] abbrev triggerModes (objectId : ObjectId) (remaining : Nat) (chosen : Array Nat) : FraChoice :=
  .costMode (.triggerModes objectId remaining chosen)
@[match_pattern] abbrev chooseKeyword (objectId : ObjectId) (options : Array Nat) : FraChoice := .costMode (.chooseKeyword objectId options)
@[match_pattern] abbrev chooseColor (objectId : ObjectId) : FraChoice := .costMode (.chooseColor objectId)
@[match_pattern] abbrev chooseCardName (objectId : ObjectId) : FraChoice := .costMode (.chooseCardName objectId)
@[match_pattern] abbrev costPicks (sourceId : ObjectId) (picks : Array CostPick) (paid : Bool) : FraChoice :=
  .costMode (.costPicks sourceId picks paid)
@[match_pattern] abbrev mayPayPickThen (pick : CostPick) (next : FraNext) (sourceId : ObjectId) : FraChoice :=
  .costMode (.mayPayPickThen pick next sourceId)
@[match_pattern] abbrev chooseCreatureType (types : Array String) : FraChoice := .costMode (.chooseCreatureType types)
@[match_pattern] abbrev mayPaySymbolsThen (symbols : Array ManaSymbol) (next : FraNext) (sourceId : ObjectId) : FraChoice :=
  .costMode (.mayPaySymbolsThen symbols next sourceId)
@[match_pattern] abbrev addManaColors (left : Nat) (use : FraManaUse) : FraChoice := .costMode (.addManaColors left use)
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
  | declareAttackers
  | declareBlockers
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- The player announces how attacking (`forAttackers`) or blocking creatures
  assign combat damage (CR 510.1c–d). -/
  | assignCombatDamage (player : PlayerId) (forAttackers : Bool)
  /-- This player chooses which of these legendary permanents with the same
  name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
  | chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId)
  /-- This player chooses the order of their waiting triggered abilities
  for the current CR 603.3b part. -/
  | chooseTriggerToStack (player : PlayerId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Spell casting and ability activation announcement steps (CR 601.2 / CR 602.2 / CR 702). -/
inductive CastPending where
  /-- The player may activate mana abilities before paying (CR 601.2g). -/
  | activateManaAbilities
  /-- The player must choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode
  /-- The player must announce a value for `{X}` (CR 107.3a / 601.2b). -/
  | chooseX
  /-- The player must announce targets for the proposed spell (CR 601.2c). -/
  | chooseTargets
  /-- After `pay`, choose an artifact or creature to sacrifice
  (another, when paying an activated ability). -/
  | sacrificePermanent (sourceId : ObjectId)
  /-- After `pay`, discard a card to finish paying an additional cost
  (CR 601.2h / 601.2b), e.g. Titania. -/
  | discardForAdditionalCost
  /-- The player must announce an additional or alternative additional cost
  (CR 601.2b), before targets (CR 601.2c). -/
  | chooseAdditionalCost
  /-- Announce whether to pay the optional kicker cost (CR 702.32 / 601.2b). -/
  | chooseKicker
  /-- Announce whether to promise a gift to an opponent (CR 702.185 / 601.2b). -/
  | chooseGift
  /-- Announce whether to pay the optional teamwork cost (CR 702.194 / 601.2b). -/
  | chooseTeamwork
  /-- Choose creatures to tap for a teamwork cost (CR 702.194). -/
  | chooseTeamworkCreatures (need : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Resolution, keyword action, and trigger choices (CR 608 / CR 701). -/
inductive ResolvePending where
  /-- A resolved trigger requires this player to sacrifice a creature
  of their choice (e.g. Crude Bent Blade). -/
  | sacrificeCreature
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (count : Nat)
  /-- This player is looking at the top `count` cards of their library to
  surveil (CR 701.25). -/
  | surveil (count : Nat)
  /-- This player may discard a card; if they do, they draw `drawCount` (CR 701.9). -/
  | mayDiscardDraw (drawCount : Nat)
  /-- This player must sacrifice a creature they control. `chosen` are
  already-selected sacrifices; `remaining` are later players in APNAP order. -/
  | chooseSacrificeCreature (chosen : Array ObjectId) (remaining : Array PlayerId)
  /-- This player must discard a card. `remaining` are later opponents. -/
  | chooseDiscardCard (remaining : Array PlayerId)
  /-- You may pay `{n}` generic mana; if you do, draw a card. -/
  | mayPayGeneric (n : Nat)
  /-- Choose one alternative of a `SpellResolution.or`. For a library
  top-or-bottom choice, `id` is the permanent and top/bottom name the side.
  Otherwise `chooseTop` is the first alternative and `chooseBottom` the second. -/
  | chooseLibraryPlacement (id : ObjectId)
  /-- You may attach an Equipment you control to this creature. -/
  | mayAttachEquipment (hostId : ObjectId)
  /-- You may resolve the effect stashed in `mayEffect`. -/
  | mayResolve
  /-- Tap any number of untapped Humans you control. A later sequence step
  draws a card for each Human tapped. -/
  | tapHumans
  /-- Pay `{n}` or let the targeted spell be countered. When the game's
  `unlessPaysInstead` is set, declining resolves that effect instead. -/
  | payOrLetCounter (n : Nat) (spellId : ObjectId)
  /-- Pay this ward cost or let the targeting spell or ability be countered
  (CR 702.21). -/
  | payWard (spellId : ObjectId) (cost : WardCost)
  /-- Discard a card for recruit; if it is not a land, create a Human Soldier. -/
  | recruitDiscard
  /-- Choose a creature you control as your Ring-bearer. -/
  | chooseRingBearer
  /-- You may sacrifice another creature to Bolg's enters instruction. -/
  | maySacrificeAnotherBolg (bolgId : ObjectId)
  /-- You may cast one of these looked-at library cards without paying its
  mana cost as the ability resolves (Cosmic Cube; MSH 356). `maxMv` is the
  greatest power among attacking creatures you control. -/
  | mayCastFromLooked (ids : Array ObjectId) (maxMv : Int)
  /-- You may put a land from hand onto the battlefield tapped. -/
  | mayPutLandFromHand
  /-- The controller chooses one alternative of a `TriggerResolution.or`. -/
  | chooseTriggerOr
  /-- You may sacrifice an artifact or discard a card. If you do, draw. -/
  | maySacArtifactOrDiscard (draw : Nat)
  /-- You may put an artifact card from your hand onto the battlefield.
  `hostId` is the creature the following step attaches it to if it is Equipment. -/
  | mayPutArtifactFromHand (hostId : ObjectId)
  /-- You may have this entering Villain connive (Baron Strucker; MSH 422). -/
  | mayHaveVillainConnive (sourceId : ObjectId) (villainId : ObjectId)
  /-- You may cast exiled `cardId` as an ability resolves, paying its costs.
  If you don't, the ability deals `damage` to each opponent (Chandra, Torch
  of Defiance). -/
  | mayCastExiledElseDamage (cardId : ObjectId) (damage : Nat)
  /-- Choose any number of permanents and players with counters to
  proliferate, `remaining` more times (CR 701.34; Tam, the Possibility). -/
  | chooseProliferate (remaining : Nat)
deriving DecidableEq, Repr, Inhabited, BEq

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
deriving DecidableEq, Repr, Inhabited, BEq

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
@[match_pattern] abbrev scry (player : PlayerId) (count : Nat) : Pending := .resolve player (.scry count)
@[match_pattern] abbrev surveil (player : PlayerId) (count : Nat) : Pending := .resolve player (.surveil count)
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

