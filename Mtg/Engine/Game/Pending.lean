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
`FraResolution`, run through the same interpreter. -/
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
  /-- Draw a card and create a Treasure. -/
  | drawAndTreasure
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnSourceToHand
deriving DecidableEq, Repr, Inhabited, BEq

def FraNext.toResolution : FraNext → FraResolution
  | .searchBasicLandTapped => .searchBasicLandTapped
  | .searchLandsTapped n => .searchLandsTapped n
  | .searchEnchantmentToHand => .searchEnchantmentToHand
  | .tappedHeartwoods n => .tappedHeartwoods n
  | .eachOpponentSacrificesCreature => .eachOpponentSacrificesCreature
  | .drawThenCountersPerDiscard => .drawThenCountersPerDiscard
  | .eyeOfJaceCheck => .eyeOfJaceCheck
  | .reflexiveDamageAnyTarget n => .reflexiveDamageAnyTarget n
  | .reflexiveDestroyPerOpponent => .reflexiveDestroyPerOpponent
  | .reflexiveReturnLandTapped => .reflexiveReturnLandTapped
  | .beastToken => .beastToken
  | .proliferate n => .proliferate n
  | .mshReflexive k paid => .queueMshReflexive k paid
  | .gainLife n => .gainLife n
  | .drawAndTreasure => .drawAndCreateTreasure
  | .returnSourceToHand => .returnSourceToHand

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

/-- A choice made while a Reality Fracture effect resolves. The player answers
with `Action.choosePermanents` (cards or permanents), `Action.accept`, or
`Action.decline`. -/
inductive FraChoice where
  /-- Choose a card from `target`'s revealed hand for them to discard: a
  nonland permanent card if `permanentOnly`, else a nonland card. -/
  | discardFromRevealedHand (target : PlayerId) (permanentOnly : Bool)
  /-- The player may discard their hand and draw `n`; `rest` choose after. -/
  | mayWheel (n : Nat) (rest : Array PlayerId)
  /-- You may sacrifice a planeswalker to search for one (Entrust the Spark). -/
  | maySacrificePlaneswalker
  /-- The owner of `id` puts it on top (accept) or on the bottom (decline) of
  their library; on top, they are dealt `damage`. -/
  | topOrBottomDamage (id : ObjectId) (damage : Nat)
  /-- You may exile `spellId` and four other cards named Sphinx's Approach. -/
  | sphinxsApproach (spellId : ObjectId)
  /-- You may reveal two cards with different names from outside the game. -/
  | extrapolateReveal
  /-- Choose one of `ids` for `revealer` to put into their hand. -/
  | extrapolatePick (revealer : PlayerId) (ids : Array ObjectId)
  /-- You may put one of the milled permanent cards `ids` into your hand;
  then you gain `life` life. -/
  | mayPutMilledPermanent (ids : Array ObjectId) (life : Nat)
  /-- You may do `next` (accept or decline). -/
  | mayThen (next : FraNext) (sourceId : Option ObjectId)
  /-- You may pay `{n}`; if you do, do `next`. -/
  | mayPayThen (n : Nat) (next : FraNext) (sourceId : Option ObjectId)
  /-- You may discard a card; if you do, do `next`. -/
  | mayDiscardThen (next : FraNext) (sourceId : Option ObjectId)
  /-- Discard a card (required while you have one), then do `next`. -/
  | discardThen (next : FraNext) (sourceId : Option ObjectId)
    (causeId : Option ObjectId)
  /-- Discard `n` cards, then tap and stun up to as many target creatures as
  nonland cards were discarded (Seasoned Cryomancer). -/
  | discardThenStun (n : Nat) (sourceId : Option ObjectId)
  /-- You may sacrifice a permanent of `kind` (land, creature or planeswalker);
  if you do, do `next`. -/
  | maySacrificeThen (kind : FraSacrifice) (next : FraNext)
    (sourceId : Option ObjectId)
  /-- You may remove a +1/+1 counter from `sourceId` (Guiding Hydra). -/
  | mayMovePlusOne (sourceId : ObjectId)
  /-- Choose a nonland card from `victim`'s revealed hand to exile, linked to
  `sourceId` (Null Summoner). -/
  | exileFromRevealedHand (victim : PlayerId) (sourceId : Option ObjectId)
  /-- Cast up to `castsLeft` of the copies `ids` with total mana value at
  most `budget` without paying their mana costs (Uldaros Theorix, Baron
  Helmut Zemo). -/
  | castCopiesFree (ids : Array ObjectId) (budget : Nat) (castsLeft : Nat)
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
  /-- Each player sacrifices a creature of their choice; `controller` creates
  a 4/4 Beast if they sacrificed one (Garruk, Veiled Butcher). `chosen` are
  sacrificed together once everyone has chosen. -/
  | sacrificeCreatureEach (controller : PlayerId) (rest : Array PlayerId)
    (chosen : Array ObjectId)
  /-- The choosing opponent discards two cards; `controller` draws a card for
  each opponent who didn't discard two nonland cards. -/
  | discardTwo (controller : PlayerId) (rest : Array PlayerId) (draws : Nat)
  /-- You may move all counters from `fromId` onto `toId` (The Ozolith). -/
  | mayMoveAllCounters (fromId toId : ObjectId)
  /-- Choose a nonland card name for `objectId` as it enters (Meddling
  Mage). Answered with `Action.chooseName`. -/
  | chooseCardName (objectId : ObjectId)
  /-- Tap untapped creatures with total power `power` or more to pay the crew
  cost of `vehicleId`'s ability `abilityId` (CR 702.122). Declining cancels
  the activation. -/
  | crew (abilityId vehicleId : ObjectId) (power : Nat)
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
  /-- You may sacrifice another creature. If you do, the source gets +1/+1
  counters equal to that creature's power (Rhovanion Rampager). -/
  | maySacrificeAnotherCreatureForPower (sourceId : ObjectId)
  /-- You may sacrifice another creature or artifact. If you do, draw a card
  and create a Treasure (The Sackville-Bagginses). -/
  | maySacrificeAnotherForDrawTreasure (sourceId : ObjectId)
  /-- You may pay `symbols`. If you do, do `next` (Silvan Reveler). -/
  | mayPaySymbolsThen (symbols : Array ManaSymbol) (next : FraNext) (sourceId : ObjectId)
  /-- Choose any number of Equipment to attach to `hostId`. Declining
  attaches none (Thorin, Mountain-king). -/
  | attachAnyEquipment (hostId : ObjectId) (eligible : Array ObjectId)
  /-- Choose one of the tied least-power creatures to sacrifice. -/
  | sacrificeLeastPower (ids : Array ObjectId)
  /-- Choose the color of each of `left` more mana to add, spendable only as
  `use` allows. Answered with `Action.chooseMode` (white, blue, black, red,
  green by index). -/
  | addManaColors (left : Nat) (use : FraManaUse)
  /-- As `objectId` enters, pay `life` life (accept), or it enters tapped
  (decline). -/
  | payLifeOrEnterTapped (objectId : ObjectId) (life : Nat)
  /-- Extort: you may pay {W/B}; if you do, drain each opponent for 1. -/
  | mayPayExtort (sourceId : Option ObjectId)
  /-- You may draw `draw` cards; if you do, discard `discard` cards. -/
  | mayDrawThenDiscard (draw discard : Nat)
  /-- Each player in turn sacrifices a nontoken creature of their choice;
  `chosen` are sacrificed together at the end (The Serpent Society). -/
  | sacrificeNontokenEach (rest : Array PlayerId) (chosen : Array ObjectId)
  /-- You may create `n` tokens of `kind`. -/
  | mayCreateTokens (kind : TokenKind) (n : Nat)
  /-- You may have `objectId`'s base power and toughness become `p`/`t`
  until end of turn. -/
  | mayBecomeBasePT (objectId : ObjectId) (p t : Int)
  /-- You may reveal one of `eligible` from among the looked-at `looked` and
  put it into your hand; the rest go on the bottom in a random order. -/
  | mayRevealToHand (looked eligible : Array ObjectId)
  /-- You may cast one of these artifact, instant, or sorcery cards from your
  graveyard, paying its cost (Bilbo, Thief in the Night). An instant or
  sorcery cast this way is exiled instead of going to the graveyard. -/
  | mayCastFromGraveyard (eligible : Array ObjectId)
  /-- Search: choose up to `count` of `eligible` (or none, CR 701.19b), send
  them to `dest`, shuffle, then do `after`. `kind` is the logged card phrase. -/
  | searchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option FraNext) (kind : String)
  /-- You may search (Old Thrush). Declining does not shuffle. Accepting
  continues as `searchLibrary`. -/
  | maySearchLibrary (eligible : Array ObjectId) (count : Nat) (dest : SearchDest)
    (after : Option FraNext) (kind : String)
  /-- You may pay `cost` up to `maxTimes` times (accept pays once; a mode
  index pays that many times); when you do, the reflexive ability `kind`
  triggers. -/
  | mayPayManaForReflexive (cost : Array ManaSymbol) (maxTimes : Nat) (kind : Nat)
    (sourceId : Option ObjectId)
  /-- You may tap the untapped source; if you do, do `next`. -/
  | mayTapSourceThen (next : FraNext) (sourceId : ObjectId)
  /-- Choose up to `left` more different modes of Hawkeye's Trick Arrows
  (0 Net, 1 Explosive, 2 Boomerang); decline to stop. -/
  | hawkeyeModes (left : Nat) (chosen : Array Nat) (sourceId : Option ObjectId)
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
  /-- Palantír of Orthanc: this opponent may have `controller` draw a card.
  Declining mills X cards and this player loses life equal to their mana values. -/
  | palantirMayDraw (controller : PlayerId) (sourceId : ObjectId)
  /-- You may cast this copy of an exiled card without paying its mana cost.
  Declining makes the copy cease to exist (Saruman of Many Colors). -/
  | mayCastCopy (copyId : ObjectId)
  /-- You may discard your hand. If you do, draw that many cards. With an
  enduring story, `sourceId` deals that much damage to each opponent (Balin). -/
  | mayDiscardHandBalin (sourceId : Option ObjectId)
  /-- You may discard your hand. If you do, draw `n` cards (Sauron). -/
  | mayDiscardHandDrawFixed (n : Nat)
  /-- Sacrifice one creature that dealt combat damage to `controller`. The
  other opponents in `rest` choose next, then the Ring tempts `controller`
  (Witch-king of Angmar). -/
  | sacrificeDamager (ids : Array ObjectId) (rest : Array PlayerId)
    (controller : PlayerId)
  /-- You may cast one of these instant or sorcery cards from your hand
  without paying its mana cost (Gandalf, Party Guest; Glamdring). -/
  | mayCastInstantSorceryFromHand (eligible : Array ObjectId)
  /-- You may cast up to `left` more of these exiled cards without paying
  their mana costs (Doom Reigns Supreme). -/
  | mayCastUpToFromExile (eligible : Array ObjectId) (left : Nat)
  /-- Mister Hyde: choose mode 0 (+1/+1 counter) or 1 (remove a counter
  and draw). -/
  | hydeMode (sourceId : ObjectId)
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
  /-- Choose a Vision mode that hasn't been chosen this turn.
  0 double strike, 1 indestructible, 2 draw. -/
  | visionMode (sourceId : ObjectId) (available : Array Nat)
  /-- You may exile the discarded card and play it until the end of your next
  turn (Moonstone). -/
  | moonstoneMayExile (cardId : ObjectId)
  /-- You may pay 2 life so creatures you control assign combat damage equal
  to their toughness (The Kingpin of Crime). -/
  | kingpinMayPay2Life
  /-- You may exile the top card of your library (Daredevil). -/
  | daredevilMayExile (sourceId : Option ObjectId)
  /-- You may choose a new target for one slot of `spellId`, or decline to
  keep it. `index` walks the spell's targets (Speedball). -/
  | mayChangeSpellTarget (spellId : ObjectId) (index : Nat)
  /-- Choose a new target for the first of `copies`, or decline to keep its
  target; then the rest. -/
  | newTargetsForCopies (copies : Array ObjectId)
deriving DecidableEq, Repr, Inhabited, BEq

/-- Choice that must be made before priority proceeds. -/
inductive Pending where
  | none
  | declareAttackers
  | declareBlockers
  /-- The player may activate mana abilities before paying (CR 601.2g). -/
  | activateManaAbilities (caster : PlayerId)
  /-- The player must choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (caster : PlayerId)
  /-- The player must announce a value for `{X}` (CR 107.3a / 601.2b). -/
  | chooseX (caster : PlayerId)
  /-- The player must announce targets for the proposed spell (CR 601.2c). -/
  | chooseTargets (caster : PlayerId)
  /-- After `pay`, choose an artifact or creature to sacrifice
  (another, when paying an activated ability). -/
  | sacrificePermanent (player : PlayerId) (sourceId : ObjectId)
  /-- After `pay`, discard a card to finish paying an additional cost
  (CR 601.2h / 601.2b), e.g. Titania. -/
  | discardForAdditionalCost (player : PlayerId)
  /-- A resolved trigger requires this player to sacrifice a creature
  of their choice (e.g. Crude Bent Blade). -/
  | sacrificeCreature (player : PlayerId)
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library to
  surveil (CR 701.25). -/
  | surveil (player : PlayerId) (count : Nat)
  /-- This player may discard a card; if they do, they draw `drawCount` (CR 701.9). -/
  | mayDiscardDraw (player : PlayerId) (drawCount : Nat)
  /-- The player must announce an additional or alternative additional cost
  (CR 601.2b), before targets (CR 601.2c). -/
  | chooseAdditionalCost (player : PlayerId)
  /-- This player must sacrifice a creature they control. `chosen` are
  already-selected sacrifices; `remaining` are later players in APNAP order. -/
  | chooseSacrificeCreature (player : PlayerId) (chosen : Array ObjectId)
      (remaining : Array PlayerId)
  /-- This player must discard a card. `remaining` are later opponents. -/
  | chooseDiscardCard (player : PlayerId) (remaining : Array PlayerId)
  /-- The player announces how attacking (`forAttackers`) or blocking creatures
  assign combat damage (CR 510.1c–d). -/
  | assignCombatDamage (player : PlayerId) (forAttackers : Bool)
  /-- This player chooses which of these legendary permanents with the same
  name to keep; the rest are put into their owners' graveyards (CR 704.5j). -/
  | chooseLegend (player : PlayerId) (name : String) (ids : Array ObjectId)
  /-- This player chooses the order of their waiting triggered abilities
  for the current CR 603.3b part. -/
  | chooseTriggerToStack (player : PlayerId)
  /-- You may pay `{n}` generic mana; if you do, draw a card. -/
  | mayPayGeneric (player : PlayerId) (n : Nat)
  /-- Choose top or bottom of library for this card. -/
  | chooseLibraryPlacement (player : PlayerId) (id : ObjectId)
  /-- You may attach an Equipment you control to this creature. -/
  | mayAttachEquipment (player : PlayerId) (hostId : ObjectId)
  /-- Tap any number of Humans you control, then draw that many. -/
  | tapHumans (player : PlayerId)
  /-- Pay `{n}` or let the targeted spell be countered. -/
  | payOrLetCounter (player : PlayerId) (n : Nat) (spellId : ObjectId)
  /-- Pay this ward cost or let the targeting spell or ability be countered
  (CR 702.21). -/
  | payWard (player : PlayerId) (spellId : ObjectId) (cost : WardCost)
  /-- Discard a card for recruit; if it is not a land, create a Human Soldier. -/
  | recruitDiscard (player : PlayerId)
  /-- Announce whether to pay the optional kicker cost (CR 702.32 / 601.2b). -/
  | chooseKicker (player : PlayerId)
  /-- Announce whether to promise a gift to an opponent (CR 702.185 / 601.2b). -/
  | chooseGift (player : PlayerId)
  /-- Announce whether to pay the optional teamwork cost (CR 702.194 / 601.2b). -/
  | chooseTeamwork (player : PlayerId)
  /-- Choose creatures to tap for a teamwork cost (CR 702.194). -/
  | chooseTeamworkCreatures (player : PlayerId) (need : Nat)
  /-- Choose a creature you control as your Ring-bearer. -/
  | chooseRingBearer (player : PlayerId)
  /-- You may sacrifice another creature to Bolg's enters instruction. -/
  | maySacrificeAnotherBolg (player : PlayerId) (bolgId : ObjectId)
  /-- You may cast one of these looked-at library cards without paying its
  mana cost as the ability resolves (Cosmic Cube; MSH 356). `maxMv` is the
  greatest power among attacking creatures you control. -/
  | mayCastFromLooked (player : PlayerId) (ids : Array ObjectId) (maxMv : Int)
  /-- You may put a land from hand onto the battlefield tapped. -/
  | mayPutLandFromHand (player : PlayerId)
  /-- Create a Food token or a Treasure token. -/
  | chooseFoodOrTreasure (player : PlayerId)
  /-- Choose tap or untap for this nonland permanent. -/
  | chooseTapOrUntap (player : PlayerId) (targetId : ObjectId)
  /-- You may sacrifice an artifact or discard a card. If you do, draw. -/
  | maySacArtifactOrDiscard (player : PlayerId)
  /-- You may put an artifact card from your hand onto the battlefield.
  If it is Equipment, attach it to `hostId`. -/
  | mayPutArtifactFromHand (player : PlayerId) (hostId : ObjectId)
  /-- You may have this entering Villain connive (Baron Strucker; MSH 422). -/
  | mayHaveVillainConnive (player : PlayerId) (sourceId : ObjectId) (villainId : ObjectId)
  /-- You may cast exiled `cardId` as an ability resolves, paying its costs.
  If you don't, the ability deals `damage` to each opponent (Chandra, Torch
  of Defiance). -/
  | mayCastExiledElseDamage (player : PlayerId) (cardId : ObjectId) (damage : Nat)
  /-- Choose any number of permanents and players with counters to
  proliferate, `remaining` more times (CR 701.34; Tam, the Possibility). -/
  | chooseProliferate (player : PlayerId) (remaining : Nat)
  /-- A Reality Fracture choice made while an effect resolves. -/
  | fraChoice (player : PlayerId) (choice : FraChoice)
  /-- A random event must be resolved by supplying its result (`--norandom`). -/
  | resolveRandom (req : RandomRequest)
deriving DecidableEq, Repr, Inhabited, BEq

end Mtg.Engine
