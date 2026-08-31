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
  /-- Put the chosen creature onto the battlefield for `controller`, then shuffle. -/
  | putCreatureThenShuffle (controller : PlayerId)
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
deriving DecidableEq, Repr, Inhabited, BEq

/-- A queued ward obligation waiting to be announced. -/
structure WardObligation where
  player : PlayerId
  spellId : ObjectId
  cost : WardCost
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
  /-- A resolved trigger requires this player to sacrifice a creature
  of their choice (e.g. Crude Bent Blade). -/
  | sacrificeCreature (player : PlayerId)
  /-- This player declares whether they will take a mulligan (CR 103.5). -/
  | declareMulligan (player : PlayerId)
  /-- This player puts `count` cards on the bottom after a mulligan (CR 103.5). -/
  | putOnBottom (player : PlayerId) (count : Nat)
  /-- This player is looking at the top `count` cards of their library (CR 701.20). -/
  | scry (player : PlayerId) (count : Nat)
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
  /-- A random event must be resolved by supplying its result (`--norandom`). -/
  | resolveRandom (req : RandomRequest)
deriving DecidableEq, Repr, Inhabited, BEq

end Mtg.Engine
