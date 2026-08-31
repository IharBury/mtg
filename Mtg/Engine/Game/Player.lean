import Mtg.Engine.Game.Pending

/-!
# Players, actions, and setup (CR 102 / 103)

`GameResult`, `Player` — life, zones, mulligan bookkeeping, designations,
and per-turn flags — `Seat` and `StartConfig` for starting a game, and
the `Action` interface players use to act.
-/

namespace Mtg.Engine

inductive GameResult where
  | won (player : PlayerId)
  | draw
deriving DecidableEq, Repr, BEq

structure Player where
  id : PlayerId
  name : String
  life : Int := 20
  startingLife : Int := 20
  maxHandSize : Nat := 7
  /-- Cards drawn as the game begins (CR 103.5); normally seven. -/
  startingHandSize : Nat := 7
  manaPool : ManaPool := {}
  landsPlayedThisTurn : Nat := 0
  /-- Extra land plays granted this turn (CR 305.2b). Reset in untap. -/
  additionalLandsThisTurn : Nat := 0
  poison : Nat := 0
  lost : Bool := false
  /-- CR 800.4a has already been performed for this player. -/
  leftTheGame : Bool := false
  drewFromEmpty : Bool := false
  /-- Completed London mulligans this game (CR 103.5). The first may not
  count toward bottoming or the zero-card limit (CR 103.5c). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- A Hero you control entered this turn (Avengers Assemble). -/
  heroEnteredThisTurn : Bool := false
  /-- You attacked with a Hero this turn (Avengers Assemble). -/
  attackedWithHeroThisTurn : Bool := false
  /-- Cards drawn during your current draw step (Bard, King of Dale). -/
  cardsDrawnThisDrawStep : Nat := 0
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
  /-- Number of The Ring emblem abilities gained (0 = no emblem). Max 4. -/
  theRingAbilities : Nat := 0
  /-- Current Ring-bearer, if any. -/
  ringBearerId : Option ObjectId := none
  /-- Ascend: the city's blessing for the rest of the game. -/
  citysBlessing : Bool := false
  /-- Mana value of each spell this player has cast this turn. -/
  castManaValuesThisTurn : Array Nat := #[]
  /-- True when this player has a commander (Commander / Oathbreaker). -/
  hasCommander : Bool := false
  /-- Combined color identity of this player's commander(s). Empty when they
  have no commander or the commander is colorless (CR 903.4). -/
  commanderColorIdentity : ColorSet := {}
  /-- Times Belladonna Took's token-enters ability has resolved this turn. -/
  belladonnaResolvesThisTurn : Nat := 0
  /-- Protection from everything until this player's next turn
  (e.g. The One Ring). -/
  protectionFromEverything : Bool := false
  /-- Bird Soldier tokens to create at the beginning of the next upkeep
  (The Eagles Are Coming!). -/
  eaglesBirdsNextUpkeep : Nat := 0
  /-- Life gained this turn (The Gaffer and similar “if you gained” triggers). -/
  lifeGainedThisTurn : Nat := 0
  /-- Creature spells cast this turn (Radagast of Rhosgobel). -/
  creatureSpellsCastThisTurn : Nat := 0
  /-- Qualities beheld this game (Elven Passage and similar). A later zone
  change of the revealed card or chosen permanent does not un-behold. -/
  beheldQualities : Array String := #[]
  /-- Players can't cast spells this turn (Bilbo's Gambit). -/
  cantCastSpellsThisTurn : Bool := false
  /-- Delayed “whenever you attack this turn, pump per Plains” chapters
  still waiting to fire (Roads Go Ever, Ever On). -/
  attackPumpPerPlainsThisTurn : Nat := 0
  /-- This player's life total can't change (Platinum Emperion; MSH 292). -/
  lifeLocked : Bool := false
  /-- Cards discarded this turn (Misty Knight; MSH 375). -/
  cardsDiscardedThisTurn : Nat := 0
  /-- An artifact entered under this player's control this turn (Iron Man;
  MSH 242 / 323). Still true if that artifact later left or changed types. -/
  artifactEnteredThisTurn : Bool := false
  /-- Two-Headed Giant teammate (MSH 57 / 236). -/
  teammate : Option PlayerId := none
deriving Repr, Inhabited

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
deriving Repr, Inhabited

structure StartConfig where
  seats : Array Seat
  format : Format := .constructed
  /-- CR 903.12 Brawl option. The first mulligan is free (CR 103.5c / 903.12g). -/
  brawl : Bool := false
  seed : UInt64 := 20260807
  /-- Index into `seats`. `none` means the RNG chooses. -/
  startingPlayer : Option Nat := none
  /-- When true, never shuffle or roll; leave a `Pending.resolveRandom`. -/
  norandom : Bool := false

inductive Action where
  | pass
  | playLand (id : ObjectId)
  | tapForMana (id : ObjectId) (mana : ManaType)
  | cast (id : ObjectId)
  /-- Cast this adventurer card as its Adventure (CR 715.3). -/
  | castAdventure (id : ObjectId)
  /-- Choose a mode of a modal spell or ability (CR 601.2b). -/
  | chooseMode (idx : Nat)
  /-- Announce a value for `{X}` (CR 107.3a / 601.2b). -/
  | chooseX (n : Nat)
  /-- Announce a target for the current instance of the word “target”
  (CR 601.2c). For a divided-damage ability, assigns all remaining damage
  to this one target (CR 601.2d). For “one or two target creatures”, this
  chooses exactly that one creature. -/
  | target (t : Target)
  /-- Announce every target of one instance of the word “target” together
  (CR 601.2c), e.g. both creatures of “one or two target creatures”. -/
  | targets (ts : Array Target)
  /-- Announce every target of one instance of the word “target” on a
  “divided as you choose” effect, together with the damage assigned to each
  (CR 601.2c / 601.2d). -/
  | divideDamage (assignments : Array (Target × Nat))
  /-- Activate a non-mana activated ability of a permanent (CR 602). -/
  | activate (id : ObjectId) (abilityIdx : Nat)
  /-- Pay the locked-in cost of a proposed spell or ability (CR 601.2h / 602.2b). -/
  | pay
  /-- After `pay`, sacrifice an artifact or creature to finish paying
  (CR 601.2h / 602.2b), a creature a resolved trigger requires, or a creature
  as a resolving effect. -/
  | sacrifice (id : ObjectId)
  /-- Choose to pay extra generic mana rather than sacrifice, as an additional
  cost (CR 601.2b). `true` pays the generic alternative; `false` sacrifices. -/
  | chooseAdditionalCost (payGeneric : Bool)
  /-- `defender` is the destination when `each` is omitted or an entry is
  `none`. `each[i]` is the player `ids[i]` attacks (CR 508.1). -/
  | declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
      (each : Array (Option PlayerId) := #[])
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Announce combat damage assignment (CR 510.1). Omitted sources use a
  legal default; listed sources must divide their power among legal creature
  recipients (and leftover to the defending player only with trample). -/
  | assignCombatDamage (assignments : Array CreatureCombatAssignment)
  /-- Keep this hand as the opening hand (CR 103.5). -/
  | keep
  /-- Choose which legendary permanent to keep under the legend rule (CR 704.5j). -/
  | keepLegend (id : ObjectId)
  /-- Put waiting triggered abilities on the stack in this source order
  (first listed is put first, so it is farthest from the top) (CR 603.3b). -/
  | stackTriggers (ids : Array ObjectId)
  /-- Declare a London mulligan; it is taken after every remaining player has
  declared (CR 103.5). -/
  | takeMulligan
  /-- Put these cards on the bottom after a mulligan, first listed = new bottom. -/
  | putOnBottom (ids : Array ObjectId)
  /-- Finish scrying: `top` (last = new top) go on top of the library in that
  order; `bottom` (first = new bottom) go to the bottom (CR 701.20). -/
  | scry (top : Array ObjectId) (bottom : Array ObjectId)
  /-- Discard this card from hand; if a pending “may discard, then draw” is
  waiting, draw afterward (CR 701.9). -/
  | discard (id : ObjectId)
  /-- Decline an optional “you may discard a card”, or choose no target for an
  “up to one” trigger (CR 608.2d / 601.2c). -/
  | decline
  /-- Have the entering Villain connive (Baron Strucker; MSH 422). -/
  | haveVillainConnive
  /-- Pay a pending generic-mana “you may pay” or “unless pays” cost. -/
  | payGeneric
  /-- Put the pending card on top of its owner's library. -/
  | chooseTop
  /-- Put the pending card on the bottom of its owner's library. -/
  | chooseBottom
  /-- Attach this Equipment, or tap these Humans. -/
  | choosePermanents (ids : Array ObjectId)
  /-- Pay (`true`) or decline (`false`) the optional kicker cost. -/
  | announceKicker (kick : Bool)
  /-- Promise a gift to this opponent, or `none` to decline. -/
  | announceGift (to : Option PlayerId)
  /-- Pay (`true`) or decline (`false`) the optional teamwork cost. -/
  | announceTeamwork (pay : Bool)
  /-- Choose this creature as your Ring-bearer, or `none` if you control none. -/
  | chooseRingBearer (id : Option ObjectId)
  | concede
  /-- Supply the order or chosen object for a pending random event
  (`--norandom`). An empty list keeps the current order of a shuffle. -/
  | supplyOrder (ids : Array ObjectId)
  /-- Supply an index for a pending `chooseIndex` random event (`--norandom`). -/
  | supplyIndex (i : Nat)
deriving Repr

end Mtg.Engine
