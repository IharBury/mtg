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

/-- Per-turn player tracking state, reset as the turn ends (CR 514.3 / CR 603.2). -/
structure PlayerTurnState where
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- A Hero you control entered this turn (Avengers Assemble). -/
  heroEnteredThisTurn : Bool := false
  /-- You attacked with a Hero this turn (Avengers Assemble). -/
  attackedWithHeroThisTurn : Bool := false
  /-- Creatures this player attacked with this turn (Minas Tirith). -/
  creaturesAttackedWithThisTurn : Nat := 0
  /-- Equip abilities this player activated this turn (Kíli the Resourceful). -/
  equipActivationsThisTurn : Nat := 0
  /-- Cards drawn during your current draw step (Bard, King of Dale). -/
  cardsDrawnThisDrawStep : Nat := 0
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Mana value of each spell this player has cast this turn. -/
  castManaValuesThisTurn : Array Nat := #[]
  /-- Times `noteResolveThisTurn` has counted for this player this turn
  (Belladonna Took). -/
  belladonnaResolvesThisTurn : Nat := 0
  /-- Life gained this turn (The Gaffer and similar “if you gained” triggers). -/
  lifeGainedThisTurn : Nat := 0
  /-- Creature spells cast this turn (Radagast of Rhosgobel). -/
  creatureSpellsCastThisTurn : Nat := 0
  /-- Players can't cast spells this turn (Bilbo's Gambit). -/
  cantCastSpellsThisTurn : Bool := false
  /-- Delayed “whenever you attack this turn, pump per Plains” chapters
  still waiting to fire (Roads Go Ever, Ever On). -/
  attackPumpPerPlainsThisTurn : Nat := 0
  /-- Cards discarded this turn (Misty Knight; MSH 375). -/
  cardsDiscardedThisTurn : Nat := 0
  /-- Generic mana less to cast spells of each of these types or supertypes this turn
  (CR 601.2f, Armor Wars II). -/
  spellsCostLessThisTurn : Array (SpellCostLess × Nat) := #[]
  /-- An artifact entered under this player's control this turn (Iron Man;
  MSH 242 / 323). Still true if that artifact later left or changed types. -/
  artifactEnteredThisTurn : Bool := false
  /-- Until end of turn, loyalty abilities of Jace planeswalkers this player
  controls may be activated any time they could cast an instant (Jace's
  Machinations). Each permanent is still limited to one per turn (ruling 766). -/
  jaceLoyaltyAtInstantSpeed : Bool := false
  /-- Instant or sorcery spells this player casts this turn that are copied
  (Way of the Cryomancer). -/
  copyNextInstantSorceryThisTurn : Nat := 0
  /-- This player was dealt noncombat damage this turn (Grim Repriser). -/
  dealtNoncombatDamageThisTurn : Bool := false
  /-- This player scried this turn (Desperate Futurescribe).
  Scry 0 does not count. -/
  scriedThisTurn : Bool := false
  /-- This player surveilled this turn (Desperate Futurescribe).
  Surveil 0 does not count. -/
  surveilledThisTurn : Bool := false
  /-- This player was dealt noncombat damage during the previous turn. -/
  dealtNoncombatDamageLastTurn : Bool := false
  /-- This player activated a loyalty ability this turn. -/
  activatedLoyaltyThisTurn : Bool := false
  /-- Cards put into this player's graveyard from their library this turn
  (Cruel Calculations). -/
  cardsMilledThisTurn : Nat := 0
  /-- Until end of turn, each Mountain this player taps for mana adds this
  many additional {R} (Molten Tide). -/
  mountainExtraRedThisTurn : Nat := 0
  /-- The next spell this player casts this turn can't be countered
  (Theorist's Proxy). -/
  nextSpellCantBeCountered : Bool := false
  /-- Life lost this turn, including from damage (CR 119.3). -/
  lifeLostThisTurn : Nat := 0
  /-- Creatures this player controls can't attack Jace planeswalkers this turn. -/
  cantAttackJaces : Bool := false
deriving Repr, Inhabited, BEq

/-- Player designations, emblems, commander identity, and multi-turn permissions/locks (CR 701.54 / CR 702.131 / CR 722 / CR 903). -/
structure PlayerDesignations where
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
  /-- Number of The Ring emblem abilities gained (0 = no emblem). Max 4. -/
  theRingAbilities : Nat := 0
  /-- Current Ring-bearer, if any. -/
  ringBearerId : Option ObjectId := none
  /-- Ascend: the city's blessing for the rest of the game. -/
  citysBlessing : Bool := false
  /-- True when this player has a commander (Commander / Oathbreaker). -/
  hasCommander : Bool := false
  /-- Combined color identity of this player's commander(s). Empty when they
  have no commander or the commander is colorless (CR 903.4). -/
  commanderColorIdentity : ColorSet := {}
  /-- Protection from everything until this player's next turn
  (e.g. The One Ring). -/
  protectionFromEverything : Bool := false
  /-- Bird Soldier tokens to create at the beginning of the next upkeep
  (The Eagles Are Coming!). -/
  eaglesBirdsNextUpkeep : Nat := 0
  /-- Qualities beheld this game (Elven Passage and similar). A later zone
  change of the revealed card or chosen permanent does not un-behold. -/
  beheldQualities : Array String := #[]
  /-- This player's life total can't change (Platinum Emperion; MSH 292). -/
  lifeLocked : Bool := false
  /-- The legend rule doesn't apply to permanents this player controls this
  turn (Hall of Echoes). Ends in cleanup with the copy effect (ruling 817). -/
  legendRuleOffThisTurn : Bool := false
  /-- Two-Headed Giant teammate (MSH 57 / 236). -/
  teammate : Option PlayerId := none
  /-- This player is the monarch (CR 722). -/
  isMonarch : Bool := false
  /-- This player's life total can't change until their next turn. -/
  lifeCantChange : Bool := false
  /-- Creature types of this player's commander, for Path of Ancestry. -/
  commanderCreatureTypes : Array String := #[]
deriving Repr, Inhabited, BEq

structure Player extends PlayerTurnState, PlayerDesignations where
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
  /-- Sideboard cards not yet brought into play as objects outside the game
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
deriving Repr, Inhabited

namespace Player

def typeSpellCostLessThisTurn (pl : Player) : Array (CardType × Nat) :=
  pl.spellsCostLessThisTurn.filterMap fun
    | (.cardType ty, n) => some (ty, n)
    | _ => none

def supertypeSpellCostLessThisTurn (pl : Player) : Array (Supertype × Nat) :=
  pl.spellsCostLessThisTurn.filterMap fun
    | (.supertype s, n) => some (s, n)
    | _ => none

/-- True when this player has per-turn tracking state to reset at the end of a turn. -/
def hasTurnStateToClear (pl : Player) : Bool :=
  pl.toPlayerTurnState != {}

/-- Player with per-turn tracking fields reset as the turn ends. -/
def clearedAtEndOfTurn (pl : Player) : Player :=
  { pl with toPlayerTurnState := { dealtNoncombatDamageLastTurn := pl.dealtNoncombatDamageThisTurn } }

end Player

/-- A seat at the table before objects are created. -/
structure Seat where
  name : String
  deck : Array CardDef
  /-- Cards outside the game the player may use, such as a sideboard
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
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
  /-- Priority, cost payment, mulligan, or choice response: pass (`false, false, false`), pay (`true, false, false`), keep (`false, true, false`), mulligan (`true, true, false`), decline (`false, false, true`), accept (`true, false, true`), villain connive (`false, true, true`), or pay generic (`true, true, true`). -/
  | stepOrResponse (alt1 : Bool := false) (alt2 : Bool := false) (response : Bool := false)
  /-- Single-object action: play land (`false, false, false`), keep legend (`false, false, true`), cast (`true, false, false`), cast Adventure (`true, false, true`), sacrifice (`false, true, false`), or discard (`false, true, true`). -/
  | objectAction (id : ObjectId) (cast : Bool := false) (sacOrDiscard : Bool := false) (flag : Bool := false)
  | tapForMana (id : ObjectId) (mana : ManaType)
  /-- Activate mana ability `idx` of `id` (CR 605.3), adding exactly `mana`
  and paying costs that need chosen objects with `costIds`, in order. -/
  | activateManaAbility (id : ObjectId) (idx : Nat) (mana : Array ManaType)
      (costIds : Array ObjectId := #[])
  /-- Activate a non-mana activated ability (`sneak = false`, CR 602) or cast for sneak cost returning `attackerId` (`sneak = true`, MSH sneak). -/
  | activateOrSneak (id : ObjectId) (abilityIdx : Nat := 0) (attackerId : ObjectId := ⟨0⟩) (sneak : Bool := false)
  /-- Choose a mode (`mode = true`, CR 601.2b), announce `{X}` (`mode = false, supplyRandom = false`, CR 107.3a), or supply a random index (`mode = false, supplyRandom = true`). -/
  | chooseNat (n : Nat) (mode : Bool := false) (supplyRandom : Bool := false)
  /-- Announce a single target (`multi = false`, CR 601.2c) or all targets of one target instance together (`multi = true`). -/
  | announceTargetAction (t : Target := .player ⟨0⟩) (ts : Array Target := #[]) (multi : Bool := false)
  /-- Announce every target of one instance of the word “target” on a
  “divided as you choose” effect, together with the damage assigned to each
  (CR 601.2c / 601.2d). -/
  | divideDamage (assignments : Array (Target × Nat))
  /-- `defender` is the destination when `each` is omitted or an entry is
  `none`. `each[i]` is the player `ids[i]` attacks (CR 508.1).
  `planeswalkers[i]`, when set, is the planeswalker `ids[i]` attacks instead
  (CR 506.3 / 508.1b). -/
  | declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
      (each : Array (Option PlayerId) := #[])
      (planeswalkers : Array (Option ObjectId) := #[])
  | declareBlockers (assignments : Array (ObjectId × ObjectId))
  /-- Announce combat damage assignment (CR 510.1). Omitted sources use a
  legal default; listed sources must divide their power among legal creature
  recipients (and leftover to the defending player only with trample). -/
  | assignCombatDamage (assignments : Array CreatureCombatAssignment)
  /-- Select/stack objects (`lookLibrary = false, order = false`), order/bottom cards (`lookLibrary = false, order = true`), or finish scrying/surveilling (`lookLibrary = true`, surveil if `flag`, CR 701.20 / 701.25). -/
  | arrayObjectAction (ids : Array ObjectId) (rest : Array ObjectId := #[]) (order : Bool := false) (flag : Bool := false) (lookLibrary : Bool := false)
  /-- Boolean choice or concession: library top/bottom (`false, false, false`), additional cost (`false, true, false`), kicker (`true, false, false`), teamwork (`true, true, false`), or concede (`concede = true`). -/
  | booleanOrConcede (flag : Bool := true) (optionalCost : Bool := false) (teamworkOrAdditional : Bool := false) (concede : Bool := false)
  /-- Promise a gift (`ringBearer = false`) or choose a Ring-bearer (`ringBearer = true`). -/
  | optionalDesignation (to : Option PlayerId := none) (id : Option ObjectId := none) (ringBearer : Bool := false)
  /-- Name a card (CR 201.3), e.g. for Meddling Mage. -/
  | chooseName (name : String)
deriving Repr

namespace Action

@[match_pattern] abbrev stepAction (pay : Bool := false) (keep : Bool := false) : Action := .stepOrResponse pay keep false
@[match_pattern] abbrev pass : Action := .stepOrResponse false false false
@[match_pattern] abbrev pay : Action := .stepOrResponse true false false
@[match_pattern] abbrev keep : Action := .stepOrResponse false true false
@[match_pattern] abbrev takeMulligan : Action := .stepOrResponse true true false
@[match_pattern] abbrev choiceResponse (accept : Bool := false) (villainConnive : Bool := false) : Action :=
  .stepOrResponse accept villainConnive true
@[match_pattern] abbrev decline : Action := .stepOrResponse false false true
@[match_pattern] abbrev accept : Action := .stepOrResponse true false true
@[match_pattern] abbrev haveVillainConnive : Action := .stepOrResponse false true true
@[match_pattern] abbrev payGeneric : Action := .stepOrResponse true true true
@[match_pattern] abbrev concede : Action := .booleanOrConcede false false false true
@[match_pattern] abbrev playLandOrKeepLegend (id : ObjectId) (keepLegend : Bool := false) : Action :=
  .objectAction id false false keepLegend
@[match_pattern] abbrev playLand (id : ObjectId) : Action := .playLandOrKeepLegend id false
@[match_pattern] abbrev keepLegend (id : ObjectId) : Action := .playLandOrKeepLegend id true
@[match_pattern] abbrev castCard (id : ObjectId) (adventure : Bool := false) : Action :=
  .objectAction id true false adventure
@[match_pattern] abbrev cast (id : ObjectId) : Action := .castCard id false
@[match_pattern] abbrev castAdventure (id : ObjectId) : Action := .castCard id true
@[match_pattern] abbrev activate (id : ObjectId) (abilityIdx : Nat) : Action := .activateOrSneak id abilityIdx ⟨0⟩ false
@[match_pattern] abbrev castWithSneak (id attackerId : ObjectId) : Action := .activateOrSneak id 0 attackerId true
@[match_pattern] abbrev target (t : Target) : Action := .announceTargetAction t #[] false
@[match_pattern] abbrev targets (ts : Array Target) : Action := .announceTargetAction (.player ⟨0⟩) ts true
@[match_pattern] abbrev chooseMode (idx : Nat) : Action := .chooseNat idx true false
@[match_pattern] abbrev chooseNumber (n : Nat) (supplyRandom : Bool := false) : Action :=
  .chooseNat n false supplyRandom
@[match_pattern] abbrev chooseX (n : Nat) : Action := .chooseNumber n false
@[match_pattern] abbrev supplyIndex (i : Nat) : Action := .chooseNumber i true
@[match_pattern] abbrev sacrificeOrDiscard (id : ObjectId) (discard : Bool := false) : Action :=
  .objectAction id false true discard
@[match_pattern] abbrev sacrifice (id : ObjectId) : Action := .sacrificeOrDiscard id false
@[match_pattern] abbrev discard (id : ObjectId) : Action := .sacrificeOrDiscard id true
@[match_pattern] abbrev selectOrOrderObjects (ids : Array ObjectId) (order : Bool := false) (flag : Bool := false) : Action :=
  .arrayObjectAction ids #[] order flag false
@[match_pattern] abbrev chooseObjects (ids : Array ObjectId) (stackTriggers : Bool := false) : Action :=
  .arrayObjectAction ids #[] false stackTriggers false
@[match_pattern] abbrev choosePermanents (ids : Array ObjectId) : Action := .chooseObjects ids false
@[match_pattern] abbrev stackTriggers (ids : Array ObjectId) : Action := .chooseObjects ids true
@[match_pattern] abbrev orderCards (ids : Array ObjectId) (supplyRandom : Bool := false) : Action :=
  .arrayObjectAction ids #[] true supplyRandom false
@[match_pattern] abbrev putOnBottom (ids : Array ObjectId) : Action := .orderCards ids false
@[match_pattern] abbrev supplyOrder (ids : Array ObjectId) : Action := .orderCards ids true
@[match_pattern] abbrev lookLibrary (top rest : Array ObjectId) (surveil : Bool := false) : Action :=
  .arrayObjectAction top rest false surveil true
@[match_pattern] abbrev scry (top bottom : Array ObjectId) : Action := .lookLibrary top bottom false
@[match_pattern] abbrev surveil (top graveyard : Array ObjectId) : Action := .lookLibrary top graveyard true
@[match_pattern] abbrev booleanChoice (flag : Bool := true) (optionalCost : Bool := false) (teamworkOrAdditional : Bool := false) : Action :=
  .booleanOrConcede flag optionalCost teamworkOrAdditional false
@[match_pattern] abbrev chooseLibrarySide (top : Bool := true) : Action := .booleanChoice top false false
@[match_pattern] abbrev chooseTop : Action := .chooseLibrarySide true
@[match_pattern] abbrev chooseBottom : Action := .chooseLibrarySide false
@[match_pattern] abbrev chooseAdditionalCost (payGeneric : Bool) : Action := .booleanChoice payGeneric false true
@[match_pattern] abbrev announceOptionalCost (pay : Bool) (teamwork : Bool := false) : Action :=
  .booleanChoice pay true teamwork
@[match_pattern] abbrev announceKicker (kick : Bool) : Action := .announceOptionalCost kick false
@[match_pattern] abbrev announceTeamwork (pay : Bool) : Action := .announceOptionalCost pay true
@[match_pattern] abbrev announceGift (to : Option PlayerId) : Action := .optionalDesignation to none false
@[match_pattern] abbrev chooseRingBearer (id : Option ObjectId) : Action := .optionalDesignation none id true

end Action

end Mtg.Engine
