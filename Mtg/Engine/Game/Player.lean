import Mtg.Engine.Game.Pending

/-!
# Players, actions, and setup (CR 102 / 103)

`GameResult`, `Player` — life, zones, mulligan bookkeeping, designations,
and per-turn flags — `Seat` and `StartConfig` for starting a game, and
the `Action` interface players use to act.
-/

namespace Mtg.Engine

inductive GameResult where
  | gameResultKind (winner : Option PlayerId := none)
deriving DecidableEq, Repr, BEq

namespace GameResult

@[match_pattern] abbrev won (player : PlayerId) : GameResult := .gameResultKind (some player)
@[match_pattern] abbrev draw : GameResult := .gameResultKind none

end GameResult

/-- Per-turn spell casting and cost modification state on a player (CR 601.2f / CR 603.2). -/
structure PlayerSpellTurnState where
  /-- Spells cast this turn (for “second spell each turn” triggers). -/
  spellsCastThisTurn : Nat := 0
  /-- Noncreature spells cast this turn. -/
  noncreatureSpellsCastThisTurn : Nat := 0
  /-- Mana value of each spell this player has cast this turn. -/
  castManaValuesThisTurn : Array Nat := #[]
  /-- Creature spells cast this turn (Radagast of Rhosgobel). -/
  creatureSpellsCastThisTurn : Nat := 0
  /-- Players can't cast spells this turn (Bilbo's Gambit). -/
  cantCastSpellsThisTurn : Bool := false
  /-- Generic mana less to cast spells of each of these types or supertypes this turn
  (CR 601.2f, Armor Wars II). -/
  spellsCostLessThisTurn : Array (SpellCostLess × Nat) := #[]
  /-- Instant or sorcery spells this player casts this turn that are copied
  (Way of the Cryomancer). -/
  copyNextInstantSorceryThisTurn : Nat := 0
  /-- The next spell this player casts this turn can't be countered
  (Theorist's Proxy). -/
  nextSpellCantBeCountered : Bool := false
deriving Repr, Inhabited, BEq

/-- Per-turn draw, discard, mill, scry/surveil, and activation state on a player (CR 504 / CR 603.2 / CR 701). -/
structure PlayerActionAndEventTurnState where
  /-- Cards drawn this turn (for “second card each turn” triggers). -/
  cardsDrawnThisTurn : Nat := 0
  /-- Cards drawn during your current draw step (Bard, King of Dale). -/
  cardsDrawnThisDrawStep : Nat := 0
  /-- Equip abilities this player activated this turn (Kíli the Resourceful). -/
  equipActivationsThisTurn : Nat := 0
  /-- Times `noteResolveThisTurn` has counted for this player this turn
  (Belladonna Took). -/
  belladonnaResolvesThisTurn : Nat := 0
  /-- Cards discarded this turn (Misty Knight; MSH 375). -/
  cardsDiscardedThisTurn : Nat := 0
  /-- Until end of turn, loyalty abilities of Jace planeswalkers this player
  controls may be activated any time they could cast an instant (Jace's
  Machinations). Each permanent is still limited to one per turn (ruling 766). -/
  jaceLoyaltyAtInstantSpeed : Bool := false
  /-- This player scried this turn (Desperate Futurescribe).
  Scry 0 does not count. -/
  scriedThisTurn : Bool := false
  /-- This player surveilled this turn (Desperate Futurescribe).
  Surveil 0 does not count. -/
  surveilledThisTurn : Bool := false
  /-- This player activated a loyalty ability this turn. -/
  activatedLoyaltyThisTurn : Bool := false
  /-- Cards put into this player's graveyard from their library this turn
  (Cruel Calculations). -/
  cardsMilledThisTurn : Nat := 0
  /-- Until end of turn, each Mountain this player taps for mana adds this
  many additional {R} (Molten Tide). -/
  mountainExtraRedThisTurn : Nat := 0
deriving Repr, Inhabited, BEq

/-- Per-turn life, damage, combat, and permanent-entering state on a player (CR 119 / CR 508). -/
structure PlayerCombatAndLifeTurnState where
  /-- A Hero you control entered this turn (Avengers Assemble). -/
  heroEnteredThisTurn : Bool := false
  /-- You attacked with a Hero this turn (Avengers Assemble). -/
  attackedWithHeroThisTurn : Bool := false
  /-- Creatures this player attacked with this turn (Minas Tirith). -/
  creaturesAttackedWithThisTurn : Nat := 0
  /-- Life gained this turn (The Gaffer and similar “if you gained” triggers). -/
  lifeGainedThisTurn : Nat := 0
  /-- Delayed “whenever you attack this turn, pump per Plains” chapters
  still waiting to fire (Roads Go Ever, Ever On). -/
  attackPumpPerPlainsThisTurn : Nat := 0
  /-- An artifact entered under this player's control this turn (Iron Man;
  MSH 242 / 323). Still true if that artifact later left or changed types. -/
  artifactEnteredThisTurn : Bool := false
  /-- This player was dealt noncombat damage this turn (Grim Repriser). -/
  dealtNoncombatDamageThisTurn : Bool := false
  /-- This player was dealt noncombat damage during the previous turn. -/
  dealtNoncombatDamageLastTurn : Bool := false
  /-- Life lost this turn, including from damage (CR 119.3). -/
  lifeLostThisTurn : Nat := 0
  /-- Creatures this player controls can't attack Jace planeswalkers this turn. -/
  cantAttackJaces : Bool := false
deriving Repr, Inhabited, BEq

/-- Per-turn player tracking state, reset as the turn ends (CR 514.3 / CR 603.2). -/
structure PlayerTurnState extends
    PlayerSpellTurnState,
    PlayerActionAndEventTurnState,
    PlayerCombatAndLifeTurnState where
deriving Repr, Inhabited, BEq

/-- Commander identity, multiplayer teammate, and beheld qualities on a player (CR 810 / CR 903). -/
structure PlayerCommanderAndTeamState where
  /-- True when this player has a commander (Commander / Oathbreaker). -/
  hasCommander : Bool := false
  /-- Combined color identity of this player's commander(s). Empty when they
  have no commander or the commander is colorless (CR 903.4). -/
  commanderColorIdentity : ColorSet := {}
  /-- Qualities beheld this game (Elven Passage and similar). A later zone
  change of the revealed card or chosen permanent does not un-behold. -/
  beheldQualities : Array String := #[]
  /-- Two-Headed Giant teammate (MSH 57 / 236). -/
  teammate : Option PlayerId := none
  /-- Creature types of this player's commander, for Path of Ancestry. -/
  commanderCreatureTypes : Array String := #[]
deriving Repr, Inhabited, BEq

/-- Game-long designations, emblems, and multi-turn player locks (CR 701.54 / CR 702.131 / CR 722). -/
structure PlayerEmblemsAndLocks where
  /-- Storied: enduring story for the rest of the game. -/
  enduringStory : Bool := false
  /-- Number of The Ring emblem abilities gained (0 = no emblem). Max 4. -/
  theRingAbilities : Nat := 0
  /-- Current Ring-bearer, if any. -/
  ringBearerId : Option ObjectId := none
  /-- Ascend: the city's blessing for the rest of the game. -/
  citysBlessing : Bool := false
  /-- Protection from everything until this player's next turn
  (e.g. The One Ring). -/
  protectionFromEverything : Bool := false
  /-- Bird Soldier tokens to create at the beginning of the next upkeep
  (The Eagles Are Coming!). -/
  eaglesBirdsNextUpkeep : Nat := 0
  /-- This player's life total can't change (Platinum Emperion; MSH 292). -/
  lifeLocked : Bool := false
  /-- The legend rule doesn't apply to permanents this player controls this
  turn (Hall of Echoes). Ends in cleanup with the copy effect (ruling 817). -/
  legendRuleOffThisTurn : Bool := false
  /-- This player is the monarch (CR 722). -/
  isMonarch : Bool := false
  /-- This player's life total can't change until their next turn. -/
  lifeCantChange : Bool := false
deriving Repr, Inhabited, BEq

/-- Player designations, emblems, commander identity, and multi-turn permissions/locks (CR 701.54 / CR 702.131 / CR 722 / CR 903). -/
structure PlayerDesignations extends PlayerCommanderAndTeamState, PlayerEmblemsAndLocks where
deriving Repr, Inhabited, BEq

/-- Player-owned zones and sideboard (CR 400). -/
structure PlayerZones where
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Sideboard cards not yet brought into play as objects outside the game
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
deriving Repr, Inhabited

/-- Opening hand/mulligan setup and game-loss tracking on a player (CR 103.5 / CR 104.3 / CR 800.4a). -/
structure PlayerSetupAndLossState where
  startingLife : Int := 20
  maxHandSize : Nat := 7
  /-- Cards drawn as the game begins (CR 103.5); normally seven. -/
  startingHandSize : Nat := 7
  lost : Bool := false
  /-- CR 800.4a has already been performed for this player. -/
  leftTheGame : Bool := false
  drewFromEmpty : Bool := false
  /-- Completed London mulligans this game (CR 103.5). The first may not
  count toward bottoming or the zero-card limit (CR 103.5c). -/
  mulligansTaken : Nat := 0
  /-- Set once this player declines further mulligans (CR 103.5). -/
  keptOpeningHand : Bool := false
deriving Repr, Inhabited, BEq

structure Player extends
    PlayerTurnState,
    PlayerDesignations,
    PlayerZones,
    PlayerSetupAndLossState where
  id : PlayerId
  name : String
  life : Int := 20
  manaPool : ManaPool := {}
  landsPlayedThisTurn : Nat := 0
  /-- Extra land plays granted this turn (CR 305.2b). Reset in untap. -/
  additionalLandsThisTurn : Nat := 0
  poison : Nat := 0
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
  | actionKind (val :
      (Nat × Option String × Bool × Bool × Bool × Bool × Bool × Bool) ⊕
      (ObjectId × Nat × ObjectId × Option PlayerId × Option ObjectId × Bool × Bool × Bool × Bool × Bool) ⊕
      (Target × Array Target × Bool) ⊕
      (Array ObjectId × Array ObjectId × Bool × Bool × Bool) ⊕
      (ObjectId × ManaType) ⊕
      (ObjectId × Nat × Array ManaType × Array ObjectId) ⊕
      Array (Target × Nat) ⊕
      (Array ObjectId × Option PlayerId × Array (Option PlayerId) × Array (Option ObjectId)) ⊕
      Array (ObjectId × ObjectId) ⊕
      Array CreatureCombatAssignment)
deriving Repr

namespace Action

@[match_pattern] abbrev simpleOrNatAction (n : Nat := 0) (nameOpt : Option String := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
    (natChoice : Bool := false) (boolOrConcede : Bool := false) : Action :=
  .actionKind (.inl (n, nameOpt, alt1, alt2, alt3, alt4, natChoice, boolOrConcede))
@[match_pattern] abbrev singleObjectOrDesignationAction (id : ObjectId := ⟨0⟩) (abilityIdx : Nat := 0)
    (attackerId : ObjectId := ⟨0⟩) (to : Option PlayerId := none) (optId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (actOrSneak : Bool := false) (designation : Bool := false) : Action :=
  .actionKind (.inr (.inl (id, abilityIdx, attackerId, to, optId, alt1, alt2, alt3, actOrSneak, designation)))
@[match_pattern] abbrev announceTargetAction (t : Target := .player ⟨0⟩) (ts : Array Target := #[]) (multi : Bool := false) : Action :=
  .actionKind (.inr (.inr (.inl (t, ts, multi))))
@[match_pattern] abbrev arrayObjectAction (ids : Array ObjectId) (rest : Array ObjectId := #[]) (order : Bool := false) (flag : Bool := false) (lookLibrary : Bool := false) : Action :=
  .actionKind (.inr (.inr (.inr (.inl (ids, rest, order, flag, lookLibrary)))))
@[match_pattern] abbrev tapForMana (id : ObjectId) (mana : ManaType) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inl (id, mana))))))
@[match_pattern] abbrev activateManaAbility (id : ObjectId) (idx : Nat) (mana : Array ManaType)
    (costIds : Array ObjectId := #[]) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inr (.inl (id, idx, mana, costIds)))))))
@[match_pattern] abbrev divideDamage (assignments : Array (Target × Nat)) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inr (.inr (.inl assignments)))))))
@[match_pattern] abbrev declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
    (each : Array (Option PlayerId) := #[])
    (planeswalkers : Array (Option ObjectId) := #[]) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (ids, defender, each, planeswalkers)))))))))
@[match_pattern] abbrev declareBlockers (assignments : Array (ObjectId × ObjectId)) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl assignments)))))))))
@[match_pattern] abbrev assignCombatDamage (assignments : Array CreatureCombatAssignment) : Action :=
  .actionKind (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr assignments)))))))))

@[match_pattern] abbrev stepOrResponse (alt1 : Bool := false) (alt2 : Bool := false) (response : Bool := false) : Action :=
  .simpleOrNatAction 0 none alt1 alt2 response false false false
@[match_pattern] abbrev chooseNat (n : Nat) (mode : Bool := false) (supplyRandom : Bool := false) : Action :=
  .simpleOrNatAction n none mode supplyRandom false false true false
@[match_pattern] abbrev booleanOrConcede (flag : Bool := true) (optionalCost : Bool := false) (teamworkOrAdditional : Bool := false) (concede : Bool := false) : Action :=
  .simpleOrNatAction 0 none flag optionalCost teamworkOrAdditional concede false true
@[match_pattern] abbrev chooseName (name : String) : Action :=
  .simpleOrNatAction 0 (some name) false false false false false false
@[match_pattern] abbrev objectAction (id : ObjectId) (cast : Bool := false) (sacOrDiscard : Bool := false) (flag : Bool := false) : Action :=
  .singleObjectOrDesignationAction id 0 ⟨0⟩ none none cast sacOrDiscard flag false false
@[match_pattern] abbrev activateOrSneak (id : ObjectId) (abilityIdx : Nat := 0) (attackerId : ObjectId := ⟨0⟩) (sneak : Bool := false) : Action :=
  .singleObjectOrDesignationAction id abilityIdx attackerId none none sneak false false true false
@[match_pattern] abbrev optionalDesignation (to : Option PlayerId := none) (id : Option ObjectId := none) (ringBearer : Bool := false) : Action :=
  .singleObjectOrDesignationAction ⟨0⟩ 0 ⟨0⟩ to id ringBearer false false false true

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
