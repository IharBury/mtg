import Mtg.Engine.Game.Pending

/-!
# Players, actions, and setup (CR 102 / 103)

`GameResult`, `Player` — life, zones, mulligan bookkeeping, designations,
and per-turn flags — `Seat` and `StartConfig` for starting a game, and
the `Action` interface players use to act.
-/

namespace Mtg.Engine

abbrev GameResult := Target

namespace GameResult

@[match_pattern] abbrev won (player : PlayerId) : GameResult := .targetKind (.inl player)
@[match_pattern] abbrev draw : GameResult := .targetKind (.inr (⟨0⟩, false))

end GameResult

namespace Target
export GameResult (won draw)
end Target

/-- Per-turn player tracking state, reset as the turn ends (CR 119 / CR 504 / CR 508 / CR 514.3 / CR 601.2f / CR 603.2 / CR 701). -/
abbrev PlayerTurnState := PermanentTurnState

set_option maxHeartbeats 800000 in
structure Player extends PermanentTurnState where
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
  library : Array ObjectId := #[]
  hand : Array ObjectId := #[]
  graveyard : Array ObjectId := #[]
  /-- Sideboard cards not yet brought into play as objects outside the game
  (CR 400.11b). -/
  sideboard : Array CardDef := #[]
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
  pl.toPermanentTurnState != {}

/-- Player with per-turn tracking fields reset as the turn ends. -/
def clearedAtEndOfTurn (pl : Player) : Player :=
  { pl with toPermanentTurnState := { dealtNoncombatDamageLastTurn := pl.dealtNoncombatDamageThisTurn } }

end Player

/-- A seat at the table before objects are created. -/
abbrev Seat := CopyEffect

abbrev StartConfig := WaitingTrigger

abbrev Action := LibraryChoice

namespace Action

@[match_pattern] abbrev actionKind (n : Nat := 0) (nameOpt : Option String := none)
    (id : ObjectId := ⟨0⟩) (attackerId : ObjectId := ⟨0⟩)
    (to : Option PlayerId := none) (optId : Option ObjectId := none)
    (targetOpt : Option Target := none) (tsOpt : Option (Array Target) := none)
    (ids : Array ObjectId := #[]) (rest : Array ObjectId := #[])
    (manaOpt : Option ManaType := none) (manaArrOpt : Option (Array ManaType) := none)
    (divOpt : Option (Array (Target × Nat)) := none)
    (eachOpt : Option (Array (Option PlayerId)) := none)
    (pwOpt : Option (Array (Option ObjectId)) := none)
    (blockOpt : Option (Array (ObjectId × ObjectId)) := none)
    (combatOpt : Option (Array CreatureCombatAssignment) := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
    (b5 : Bool := false) (b6 : Bool := false)
    (isSingleObj : Bool := false) (isArrayObj : Bool := false) : Action :=
  LibraryChoice.libraryChoiceKind ids rest #[] id attackerId ⟨0⟩ n 0 0 0 #[] optId none to none none nameOpt none none #[] targetOpt none #[] #[] none #[] none alt1 alt2 alt3 alt4 b5 b6 isSingleObj isArrayObj false false tsOpt manaOpt manaArrOpt divOpt eachOpt pwOpt blockOpt combatOpt

@[match_pattern] abbrev simpleOrNatAction (n : Nat := 0) (nameOpt : Option String := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false) (alt4 : Bool := false)
    (natChoice : Bool := false) (boolOrConcede : Bool := false) : Action :=
  .actionKind n nameOpt ⟨0⟩ ⟨0⟩ none none none none #[] #[] none none none none none none none alt1 alt2 alt3 alt4 natChoice boolOrConcede false false
@[match_pattern] abbrev singleObjectOrDesignationAction (id : ObjectId := ⟨0⟩) (abilityIdx : Nat := 0)
    (attackerId : ObjectId := ⟨0⟩) (to : Option PlayerId := none) (optId : Option ObjectId := none)
    (alt1 : Bool := false) (alt2 : Bool := false) (alt3 : Bool := false)
    (actOrSneak : Bool := false) (designation : Bool := false) : Action :=
  .actionKind abilityIdx none id attackerId to optId none none #[] #[] none none none none none none none alt1 alt2 alt3 actOrSneak designation false true false
@[match_pattern] abbrev announceTargetAction (targetOpt : Option Target := none) (tsOpt : Option (Array Target) := none) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ none none targetOpt tsOpt #[] #[] none none none none none none none false false false false false false false false
@[match_pattern] abbrev arrayObjectAction (ids : Array ObjectId) (rest : Array ObjectId := #[]) (order : Bool := false) (flag : Bool := false) (lookLibrary : Bool := false) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ none none none none ids rest none none none none none none none order flag lookLibrary false false false false true
@[match_pattern] abbrev tapForMana (id : ObjectId) (mana : ManaType) : Action :=
  .actionKind 0 none id ⟨0⟩ none none none none #[] #[] (some mana) none none none none none none false false false false false false false false
@[match_pattern] abbrev activateManaAbility (id : ObjectId) (idx : Nat) (mana : Array ManaType)
    (costIds : Array ObjectId := #[]) : Action :=
  .actionKind idx none id ⟨0⟩ none none none none costIds #[] none (some mana) none none none none none false false false false false false false false
@[match_pattern] abbrev divideDamage (assignments : Array (Target × Nat)) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ none none none none #[] #[] none none (some assignments) none none none none false false false false false false false false
@[match_pattern] abbrev declareAttackers (ids : Array ObjectId) (defender : Option PlayerId := none)
    (each : Array (Option PlayerId) := #[])
    (planeswalkers : Array (Option ObjectId) := #[]) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ defender none none none ids #[] none none none (some each) (some planeswalkers) none none false false false false false false false false
@[match_pattern] abbrev declareBlockers (assignments : Array (ObjectId × ObjectId)) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ none none none none #[] #[] none none none none none (some assignments) none false false false false false false false false
@[match_pattern] abbrev assignCombatDamage (assignments : Array CreatureCombatAssignment) : Action :=
  .actionKind 0 none ⟨0⟩ ⟨0⟩ none none none none #[] #[] none none none none none none (some assignments) false false false false false false false false

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
@[match_pattern] abbrev target (t : Target) : Action := .announceTargetAction (some t) none
@[match_pattern] abbrev targets (ts : Array Target) : Action := .announceTargetAction none (some ts)
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
