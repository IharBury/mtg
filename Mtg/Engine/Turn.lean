/-!
# Turn structure (CR 500)

A turn consists of five phases, in this order: beginning, precombat main,
combat, postcombat main, and ending. The beginning, combat, and ending
phases are further broken down into steps.
-/

namespace Mtg.Engine

/-- A step or a main phase (main phases have no steps; CR 505.2). -/
inductive Step where
  | untap
  | upkeep
  | draw
  | precombatMain
  | beginningOfCombat
  | declareAttackers
  | declareBlockers
  | combatDamage
  | endOfCombat
  | postcombatMain
  | end
  | cleanup
deriving DecidableEq, Repr, Inhabited, BEq

namespace Step

/-- Canonical order of steps/phases in a turn (CR 500.1, 501.1, 506, 512). -/
def all : List Step :=
  [.untap, .upkeep, .draw, .precombatMain,
   .beginningOfCombat, .declareAttackers, .declareBlockers, .combatDamage, .endOfCombat,
   .postcombatMain, .end, .cleanup]

def englishName : Step → String
  | .untap => "untap step"
  | .upkeep => "upkeep step"
  | .draw => "draw step"
  | .precombatMain => "precombat main phase"
  | .beginningOfCombat => "beginning of combat step"
  | .declareAttackers => "declare attackers step"
  | .declareBlockers => "declare blockers step"
  | .combatDamage => "combat damage step"
  | .endOfCombat => "end of combat step"
  | .postcombatMain => "postcombat main phase"
  | .end => "end step"
  | .cleanup => "cleanup step"

instance : ToString Step where
  toString := englishName

/-- Beginning phase: untap, upkeep, draw (CR 501.1). -/
def isBeginningPhase : Step → Bool
  | .untap | .upkeep | .draw => true
  | _ => false

/-- Combat phase steps (CR 506). -/
def isCombatPhase : Step → Bool
  | .beginningOfCombat | .declareAttackers | .declareBlockers
  | .combatDamage | .endOfCombat => true
  | _ => false

/-- Either main phase (CR 505). -/
def isMainPhase : Step → Bool
  | .precombatMain | .postcombatMain => true
  | _ => false

/-- Ending phase: end step and cleanup step (CR 512). -/
def isEndingPhase : Step → Bool
  | .end | .cleanup => true
  | _ => false

/-- Players do not receive priority during the untap step (CR 502.4). -/
def playersReceivePriority : Step → Bool
  | .untap => false
  | _ => true

/-- The next step in a normal turn, wrapping from cleanup to the next player’s untap. -/
def next? : Step → Option Step
  | .untap => some .upkeep
  | .upkeep => some .draw
  | .draw => some .precombatMain
  | .precombatMain => some .beginningOfCombat
  | .beginningOfCombat => some .declareAttackers
  | .declareAttackers => some .declareBlockers
  | .declareBlockers => some .combatDamage
  | .combatDamage => some .endOfCombat
  | .endOfCombat => some .postcombatMain
  | .postcombatMain => some .end
  | .end => some .cleanup
  | .cleanup => none

#guard Step.all.length == 12
#guard Step.precombatMain.isMainPhase
#guard !Step.untap.playersReceivePriority
#guard (Step.cleanup.next?).isNone
#guard Step.untap.next? == some .upkeep

end Step

end Mtg.Engine
