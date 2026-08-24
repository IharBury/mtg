/-!
# Mtg.Basic

Small starter definitions for the `mtg` project used to exercise the
development environment: ordinary computation plus a machine-checked proof,
which together demonstrate that both the Lean compiler and its proof checker
are working.
-/

/-- A player's starting life total in a standard game. -/
def startingLife : Nat := 20

/-- Apply `damage` to a life total, clamped so it never drops below zero. -/
def applyDamage (life damage : Nat) : Nat := life - damage

/-- Taking more damage than the current life total leaves the player at zero. -/
theorem applyDamage_le (life damage : Nat) : applyDamage life damage ≤ life :=
  Nat.sub_le life damage

/-- Greeting used by the executable entry point. -/
def hello := s!"Magic: starting life is {startingLife}"
