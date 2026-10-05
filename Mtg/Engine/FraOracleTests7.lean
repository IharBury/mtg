import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.FraOracleTests
import Mtg.Engine.FraOracleTests2
import Mtg.Engine.FraOracleTests4
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Mulligans
import Mtg.Engine.Tests.Turns

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 7)

Chandra, Torch of Defiance: casting the exiled card as her ability resolves,
her mana ability that uses the stack, and her emblem.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-- Chandra enters with four loyalty and `top` on top of her library. -/
def chandraBoard (g : Game) (top : CardDef) : Game :=
  let g := addToLibraryTop (emptyHand g ⟨0⟩) top ⟨0⟩
  enterPermanent g chandraTorchOfDefiance ⟨0⟩

/-- Apply idle actions until `done` holds. -/
def stepUntil (g : Game) (done : Game → Bool) : Nat → Game
  | 0 => g
  | n + 1 => if done g then g else stepUntil (applyIdle g) done n

/-- Activate Chandra's first +1 and let it resolve. -/
def chandraExileTop (g : Game) : Game :=
  let chandra := namedPermanent g "Chandra, Torch of Defiance"
  passBoth (mustApply g ⟨0⟩ (.activate chandra.id 0))

def exiledNamed (g : Game) (name : String) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == name) with
  | some o => o
  | none => panic! s!"expected {name} in exile"

/- Ruling 855: a land can't be cast, so Chandra deals 2 damage to each
opponent. -/
#guard
  let g := chandraExileTop (chandraBoard afterDraw forest)
  (g.player ⟨1⟩).life == 18 && g.pending == .none &&
    g.objects.any (fun o => o.zone == .exile && o.name == "Forest")
#guard (fraRuling 855).comment.contains "doesn't allow you to play lands"

/- Declining to cast also deals the damage. -/
#guard
  let g := chandraExileTop (chandraBoard afterDraw grizzlyBears)
  let g := mustApply g ⟨0⟩ .decline
  (g.player ⟨1⟩).life == 18

/-- Rulings 857 / 859: the card is cast as the ability resolves, ignoring the
creature's sorcery timing, and Chandra pays its costs. -/
def chandraCastsGiant : Game :=
  let g := withRedMana (chandraExileTop (chandraBoard afterDraw hillGiant)) ⟨0⟩ 4
  mustApply g ⟨0⟩ (.cast (exiledNamed g "Hill Giant").id)

#guard topOfStack chandraCastsGiant == "Hill Giant"
#guard (chandraCastsGiant.player ⟨0⟩).manaPool.total == 0
#guard (chandraCastsGiant.player ⟨1⟩).life == 20
#guard (passBoth chandraCastsGiant).battlefield.any (fun o => o.name == "Hill Giant")
#guard
  let g := chandraExileTop (chandraBoard afterDraw hillGiant)
  rejects g ⟨0⟩ (.cast (exiledNamed g "Hill Giant").id) "cannot pay"
#guard (fraRuling 857).comment.contains "You pay the costs for the exiled card"
#guard (fraRuling 859).comment.contains "Timing permissions based on the card's type are ignored"

/- A cast spell with a target still announces it. -/
#guard
  let g := withRedMana (chandraExileTop (chandraBoard afterDraw shock)) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (exiledNamed g "Shock").id)
  let g := mustApply g ⟨0⟩ (.target (.player ⟨1⟩))
  (passBoth g |>.player ⟨1⟩).life == 18

/- Ruling 856: Chandra's “+1: Add {R}{R}.” isn't a mana ability; it uses
the stack. -/
#guard
  let g := chandraBoard afterDraw forest
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Chandra, Torch of Defiance").id 1)
  g.stack.size == 1 && (passBoth g |>.player ⟨0⟩).manaPool.total == 2

/- Ruling 854: with two opponents, each is dealt 2 damage, 4 in total (as
the opposing team would be in Two-Headed Giant). -/
#guard
  let g := chandraBoard (skipTo threeStarted .precombatMain 80) forest
  let g := mustApply g ⟨0⟩ (.activate (namedPermanent g "Chandra, Torch of Defiance").id 0)
  let g := resolveStack g 20
  (g.player ⟨1⟩).life == 18 && (g.player ⟨2⟩).life == 18
#guard (fraRuling 854).comment.contains "4 damage total"

/-- Chandra with seven loyalty uses her −7 for the emblem. -/
def chandraEmblem : Game :=
  let g := chandraBoard afterDraw forest
  let chandra := namedPermanent g "Chandra, Torch of Defiance"
  let g := g.mapObjectStatus chandra (fun s => { s with loyaltyCounters := 7 })
  passBoth (mustApply g ⟨0⟩ (.activate chandra.id 3))

/- Ruling 858: the emblem is colorless. -/
#guard chandraEmblem.objects.any (fun o =>
  o.zone == .command && o.controlledBy ⟨0⟩ && o.printed.colors.isColorless)
#guard (fraRuling 858).comment.contains "The emblem created by Chandra's last ability is colorless"

/- Ruling 860: the emblem's trigger resolves before the spell. -/
#guard
  let g := castShockAtNissa chandraEmblem
  let g := stepUntil g (fun g => g.stack.size == 1) 20
  topOfStack g == "Shock" && (g.player ⟨1⟩).life == 15
#guard (fraRuling 860).comment.contains "resolves before the spell that caused it to trigger"

end Mtg.Engine.FraRulingTests
