import Mtg.Demo
import Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match applyIgnore Tests.afterDraw ⟨0⟩ [] with
  | .error _ => false
  | .ok r =>
    match r.game.apply ⟨1⟩ .pass with
    | .error _ => false
    | .ok g2 =>
      g2.step == .beginningOfCombat &&
        match applyIgnore g2 ⟨0⟩ [] with
        | .ok r2 =>
          r2.commands == #["pass"] && r2.game.hasPriority ⟨1⟩
        | .error _ => false


#guard isFlagLine "--visible"

#guard !isFlagLine "first Chandra"

#guard commandsFromLines #["", "  \t  "] == []

#guard (inputScriptFromLines #["--visible", "keep", "pass"]).commands == ["keep", "pass"]

#guard (inputScriptFromLines #["  --visible  ", "", "keep"]).flags == ["--visible"]

#guard flagTokens ["--decides", "Nissa"] == ["--decides", "Nissa"]

#guard !sameInputOutput none (some "session.txt")

#guard shouldWriteInputFlags false ["--seed 42", "--visible"]

#guard shouldRecordCommand false false

#guard isNonStateCommand "state"

#guard isNonStateCommand "visible"

#guard !isNonStateCommand "play"


#guard !isCheckSkipCommand "keep"


#guard
  match takeStartingPlayer demoSeats true 0 [] with
  | .error msg => msg == "Missing first <name> (CR 103.1)"
  | _ => false


#guard
  match replayCompleteGame Tests.started [] with
  | .error msg => msg == "Game is not complete"
  | .ok _ => false


#guard
  match replayCompleteGame Tests.started ["not-a-command"] with
  | .error msg => msg == "Invalid command `not-a-command`: Unknown command: not-a-command"
  | .ok _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["attack step", "concede"] with
  | .ok g' =>
    match g'.result with
    | some (.won p) =>
      p == ⟨0⟩ && g'.log.any (fun s => Tests.mentions s "Nissa concedes") &&
        !g'.log.any (fun s => Tests.mentions s "declare attackers")
    | _ => false
  | .error _ => false


#guard
  match replayCompleteGame Tests.afterDraw ["ignore now"] with
  | .error msg => msg == s!"Invalid command `ignore now`: {ignoreUsage}"
  | .ok _ => false


#guard
  let g0 := Tests.ogreDeclaredAttacker
  let ogre := Tests.namedPermanent g0 "Gray Ogre"
  let bears := Tests.namedPermanent g0 "Grizzly Bears"
  match replayCompleteGame g0
      ["main phase", "pass", s!"block {bears.id} {ogre.id}", "concede"] with
  | .ok g' =>
    g'.over && !g'.log.any (fun s => Tests.mentions s "postcombat main")
  | .error _ => false

-- `ignore` is not cancelled when the other player uses `main phase`.

#guard describeCheckResult { Tests.started with result := some (.won ⟨0⟩) } == "Winner: Chandra"

#guard shouldWriteOutput false false true "first"

#guard !shouldWriteOutput false false true "state"

#guard !shouldWriteOutput false false true "visible"

#guard shouldAutoPay Tests.targetedBolt []

#guard !shouldAutoPay Tests.paidHunter []

#guard shouldAutoPay Tests.proposedBauble []

#guard shouldAutoPay Tests.titaniaPaidDiscard []


#guard shouldAutoPass Tests.started []

#guard
  let g := { Tests.readyToDeclareAttackers with
    objects := Tests.readyToDeclareAttackers.objects.map (fun o =>
      { o with status := { o.status with tapped := true } }) }
  shouldAutoNoAttack g []

#guard
  let g := { Tests.readyToDeclareBlockers with
    objects := Tests.readyToDeclareBlockers.objects.map (fun o =>
      if o.controlledBy ⟨1⟩ then
        { o with status := { o.status with tapped := true } }
      else o) }
  !shouldAutoNoBlock g ["noblock"]

#guard !shouldAutoTarget Tests.proposedSmite ["target opponent"]
