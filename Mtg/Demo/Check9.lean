import Mtg.Demo
import Mtg.Engine.Fixture

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Game
open Mtg.Engine.Tests
open Mtg.Demo
open Mtg.Demo.Render

#guard
  match parseArgs [
      "--name", "Elspeth", "--deck", "white",
      "--name", "Jace", "--deck", "blue"] with
  | .ok opt => opt.players == elspethJace
  | _ => false


#guard
  match parseArgs ["--interactive", "--name", "Elspeth", "--deck", "W",
      "--name", "Chandra", "--deck", "r"] with
  | .ok opt =>
    opt.interactive &&
    opt.players[0]!.name == "Elspeth" && opt.players[0]!.deck == .welcome .white &&
    opt.players[1]!.name == "Chandra" && opt.players[1]!.deck == .welcome .red
  | _ => false


#guard
  match parseDeckList (hobbitRed.map (·.name)) with
  | .ok cards =>
    cards.size == 40 && cards.map (·.name) == hobbitRed.map (·.name)
  | .error _ => false


/- Phase 33 Item 4: `randomChoiceLines`, `parseAttackDest`, and `applyTap` read
layered `g.nameWithToken` and `g.isPlaneswalker` rather than printed fields. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let pwDef : CardDef := { name := "Printed Walker", types := #[.planeswalker], loyalty := some 4 }
  let cloneCardDef : CardDef := { grizzlyBears with name := "Cloned Relic" }
  let cloneGroveDef : CardDef := { forest with name := "Cloned Grove" }
  let tokDef : CardDef := { grizzlyBears with name := "Printed Cub", isToken := true }
  let cloneTokDef : CardDef := { grizzlyBears with name := "Cloned Wolf" }
  let g0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent afterDraw grizzlyBears p1 p1) pwDef p1 p1)
        grizzlyBears p0 p0)
      forest p0 p0
  let (g0, tokObj) := g0.createOneToken p0 tokDef (cause := some (.gameRule .staticAbility))
  let p1BearId := (g0.permanentsOf p1).find? (·.name == grizzlyBears.name) |>.get!.id
  let p1PwId := (g0.permanentsOf p1).find? (·.name == "Printed Walker") |>.get!.id
  let p0BearId := (g0.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let p0ForestId := (g0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  -- Apply Layer 1 copy names and Layer 4 type modifications:
  let g :=
    (((((g0.createEffect (.layered (.objects #[p1BearId]) (.types .add #[.planeswalker] #[] #[]) .indefinite)).createEffect
      (ContinuousEffectSpec.copy p1PwId cloneCardDef)).createEffect
      (ContinuousEffectSpec.onlyFoodArtifact p1PwId)).createEffect
      (ContinuousEffectSpec.copy p0BearId cloneCardDef)).createEffect
      (ContinuousEffectSpec.copy p0ForestId cloneGroveDef)).createEffect
      (ContinuousEffectSpec.copy tokObj.id cloneTokDef)
  -- 1. `randomChoiceLines` formats Layer 1 copy names (with `" (token)"` suffix for tokens):
  let choiceStr := randomChoiceLines g #[p0BearId, tokObj.id]
  let randomChoiceOk :=
    choiceStr == s!"  {p0BearId} Cloned Relic\n  {tokObj.id} Cloned Wolf (token)"
  -- 2. `parseAttackDest` accepts a creature granted `.planeswalker` in Layer 4, and rejects a
  --    printed planeswalker that lost `.planeswalker` in Layer 4 using its Layer 1 name:
  let attackGrantedPwOk :=
    match parseAttackDest g p0 s!"{p1BearId}" with
    | .ok (pid, oid) => pid == p1 && oid == some p1BearId
    | .error _ => false
  let attackLostPwOk :=
    match parseAttackDest g p0 s!"{p1PwId}" with
    | .error msg => msg == "Cloned Relic is not a planeswalker on the battlefield"
    | .ok _ => false
  -- 3. `applyTap` error messages use `g.nameWithToken`:
  let tapNoManaOk :=
    match applyTap g p0 [s!"{p0BearId}"] with
    | .error msg => msg == "Cloned Relic has no mana ability"
    | .ok _ => false
  let tapWrongColorOk :=
    match applyTap g p0 [s!"{p0ForestId}", "R"] with
    | .error msg => msg == s!"Cloned Grove cannot produce {ManaType.colored .red}"
    | .ok _ => false
  randomChoiceOk && attackGrantedPwOk && attackLostPwOk && tapNoManaOk && tapWrongColorOk


