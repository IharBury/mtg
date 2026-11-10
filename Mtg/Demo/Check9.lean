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


/- Phase 34 Item 4: `defaultTapMana`, `applySacrifice`, `applyDiscard`, `parseTarget`,
`hasGameStatePriorityAction`, `stackFaceExtras`, `exilePlayManaCost`, and `zoneLine`
use `g.baseCard` / `g.name` / `g.retainsPrintedAbilities` instead of `o.printed`. -/
private def mustHoldCheck9 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Check9 Phase 34 Item 4 failed: {label}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gMain := emptyHand afterDraw p0
  -- 1. `defaultTapMana`: printed `tapAddAnyColorEqualToPower` lost via Layer 6 `.abilities {} .all`
  --    with a granted `{T}: Add {C}{C}` mana ability returns `.colorless` (not `.green`),
  --    while a `grizzlyBears` copied in Layer 1 to `tapAnyPowerDef` uses the `tapAddAnyColorEqualToPower` branch:
  let tapAnyPowerDef : CardDef := {
    grizzlyBears with
    name := "Power Channeler"
    tapAddAnyColorEqualToPower := true
  }
  let gTap0 := addPermanent (addPermanent gMain tapAnyPowerDef p0 p0) grizzlyBears p0 p0
  let chanId := (gTap0.permanentsOf p0).find? (·.name == "Power Channeler") |>.get!.id
  let bearId := (gTap0.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let gTapLayered :=
    ((gTap0.createEffect (.layered (.objects #[chanId]) (.abilities {} .all) .indefinite)).createEffect
      (.permission (some p0) (.colorlessGrant chanId chanId) .indefinite)).createEffect
      (ContinuousEffectSpec.copy bearId tapAnyPowerDef)
  let defaultTapOk :=
    defaultTapMana gTapLayered p0 (gTapLayered.object! chanId) == some .colorless &&
    defaultTapMana gTapLayered p0 (gTapLayered.object! bearId) == some (.colored .green)
  -- 2. `applySacrifice []` and `applyDiscard []` inspect `(g.baseCard spell)` on `chooseAdditionalCost`:
  let sacOrPayDef : CardDef := {
    name := "Sac Or Pay Copy"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostOrPayGeneric := some 2
    spellEffect := some (Effect.gainLife 1)
  }
  let discOrPayDef : CardDef := {
    name := "Disc Or Pay Copy"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    additionalCostDiscardOrPayGeneric := some 2
    spellEffect := some (Effect.gainLife 1)
  }
  let plainSorcery : CardDef := {
    name := "Plain Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let gAdd0 :=
    addPermanent
      (insertObject (insertObject gMain forest p0 (.hand p0)) plainSorcery p0 (.hand p0))
      grizzlyBears p0 p0
  let handSpellId := (gAdd0.player p0).hand.back!
  let (gAddStack, stackSpellId) := gAdd0.move handSpellId .stack (some p0)
  let spellObj := gAddStack.object! stackSpellId
  let prop : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := stackSpellId
    original := spellObj
    originalSnapshot := gAddStack.snapshot spellObj
  }
  let gChooseAddPrompt :=
    gAddStack.changes #[
      .pushStack { objectId := stackSpellId, controller := p0, targets := #[] },
      .proposedSpell (some prop),
      .pending (.chooseAdditionalCost p0) ]
  let gSacCopied := gChooseAddPrompt.createEffect (ContinuousEffectSpec.copy stackSpellId sacOrPayDef)
  let gDiscCopied := gChooseAddPrompt.createEffect (ContinuousEffectSpec.copy stackSpellId discOrPayDef)
  let addCostDispatchOk :=
    !(applySacrifice gChooseAddPrompt p0 []).isOk &&
    (applySacrifice gSacCopied p0 []).isOk &&
    !(applyDiscard gChooseAddPrompt p0 []).isOk &&
    (applyDiscard gDiscCopied p0 []).isOk
  -- 3. `parseTarget` by card name matches Layer 1 `g.name o` rather than `o.name`:
  let boltDef : CardDef := {
    lightningBolt with
    manaCost := ManaCost.empty
  }
  let gTarg0 :=
    insertObject (addPermanent gMain grizzlyBears p1 p1) boltDef p0 (.hand p0)
  let p1BearId := (gTarg0.permanentsOf p1)[0]!.id
  let boltHandId := (gTarg0.player p0).hand.back!
  let cloneTargetDef : CardDef := { grizzlyBears with name := "Cloned Target" }
  let gTargCopied := gTarg0.createEffect (ContinuousEffectSpec.copy p1BearId cloneTargetDef)
  let gTargPrompt := mustApply gTargCopied p0 (.cast boltHandId)
  let parseTargetOk :=
    (match parseTarget gTargPrompt p0 "cloned target" with
     | .ok t => t == Target.permanent p1BearId
     | .error _ => false) &&
    (match parseTarget gTargPrompt p0 "grizzly bears" with
     | .error msg => msg == targetUsage
     | .ok _ => false)
  -- 4. `hasGameStatePriorityAction` reads `(g.baseCard o).manaCost` and `(g.baseCard o).adventure`:
  let expensiveSpell : CardDef := {
    name := "Expensive Orb"
    manaCost := ManaCost.ofGeneric 5
    types := #[.sorcery]
    spellEffect := some (Effect.gainLife 1)
  }
  let freeSpellCopy : CardDef := {
    expensiveSpell with
    name := "Zero Orb"
    manaCost := ManaCost.empty
  }
  let advCopy : CardDef := {
    expensiveSpell with
    name := "Zero Adventure"
    adventure := some {
      name := "Free Quest"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellEffect := some (Effect.gainLife 1)
    }
  }
  let gPrio0 := insertObject gMain expensiveSpell p0 (.hand p0)
  let expHandId := (gPrio0.player p0).hand.back!
  let gPrioFreeCast := gPrio0.createEffect (ContinuousEffectSpec.copy expHandId freeSpellCopy)
  let gPrioFreeAdv := gPrio0.createEffect (ContinuousEffectSpec.copy expHandId advCopy)
  let prioActionOk :=
    !hasGameStatePriorityAction gPrio0 p0 &&
    hasGameStatePriorityAction gPrioFreeCast p0 &&
    hasGameStatePriorityAction gPrioFreeAdv p0
  -- 5. `stackFaceExtras`, `exilePlayManaCost`, and `zoneLine` use `g.baseCard o`:
  let copiedStackDef : CardDef := {
    plainSorcery with
    name := "Copied Stack Spell"
    keywords := { flying := true }
  }
  let gStackCopied := gChooseAddPrompt.createEffect (ContinuousEffectSpec.copy stackSpellId copiedStackDef)
  let gUnlistedStack := gStackCopied.change (.removeStackEntry stackSpellId)
  let gExLand0 := insertObject gMain forest p1 .exile
  let exLandObj := (gExLand0.objects.filter (fun o => o.zone == .exile)).back!
  let gExLandPerm :=
    (gExLand0.createEffect (.playPermission exLandObj.id {
      player := p0
      whileExiled := true
      withoutManaCost := false } 0)).createEffect
      (ContinuousEffectSpec.copy exLandObj.id grayOgre)
  let gExLandFreePerm :=
    (gExLand0.createEffect (.playPermission exLandObj.id {
      player := p0
      whileExiled := true
      withoutManaCost := true } 0)).createEffect
      (ContinuousEffectSpec.copy exLandObj.id grayOgre)
  let renderLayeredOk :=
    mustHoldCheck9 "5a.stackFaceExtras"
      (mentions (stackFaceExtras gStackCopied (gStackCopied.object! stackSpellId)) "flying") &&
    mustHoldCheck9 "5b.zoneLineStack"
      (mentions (zoneLine gStackCopied .stack stackSpellId) "flying") &&
    mustHoldCheck9 "5c.zoneLineUnlistedStack"
      (mentions (zoneLine gUnlistedStack .stack stackSpellId) "flying") &&
    mustHoldCheck9 "5d.zoneLineCommand"
      (mentions (zoneLine gUnlistedStack .command stackSpellId) "flying") &&
    mustHoldCheck9 "5e.exilePlayManaCost"
      (exilePlayManaCost gExLandPerm (gExLandPerm.object! exLandObj.id) == "{2}{R}") &&
    mustHoldCheck9 "5f.exilePlayManaCostFree"
      (exilePlayManaCost gExLandFreePerm (gExLandFreePerm.object! exLandObj.id) == "{0}")
  mustHoldCheck9 "defaultTapOk" defaultTapOk &&
  mustHoldCheck9 "addCostDispatchOk" addCostDispatchOk &&
  mustHoldCheck9 "parseTargetOk" parseTargetOk &&
  mustHoldCheck9 "prioActionOk" prioActionOk &&
  mustHoldCheck9 "renderLayeredOk" renderLayeredOk
