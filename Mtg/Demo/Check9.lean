import Mtg.Engine.Tests.Builders
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
  -- 1. `defaultTapMana`: printed power-scaled any-color mana lost via Layer 6 `.abilities {} .all`
  --    with a granted `{T}: Add {C}{C}` mana ability returns `.colorless` (not `.green`),
  --    while a `grizzlyBears` copied in Layer 1 to `tapAnyPowerDef` uses the power-scaled branch:
  let tapAnyPowerDef : CardDef := {
    grizzlyBears with
    name := "Power Channeler"
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf .anyColor (.objectStat .power .this))]
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
    spellAbility := some { effect := Effect.gainLife 1, additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.sacrificeArtifactOrCreatureOrPayGeneric 2)] }
  }
  let discOrPayDef : CardDef := {
    name := "Disc Or Pay Copy"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1, additionalCosts := #[AdditionalCostSpec.mandatory (CostSpec.discardCardOrPayGeneric 2)] }
  }
  let plainSorcery : CardDef := {
    name := "Plain Sorcery"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
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
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let freeSpellCopy : CardDef := {
    expensiveSpell with
    name := "Zero Orb"
    manaCost := ManaCost.empty
  }
  let advCopy : CardDef := {
    expensiveSpell with
    name := "Zero Adventure"
    subFaces := #[{
      kind := .adventure
      name := "Free Quest"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellAbility := some { effect := Effect.gainLife 1 }
    }]
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
    keywords := #[Keyword.flying]
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


/- Phase 46 Items 2 & 4: `Demo.Render` multi-grantee / `prepareSource` exile permissions and
`Demo` full `proposedManaSpend` + `tapPreservesPostManaCosts` on `uniquePayingSourceSet`. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gMain := emptyHand afterDraw p0
  -- 1. Multi-grantee exile permissions: `p0` free (`withoutManaCost := true`) + later `p1` paid:
  let gMultiEx0 := insertObject gMain grayOgre p1 .exile
  let exId := (gMultiEx0.objects.filter (·.zone == .exile)).back!.id
  let gMultiEx :=
    ((gMultiEx0.createEffect
        (.permission (some p0) (.playFromExile exId { player := p0, withoutManaCost := true }) (.untilNextTurnOf p0))
        (cause := some (.gameRule .staticAbility))).createEffect
      (.permission (some p1) (.playFromExile exId { player := p1 }) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility)))
  let multiExObj := gMultiEx.object! exId
  let multiRenderOk :=
    exilePlayManaCost gMultiEx multiExObj == "{0}" &&
    mentions (exilePlayPermissionClause gMultiEx multiExObj) "may be played by Chandra without paying its mana cost" &&
    mentions (exilePlayPermissionClause gMultiEx multiExObj) "may be played by Nissa)"
  -- 2. Stolen `prepareSource` attributes exile permission to new controller `p1`:
  let prepDef : CardDef := {
    grizzlyBears with
    name := "P46 PrepScout"
    subFaces := #[{
      kind := .prepare
      name := "P46 ScoutCall"
      manaCost := ManaCost.empty
      types := #[.instant]
      spellAbility := some { effect := Effect.gainLife 1 }
    }]
  }
  let gPrep0 := (addPermanent gMain prepDef p0 p0)
  let prepObj := (gPrep0.permanentsOf p0).back!
  let gPrep1 := gPrep0.becomePrepared prepObj
  let prepCopyId := (gPrep1.objects.filter (·.zone == .exile)).back!.id
  let gPrepStolen :=
    gPrep1.createEffect (.layered (.objects #[prepObj.id]) (.control p1) .untilEndOfTurn)
  let stolenPrepRenderOk :=
    mentions (exilePlayPermissionClause gPrepStolen (gPrepStolen.object! prepCopyId)) "may be played by Nissa" &&
    !mentions (exilePlayPermissionClause gPrepStolen (gPrepStolen.object! prepCopyId)) "Chandra"
  -- 3. `Demo` `canPayProposed`, `defaultTapMana`, `hasGameStatePriorityAction`, and `hasUniqueManaPayment`
  --    with `.subtypeSpellOrSource .goblin` and post-mana `.crew 2` preservation:
  let gobShrineDef : CardDef := {
    name := "P46 GobShrine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := Effect.addAnyColorSpendOnlySubtype "Goblin"
    }]
  }
  let gobAbDef : CardDef := {
    ragingGoblin with
    name := "P46 GobMage"
    activatedAbilities := #[{ cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1)], effect := Effect.gainLife 1 }]
  }
  let gGobDemo0 := addPermanent (addPermanent gMain gobShrineDef p0 p0) gobAbDef p0 p0
  let shrineObj := (gGobDemo0.permanentsOf p0).find? (·.name == "P46 GobShrine") |>.get!
  let gobMageId := (gGobDemo0.permanentsOf p0).find? (·.name == "P46 GobMage") |>.get!.id
  let gGobPool :=
    match gGobDemo0.activateManaAbility p0 shrineObj.id 0 #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gGobPoolProp := mustApply gGobPool p0 (.activate gobMageId 0)
  let gGobProp := mustApply gGobDemo0 p0 (.activate gobMageId 0)
  -- Post-mana `.crew 2` preservation in `hasUniqueManaPayment`: `[dork22 ({G}, 2/2), forest ({G})]` for `{1}` + `Crew 2`
  -- has a UNIQUE cost-preserving paying source (`#[forest]`, since `#[dork22]` breaks `Crew 2`!):
  let dork22 : CardDef := {
    grizzlyBears with
    name := "P46 CrewDork"
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .green]) (.const 1))]
  }
  let crewVeh : CardDef := {
    name := "P46 Skiff"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some (.fixed 4)
    toughness := some (.fixed 4)
    activatedAbilities := #[{ cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.otherThan .this, .hasType .creature, .tapped false, .controlledBy .you])], effect := Effect.gainLife 1 }]
  }
  let gUniqueCrew0 := addPermanent (addPermanent (addPermanent gMain crewVeh p0 p0) dork22 p0 p0) forest p0 p0
  let skiffId := (gUniqueCrew0.permanentsOf p0).find? (·.name == "P46 Skiff") |>.get!.id
  let forestId := (gUniqueCrew0.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let gUniqueCrewProp := mustApply gUniqueCrew0 p0 (.activate skiffId 0)
  let demoAllowancesAndCrewOk :=
    hasGameStatePriorityAction gGobPool p0 &&
    canPayProposed gGobPoolProp p0 gGobPoolProp.proposedSpell.get! &&
    defaultTapMana gGobProp p0 (gGobProp.object! shrineObj.id) == some (.colored .white) &&
    hasUniqueManaPayment gUniqueCrewProp &&
    (let prop := gUniqueCrewProp.proposedSpell.get!
     let spend := gUniqueCrewProp.proposedManaSpend prop
     match uniquePayingSourceSet gUniqueCrewProp (gUniqueCrewProp.player p0).manaPool prop.cost
       (gUniqueCrewProp.manaSourcesForProposed p0 prop) spend (some (p0, prop)) with
     | some #[src] => src.1.id == forestId
     | _ => false)
  mustHoldCheck9 "p46_multiRenderOk" multiRenderOk &&
  mustHoldCheck9 "p46_stolenPrepRenderOk" stolenPrepRenderOk &&
  mustHoldCheck9 "p46_demoAllowancesAndCrewOk" demoAllowancesAndCrewOk


/- Phase 47 Items 2 & 4: `Demo.hasGameStatePriorityAction` exile permissions & `canActivate`
(`idx? := some idx` + `activationManaCost`), `uniquePayingSourceSetLarge` `!subOk rest`, and
`hasUniqueManaPayment` Convoke / Improvise guard. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0
  -- 1. `hasGameStatePriorityAction` exile permissions (`withoutManaCost`, `payLifeEqualManaValue`, `fromAdventure`):
  let sorc3Def : CardDef := {
    name := "P47 Sorc3"
    manaCost := ManaCost.ofGeneric 3
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let adv3Def : CardDef := {
    grizzlyBears with
    name := "P47 AdvKnight"
    manaCost := ManaCost.ofGeneric 3
    subFaces := #[{
      kind := .adventure
      name := "P47 AdvQuest"
      manaCost := ManaCost.zero
      types := #[.instant]
      spellAbility := some { effect := Effect.gainLife 1 }
    }]
  }
  let gEx0 := insertObject gMain sorc3Def p0 .exile
  let exSorcId := (gEx0.objects.filter (·.zone == .exile)).back!.id
  let gExPaidNoMana :=
    gEx0.createEffect (.permission (some p0) (.playFromExile exSorcId { player := p0 }) .untilEndOfTurn)
  let gExFree :=
    gEx0.createEffect (.permission (some p0) (.playFromExile exSorcId { player := p0, withoutManaCost := true }) .untilEndOfTurn)
  let gExPayLifeOk :=
    gEx0.createEffect (.permission (some p0) (.playFromExile exSorcId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
  let gExPayLifeLow := gExPayLifeOk.loseLife p0 18
  let gExAdv0 := insertObject gMain adv3Def p0 .exile
  let exAdvId := (gExAdv0.objects.filter (·.zone == .exile)).back!.id
  let gExFromAdv :=
    gExAdv0.createEffect (.permission (some p0) (.playFromExile exAdvId { player := p0, fromAdventure := true }) .untilEndOfTurn)
  let gExCleanAdv :=
    gExAdv0.createEffect (.permission (some p0) (.playFromExile exAdvId { player := p0 }) .untilEndOfTurn)
  let demoExilePrioOk :=
    !hasGameStatePriorityAction gExPaidNoMana p0 &&
    hasGameStatePriorityAction gExFree p0 &&
    hasGameStatePriorityAction gExPayLifeOk p0 &&
    !hasGameStatePriorityAction gExPayLifeLow p0 &&
    !hasGameStatePriorityAction gExFromAdv p0 &&
    hasGameStatePriorityAction gExCleanAdv p0

  -- 2. `hasGameStatePriorityAction` `canActivate` (`(idx? := some idx)` & `activationManaCost`):
  let onceAb : ActivatedAbility := {
    cost := CostSpec.empty
    turnLimit? := some 1
    effect := Effect.gainLife 1
  }
  let twinOnceDef : CardDef := {
    name := "P47 TwinShrine"
    types := #[.artifact]
    activatedAbilities := #[onceAb, onceAb]
  }
  let gTwin0 := addPermanent gMain twinOnceDef p0 p0
  let twinId := (gTwin0.permanentsOf p0).back!.id
  let gTwinUsed0 := mustApply gTwin0 p0 (.activate twinId 0)
  let gTwinUsedBoth := mustApply gTwinUsed0 p0 (.activate twinId 1)
  let legCreatureDef : CardDef := {
    grizzlyBears with
    name := "P47 LegendHero"
    supertypes := #[.legendary]
  }
  let discRelicDef : CardDef := {
    name := "P47 LegendRelic"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)]
      costReductions := #[ActivationCostReduction.ifControlLegendary 2]
      effect := Effect.gainLife 1
    }]
  }
  let gMainOneMana := gMain.addMana p0 (.colored .green) 1
  let gRelicNoLeg := addPermanent gMainOneMana discRelicDef p0 p0
  let gRelicWithLeg := addPermanent gRelicNoLeg legCreatureDef p0 p0
  let demoCanActivateOk :=
    hasGameStatePriorityAction gTwinUsed0 p0 &&
    !hasGameStatePriorityAction gTwinUsedBoth p0 &&
    !hasGameStatePriorityAction gRelicNoLeg p0 &&
    hasGameStatePriorityAction gRelicWithLeg p0

  -- 3. `uniquePayingSourceSetLarge` (>20 sources, `singles.size == 1`, `!subOk rest`):
  let urBoilerDef : CardDef := {
    name := "P47 Boilerworks"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .blue, .const 1), (.colored .red, .const 1)])]
  }
  let gLarge0 :=
    Id.run do
      let mut g := addPermanent gMain urBoilerDef p0 p0
      for _ in [0:20] do
        g := addPermanent g forest p0 p0
      return g
  let boilerId := (gLarge0.permanentsOf p0).find? (·.name == urBoilerDef.name) |>.get!.id
  let largeSrcs := gLarge0.manaSources p0
  let urCost : ManaCost := { symbols := #[.colored .blue, .colored .red] }
  let largeGenericNotUnique :=
    largeSrcs.size == 21 &&
    (uniquePayingSourceSetLarge gLarge0 ManaPool.empty (ManaCost.ofGeneric 2) largeSrcs).isNone
  let largeUrUnique :=
    match uniquePayingSourceSetLarge gLarge0 ManaPool.empty urCost largeSrcs with
    | some #[src] => src.1.id == boilerId
    | _ => false

  -- 4. `hasUniqueManaPayment` Convoke & Improvise guard:
  let convokeSpellDef : CardDef := {
    name := "P47 ConvokeChant"
    manaCost := ManaCost.ofGenericAndColor 1 .green
    types := #[.sorcery]
    keywords := #[Keyword.convoke]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let improviseSpellDef : CardDef := {
    name := "P47 ImproviseBolt"
    manaCost := ManaCost.ofGenericAndColor 1 .blue
    types := #[.sorcery]
    keywords := #[.simple .improvise]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let inertArtDef : CardDef := { name := "P47 InertCog", types := #[.artifact] }
  let gConv0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent gMain forest p0 p0) forest p0 p0) grizzlyBears p0 p0)
      convokeSpellDef p0 (.hand p0)
  let gConvProp := mustApply gConv0 p0 (.cast (gConv0.player p0).hand.back!)
  let convBearId := (gConv0.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let (gConvNoCreature, _) := gConvProp.move convBearId .exile none
  let gImp0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent gMain island p0 p0) forest p0 p0) inertArtDef p0 p0)
      improviseSpellDef p0 (.hand p0)
  let gImpProp := mustApply gImp0 p0 (.cast (gImp0.player p0).hand.back!)
  let impCogId := (gImp0.permanentsOf p0).find? (·.name == inertArtDef.name) |>.get!.id
  let (gImpNoArtifact, _) := gImpProp.move impCogId .exile none
  let demoConvImpOk :=
    !hasUniqueManaPayment gConvProp &&
    hasUniqueManaPayment gConvNoCreature &&
    !hasUniqueManaPayment gImpProp &&
    hasUniqueManaPayment gImpNoArtifact

  mustHoldCheck9 "p47_demoExilePrioOk" demoExilePrioOk &&
  mustHoldCheck9 "p47_demoCanActivateOk" demoCanActivateOk &&
  mustHoldCheck9 "p47_largeGenericNotUnique" largeGenericNotUnique &&
  mustHoldCheck9 "p47_largeUrUnique" largeUrUnique &&
  mustHoldCheck9 "p47_demoConvImpOk" demoConvImpOk


/- Phase 48 Items 2 & 4: `Demo.hasGameStatePriorityAction` Null Summoner `anyMana` &
`useImplicitPermissions := false` + usable non-plain CR 605 mana abilities,
`uniquePayingSourceSetLarge` post-mana cost-preserving subset check (`anySubsetOk rest`),
`hasUniqueManaPayment` non-plain CR 605 guard, and mixed-color `.combination` `autopay`. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `hasGameStatePriorityAction` Null Summoner (`mayCastExiledBySource`) `anyMana` & unpayable `payLifeEqualManaValue` guard:
  let nullSummonerDef : CardDef := {
    grizzlyBears with
    name := "P48 NullSummoner"
    staticAbilities := #[.castExiledWithSevenInGraveyard]
    activatedAbilities := #[]
  }
  let rrSorcDef : CardDef := {
    name := "P48 RedPyre"
    manaCost := { symbols := #[.colored .red, .colored .red] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gNullBase :=
    Id.run do
      let mut g := addPermanent gMain nullSummonerDef p0 p0
      for _ in [0:7] do
        g := insertObject g grizzlyBears p0 (.graveyard p0)
      return g
  let nullId := (gNullBase.permanentsOf p0).find? (·.name == nullSummonerDef.name) |>.get!.id
  let gNullHand := insertObject gNullBase rrSorcDef p0 (.hand p0)
  let (gNullExRaw, nullExId) := gNullHand.move (gNullHand.player p0).hand.back! .exile none
  let gNullEx := (gNullExRaw.changeObject nullExId (.exiledBy (some nullId))).loseLife p0 19
  let gNullUnpayableLifeNoMana :=
    gNullEx.createEffect
      (.permission (some p0) (.playFromExile nullExId { player := p0, payLifeEqualManaValue := true }) .untilEndOfTurn)
  let gNullUnpayableLifeGreen := gNullUnpayableLifeNoMana.addMana p0 (.colored .green) 2
  let gNullFromAdvGreen :=
    (gNullEx.createEffect
      (.permission (some p0) (.playFromExile nullExId { player := p0, fromAdventure := true }) .untilEndOfTurn)).addMana
      p0 (.colored .green) 2
  let demoNullPrioOk :=
    !hasGameStatePriorityAction gNullUnpayableLifeNoMana p0 &&
    hasGameStatePriorityAction gNullUnpayableLifeGreen p0 &&
    hasGameStatePriorityAction gNullFromAdvGreen p0

  -- 2. Non-plain CR 605 mana abilities (`Catalog.treasureToken`) in `hasGameStatePriorityAction` & `hasUniqueManaPayment`:
  let (gWithTreasure, trObj) := gMain.createOneToken p0 Catalog.treasureToken
  let gGreenSpellDef : CardDef := {
    name := "P48 GreenChant"
    manaCost := { symbols := #[.colored .green] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gTrForest0 := insertObject (addPermanent gWithTreasure forest p0 p0) gGreenSpellDef p0 (.hand p0)
  let gTrForestProp := mustApply gTrForest0 p0 (.cast (gTrForest0.player p0).hand.back!)
  let (gNoTrForestProp, _) := gTrForestProp.move trObj.id .exile none
  let demoNonPlainOk :=
    !hasGameStatePriorityAction gMain p0 &&
    hasGameStatePriorityAction gWithTreasure p0 &&
    !hasUniqueManaPayment gTrForestProp &&
    hasUniqueManaPayment gNoTrForestProp

  -- 3. `uniquePayingSourceSetLarge` (>20 sources, `singles.size == 1`, `anySubsetOk rest` preserving post-mana tap pick):
  let solRingDef : CardDef := {
    name := "P48 SolRing"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 2)])]
  }
  let hasteElfDef : CardDef := {
    llanowarElves with
    name := "P48 HasteElf"
    keywords := #[Keyword.haste]
  }
  let tapCreature2Def : CardDef := {
    name := "P48 TapShrine"
    types := #[.enchantment]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2), .tapObjects (.exact 1) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.gainLife 2
    }]
  }
  let gLargeTap0 :=
    Id.run do
      let mut g := addPermanent (addPermanent gMain tapCreature2Def p0 p0) solRingDef p0 p0
      for _ in [0:20] do
        g := addPermanent g hasteElfDef p0 p0
      return g
  let shrineId := (gLargeTap0.permanentsOf p0).find? (·.name == tapCreature2Def.name) |>.get!.id
  let solRingId := (gLargeTap0.permanentsOf p0).find? (·.name == solRingDef.name) |>.get!.id
  let gLargeTapProp := mustApply gLargeTap0 p0 (.activate shrineId 0)
  let largeTapProp := gLargeTapProp.proposedSpell.get!
  let largeTapSrcs := gLargeTapProp.manaSourcesForProposed p0 largeTapProp
  let ccCost : ManaCost := { symbols := #[.colorless, .colorless] }
  let largePostManaSubsetOk :=
    largeTapSrcs.size == 21 &&
    (uniquePayingSourceSetLarge gLargeTapProp ManaPool.empty (ManaCost.ofGeneric 2)
      largeTapSrcs (gLargeTapProp.proposedManaSpend largeTapProp) (some (p0, largeTapProp))).isNone &&
    !hasUniqueManaPayment gLargeTapProp &&
    (match uniquePayingSourceSetLarge gLargeTapProp ManaPool.empty ccCost
        largeTapSrcs (gLargeTapProp.proposedManaSpend largeTapProp) (some (p0, largeTapProp)) with
     | some #[src] => src.1.id == solRingId
     | _ => false)

  -- 4. `applyAutopay` (`applyAutopaySteps`) emitting `mana <id> 1 UR` + `pay` on a mixed-color `.combination` ability:
  let comboFilterDef : CardDef := {
    name := "P48 CascadeConduit"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .blue, .colored .red]) (.const 2))]
  }
  let urSpellDef : CardDef := {
    name := "P48 SteamSurge"
    manaCost := { symbols := #[.colored .blue, .colored .red] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gCombo0 := insertObject (addPermanent gMain comboFilterDef p0 p0) urSpellDef p0 (.hand p0)
  let conduitId := (gCombo0.permanentsOf p0).find? (·.name == comboFilterDef.name) |>.get!.id
  let gComboProp := mustApply gCombo0 p0 (.cast (gCombo0.player p0).hand.back!)
  let demoComboAutopayOk :=
    match applyAutopay gComboProp p0 [] with
    | .ok res =>
      res.game.stack.size == 1 &&
      res.commands == #[s!"mana {conduitId} 1 UR", "pay"]
    | .error _ => false

  mustHoldCheck9 "p48_demoNullPrioOk" demoNullPrioOk &&
  mustHoldCheck9 "p48_demoNonPlainOk" demoNonPlainOk &&
  mustHoldCheck9 "p48_largePostManaSubsetOk" largePostManaSubsetOk &&
  mustHoldCheck9 "p48_demoComboAutopayOk" demoComboAutopayOk


/- Phase 49 Items 2 & 4: `Demo.hasGameStatePriorityAction` `canCastFrontFace` vs
`canCastAndPayMorphFaceDown`, `canPaySpellCostFromSources` /
`canPayAnnouncedAdditionalFromSources` / `canPayAbilityCostFromSources` on
`.combination` sources, and `hasUsableNonPlainManaAbility` `canPayFromSources` parity. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `hasGameStatePriorityAction` separates `canCastFrontFace` from `canCastAndPayMorphFaceDown`:
  --    (a) `{2}` creature whose front face requires >= 3 cards in graveyard + `morph := some {2}`:
  --        at `{2}` mana in pool, neither front face (forbidden) nor Morph `{3}` (too expensive) is castable;
  --        at `{3}` mana in pool, Morph `{3}` IS castable!
  --    (b) `{6}` creature whose front face is legal + `morph := some {2}`:
  --        at `{2}` mana, neither is affordable; at `{3}` mana, Morph `{3}` makes `hasGameStatePriorityAction` true!
  let gyThresholdMorphDef : CardDef := {
    grizzlyBears with
    name := "P49 ThresholdMorph"
    manaCost := ManaCost.ofGeneric 2
    staticAbilities := #[.castOnlyIfGraveyardAtLeast 3]
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let bigMorphDef : CardDef := {
    grizzlyBears with
    name := "P49 ColossusMorph"
    manaCost := ManaCost.ofGeneric 6
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gForbidFront2 := (insertObject gMain gyThresholdMorphDef p0 (.hand p0)).addMana p0 .colorless 2
  let gForbidFront3 := gForbidFront2.addMana p0 .colorless 1
  let gBigMorph2 := (insertObject gMain bigMorphDef p0 (.hand p0)).addMana p0 .colorless 2
  let gBigMorph3 := gBigMorph2.addMana p0 .colorless 1
  let demoMorphSplitOk :=
    !hasGameStatePriorityAction gForbidFront2 p0 &&
    hasGameStatePriorityAction gForbidFront3 p0 &&
    !hasGameStatePriorityAction gBigMorph2 p0 &&
    hasGameStatePriorityAction gBigMorph3 p0

  -- 2. `canPaySpellCostFromSources` (spell + Adventure) & `canPayAbilityCostFromSources`
  --    succeed on a mixed-color `.combination` source (`{U}`/`{R}` combination of 2)
  --    where single-color `availableMana` collapses to `{U}{U}`:
  let comboFilterDef : CardDef := {
    name := "P49 SteamConduit"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .blue, .colored .red]) (.const 2))]
  }
  let urSpellDef : CardDef := {
    name := "P49 SteamBolt"
    manaCost := { symbols := #[.colored .blue, .colored .red] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let urAdvCardDef : CardDef := {
    grizzlyBears with
    name := "P49 SteamKnight"
    manaCost := ManaCost.ofGeneric 5
    subFaces := #[{
      kind := .adventure
      name := "P49 SteamSpark"
      manaCost := { symbols := #[.colored .blue, .colored .red] }
      types := #[.instant]
      spellAbility := some { effect := Effect.gainLife 1 }
    }]
  }
  let urShrineDef : CardDef := {
    name := "P49 SteamShrine"
    types := #[.enchantment]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.colored .blue, .colored .red] }]
      effect := Effect.gainLife 1
    }]
  }
  let gComboBase := addPermanent gMain comboFilterDef p0 p0
  let gComboSpell := insertObject gComboBase urSpellDef p0 (.hand p0)
  let urSpellObj := gComboSpell.object! (gComboSpell.player p0).hand.back!
  let gComboAdv := insertObject gComboBase urAdvCardDef p0 (.hand p0)
  let urAdvObj := gComboAdv.object! (gComboAdv.player p0).hand.back!
  let gComboAct := addPermanent gComboBase urShrineDef p0 p0
  let shrineObj := (gComboAct.permanentsOf p0).find? (·.name == urShrineDef.name) |>.get!
  let demoComboPayOk :=
    !(gComboBase.availableMana p0).canPay urSpellDef.manaCost &&
    gComboSpell.canPaySpellCostFromSources p0 urSpellObj urSpellDef.manaCost &&
    gComboAdv.canPaySpellCostFromSources p0 urAdvObj
      (urAdvCardDef.adventure.get!.toCardDef).manaCost &&
    gComboAct.canPayAbilityCostFromSources p0 shrineObj
      shrineObj.printed.activatedAbilities[0]!
      shrineObj.printed.activatedAbilities[0]!.cost.mana

  -- 3. `hasUsableNonPlainManaAbility` uses `canPayFromSources` (unpayable `{1}, {T}: Add {G}{G}`
  --    without mana keeps `hasGameStatePriorityAction` false; `{U}{R}, {T}: Add {G}{G}` with
  --    `comboFilterDef` makes `hasUsableNonPlainManaAbility` true):
  let filter1ToGGDef : CardDef := {
    name := "P49 Signet1GG"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .tapSelf]
      effect := Effect.addMana #[.colored .green, .colored .green]
    }]
  }
  let filterURToGGDef : CardDef := {
    name := "P49 SignetURGG"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.colored .blue, .colored .red] }, .tapSelf]
      effect := Effect.addMana #[.colored .green, .colored .green]
    }]
  }
  let gUnpayableFilter := addPermanent gMain filter1ToGGDef p0 p0
  let gPayableFilter := gUnpayableFilter.addMana p0 .colorless 1
  let gComboFilterSignet := addPermanent gComboBase filterURToGGDef p0 p0
  let demoFilterManaOk :=
    !hasGameStatePriorityAction gUnpayableFilter p0 &&
    hasGameStatePriorityAction gPayableFilter p0 &&
    gComboFilterSignet.hasUsableNonPlainManaAbility p0

  mustHoldCheck9 "p49_demoMorphSplitOk" demoMorphSplitOk &&
  mustHoldCheck9 "p49_demoComboPayOk" demoComboPayOk &&
  mustHoldCheck9 "p49_demoFilterManaOk" demoFilterManaOk


/- Phase 50 Items 2b & 4a: `Demo.hasGameStatePriorityAction` recognizes Impending (`CR 702.176a`)
and `Demo.hasUniqueManaPayment` respects post-mana sacrifice & `.crew` reservations in
`hasUsableNonPlainManaAbility`. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0
  let impCardDef : CardDef := {
    grizzlyBears with
    name := "P50 DemoOverlord"
    types := #[.enchantment, .creature]
    manaCost := ManaCost.ofGeneric 6
    keywords := #[.impending 4 (CostSpec.ofGeneric 2)]
  }
  let gImp1 := (insertObject gMain impCardDef p0 (.hand p0)).addMana p0 .colorless 1
  let gImp2 := (insertObject gMain impCardDef p0 (.hand p0)).addMana p0 .colorless 2
  let demoImpendingPrioOk :=
    !hasGameStatePriorityAction gImp1 p0 &&
    hasGameStatePriorityAction gImp2 p0

  let sacSpellDef : CardDef := {
    name := "P50 DemoSacBolt"
    manaCost := { symbols := #[.colored .green] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 2, additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature] }
  }
  let (gTrOnly0, _) :=
    (insertObject (addPermanent gMain forest p0 p0) sacSpellDef p0 (.hand p0)).createOneToken
      p0 Game.treasureToken (cause := some (.gameRule .staticAbility))
  let gTrOnlyProp := mustApply gTrOnly0 p0 (.cast (gTrOnly0.player p0).hand.back!)
  let gTrExtra0 := addPermanent gTrOnly0 grizzlyBears p0 p0
  let gTrExtraProp := mustApply gTrExtra0 p0 (.cast (gTrExtra0.player p0).hand.back!)
  -- When Treasure is the sole sacrificeable permanent, sacrificing it for mana would make the
  -- spell's sacrifice cost unpayable, so tapping the Forest is the unique mana payment (`true`);
  -- when an extra creature exists, Treasure is also usable for mana (`false`):
  let demoUniqueManaSacOk :=
    hasUniqueManaPayment gTrOnlyProp &&
    !hasUniqueManaPayment gTrExtraProp

  mustHoldCheck9 "p50_demoImpendingPrioOk" demoImpendingPrioOk &&
  mustHoldCheck9 "p50_demoUniqueManaSacOk" demoUniqueManaSacOk


/- Phase 51 Item 4b: `Demo.hasUniqueManaPayment` / `uniquePayingSourceSet` /
`uniquePayingSourceSetLarge` soundness for `ManaSpendRestriction.legendarySpell` riders,
`ManaOutput.combination` leftover mana (CR 106.4), and post-mana preconditions
(`teamworkCreatures`, `needsBehold`, `sneakAttacker` exclusion, tap-less
`costPicksPayable`, and `zemoBoast`). -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `ManaSpendRestriction.legendarySpell` (*Delighted Halfling*):
  let legGreen2Def : CardDef := {
    grizzlyBears with
    name := "P51 LegendBear"
    supertypes := #[.legendary]
    manaCost := ManaCost.ofGenericAndColor 1 .green
  }
  let uncounterableLegDef : CardDef := {
    legGreen2Def with
    name := "P51 UncounterableLegend"
    staticAbilities := #[.spellCantBeCountered]
  }
  let legGeneric1Def : CardDef := {
    grizzlyBears with
    name := "P51 LegendConstruct"
    supertypes := #[.legendary]
    manaCost := ManaCost.ofGeneric 1
  }
  let legGreen1Def : CardDef := {
    grizzlyBears with
    name := "P51 LegendElf"
    supertypes := #[.legendary]
    manaCost := { symbols := #[.colored .green] }
  }
  let legGeneric2Def : CardDef := {
    grizzlyBears with
    name := "P51 LegendGolem"
    supertypes := #[.legendary]
    manaCost := ManaCost.ofGeneric 2
  }
  let hasteHalflingDef : CardDef := {
    Catalog.delightedHalfling with
    name := "P51 HasteHalfling"
    keywords := #[Keyword.haste]
  }
  let solRingDef : CardDef := {
    name := "P51 SolRing"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 2)])]
  }

  -- (a) Floating unrestricted `{1}{G}` in `pool` (`pool.canPay == true`) + untapped `hasteHalflingDef`:
  --     `false` on counterable legendary spell (tapping Halfling grants `.uncounterableThisCast`),
  --     `true` when already `.uncounterableThisCast` or non-legendary!
  let gFloat0 :=
    ((insertObject (addPermanent gMain hasteHalflingDef p0 p0) legGreen2Def p0 (.hand p0)).addMana
      p0 .colorless 1).addMana p0 (.colored .green) 1
  let gFloatProp := mustApply gFloat0 p0 (.cast (gFloat0.player p0).hand.back!)
  let gFloatUnc0 :=
    ((insertObject (addPermanent gMain hasteHalflingDef p0 p0) uncounterableLegDef p0 (.hand p0)).addMana
      p0 .colorless 1).addMana p0 (.colored .green) 1
  let gFloatUncProp0 := mustApply gFloatUnc0 p0 (.cast (gFloatUnc0.player p0).hand.back!)
  let gFloatUncProp :=
    gFloatUncProp0.createEffect (.uncounterableThisCast gFloatUncProp0.proposedSpell.get!.spellId)
  let gFloatNonLeg0 :=
    ((insertObject (addPermanent gMain hasteHalflingDef p0 p0) grizzlyBears p0 (.hand p0)).addMana
      p0 .colorless 1).addMana p0 (.colored .green) 1
  let gFloatNonLegProp := mustApply gFloatNonLeg0 p0 (.cast (gFloatNonLeg0.player p0).hand.back!)

  -- (b) Single `hasteHalflingDef` (`0` floating): `{1}` legendary spell -> `false` (`{C}` vs `.legendarySpell`),
  --     whereas `{G}` legendary spell -> `true` (only `.legendarySpell` ability produces `{G}`)!
  let gSingleGen0 := insertObject (addPermanent gMain hasteHalflingDef p0 p0) legGeneric1Def p0 (.hand p0)
  let gSingleGenProp := mustApply gSingleGen0 p0 (.cast (gSingleGen0.player p0).hand.back!)
  let gSingleGreen0 := insertObject (addPermanent gMain hasteHalflingDef p0 p0) legGreen1Def p0 (.hand p0)
  let gSingleGreenProp := mustApply gSingleGreen0 p0 (.cast (gSingleGreen0.player p0).hand.back!)

  -- (c) Superset rider flip (`solRing` `{C}{C}` + `hasteHalflingDef` on `{2}` legendary spell, both small and >20 sources):
  let gSup0 :=
    insertObject (addPermanent (addPermanent gMain solRingDef p0 p0) hasteHalflingDef p0 p0)
      legGeneric2Def p0 (.hand p0)
  let gSupProp := mustApply gSup0 p0 (.cast (gSup0.player p0).hand.back!)
  let restrictedElfManaDef : CardDef := {
    name := "P51 ElfOnlyRock"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := Effect.addAnyColorSpendOnlySubtype "Elf"
    }]
  }
  let gSupLarge0 := Id.run do
    let mut g := gSup0
    for _ in [0:20] do
      g := addPermanent g restrictedElfManaDef p0 p0
    return g
  let gSupLargeProp := mustApply gSupLarge0 p0 (.cast (gSupLarge0.player p0).hand.back!)
  let supLargeP := gSupLargeProp.proposedSpell.get!
  let supLargeAllSrcs :=
    (gSupLargeProp.permanentsOf p0).filterMap fun o =>
      if o.name == restrictedElfManaDef.name then some (o, #[ManaType.colored .green])
      else (gSupLargeProp.manaSourcesForProposed p0 supLargeP).find? (·.1.id == o.id)

  let demoRiderOk :=
    !hasUniqueManaPayment gFloatProp &&
    hasUniqueManaPayment gFloatUncProp &&
    hasUniqueManaPayment gFloatNonLegProp &&
    !hasUniqueManaPayment gSingleGenProp &&
    hasUniqueManaPayment gSingleGreenProp &&
    !hasUniqueManaPayment gSupProp &&
    supLargeAllSrcs.size == 22 &&
    (uniquePayingSourceSetLarge gSupLargeProp ManaPool.empty supLargeP.cost
      supLargeAllSrcs (gSupLargeProp.proposedManaSpend supLargeP) (some (p0, supLargeP))).isNone

  -- 2. `ManaOutput.combination` (`{R}`/`{G}` combination of 2) leftover mana (`CR 106.4`):
  --    Paying `{1}` leaves `{R}` or `{G}` (`!hasUniqueManaPayment`), while paying `{R}{G}` leaves `0` (`hasUniqueManaPayment`):
  let rgComboDef : CardDef := {
    name := "P51 FirelitGrove"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.combination (.explicit #[.colored .red, .colored .green]) (.const 2))]
  }
  let gen1SorcDef : CardDef := {
    name := "P51 Spark1"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let rgSorcDef : CardDef := {
    name := "P51 RgPulse"
    manaCost := { symbols := #[.colored .red, .colored .green] }
    types := #[.sorcery]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gCombo1 := insertObject (addPermanent gMain rgComboDef p0 p0) gen1SorcDef p0 (.hand p0)
  let gCombo1Prop := mustApply gCombo1 p0 (.cast (gCombo1.player p0).hand.back!)
  let gComboRg := insertObject (addPermanent gMain rgComboDef p0 p0) rgSorcDef p0 (.hand p0)
  let gComboRgProp := mustApply gComboRg p0 (.cast (gComboRg.player p0).hand.back!)
  let demoComboLeftoverOk :=
    !hasUniqueManaPayment gCombo1Prop &&
    hasUniqueManaPayment gComboRgProp

  -- 3. Post-mana preconditions in `hasUniqueManaPayment`:
  --    (a) `teamworkCreatures`, (b) `needsBehold`, (c) `sneakAttacker` as sole sacrificeable creature,
  --    (d) tap-less `costPicksPayable`, and (e) `zemoBoast`:
  let gBaseForest := addPermanent gMain forest p0 p0
  let gTw0 := insertObject (addPermanent gBaseForest grizzlyBears p0 p0) gen1SorcDef p0 (.hand p0)
  let twBearId := (gTw0.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let gTwProp0 := mustApply gTw0 p0 (.cast (gTw0.player p0).hand.back!)
  let gTwUntapped :=
    gTwProp0.change (.proposedSpell (some { gTwProp0.proposedSpell.get! with
      teamworkPaid := true, teamworkCreatures := #[twBearId] }))
  let gTwTapped := setTapped gTwUntapped twBearId true

  let gBeholdMissing :=
    gTwProp0.change (.proposedSpell (some { gTwProp0.proposedSpell.get! with needsBehold := some .dragon }))
  let dragonDef : CardDef := creature "P51 Whelp" ManaCost.empty #["Dragon"] 2 2
  let gBeholdPresent := addPermanent gBeholdMissing dragonDef p0 p0

  let sacCreatureSpellDef : CardDef := {
    name := "P51 SneakSac"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1, additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature] }
  }
  let gSneak0 :=
    ((insertObject (addPermanent gBaseForest grizzlyBears p0 p0) sacCreatureSpellDef p0 (.hand p0)).record
      (GameEvent.phaseBegan afterDraw.turnNumber .combat)).record
      (GameEvent.stepBegan afterDraw.turnNumber .declareBlockers p0)
  let snkBearId := (gSneak0.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let gSneak1 :=
    gSneak0.record (GameEvent.becameAttacking gSneak0.turnNumber
      (gSneak0.snapshot (gSneak0.object! snkBearId)) (.player p1) (.turnBased .declareAttackers))
  let gSneakProp0 := mustApply gSneak1 p0 (.cast (gSneak1.player p0).hand.back!)
  let gSneakSole :=
    gSneakProp0.change (.proposedSpell (some { gSneakProp0.proposedSpell.get! with
      needsSacrificeOther := true, sneakAttacker := some snkBearId }))
  let gSneakWithExtra := addPermanent gSneakSole grizzlyBears p0 p0

  let taplessAltarDef : CardDef := {
    name := "P51 SacAltar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .sacrifice (.exact 1) (.filter (.all #[.otherThan .this, .any #[.hasType .creature, .hasType .artifact]]))]
      effect := Effect.gainLife 1
    }]
  }
  let gAltar0 := addPermanent gBaseForest taplessAltarDef p0 p0
  let altarId := (gAltar0.permanentsOf p0).find? (·.name == taplessAltarDef.name) |>.get!.id
  let gAltarWithBear := addPermanent gAltar0 grizzlyBears p0 p0
  let bearOnAltarId := (gAltarWithBear.permanentsOf p0).find? (·.name == grizzlyBears.name) |>.get!.id
  let gAltarPropOk := mustApply gAltarWithBear p0 (.activate altarId 0)
  let (gAltarPropMissing, _) := gAltarPropOk.move bearOnAltarId .exile none

  let zemoPaidDef : CardDef := {
    Catalog.baronHelmutZemo with
    name := "P51 BaronZemo"
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric 1), .exile (.totalManaSymbolsAtLeast (some .black) (.const 15)) .yourGraveyard (.filter (.all #[.hasColor (.literal .black), .isKind .card]))]
      effect := Effect.gainLife 1
    }]
  }
  let bbbCardDef : CardDef := {
    name := "P51 DarkRitualists"
    manaCost := { symbols := #[.colored .black, .colored .black, .colored .black] }
    types := #[.creature]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
  }
  let gZemo0 := Id.run do
    let mut g := addPermanent gBaseForest zemoPaidDef p0 p0
    for _ in [0:5] do
      g := insertObject g bbbCardDef p0 (.graveyard p0)
    return g
  let zemoId := (gZemo0.permanentsOf p0).find? (·.name == zemoPaidDef.name) |>.get!.id
  let gZemoAtk :=
    gZemo0.record (GameEvent.attacked gZemo0.turnNumber p0 (gZemo0.snapshot (gZemo0.object! zemoId)) p1)
  let gZemoPropOk := mustApply gZemoAtk p0 (.activate zemoId 0)
  let oneGyId := (gZemoPropOk.player p0).graveyard.back!
  let (gZemoPropShort, _) := gZemoPropOk.move oneGyId .exile none

  let demoPostManaOk :=
    hasUniqueManaPayment gTwUntapped &&
    !hasUniqueManaPayment gTwTapped &&
    !hasUniqueManaPayment gBeholdMissing &&
    hasUniqueManaPayment gBeholdPresent &&
    !hasUniqueManaPayment gSneakSole &&
    hasUniqueManaPayment gSneakWithExtra &&
    hasUniqueManaPayment gAltarPropOk &&
    !hasUniqueManaPayment gAltarPropMissing &&
    hasUniqueManaPayment gZemoPropOk &&
    !hasUniqueManaPayment gZemoPropShort

  mustHoldCheck9 "p51_demoRiderOk" demoRiderOk &&
  mustHoldCheck9 "p51_demoComboLeftoverOk" demoComboLeftoverOk &&
  mustHoldCheck9 "p51_demoPostManaOk" demoPostManaOk

/- Phase 5: Extended `SpellRiderSpec` (`.gainsHaste` & `.entersWithPlusOneCounters n`)
in `Demo.hasUniqueManaPayment` — tapping a rider land vs. floating/plain mana changes
the creature spell's material rider outcome, whereas for a noncreature spell it does not! -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := afterDraw
  let hasteLandDef : CardDef := {
    name := "P5 Check9 HasteLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .green)) (riders := #[.gainsHaste])
    ]
  }
  let counterLandDef : CardDef := {
    name := "P5 Check9 CounterLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .green))
        (riders := #[.entersWithPlusOneCounters 2])
    ]
  }
  let gInstantDef : CardDef := {
    name := "P5 Check9 GreenInstant"
    manaCost := ManaCost.ofColor .green
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gCreatureDef : CardDef := {
    name := "P5 Check9 GreenCreature"
    manaCost := ManaCost.ofColor .green
    types := #[.creature]
    power := some (.fixed 2)
    toughness := some (.fixed 2)
  }
  -- Floating `{G}` + untapped `hasteLand`:
  -- * On a creature spell -> NOT unique (tapping hasteLand grants `.gainsHaste`)!
  -- * On a noncreature instant -> UNIQUE (`.gainsHaste` does not matter for noncreature spells)!
  let gHasteCre0 :=
    (insertObject (addPermanent gMain hasteLandDef p0 p0) gCreatureDef p0 (.hand p0)).addMana
      p0 (.colored .green) 1
  let gHasteCreProp := mustApply gHasteCre0 p0 (.cast (gHasteCre0.player p0).hand.back!)
  let gHasteInst0 :=
    (insertObject (addPermanent gMain hasteLandDef p0 p0) gInstantDef p0 (.hand p0)).addMana
      p0 (.colored .green) 1
  let gHasteInstProp := mustApply gHasteInst0 p0 (.cast (gHasteInst0.player p0).hand.back!)
  -- Untapped `forest` + untapped `counterLand` (`entersWithPlusOneCounters 2`) for `{G}`:
  -- * On a creature spell -> NOT unique (counterLand vs forest yields different counter bonus)!
  -- * With ONLY `counterLand` (no floating, no forest) for `{G}` creature -> UNIQUE!
  let gCtrBoth0 :=
    insertObject (addPermanent (addPermanent gMain forest p0 p0) counterLandDef p0 p0)
      gCreatureDef p0 (.hand p0)
  let gCtrBothProp := mustApply gCtrBoth0 p0 (.cast (gCtrBoth0.player p0).hand.back!)
  let gCtrOnly0 :=
    insertObject (addPermanent gMain counterLandDef p0 p0) gCreatureDef p0 (.hand p0)
  let gCtrOnlyProp := mustApply gCtrOnly0 p0 (.cast (gCtrOnly0.player p0).hand.back!)
  -- Floating `{G}` + untapped `counterLand` on a noncreature instant -> UNIQUE!
  let gCtrInst0 :=
    (insertObject (addPermanent gMain counterLandDef p0 p0) gInstantDef p0 (.hand p0)).addMana
      p0 (.colored .green) 1
  let gCtrInstProp := mustApply gCtrInst0 p0 (.cast (gCtrInst0.player p0).hand.back!)
  mustHoldCheck9 "p5_hasteCreNotUnique" (!hasUniqueManaPayment gHasteCreProp) &&
  mustHoldCheck9 "p5_hasteInstUnique" (hasUniqueManaPayment gHasteInstProp) &&
  mustHoldCheck9 "p5_ctrBothNotUnique" (!hasUniqueManaPayment gCtrBothProp) &&
  mustHoldCheck9 "p5_ctrOnlyUnique" (hasUniqueManaPayment gCtrOnlyProp) &&
  mustHoldCheck9 "p5_ctrInstUnique" (hasUniqueManaPayment gCtrInstProp)

/- Phase 52 Item 4a: `Demo.hasUniqueManaPayment` Treasure & *Path of Ancestry* provenance,
`ManaOutput.combination` color order with floating pool, and multi-source rider flips! -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := afterDraw
  let oneInstDef : CardDef := {
    name := "P52 Check9 OneInst"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let twoArtDef : CardDef := {
    name := "P52 Check9 TwoArt"
    manaCost := ManaCost.ofGeneric 2
    types := #[.artifact]
  }
  let smaugTrigDef : CardDef := {
    creature "P52 Check9 SmaugWatch" ManaCost.empty #["Dragon"] 4 4 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some .fromTreasure))
        (Effect.gainLife 2)
    ]
  }
  -- 1. Treasure provenance (non-plain Treasure token + floating `{1}`):
  --    With Smaug trigger on battlefield -> NOT unique (player may sacrifice Treasure for trigger)!
  --    Without Smaug trigger -> UNIQUE!
  let gTrSmaug0 :=
    (insertObject (addPermanent (addPermanent gMain smaugTrigDef p0 p0) Catalog.treasureToken p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 .colorless 1
  let gTrSmaugProp := mustApply gTrSmaug0 p0 (.cast (gTrSmaug0.player p0).hand.back!)
  let gTrNoSmaug0 :=
    (insertObject (addPermanent gMain Catalog.treasureToken p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 .colorless 1
  let gTrNoSmaugProp := mustApply gTrNoSmaug0 p0 (.cast (gTrNoSmaug0.player p0).hand.back!)

  -- Plain `{T}` Treasure land + floating `{1}` with Smaug -> NOT unique!
  let trPlainLandDef : CardDef := {
    name := "P52 Check9 PlainTreasureLand"
    types := #[.artifact, .land]
    subtypes := #["Treasure"]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne .colorless)]
  }
  let gTrPlainSmaug0 :=
    (insertObject (addPermanent (addPermanent gMain smaugTrigDef p0 p0) trPlainLandDef p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 .colorless 1
  let gTrPlainSmaugProp := mustApply gTrPlainSmaug0 p0 (.cast (gTrPlainSmaug0.player p0).hand.back!)

  -- 2. *Path of Ancestry* provenance:
  --    White/Green Elf commander + `{W}` *Path of Ancestry* + floating `{G}` on `{1}` creature:
  --    `{W}` precedes `{G}` in `ManaPool.spendAnyUnit?` (`W < G`), so tapping *Path of Ancestry*
  --    flips `ancestryScry` from `false` to `true` on an Elf (`!hasUniqueManaPayment`), while on a Bear
  --    (no shared creature type with the Elf commander) it stays unique (`hasUniqueManaPayment`)!
  let poaDef : CardDef := {
    name := "P52 Check9 PathOfAncestry"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .white))]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
  }
  let elfCmdrDef : CardDef := {
    creature "P52 Check9 ElfCmdr" ⟨#[.colored .white, .colored .green]⟩ #["Elf"] 2 2 with
    supertypes := #[.legendary]
  }
  let elfSpellDef : CardDef := creature "P52 Check9 ElfSpell" (ManaCost.ofGeneric 1) #["Elf"] 2 2
  let bearSpellDef : CardDef := creature "P52 Check9 BearSpell" (ManaCost.ofGeneric 1) #["Bear"] 2 2
  let cmdCfg : StartConfig := {
    seats := #[
      { name := "P0", deck := testGreenDeck, commanders := #[elfCmdrDef] },
      { name := "P1", deck := testRedDeck }
    ]
    format := .constructed
    seed := 529
    startingPlayer := some 0
  }
  let gCmdBase : Game :=
    match Start.start cmdCfg with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let gPoaElf0 :=
    (insertObject (addPermanent gCmdBase poaDef p0 p0) elfSpellDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gPoaElfProp := mustApply gPoaElf0 p0 (.cast (gPoaElf0.player p0).hand.back!)
  let gPoaBear0 :=
    (insertObject (addPermanent gCmdBase poaDef p0 p0) bearSpellDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gPoaBearProp := mustApply gPoaBear0 p0 (.cast (gPoaBear0.player p0).hand.back!)

  -- 3. `ManaOutput.combination #[W, U, R] 2` on `{2}` with floating `{B}`:
  --    `[W, U]` leaves `[{B}]` while `[R, R]` leaves `[{R}]`, so NOT unique!
  let comboWurDef : CardDef := {
    name := "P52 Check9 WurCombo"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.combination (.explicit #[.colored .white, .colored .blue, .colored .red]) (.const 2))
    ]
  }
  let gComboWur0 :=
    (insertObject (addPermanent gMain comboWurDef p0 p0) twoArtDef p0 (.hand p0)).addMana p0 (.colored .black) 1
  let gComboWurProp := mustApply gComboWur0 p0 (.cast (gComboWur0.player p0).hand.back!)

  -- 4. Multi-source rider flip: floating `[{R}, {G, .cantBeCountered}]` + TWO artifact-only `{C}` sources
  --    on `{2}` artifact spell -> tapping BOTH flips `cantBeCountered` from `true` to `false` (NOT unique!),
  --    whereas with only ONE such source `cantBeCountered` stays `true` (UNIQUE)!
  let artOnlyRockDef : CardDef := {
    name := "P52 Check9 ArtRock"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne .colorless)
        (restriction := some (.onlyForSpells (.hasType .artifact)))
    ]
  }
  let addFloatRider (g : Game) : Game :=
    g.addManaUnits p0 #[
      { mana := .colored .red },
      { mana := .colored .green, riders := #[.cantBeCountered] }
    ]
  let gMultiTwo0 :=
    addFloatRider (insertObject (addPermanent (addPermanent gMain artOnlyRockDef p0 p0) artOnlyRockDef p0 p0)
      twoArtDef p0 (.hand p0))
  let gMultiTwoProp := mustApply gMultiTwo0 p0 (.cast (gMultiTwo0.player p0).hand.back!)
  let gMultiOne0 :=
    addFloatRider (insertObject (addPermanent gMain artOnlyRockDef p0 p0)
      twoArtDef p0 (.hand p0))
  let gMultiOneProp := mustApply gMultiOne0 p0 (.cast (gMultiOne0.player p0).hand.back!)

  mustHoldCheck9 "p52_treasureNonPlainSmaugNotUnique" (!hasUniqueManaPayment gTrSmaugProp) &&
  mustHoldCheck9 "p52_treasureNonPlainNoSmaugUnique" (hasUniqueManaPayment gTrNoSmaugProp) &&
  mustHoldCheck9 "p52_treasurePlainSmaugNotUnique" (!hasUniqueManaPayment gTrPlainSmaugProp) &&
  mustHoldCheck9 "p52_poaMatchingCreatureNotUnique" (!hasUniqueManaPayment gPoaElfProp) &&
  mustHoldCheck9 "p52_poaNonMatchingCreatureUnique" (hasUniqueManaPayment gPoaBearProp) &&
  mustHoldCheck9 "p52_comboWurFloatingBlackNotUnique" (!hasUniqueManaPayment gComboWurProp) &&
  mustHoldCheck9 "p52_multiSourceTwoRocksFlipNotUnique" (!hasUniqueManaPayment gMultiTwoProp) &&
  mustHoldCheck9 "p52_multiSourceOneRockStaysUnique" (hasUniqueManaPayment gMultiOneProp)


/- Phase 53 Item 4a: `Demo.hasUniqueManaPayment` completeness across all `ManaSpentPred`
constructors & `ValueExpr.manaSpent`, non-WUBRG dual / combination-land `repPools`,
all 5 `manaAbilityDefCanChangeOutcome` / `nonPlainFlips` cases, and full
`treasureManaMatters` AST & zone coverage! -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := afterDraw
  let oneInstDef : CardDef := {
    name := "P53 Check9 OneInst"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let twoInstDef : CardDef := {
    name := "P53 Check9 TwoInst"
    manaCost := ManaCost.ofGeneric 2
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let twobridInstDef : CardDef := {
    name := "P53 Check9 TwobridInst"
    manaCost := ⟨#[.twobrid .blue]⟩
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let hybridWgInstDef : CardDef := {
    name := "P53 Check9 HybridWgInst"
    manaCost := ⟨#[.hybrid .white .green]⟩
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let uncounterableInstDef : CardDef := {
    oneInstDef with
    name := "P53 Check9 UncInst"
    staticAbilities := #[.spellCantBeCountered]
  }
  let mountainDef : CardDef := {
    name := "P53 Check9 Mountain"
    types := #[.land]
    subtypes := #["Mountain"]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .red))]
  }
  let islandDef : CardDef := {
    name := "P53 Check9 Island"
    types := #[.land]
    subtypes := #["Island"]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .blue))]
  }
  let borosDualDef : CardDef := {
    name := "P53 Check9 BorosDual"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.oneOf (.explicit #[.colored .red, .colored .white]) (.const 1))
    ]
  }

  -- 1. All remaining `ManaSpentPred` constructors + `ValueExpr.manaSpent`:
  -- (a) `.ofColor .red`: floating `{G}` + untapped Mountain on `{1}` -> NOT unique!
  let ofColorRedWatchDef : CardDef := {
    name := "P53 Check9 RedWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some (.ofColor .red)))
        (Effect.gainLife 1)
    ]
  }
  let gOfColor0 :=
    (insertObject (addPermanent (addPermanent gMain ofColorRedWatchDef p0 p0) mountainDef p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gOfColorProp := mustApply gOfColor0 p0 (.cast (gOfColor0.player p0).hand.back!)

  -- (b) `.colorCount .ge 2`: Boros `{R}/{W}` + Mountain on `{2}` -> `{R}{R}` (1 color) vs `{W}{R}` (2 colors) -> NOT unique!
  let colorCountWatchDef : CardDef := {
    name := "P53 Check9 ColorCountWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some (.colorCount .ge 2)))
        (Effect.gainLife 1)
    ]
  }
  let gColorCnt0 :=
    insertObject
      (addPermanent (addPermanent (addPermanent gMain colorCountWatchDef p0 p0) borosDualDef p0 p0) mountainDef p0 p0)
      twoInstDef p0 (.hand p0)
  let gColorCntProp := mustApply gColorCnt0 p0 (.cast (gColorCnt0.player p0).hand.back!)

  -- (c) General non-PoA `.fromSource`: permanent with `.fromSource` trigger + floating `{G}` on `{1}` -> NOT unique!
  let fromSourceLandDef : CardDef := {
    name := "P53 Check9 FromSourceLand"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .white))]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some .fromSource))
        (Effect.gainLife 1)
    ]
  }
  let gFromSrc0 :=
    (insertObject (addPermanent gMain fromSourceLandDef p0 p0) oneInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gFromSrcProp := mustApply gFromSrc0 p0 (.cast (gFromSrc0.player p0).hand.back!)

  -- (d) `ValueExpr.manaSpent` (Moon-Letters style) on twobrid `{2/U}` noncreature spell:
  --     floating `{C}{C}` + untapped Island -> `{2}` (2 mana spent) vs `{U}` (1 mana spent) -> NOT unique!
  let moonLettersWatchDef : CardDef := {
    name := "P53 Check9 MoonLettersWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you (.not (.hasType .creature)))
        { body := .player (.drawCards .you (.manaSpent .triggerSubject)) }
    ]
  }
  let gManaSpentAmt0 :=
    (insertObject (addPermanent (addPermanent gMain moonLettersWatchDef p0 p0) islandDef p0 p0)
      twobridInstDef p0 (.hand p0)).addMana p0 .colorless 2
  let gManaSpentAmtProp := mustApply gManaSpentAmt0 p0 (.cast (gManaSpentAmt0.player p0).hand.back!)

  -- (e) Explicit `.withRider .cantBeCountered` on an ALREADY uncounterable noncreature spell -> NOT unique!
  let explicitRiderWatchDef : CardDef := {
    name := "P53 Check9 RiderWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some (.withRider .cantBeCountered)))
        (Effect.gainLife 1)
    ]
  }
  let cbcPlainLandDef : CardDef := {
    name := "P53 Check9 CbcLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .white)) (riders := #[.cantBeCountered])
    ]
  }
  let gExplicitRider0 :=
    (insertObject (addPermanent (addPermanent gMain explicitRiderWatchDef p0 p0) cbcPlainLandDef p0 p0)
      uncounterableInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gExplicitRiderProp := mustApply gExplicitRider0 p0 (.cast (gExplicitRider0.player p0).hand.back!)

  -- 2. Non-WUBRG dual (`{R}/{W}` Boros dual) in `canExtraPlainSourcesChangeOutcome`:
  --    Floating `{B}` with `.ofColor .black` trigger + untapped `{R}/{W}` Boros dual on `{1}`:
  --    `{W}` outranks `{B}` in `ManaPool.spendAnyUnit?` (`W > B > R`), so NOT unique!
  let ofColorBlackWatchDef : CardDef := {
    name := "P53 Check9 BlackWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject (manaSpent? := some (.ofColor .black)))
        (Effect.gainLife 1)
    ]
  }
  let gBorosDisplace0 :=
    (insertObject (addPermanent (addPermanent gMain ofColorBlackWatchDef p0 p0) borosDualDef p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 (.colored .black) 1
  let gBorosDisplaceProp := mustApply gBorosDisplace0 p0 (.cast (gBorosDisplace0.player p0).hand.back!)

  -- 3. Combination-land `repPools` (>4 distinct pre-spend pools):
  --    5-color combination land `#[W, U, B, R, G] 2` (15 pools; index 4 is `[W, G]`) + extra *Path of Ancestry* `{R}`
  --    on `{2}` Elf creature matching Elf commander: `{R}` beats `{G}` on `[W, G]`, flipping `ancestryScry` -> NOT unique!
  let combo5Def : CardDef := {
    name := "P53 Check9 FiveColorCombo"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.combination (.explicit #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]) (.const 2))
    ]
  }
  let poaRedDef : CardDef := {
    name := "P53 Check9 PoaRed"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.fixedOne (.colored .red))]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
  }
  let elfCmdrDef : CardDef := {
    creature "P53 Check9 ElfCmdr" ⟨#[.colored .red, .colored .green]⟩ #["Elf"] 2 2 with
    supertypes := #[.legendary]
  }
  let twoElfSpellDef : CardDef := creature "P53 Check9 TwoElf" (ManaCost.ofGeneric 2) #["Elf"] 2 2
  let cmdCfg53 : StartConfig := {
    seats := #[
      { name := "P0", deck := testGreenDeck, commanders := #[elfCmdrDef] },
      { name := "P1", deck := testRedDeck }
    ]
    format := .constructed
    seed := 539
    startingPlayer := some 0
  }
  let gCmd53 : Game :=
    match Start.start cmdCfg53 with
    | .ok g => (keepOpeningHands g 20).advanceStep
    | .error e => panic! e
  let gComboRep0 :=
    insertObject (addPermanent (addPermanent gCmd53 combo5Def p0 p0) poaRedDef p0 p0)
      twoElfSpellDef p0 (.hand p0)
  let gComboRepProp := mustApply gComboRep0 p0 (.cast (gComboRep0.player p0).hand.back!)

  -- 4. All five `manaAbilityDefCanChangeOutcome` / `nonPlainFlips` cases:
  -- (a) Modal non-plain mana ability (`d.modeChoices` with `.cantBeCountered` on mode 2):
  let modalNonPlainDef : CardDef := {
    name := "P53 Check9 ModalLotus"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := { items := #[.tapSelf, .sacrifice (.exact 1) .self] }
      effect := {
        body := .chooseModes {
          modes := #[
            { body := .player (.addMana .you { spec := .fixedOne .colorless }) },
            { body := .player (.addMana .you { spec := .fixedOne (.colored .white), riders := #[.cantBeCountered] }) }
          ]
        }
      }
    }]
  }
  let gModalFlip0 :=
    (insertObject (addPermanent gMain modalNonPlainDef p0 p0) oneInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gModalFlipProp := mustApply gModalFlip0 p0 (.cast (gModalFlip0.player p0).hand.back!)

  -- (b) Hybrid `{W/G}` displacement by unrestricted no-rider non-plain `{W}`:
  let sacWhiteDef : CardDef := {
    name := "P53 Check9 SacWhite"
    types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .white)) (cost := { items := #[.sacrifice (.exact 1) .self] })
    ]
  }
  let gHybridFlip0 :=
    (insertObject (addPermanent gMain sacWhiteDef p0 p0) hybridWgInstDef p0 (.hand p0)).addManaUnits p0
      #[{ mana := .colored .green, riders := #[.cantBeCountered] }]
  let gHybridFlipProp := mustApply gHybridFlip0 p0 (.cast (gHybridFlip0.player p0).hand.back!)

  -- (c) Tier-3 cross-rider displacement of `outcome0.cantBeCountered`:
  --     Floating `{G}` with `.cantBeCountered` + non-plain sacrifice-self `{W}` with `.gainsHaste` on `{1}` -> NOT unique!
  let sacWhiteHasteDef : CardDef := {
    name := "P53 Check9 SacWhiteHaste"
    types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .white))
        (cost := { items := #[.sacrifice (.exact 1) .self] }) (riders := #[.gainsHaste])
    ]
  }
  let gTier3Flip0 :=
    (insertObject (addPermanent gMain sacWhiteHasteDef p0 p0) oneInstDef p0 (.hand p0)).addManaUnits p0
      #[{ mana := .colored .green, riders := #[.cantBeCountered] }]
  let gTier3FlipProp := mustApply gTier3Flip0 p0 (.cast (gTier3Flip0.player p0).hand.back!)

  -- (d) Hand non-plain mana ability (`exileSelfFromHand`) flipping outcome:
  let spiritGuideRedDef : CardDef := {
    creature "P53 Check9 SpiritGuide" (ManaCost.ofGeneric 3) #["Spirit"] 2 2 with
    activatedAbilities := #[{
      cost := { items := #[.exile (.exact 1) { zones := #[.hand], owner := .ofPlayer .you } .self] }
      activeZones := #[.hand]
      effect := { body := .player (.addMana .you { spec := .fixedOne (.colored .red) }) }
    }]
  }
  let gHandFlip0 :=
    (insertObject (insertObject (addPermanent gMain ofColorRedWatchDef p0 p0) spiritGuideRedDef p0 (.hand p0))
      oneInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gHandFlipProp := mustApply gHandFlip0 p0 (.cast (gHandFlip0.player p0).hand.back!)

  -- (e) `.mountainExtraRed` on a restricted non-plain Mountain:
  let restrMtnDef : CardDef := {
    name := "P53 Check9 RestrMtn"
    types := #[.land]
    subtypes := #["Mountain"]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .green))
        (cost := { items := #[.tapSelf, .payLife (.const 1)] })
        (restriction := some (.onlyForSpells (.hasSubtype .dragon)))
    ]
  }
  let gMtnExtra0 :=
    (insertObject (addPermanent (addPermanent gMain ofColorRedWatchDef p0 p0) restrMtnDef p0 p0)
      oneInstDef p0 (.hand p0)).addMana p0 (.colored .green) 1
      |>.createEffect (.playerRule p0 (.mountainExtraRed 1) .untilEndOfTurn) (cause := some (.gameRule .staticAbility))
  let gMtnExtraProp := mustApply gMtnExtra0 p0 (.cast (gMtnExtra0.player p0).hand.back!)

  -- 5. Complete `treasureManaMatters` AST & zone walker:
  let trCond : Condition := .castPred (.manaSpentMatches .fromTreasure .triggerSubject)
  let trCastPat : TriggerPattern := .castSpell .you .anyObject (manaSpent? := some .fromTreasure)
  let mkTrCheckGame (setup : Game → Game) (spell : CardDef := oneInstDef) : Game :=
    let g0 := (insertObject (setup (addPermanent gMain Catalog.treasureToken p0 p0)) spell p0 (.hand p0)).addMana p0 .colorless 1
    mustApply g0 p0 (.cast (g0.player p0).hand.back!)
  -- (a) `TriggerPattern.or`
  let trigOrDef : CardDef := {
    name := "P53 Check9 TrigOr", types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger (.or .thisEnters trCastPat) (Effect.gainLife 1)]
  }
  let gTrOrProp := mkTrCheckGame (fun g => addPermanent g trigOrDef p0 p0)
  -- (b) `TriggerPattern.whenCond`
  let trigWhenDef : CardDef := {
    name := "P53 Check9 TrigWhen", types := #[.enchantment]
    triggeredAbilities := #[TriggeredAbility.mkTrigger (.whenCond (.castSpell .you .anyObject) trCond) (Effect.gainLife 1)]
  }
  let gTrWhenProp := mkTrCheckGame (fun g => addPermanent g trigWhenDef p0 p0)
  -- (c) `StaticReplacementSpec.entersTapped` & `.all`
  let staticEntTapDef : CardDef := {
    creature "P53 Check9 EntTap" (ManaCost.ofGeneric 1) #["Elf"] 2 2 with
    staticAbilities := #[.replacement none (.all #[.entersTapped .self (some (.castPred (.manaSpentMatches .fromTreasure .this)))])]
  }
  let gTrEntTapProp := mkTrCheckGame id staticEntTapDef
  -- (d) `ContinuousModification.grantTriggered` & `.grantStatic` & `.all`
  let grantTrigDef : CardDef := {
    name := "P53 Check9 GrantTrig", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.battlefield], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.all #[.grantTriggered #[TriggeredAbility.mkTrigger trCastPat (Effect.gainLife 1)]])
    ]
  }
  let gTrGrantProp := mkTrCheckGame (fun g => addPermanent g grantTrigDef p0 p0)
  -- (e) `ModalSpec.altCountIf?`
  let modalAltSpellDef : CardDef := {
    oneInstDef with
    name := "P53 Check9 ModalAlt"
    spellAbility := some {
      effect := {
        body := .chooseModes {
          altCountIf? := some (.castPred (.manaSpentMatches .fromTreasure .this), .const 2, .const 2)
          chooseAtResolution := true
          modes := #[Effect.gainLife 1, Effect.gainLife 2]
        }
      }
    }
  }
  let gTrModalAltProp := mkTrCheckGame id modalAltSpellDef
  -- (f) `Instruction.installEffect`
  let installEffSpellDef : CardDef := {
    oneInstDef with
    name := "P53 Check9 InstallEff"
    spellAbility := some {
      effect := {
        body := .installEffect (.applyReplacement .untilEndOfTurn
          (.entersTapped .self (some (.castPred (.manaSpentMatches .fromTreasure .this)))))
      }
    }
  }
  let gTrInstallProp := mkTrCheckGame id installEffSpellDef
  -- (g) `g.delayedTriggers`
  let gTrDelayedProp := mkTrCheckGame (fun g =>
    g.registerDelayedTrigger {
      controller := p0
      kind := .copyNextInstantSorceryThisTurn
      cause := .gameRule .staticAbility
      instruction? := some (.ifCond trCond (Instruction.gainLifeFixed 1 .you) .noop)
    })
  -- (h) Non-battlefield `activeZones` (graveyard trigger)
  let gyTrigDef : CardDef := {
    name := "P53 Check9 GyTrig", types := #[.enchantment]
    triggeredAbilities := #[{
      TriggeredAbility.mkTrigger trCastPat (Effect.gainLife 1) with
      activeZones := #[.graveyard]
    }]
  }
  let gTrGyProp := mkTrCheckGame (fun g => insertObject g gyTrigDef p0 (.graveyard p0))

  mustHoldCheck9 "p53_ofColorRedNotUnique" (!hasUniqueManaPayment gOfColorProp) &&
  mustHoldCheck9 "p53_colorCountNotUnique" (!hasUniqueManaPayment gColorCntProp) &&
  mustHoldCheck9 "p53_fromSourceNotUnique" (!hasUniqueManaPayment gFromSrcProp) &&
  mustHoldCheck9 "p53_valueExprManaSpentTwobridNotUnique" (!hasUniqueManaPayment gManaSpentAmtProp) &&
  mustHoldCheck9 "p53_explicitWithRiderUncounterableNotUnique" (!hasUniqueManaPayment gExplicitRiderProp) &&
  mustHoldCheck9 "p53_borosDualDisplacesBlackNotUnique" (!hasUniqueManaPayment gBorosDisplaceProp) &&
  mustHoldCheck9 "p53_combo5RepPoolsPoaFlipNotUnique" (!hasUniqueManaPayment gComboRepProp) &&
  mustHoldCheck9 "p53_modalNonPlainModeChoicesNotUnique" (!hasUniqueManaPayment gModalFlipProp) &&
  mustHoldCheck9 "p53_hybridDisplacedByPlainNonPlainNotUnique" (!hasUniqueManaPayment gHybridFlipProp) &&
  mustHoldCheck9 "p53_tier3CrossRiderDisplacesCbcNotUnique" (!hasUniqueManaPayment gTier3FlipProp) &&
  mustHoldCheck9 "p53_handNonPlainManaAbilityNotUnique" (!hasUniqueManaPayment gHandFlipProp) &&
  mustHoldCheck9 "p53_restrictedMountainExtraRedNotUnique" (!hasUniqueManaPayment gMtnExtraProp) &&
  mustHoldCheck9 "p53_treasureTriggerOrNotUnique" (!hasUniqueManaPayment gTrOrProp) &&
  mustHoldCheck9 "p53_treasureTriggerWhenCondNotUnique" (!hasUniqueManaPayment gTrWhenProp) &&
  mustHoldCheck9 "p53_treasureEntersTappedAllNotUnique" (!hasUniqueManaPayment gTrEntTapProp) &&
  mustHoldCheck9 "p53_treasureGrantTriggeredAllNotUnique" (!hasUniqueManaPayment gTrGrantProp) &&
  mustHoldCheck9 "p53_treasureModalAltCountIfNotUnique" (!hasUniqueManaPayment gTrModalAltProp) &&
  mustHoldCheck9 "p53_treasureInstallEffectNotUnique" (!hasUniqueManaPayment gTrInstallProp) &&
  mustHoldCheck9 "p53_treasureDelayedTriggerNotUnique" (!hasUniqueManaPayment gTrDelayedProp) &&
  mustHoldCheck9 "p53_treasureGraveyardActiveZoneNotUnique" (!hasUniqueManaPayment gTrGyProp)
