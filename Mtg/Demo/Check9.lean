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


/- Phase 54 Item 4: `Demo.hasGameStatePriorityAction` exile Layer-3 self-flash `timingAllowsCast (card? := some o)`
(front face and Adventure), `Demo.uniqueDiscardCommand` filtering bounced creature tokens (CR 108.2b / 111.8), and
all four `Demo.hasUniqueManaPayment` soundness fixes (plain Mountain `.mountainExtraRed` `fromSource` attribution,
chained `.hybrid` + `.twobrid` `anyAmount` displacement, Layer-3 color-word `spellManaSpentInterest`, and
conservative `canExtraPlainSourcesChangeOutcome` DFS budget exhaustion for `anyColorCount`). -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `Demo.hasGameStatePriorityAction` exile Layer-3 text-changed self-flash (front face & Adventure):
  --    Exiled creature (with `.playFromExile` permission) has "You may cast this spell as though it had flash if you
  --    control a Swamp"; Layer-3 text change swaps Swamp -> Forest while `p0` controls a Forest on `p1`'s turn!
  let exileSelfFlashDef : CardDef := {
    creature "P54 Check9 ExSwampFlash" ManaCost.zero #["Beast"] 2 2 with
    staticAbilities := #[
      .ruleModifying (some (.exists (.inZones { zones := #[.battlefield], owner := .ofPlayer .you } (.hasSubtype (.literal .swamp)))))
        (.play (.castAsThoughFlash .you .anyObject true none))
    ]
  }
  let exileAdvFlashDef : CardDef := {
    creature "P54 Check9 ExAdvHost" (ManaCost.ofGeneric 5) #["Beast"] 4 4 with
    subFaces := #[{
      kind := .adventure
      name := "P54 Check9 ExAdvSorc"
      manaCost := ManaCost.zero
      types := #[.sorcery]
      staticAbilities := #[
        .ruleModifying (some (.exists (.inZones { zones := #[.battlefield], owner := .ofPlayer .you } (.hasSubtype (.literal .swamp)))))
          (.play (.castAsThoughFlash .you .anyObject true none))
      ]
      spellAbility := some { effect := Effect.gainLife 1 }
    }]
  }
  let gWithTappedForest :=
    (gMain.allocObject forest p0 .battlefield (some p0) { tapped := true }).1
  let gExFlash0 :=
    ((insertObject gWithTappedForest exileSelfFlashDef p0 .exile).record
      (GameEvent.turnBegan 2 p1)).change (.priority p0)
  let exFlashId := (gExFlash0.objects.filter (·.zone == .exile)).back!.id
  let gExFlashPerm :=
    gExFlash0.createEffect (.permission (some p0) (.playFromExile exFlashId { player := p0 }) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility))
  let gExFlashChanged :=
    gExFlashPerm.createEffect
      (.layered (.objects #[exFlashId]) (.text (.replaceCreatureType .swamp .forest)) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility))
  let gExAdv0 :=
    ((insertObject gWithTappedForest exileAdvFlashDef p0 .exile).record
      (GameEvent.turnBegan 2 p1)).change (.priority p0)
  let exAdvId := (gExAdv0.objects.filter (·.zone == .exile)).back!.id
  let gExAdvPerm :=
    gExAdv0.createEffect (.permission (some p0) (.playFromExile exAdvId { player := p0 }) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility))
  let gExAdvChanged :=
    gExAdvPerm.createEffect
      (.layered (.objects #[exAdvId]) (.text (.replaceCreatureType .swamp .forest)) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility))

  -- 2. `Demo.uniqueDiscardCommand` filters bounced creature tokens in hand (CR 108.2b / 111.8):
  let tokBearDef : CardDef := { grizzlyBears with name := "P54 Check9 TokBear", isToken := true }
  let gDiscOnlyTok :=
    (insertObject gMain tokBearDef p0 (.hand p0)).change (.pending (.discardForAdditionalCost p0))
  let gDiscTokPlusCard :=
    (insertObject gDiscOnlyTok grizzlyBears p0 (.hand p0))
  let realCardHandId := (gDiscTokPlusCard.player p0).hand.back!

  -- 3. `hasUniqueManaPayment` plain Mountain `.mountainExtraRed` `fromSource` attribution:
  --    `mtnBoostDef` has a `.fromSource` cast trigger AND grants `.mountainExtraRed 1` (`source := some boostId`);
  --    `p0` has floating `{G}{G}` and an untapped plain Mountain; on `{2}` spell, tapping the plain Mountain adds
  --    `{R}` (`source := some mountainId`) + `{R}` (`source := some boostId`), so paying `{2}` with `{R}{R}`
  --    triggers `mtnBoostDef`'s `.fromSource` -> NOT unique!
  let mtnBoostWatchDef : CardDef := {
    name := "P54 Check9 MtnBoostWatch", types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.castSpell .you .anyObject (manaSpent? := some .fromSource)) (Effect.gainLife 1)
    ]
  }
  let twoInstDef : CardDef := {
    name := "P54 Check9 TwoInst", manaCost := ManaCost.ofGeneric 2, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gMtnFromSrc0 :=
    (insertObject (addPermanent (addPermanent gMain mtnBoostWatchDef p0 p0) mountain p0 p0)
      twoInstDef p0 (.hand p0)).addMana p0 (.colored .green) 2
  let boostId := (gMtnFromSrc0.permanentsOf p0).find? (·.name == mtnBoostWatchDef.name) |>.get!.id
  let gMtnFromSrc1 :=
    gMtnFromSrc0.createEffect (.playerRule p0 (.mountainExtraRed 1) .untilEndOfTurn)
      (cause := some (.oneShotEffect none (some boostId) (some p0)))
  let gMtnFromSrcProp := mustApply gMtnFromSrc1 p0 (.cast (gMtnFromSrc1.player p0).hand.back!)

  -- 4. `hasUniqueManaPayment` chained `.hybrid` + `.twobrid` `anyAmount` displacement:
  --    Spell costs `{W/U}{2/U}` + watcher cares about `ValueExpr.manaSpent`;
  --    floating `{U}{C}{C}` pays `{W/U}` with `{U}` and `{2/U}` with `{C}{C}` (3 mana spent);
  --    untapped non-plain sacrifice-self `{W}` artifact pays `{W/U}` with `{W}`, freeing `{U}` to pay `{2/U}` (2 mana spent) -> NOT unique!
  let chainSpellDef : CardDef := {
    name := "P54 Check9 ChainHybTwo"
    manaCost := ⟨#[.hybrid .white .blue, .twobrid .blue]⟩
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let sacWhiteArtDef : CardDef := {
    name := "P54 Check9 SacWhite", types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .white)) (cost := { items := #[.sacrifice (.exact 1) .self] })
    ]
  }
  let amtWatchDef : CardDef := {
    name := "P54 Check9 AmtWatch", types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.castSpell .you .anyObject)
        { body := .player (.drawCards .you (.manaSpent .triggerSubject)) }
    ]
  }
  let gChain0 :=
    (insertObject (addPermanent (addPermanent gMain amtWatchDef p0 p0) sacWhiteArtDef p0 p0)
      chainSpellDef p0 (.hand p0)).addMana p0 (.colored .blue) 1 |>.addMana p0 .colorless 2
  let gChainProp := mustApply gChain0 p0 (.cast (gChain0.player p0).hand.back!)

  -- 5. `hasUniqueManaPayment` Layer-3 color-word `spellManaSpentInterest`:
  --    Spell effect checks `.manaSpentMatches (.ofColor .blue) .this`; Layer-3 text change swaps blue -> red;
  --    with floating `{G}` and untapped Mountain, spending `{R}` changes the spell's effect -> NOT unique!
  let blueCheckSpellDef : CardDef := {
    name := "P54 Check9 BlueCheck"
    manaCost := ManaCost.ofGeneric 1
    types := #[.instant]
    spellAbility := some {
      effect := {
        body := .ifCond (.castPred (.manaSpentMatches (.ofColor .blue) .this))
          (Instruction.gainLifeFixed 5 .you) .noop
      }
    }
  }
  let gL3Mana0 :=
    (insertObject (addPermanent gMain mountain p0 p0) blueCheckSpellDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gL3ManaProp0 := mustApply gL3Mana0 p0 (.cast (gL3Mana0.player p0).hand.back!)
  let l3SpellId := gL3ManaProp0.proposedSpell.get!.spellId
  let gL3ManaProp :=
    gL3ManaProp0.createEffect
      (.layered (.objects #[l3SpellId]) (.text (.replaceColorWord .blue .red)) .untilEndOfTurn)
      (cause := some (.gameRule .staticAbility))

  -- 6. `hasUniqueManaPayment` conservative `canExtraPlainSourcesChangeOutcome` DFS budget exhaustion:
  --    With many 5-color plain lands and `interest.anyColorCount` (`.colorCount .ge 4`) on `{4}` with `{C}{C}{C}{C}` floating,
  --    exhausting DFS budget (or finding a distinct-color assignment) refuses autopay (`hasUniqueManaPayment == false`)!
  let fiveColorLandDef : CardDef := {
    name := "P54 Check9 CityOfBrass", types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green]) (.const 1))]
  }
  let fourColorWatchDef : CardDef := {
    name := "P54 Check9 FourColorWatch", types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.castSpell .you .anyObject (manaSpent? := some (.colorCount .ge 4)))
        (Effect.gainLife 1)
    ]
  }
  let fourInstDef : CardDef := {
    name := "P54 Check9 FourInst", manaCost := ManaCost.ofGeneric 4, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gBudget0 :=
    Id.run do
      let mut g := addPermanent gMain fourColorWatchDef p0 p0
      for _ in [0:10] do
        g := addPermanent g fiveColorLandDef p0 p0
      g := insertObject g fourInstDef p0 (.hand p0)
      return g.addMana p0 .colorless 4
  let gBudgetProp := mustApply gBudget0 p0 (.cast (gBudget0.player p0).hand.back!)

  mustHoldCheck9 "p54_exileLayer3SelfFlashFrontFace"
    (!hasGameStatePriorityAction gExFlashPerm p0 && hasGameStatePriorityAction gExFlashChanged p0) &&
  mustHoldCheck9 "p54_exileLayer3SelfFlashAdventure"
    (!hasGameStatePriorityAction gExAdvPerm p0 && hasGameStatePriorityAction gExAdvChanged p0) &&
  mustHoldCheck9 "p54_uniqueDiscardCommandFiltersToken"
    (uniqueDiscardCommand gDiscOnlyTok == none &&
     uniqueDiscardCommand gDiscTokPlusCard == some s!"discard {realCardHandId}") &&
  mustHoldCheck9 "p54_plainMountainExtraRedFromSourceNotUnique"
    (!hasUniqueManaPayment gMtnFromSrcProp) &&
  mustHoldCheck9 "p54_chainedHybridTwobridAnyAmountNotUnique"
    (!hasUniqueManaPayment gChainProp) &&
  mustHoldCheck9 "p54_layer3ColorWordSpellManaSpentInterestNotUnique"
    (!hasUniqueManaPayment gL3ManaProp) &&
  mustHoldCheck9 "p54_manyFiveColorLandsAnyColorCountNotUnique"
    (!hasUniqueManaPayment gBudgetProp)


/- Phase 55 Item 4b: `Demo.hasGameStatePriorityAction` graveyard/library-top
playables, Sneak, Convoke/Improvise, and target-reduced costs, plus
`Demo.hasUniqueManaPayment` `extra`-before-`minSub` & `minSub` tap-order flips,
filter-land/signet `spendsPoolMana` laundering, and `instrInterest` AST
traversals (`MoveMods.choice?`, `ManaSpec`, `DelayedTokenAction`). -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `hasGameStatePriorityAction` graveyard Flashback & Mole Man graveyard land:
  let fbSorcDef : CardDef := {
    name := "P55 Check9 FlashbackSpark"
    manaCost := ManaCost.ofGeneric 4
    types := #[.sorcery]
    keywords := #[.flashback (CostSpec.ofItems #[.mana (ManaCost.ofGenericAndColor 1 .red)])]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gFb0 := insertObject gMain fbSorcDef p0 (.graveyard p0)
  let gFb1 := gFb0.addMana p0 (.colored .red) 1
  let gFb2 := gFb1.addMana p0 .colorless 1
  let moleManLikeDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 MoleMan"
    staticAbilities := #[.ruleModifying none (.play (.mayPlayFrom .you .graveyard (.hasType .land) true false))]
  }
  let inertLandDef : CardDef := { name := "P55 Check9 InertLand", types := #[.land] }
  let gGyLandNoPerm := insertObject gMain mountain p0 (.graveyard p0)
  let gGyLandWithPerm := addPermanent gGyLandNoPerm moleManLikeDef p0 p0
  let gGyLandPlayed :=
    let gWithHandLand := insertObject gGyLandWithPerm inertLandDef p0 (.hand p0)
    mustApply gWithHandLand p0 (.playLand (gWithHandLand.player p0).hand.back!)

  -- 2. `hasGameStatePriorityAction` library-top creature/Morph (Elven Chorus) & library-top land:
  let elvenChorusLikeDef : CardDef := {
    name := "P55 Check9 ElvenChorus"
    types := #[.enchantment]
    staticAbilities := #[.ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .creature) false false))]
  }
  let libLandPermDef : CardDef := {
    name := "P55 Check9 Courser"
    types := #[.enchantment]
    staticAbilities := #[.ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .land) true false))]
  }
  let topMorphDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 TopMorph"
    manaCost := ManaCost.ofGeneric 6
    keywords := #[.morph (CostSpec.ofGeneric 2)]
  }
  let gTopCr0 :=
    (insertObject (addPermanent gMain elvenChorusLikeDef p0 p0) grizzlyBears p0 (.library p0))
  let gTopCrPay := gTopCr0.addMana p0 (.colored .green) 1 |>.addMana p0 .colorless 1
  let gTopMorph0 :=
    (insertObject (addPermanent gMain elvenChorusLikeDef p0 p0) topMorphDef p0 (.library p0))
  let gTopMorphPay := gTopMorph0.addMana p0 .colorless 3
  let gTopLandNoPerm := insertObject gMain forest p0 (.library p0)
  let gTopLandWithPerm := addPermanent gTopLandNoPerm libLandPermDef p0 p0

  -- 3. `hasGameStatePriorityAction` Sneak casting (CR 702.190a):
  let sneakNinjaDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 SneakNinja"
    manaCost := ManaCost.ofGenericAndColor 4 .black
    keywords := #[.sneak (CostSpec.ofItems #[.mana { symbols := #[.colored .black] }])]
  }
  let sneakSacNinjaDef : CardDef := {
    sneakNinjaDef with
    name := "P55 Check9 SneakSacNinja"
    spellAbility := some {
      effect := { body := .noop }
      additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeArtifactOrCreature]
    }
  }
  let gBlk0 :=
    (addPermanent (addPermanent gMain grizzlyBears p0 p0) grizzlyBears p1 p1).record
      (GameEvent.stepBegan gMain.turnNumber .declareBlockers p0 (cause := some (.turnBased .declareBlockers)))
    |>.change (.priority p0)
  let atkObj := (gBlk0.permanentsOf p0)[0]!
  let blkObj := (gBlk0.permanentsOf p1)[0]!
  let gBlkUnblocked :=
    gBlk0.record (GameEvent.attackersDeclared gBlk0.turnNumber p0 #[(gBlk0.snapshot atkObj, .player p1)])
  let gBlkBlocked :=
    gBlkUnblocked.record (GameEvent.becameBlocked gBlkUnblocked.turnNumber (gBlkUnblocked.snapshot atkObj) #[blkObj.id])
  let gSnkUnblkPay :=
    (insertObject gBlkUnblocked sneakNinjaDef p0 (.hand p0)).addMana p0 (.colored .black) 1
  let gSnkUnblkNoMana := insertObject gBlkUnblocked sneakNinjaDef p0 (.hand p0)
  let gSnkBlockedPay :=
    (insertObject gBlkBlocked sneakNinjaDef p0 (.hand p0)).addMana p0 (.colored .black) 1
  -- Mandatory sacrifice fails after `probeAfterSneakReturn` bounces the sole creature:
  let gSnkSacOnlyAtk :=
    (insertObject gBlkUnblocked sneakSacNinjaDef p0 (.hand p0)).addMana p0 (.colored .black) 1
  let gSnkSacExtraCr := addPermanent gSnkSacOnlyAtk grizzlyBears p0 p0

  -- 4. `hasGameStatePriorityAction` Convoke (CR 702.51a) & Improvise (CR 702.126a):
  let convSpellDef : CardDef := {
    name := "P55 Check9 ConvokeSpell"
    manaCost := ManaCost.ofGenericAndColor 2 .green
    types := #[.sorcery]
    keywords := #[Keyword.convoke]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let impSpellDef : CardDef := {
    name := "P55 Check9 ImproviseSpell"
    manaCost := ManaCost.ofGenericAndColor 2 .blue
    types := #[.sorcery]
    keywords := #[.simple .improvise]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let inertCogDef : CardDef := { name := "P55 Check9 Cog", types := #[.artifact] }
  let gConvShort :=
    insertObject
      (addPermanent (addPermanent gMain grizzlyBears p0 p0) grizzlyBears p0 p0)
      convSpellDef p0 (.hand p0)
  let gConvEnough := addPermanent gConvShort grizzlyBears p0 p0
  let gImpShort :=
    (insertObject (addPermanent gMain inertCogDef p0 p0) impSpellDef p0 (.hand p0)).addMana
      p0 (.colored .blue) 1
  let gImpEnough := addPermanent gImpShort inertCogDef p0 p0

  -- 5. `hasGameStatePriorityAction` target-reduced spell (`mentionsTarget`) & equip (`nEquip`) costs:
  let goblinDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 Goblin"
    subtypes := #["Goblin"]
  }
  let tgtRedSpellDef : CardDef := {
    name := "P55 Check9 GoblinBolt"
    manaCost := ManaCost.ofGenericAndColor 4 .red
    types := #[.instant]
    staticAbilities := #[
      .costModifier (some (.forAll (.target 0) (.hasSubtype (.literal .goblin)))) .thisSpell (.reduceGeneric (.const 3))
    ]
    spellAbility := some {
      effect := {
        targets := TargetSpec.creature
        body := .damage (.deal .this (.targetSlot 0) (.const 2))
      }
    }
  }
  let gTgtNoGob :=
    (insertObject (addPermanent gMain grizzlyBears p0 p0) tgtRedSpellDef p0 (.hand p0)).addMana
      p0 (.colored .red) 1 |>.addMana p0 .colorless 1
  let gTgtWithGob := addPermanent gTgtNoGob goblinDef p0 p0
  let equip4Def : CardDef := {
    name := "P55 Check9 HeavySword"
    types := #[.artifact]
    subtypes := #["Equipment"]
    keywords := #[.equip (.hasType .creature) (CostSpec.ofGeneric 4)]
  }
  let cheapEquipBearerDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 Squire"
    staticAbilities := #[
      .costModifier none (.abilities .you (some (.equip none)) { zones := .battlefield, pred := .anyObject } (some (.sameAs .this)) none)
        (.reduceGeneric (.const 3))
    ]
  }
  let gEquipNoDisc :=
    (addPermanent (addPermanent gMain equip4Def p0 p0) grizzlyBears p0 p0).addMana p0 .colorless 1
  let gEquipWithDisc := addPermanent gEquipNoDisc cheapEquipBearerDef p0 p0

  -- 6. `hasUniqueManaPayment` `extra`-before-`minSub` tap order:
  --    Commander is a Red Goblin; `p0` casts a `{R}` Goblin creature spell with an untapped Mountain
  --    (`minSub` = #[Mountain]) and an extra untapped *Path of Ancestry* (also producing `{R}`).
  --    Tapping Path of Ancestry *before* Mountain spends Ancestry `{R}` -> scry 1 (`ancestryScry = true`)!
  let redGobCmdDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 CmdGoblin"
    manaCost := { symbols := #[.colored .red] }
    supertypes := #[.legendary]
    subtypes := #["Goblin"]
  }
  let redGobSpellDef : CardDef := {
    grizzlyBears with
    name := "P55 Check9 GobSpell"
    manaCost := { symbols := #[.colored .red] }
    subtypes := #["Goblin"]
  }
  let ancDeck := Array.replicate 60 mountain
  let gAncStart : Game :=
    match Start.start {
      seats := #[
        { name := "Alice", deck := ancDeck, commanders := #[redGobCmdDef] },
        { name := "Bob", deck := ancDeck }
      ]
      format := .constructed
      seed := 1
      startingPlayer := some 0
    } with
    | .ok g =>
      let g1 := mustApply g p0 .keep
      let g2 := mustApply g1 p1 .keep
      -- Advance from upkeep to precombat main:
      let g3 := mustApply g2 p0 .pass
      let g4 := mustApply g3 p1 .pass
      emptyHand g4 p0
    | .error e => panic! s!"gAncStart failed: {e}"
  let gAncLands :=
    insertObject
      (addPermanent (addPermanent gAncStart mountain p0 p0) pathOfAncestry p0 p0)
      redGobSpellDef p0 (.hand p0)
  let gAncProp := mustApply gAncLands p0 (.cast (gAncLands.player p0).hand.back!)

  -- 7. `hasUniqueManaPayment` `minSub` tap-order flip when `!leftPool.units.isEmpty`:
  --    Two plain `{R}{R}` sources (`srcA`, `srcB`) paying `{R}{R}{R}`: both are required (`minSub`),
  --    leaving 1 `{R}` in `leftPool` whose `ManaUnit.source` depends on tap order!
  let doubleRedLandDef : CardDef := {
    name := "P55 Check9 DoubleRedLand"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 2)])]
  }
  let rrrSpellDef : CardDef := {
    name := "P55 Check9 TripleRed"
    manaCost := { symbols := #[.colored .red, .colored .red, .colored .red] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gMinOrder0 :=
    insertObject
      (addPermanent (addPermanent gMain doubleRedLandDef p0 p0) doubleRedLandDef p0 p0)
      rrrSpellDef p0 (.hand p0)
  let gMinOrderProp := mustApply gMinOrder0 p0 (.cast (gMinOrder0.player p0).hand.back!)

  -- 8. `hasUniqueManaPayment` filter-land `spendsPoolMana` laundering:
  --    Floating `{R}` from a Treasure token pays `{R}` (`outcome0.fromTreasure = true`),
  --    while an untapped filter land `{R}, {T}: Add {R}{R}` launders the Treasure mana into
  --    plain `{R}{R}`, flipping `fromTreasure` to `false`!
  let trWatchDef : CardDef := {
    name := "P55 Check9 TrWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger (.castSpell .you .anyObject (manaSpent? := some .fromTreasure))
        (Effect.gainLife 1)
    ]
  }
  let filterRtoRRDef : CardDef := {
    name := "P55 Check9 FilterRtoRR"
    types := #[.land]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.colored .red] }, .tapSelf]
      effect := Effect.addMana #[.colored .red, .colored .red]
    }]
  }
  let rInstDef : CardDef := {
    name := "P55 Check9 RedInst"
    manaCost := { symbols := #[.colored .red] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gFilterLaunder0 :=
    let g0 :=
      insertObject
        (addPermanent (addPermanent gMain trWatchDef p0 p0) filterRtoRRDef p0 p0)
        rInstDef p0 (.hand p0)
    g0.record (GameEvent.manaAdded g0.turnNumber p0 #[{ mana := .colored .red, fromTreasure := true }])
  let gFilterLaunderProp := mustApply gFilterLaunder0 p0 (.cast (gFilterLaunder0.player p0).hand.back!)

  -- 9. `hasUniqueManaPayment` `instrInterest` AST traversals (`MoveMods.choice?`, `ManaSpec`, `DelayedTokenAction`):
  let twoWhiteCost : ManaCost := ⟨#[.twobrid .white]⟩
  let moveChoiceSpellDef : CardDef := {
    name := "P55 Check9 MoveChoiceMana"
    manaCost := twoWhiteCost
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .moveZone (.inZones { zones := #[.hand], owner := .ofPlayer .you } .anyObject) .graveyard .discard
          { choice? := some { count := .exact (.manaSpent .this) } }
      }
    }
  }
  let addManaSpecSpellDef : CardDef := {
    name := "P55 Check9 AddManaSpec"
    manaCost := twoWhiteCost
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .player (.addMana .you { spec := .sequence #[(.colored .red, .manaSpent .this)] })
      }
    }
  }
  let delayedTokSpellDef : CardDef := {
    name := "P55 Check9 DelayedTokMana"
    manaCost := ManaCost.ofGeneric 1
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .create (.tokens .you (.const 1) (.predefined .treasure)
          { delayedAction? := some (.sacrificeAtEndStepUnless
              (.castPred (.manaSpentMatches (.ofColor .red) .this))) })
      }
    }
  }
  let gMoveChoice0 :=
    (insertObject (addPermanent gMain plains p0 p0) moveChoiceSpellDef p0 (.hand p0)).addMana p0 .colorless 2
  let gMoveChoiceProp := mustApply gMoveChoice0 p0 (.cast (gMoveChoice0.player p0).hand.back!)
  let gManaSpec0 :=
    (insertObject (addPermanent gMain plains p0 p0) addManaSpecSpellDef p0 (.hand p0)).addMana p0 .colorless 2
  let gManaSpecProp := mustApply gManaSpec0 p0 (.cast (gManaSpec0.player p0).hand.back!)
  let gDelayedTok0 :=
    (insertObject (addPermanent gMain mountain p0 p0) delayedTokSpellDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gDelayedTokProp := mustApply gDelayedTok0 p0 (.cast (gDelayedTok0.player p0).hand.back!)

  mustHoldCheck9 "p55_prioFlashbackAndGyLand"
    (!hasGameStatePriorityAction gFb0 p0 &&
     !hasGameStatePriorityAction gFb1 p0 &&
     hasGameStatePriorityAction gFb2 p0 &&
     !hasGameStatePriorityAction gGyLandNoPerm p0 &&
     hasGameStatePriorityAction gGyLandWithPerm p0 &&
     !hasGameStatePriorityAction gGyLandPlayed p0) &&
  mustHoldCheck9 "p55_prioLibraryTopCreatureMorphLand"
    (!hasGameStatePriorityAction gTopCr0 p0 &&
     hasGameStatePriorityAction gTopCrPay p0 &&
     !hasGameStatePriorityAction gTopMorph0 p0 &&
     hasGameStatePriorityAction gTopMorphPay p0 &&
     !hasGameStatePriorityAction gTopLandNoPerm p0 &&
     hasGameStatePriorityAction gTopLandWithPerm p0) &&
  mustHoldCheck9 "p55_prioSneak"
    (hasGameStatePriorityAction gSnkUnblkPay p0 &&
     !hasGameStatePriorityAction gSnkUnblkNoMana p0 &&
     !hasGameStatePriorityAction gSnkBlockedPay p0 &&
     !hasGameStatePriorityAction gSnkSacOnlyAtk p0 &&
     hasGameStatePriorityAction gSnkSacExtraCr p0) &&
  mustHoldCheck9 "p55_prioConvokeAndImprovise"
    (!hasGameStatePriorityAction gConvShort p0 &&
     hasGameStatePriorityAction gConvEnough p0 &&
     !hasGameStatePriorityAction gImpShort p0 &&
     hasGameStatePriorityAction gImpEnough p0) &&
  mustHoldCheck9 "p55_prioTargetReducedSpellAndEquip"
    (!hasGameStatePriorityAction gTgtNoGob p0 &&
     hasGameStatePriorityAction gTgtWithGob p0 &&
     !hasGameStatePriorityAction gEquipNoDisc p0 &&
     hasGameStatePriorityAction gEquipWithDisc p0) &&
  mustHoldCheck9 "p55_uniqueManaExtraBeforeMinSub"
    (!hasUniqueManaPayment gAncProp) &&
  mustHoldCheck9 "p55_uniqueManaMinSubTapOrder"
    (!hasUniqueManaPayment gMinOrderProp) &&
  mustHoldCheck9 "p55_uniqueManaFilterLandSpendsPoolMana"
    (!hasUniqueManaPayment gFilterLaunderProp) &&
  mustHoldCheck9 "p55_uniqueManaInstrInterestAst"
    (!hasUniqueManaPayment gMoveChoiceProp &&
     !hasUniqueManaPayment gManaSpecProp &&
     !hasUniqueManaPayment gDelayedTokProp)

/- Phase 56 Item 4: `Demo.hasGameStatePriorityAction` stack-granted Convoke,
Morph & Impending Convoke/Improvise/target-reduction, zero-output mana abilities,
and `Demo.hasUniqueManaPayment` `minSub`-interleaved `extra`, non-covering
`spendsPoolMana` laundering across both branches, pain-land `damageYou`, and
remaining `spellManaSpentInterest` AST nodes. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0

  -- 1. `hasGameStatePriorityAction`: stack-granted Layer-6 Convoke:
  --    `"Creature spells you cast have convoke"` makes a `{3}` creature affordable with 3 creatures and 0 lands!
  let convokeLordDef : CardDef := {
    name := "P56 Check9 ConvokeLord"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .all #[.hasType .creature, .controlledBy .you] }
        (.grantKeywords #[Keyword.convoke])
    ]
  }
  let bear3Def : CardDef := creature "P56 Check9 Bear3" (ManaCost.ofGeneric 3) #["Bear"] 3 3
  let gStackConv0 :=
    insertObject (addPermanent (addPermanent (addPermanent gMain grizzlyBears p0 p0) grizzlyBears p0 p0) grizzlyBears p0 p0)
      bear3Def p0 (.hand p0)
  let gStackConv1 := addPermanent gStackConv0 convokeLordDef p0 p0

  -- 2. `hasGameStatePriorityAction`: Morph with stack-granted Convoke, Impending with Improvise,
  --    and zero-output tap mana ability (`{T}: Add {R} for each charge counter on ~` at 0 counters):
  let morphDef : CardDef := {
    creature "P56 Check9 MorphCr" (ManaCost.ofGeneric 6) #["Human"] 5 5 with
    keywords := #[.morph (CostSpec.ofGeneric 4)]
  }
  let gMorphConv0 :=
    insertObject (addPermanent (addPermanent (addPermanent gMain grizzlyBears p0 p0) grizzlyBears p0 p0) grizzlyBears p0 p0)
      morphDef p0 (.hand p0)
  let gMorphConv1 := addPermanent gMorphConv0 convokeLordDef p0 p0
  let impImpDef : CardDef := {
    creature "P56 Check9 ImpImp" (ManaCost.ofGeneric 6) #["Avatar"] 5 5 with
    keywords := #[Keyword.improvise, .impending 3 (CostSpec.ofGeneric 2)]
  }
  let art0Def : CardDef := { name := "P56 Check9 Relic", types := #[.artifact] }
  let gImpImp0 := insertObject gMain impImpDef p0 (.hand p0)
  let gImpImp1 := addPermanent (addPermanent gImpImp0 art0Def p0 p0) art0Def p0 p0
  let zeroOutManaDef : CardDef := {
    name := "P56 Check9 ChargeRock"
    types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .red, .counterCount (some .charge) .this)])
    ]
  }
  let gZeroOut := addPermanent gMain zeroOutManaDef p0 p0

  -- 3. `hasUniqueManaPayment`: `minSub`-interleaved `extra` (`S0: {W}{G}(+2)`, `S1: {U}{G}(+1)`, `E: {G}(+1)`
  --    paying `{W}{U}{2}` where `S1, E, S0` spends 5 counters vs 6 in `S0, S1, E` and `E, S0, S1`):
  let s0Def : CardDef := {
    name := "P56 Check9 S0"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .white, .const 1), (.colored .green, .const 1)])
        (riders := #[.entersWithPlusOneCounters 2])
    ]
  }
  let s1Def : CardDef := {
    name := "P56 Check9 S1"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .blue, .const 1), (.colored .green, .const 1)])
        (riders := #[.entersWithPlusOneCounters 1])
    ]
  }
  let eDef : CardDef := {
    name := "P56 Check9 E"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])
        (riders := #[.entersWithPlusOneCounters 1])
    ]
  }
  let wu2CreatureDef : CardDef :=
    creature "P56 Check9 WU2" { symbols := #[.generic 2, .colored .white, .colored .blue] } #["Beast"] 2 2
  let gInterleave0 :=
    insertObject (addPermanent (addPermanent (addPermanent gMain s0Def p0 p0) s1Def p0 p0) eDef p0 p0)
      wu2CreatureDef p0 (.hand p0)
  let gInterleaveProp := mustApply gInterleave0 p0 (.cast (gInterleave0.player p0).hand.back!)

  -- 4. `hasUniqueManaPayment`: non-covering `spendsPoolMana` filter (`{R}: Add {G}`) in BOTH branches
  --    (`| some =>` pool already covers `{R}`, AND `| none =>` pool partially covers `{R}{U}`):
  let filterRtoGDef : CardDef := {
    name := "P56 Check9 RtoG"
    types := #[.artifact]
    activatedAbilities := #[
      { ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])
          (CostSpec.ofMana { symbols := #[.colored .red] }) with }
    ]
  }
  let trWatchDef : CardDef := {
    name := "P56 Check9 TrWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject none (some .fromTreasure)) (Effect.gainLife 1)
    ]
  }
  let rSpellDef : CardDef := {
    name := "P56 Check9 RSpell", manaCost := { symbols := #[.colored .red] }, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let ruSpellDef : CardDef := {
    name := "P56 Check9 RUSpell", manaCost := { symbols := #[.colored .red, .colored .blue] }, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gLaunderSome0 :=
    let g := insertObject
      (addPermanent (addPermanent (addPermanent gMain trWatchDef p0 p0) filterRtoGDef p0 p0) mountain p0 p0)
      rSpellDef p0 (.hand p0)
    g.record (GameEvent.manaAdded g.turnNumber p0 #[{ mana := .colored .red, fromTreasure := true }])
  let gLaunderSomeProp := mustApply gLaunderSome0 p0 (.cast (gLaunderSome0.player p0).hand.back!)
  let gLaunderNone0 :=
    let g := insertObject
      (addPermanent (addPermanent (addPermanent gMain trWatchDef p0 p0) filterRtoGDef p0 p0) island p0 p0)
      ruSpellDef p0 (.hand p0)
    g.record (GameEvent.manaAdded g.turnNumber p0 #[{ mana := .colored .red, fromTreasure := true }])
  let gLaunderNoneProp := mustApply gLaunderNone0 p0 (.cast (gLaunderNone0.player p0).hand.back!)

  -- 5. `hasUniqueManaPayment`: pain land (`damageYou := 1`) paying `{1}` is NOT collapsed as unique:
  let painLandDef : CardDef := {
    name := "P56 Check9 PainLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)]),
      ActivatedAbility.manaAbility (.oneOf (.explicit #[.colored .red, .colored .white]) (.const 1)) (damageYou := 1)
    ]
  }
  let cost1SpellDef : CardDef := {
    name := "P56 Check9 Cost1", manaCost := ManaCost.ofGeneric 1, types := #[.instant],
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gPain0 := insertObject (addPermanent gMain painLandDef p0 p0) cost1SpellDef p0 (.hand p0)
  let gPainProp := mustApply gPain0 p0 (.cast (gPain0.player p0).hand.back!)

  -- 6. `hasUniqueManaPayment`: remaining AST nodes in `spellManaSpentInterest`:
  --    (a) `.stack (.mayCastOrPlay ..)` (`GrantPlayPermSpec.maxTotalManaValue?`),
  --    (b) `Instruction.optional` `CostSpec`,
  --    (c) `Condition.playerPred`,
  --    (d) `ActivatedAbility.condition?` on a battlefield permanent!
  let twoWhiteCost : ManaCost := ⟨#[.twobrid .white]⟩
  let stackMayCastSpellDef : CardDef := {
    name := "P56 Check9 StackMayCast"
    manaCost := twoWhiteCost
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .ofPlayer .you } .anyObject)
          { maxTotalManaValue? := some (.manaSpent .this) })
      }
    }
  }
  let optCostSpellDef : CardDef := {
    name := "P56 Check9 OptCost"
    manaCost := twoWhiteCost
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .optional .you (some (CostSpec.ofItems #[.payLife (.manaSpent .this)]))
          (Effect.gainLife 1).body .noop
      }
    }
  }
  let playerPredSpellDef : CardDef := {
    name := "P56 Check9 PlayerPred"
    manaCost := twoWhiteCost
    types := #[.sorcery]
    spellAbility := some {
      effect := {
        body := .ifCond (.playerPred .you (.metric .life .ge (.manaSpent .this)))
          (Effect.gainLife 1).body .noop
      }
    }
  }
  let actCondPermDef : CardDef := {
    name := "P56 Check9 ActCondPerm"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := Effect.gainLife 1
      condition? := some (.castPred (.manaSpentMatches (.ofColor .red) .this))
    }]
  }
  let gAst1 :=
    (insertObject (addPermanent gMain plains p0 p0) stackMayCastSpellDef p0 (.hand p0)).addMana p0 .colorless 2
  let gAst1Prop := mustApply gAst1 p0 (.cast (gAst1.player p0).hand.back!)
  let gAst2 :=
    (insertObject (addPermanent gMain plains p0 p0) optCostSpellDef p0 (.hand p0)).addMana p0 .colorless 2
  let gAst2Prop := mustApply gAst2 p0 (.cast (gAst2.player p0).hand.back!)
  let gAst3 :=
    (insertObject (addPermanent gMain plains p0 p0) playerPredSpellDef p0 (.hand p0)).addMana p0 .colorless 2
  let gAst3Prop := mustApply gAst3 p0 (.cast (gAst3.player p0).hand.back!)
  let gAst4 :=
    (insertObject (addPermanent (addPermanent gMain actCondPermDef p0 p0) mountain p0 p0)
      cost1SpellDef p0 (.hand p0)).addMana p0 (.colored .green) 1
  let gAst4Prop := mustApply gAst4 p0 (.cast (gAst4.player p0).hand.back!)

  -- 4b(i) k >= 5 distinct `minSub` blocks + extra plain source:
  --       With 5+ distinct rider/mana blocks in `minSub`, `canExtraPlainSourcesChangeOutcome`
  --       either exhaustively finds a non-sampled order (such as a 3-cycle) or fails closed
  --       when the permutation budget is exhausted, never falsely autopaying!
  let bigRiderSpellDef : CardDef :=
    creature "P56 Check9 BigRider"
      { symbols := #[.colored .white, .colored .blue, .colored .black, .colored .red, .colored .green, .generic 1] }
      #["Human"] 5 5
  let mkDistinctRiderLand (nm : String) (m : ManaType) (n : Nat) : CardDef := {
    name := nm
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(m, .const 1)])
        (riders := #[.entersWithPlusOneCounters n])
    ]
  }
  let gPerm6_0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent
              (addPermanent
                (addPermanent
                  (addPermanent gMain (mkDistinctRiderLand "P56 L1" (.colored .white) 1) p0 p0)
                  (mkDistinctRiderLand "P56 L2" (.colored .blue) 2) p0 p0)
                (mkDistinctRiderLand "P56 L3" (.colored .black) 3) p0 p0)
              (mkDistinctRiderLand "P56 L4" (.colored .red) 4) p0 p0)
            (mkDistinctRiderLand "P56 L5" (.colored .green) 5) p0 p0)
          (mkDistinctRiderLand "P56 L6" .colorless 6) p0 p0)
        (mkDistinctRiderLand "P56 LExtra" .colorless 7) p0 p0)
      bigRiderSpellDef p0 (.hand p0)
  let gPerm6Prop := mustApply gPerm6_0 p0 (.cast (gPerm6_0.player p0).hand.back!)

  mustHoldCheck9 "p56_prioStackConvoke"
    (!hasGameStatePriorityAction gStackConv0 p0 &&
     hasGameStatePriorityAction gStackConv1 p0) &&
  mustHoldCheck9 "p56_prioMorphConvokeImpendingImproviseZeroOut"
    (!hasGameStatePriorityAction gMorphConv0 p0 &&
     hasGameStatePriorityAction gMorphConv1 p0 &&
     !hasGameStatePriorityAction gImpImp0 p0 &&
     hasGameStatePriorityAction gImpImp1 p0 &&
     hasGameStatePriorityAction gZeroOut p0) &&
  mustHoldCheck9 "p56_uniqueManaInterleavedExtra"
    (!hasUniqueManaPayment gInterleaveProp &&
     !hasUniqueManaPayment gPerm6Prop) &&
  mustHoldCheck9 "p56_uniqueManaNonCoveringPoolSpendBothBranches"
    (!hasUniqueManaPayment gLaunderSomeProp &&
     !hasUniqueManaPayment gLaunderNoneProp) &&
  mustHoldCheck9 "p56_uniqueManaPainLand"
    (!hasUniqueManaPayment gPainProp) &&
  mustHoldCheck9 "p56_uniqueManaRemainingAstNodes"
    (!hasUniqueManaPayment gAst1Prop &&
     !hasUniqueManaPayment gAst2Prop &&
     !hasUniqueManaPayment gAst3Prop &&
     !hasUniqueManaPayment gAst4Prop)

/- Phase 57 Item 4b: `Demo.hasUniqueManaPayment` empty-initial-`pool` laundering on the
`| none =>` branch, `manaAbilityDefCanChangeOutcome` / pool-covered `extraEffect?` &
modal `m.output? = none` modes, unprojected `CostItem` rejection in `isPlainTap` /
`isPlainTapManaAbilityDef`, and `spellManaSpentInterest` traversal of `g.activeEffects`
(CR 106.6 / 601.2f-g / 605.1a / 605.3a-b). -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := afterDraw
  let cause57 : EventCause := .oneShotEffect (some ⟨1⟩) none (some p0)

  -- 1. Empty-initial-`pool` laundering on `| none =>` branch:
  --    Empty pool + plain `{R}` land with `.cantBeCountered` rider + `{R}: Add {G}` filter
  --    + plain Island casting `{1}{U}` instant: paying via filter drops `.cantBeCountered`!
  let cbcRedLandDef : CardDef := {
    name := "P57 Check9 CbcRedLand"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .red, .const 1)])
        (riders := #[.cantBeCountered])
    ]
  }
  let filterRtoG57Def : CardDef := {
    name := "P57 Check9 FilterRtoG"
    types := #[.artifact]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.sequence #[(.colored .green, .const 1)])
        (CostSpec.ofMana { symbols := #[.colored .red] })
    ]
  }
  let oneUSpellDef : CardDef := {
    name := "P57 Check9 OneUSpell"
    manaCost := { symbols := #[.generic 1, .colored .blue] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gEmptyLaunder0 :=
    insertObject
      (addPermanent
        (addPermanent (addPermanent gMain cbcRedLandDef p0 p0) filterRtoG57Def p0 p0)
        island p0 p0)
      oneUSpellDef p0 (.hand p0)
  let gEmptyLaunderProp := mustApply gEmptyLaunder0 p0 (.cast (gEmptyLaunder0.player p0).hand.back!)

  -- 2. `manaAbilityDefCanChangeOutcome` & `hasUniqueManaPayment` with `extraEffect?`
  --    and modal `m.output? = none` non-mana modes on the `| some (_, spent0) =>` branch:
  let extraEffManaDef : CardDef := {
    name := "P57 Check9 ExtraEffMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := { body := .seq #[Instruction.addSimpleMana #[.colored .green],
        .life (.gain .you (.const 1))] }
    }]
  }
  let modalNonManaDef : CardDef := {
    name := "P57 Check9 ModalNonMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf]
      effect := { body := .chooseModes {
        modes := #[
          { body := Instruction.addSimpleMana #[.colored .green] },
          { body := .life (.gain .you (.const 1)) }
        ]
      } }
    }]
  }
  let gSpell57Def : CardDef := {
    name := "P57 Check9 GSpell"
    manaCost := { symbols := #[.colored .green] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let trWatch57Def : CardDef := {
    name := "P57 Check9 TrWatch"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject none (some .fromTreasure)) (Effect.gainLife 1)
    ]
  }
  -- (a) With `anyOutcomeMatters == true` AND pool already paying `{G}`:
  let gExtraMatters0 :=
    (insertObject (addPermanent (addPermanent gMain trWatch57Def p0 p0) extraEffManaDef p0 p0)
      gSpell57Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gExtraMattersProp := mustApply gExtraMatters0 p0 (.cast (gExtraMatters0.player p0).hand.back!)
  let gModalMatters0 :=
    (insertObject (addPermanent (addPermanent gMain trWatch57Def p0 p0) modalNonManaDef p0 p0)
      gSpell57Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gModalMattersProp := mustApply gModalMatters0 p0 (.cast (gModalMatters0.player p0).hand.back!)
  -- (b) Even with `!anyOutcomeMatters` and pool already paying `{G}`, state-changing
  --     `extraEffect?` / non-mana modal mana abilities still prevent false auto-pay:
  let gExtraPlain0 :=
    (insertObject (addPermanent gMain extraEffManaDef p0 p0) gSpell57Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gExtraPlainProp := mustApply gExtraPlain0 p0 (.cast (gExtraPlain0.player p0).hand.back!)
  let gModalPlain0 :=
    (insertObject (addPermanent gMain modalNonManaDef p0 p0) gSpell57Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gModalPlainProp := mustApply gModalPlain0 p0 (.cast (gModalPlain0.player p0).hand.back!)
  -- Direct `manaAbilityDefCanChangeOutcome` unit check for both definitions:
  let extraObj := (gExtraMattersProp.permanentsOf p0).find? (·.name == extraEffManaDef.name) |>.get!
  let extraDef := (gExtraMattersProp.manaAbilityDefs extraObj)[0]!
  let modalObj := (gModalMattersProp.permanentsOf p0).find? (·.name == modalNonManaDef.name) |>.get!
  let modalDef := (gModalMattersProp.manaAbilityDefs modalObj)[0]!
  let extraCanChange :=
    match gExtraMattersProp.proposedSpell with
    | some prop =>
      manaAbilityDefCanChangeOutcome gExtraMattersProp (gExtraMattersProp.proposedManaSpend prop)
        prop extraObj extraDef {}
    | none => false
  let modalCanChange :=
    match gModalMattersProp.proposedSpell with
    | some prop =>
      manaAbilityDefCanChangeOutcome gModalMattersProp (gModalMattersProp.proposedManaSpend prop)
        prop modalObj modalDef {}
    | none => false

  -- 3. Unprojected `CostItem`s (`.putCounters`, `.untapSelf`) rejected by `isPlainTap` /
  --    `isPlainTapManaAbilityDef`:
  let unprojCostManaDef : CardDef := {
    name := "P57 Check9 UnprojCostMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .putCounters (.const 1) .charge .self]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let gUnproj0 := insertObject (addPermanent gMain unprojCostManaDef p0 p0) gSpell57Def p0 (.hand p0)
  let unprojObj := (gUnproj0.permanentsOf p0).find? (·.name == unprojCostManaDef.name) |>.get!
  let unprojDef := (gUnproj0.manaAbilityDefs unprojObj)[0]!
  let gUnprojProp := mustApply gUnproj0 p0 (.cast (gUnproj0.player p0).hand.back!)

  -- 4. `spellManaSpentInterest` traverses active `.layered _ (.abilities add _) d` in `g.activeEffects`
  --    even when NO matching permanent is on the battlefield yet:
  let gActEff0 :=
    ((insertObject (addPermanent gMain Catalog.treasureToken p0 p0) gSpell57Def p0 (.hand p0)).createEffect
      (.layered (.creaturesControlledBy p0)
        (.abilities {
          triggeredAbilities := #[
            TriggeredAbility.mkTrigger
              (.castSpell .you .anyObject none (some .fromTreasure)) (Effect.gainLife 1)
          ]
        } .none)
        .untilEndOfTurn)
      (cause := some cause57)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gActEffProp := mustApply gActEff0 p0 (.cast (gActEff0.player p0).hand.back!)
  let actEffInterestOk :=
    match gActEffProp.proposedSpell with
    | some prop => (spellManaSpentInterest gActEffProp (gActEffProp.proposedManaSpend prop) (some prop)).fromTreasure
    | none => false

  mustHoldCheck9 "p57_emptyPoolLaundering"
    ((gEmptyLaunderProp.player p0).manaPool.units.isEmpty &&
     !hasUniqueManaPayment gEmptyLaunderProp) &&
  mustHoldCheck9 "p57_extraEffectAndModalNonMana"
    (extraDef.extraEffect?.isSome &&
     modalDef.modeChoices.any (·.output?.isNone) &&
     extraCanChange && modalCanChange &&
     !hasUniqueManaPayment gExtraMattersProp &&
     !hasUniqueManaPayment gModalMattersProp &&
     !hasUniqueManaPayment gExtraPlainProp &&
     !hasUniqueManaPayment gModalPlainProp) &&
  mustHoldCheck9 "p57_unprojectedCostNotPlainTap"
    (!unprojDef.isPlainTap &&
     !gUnproj0.isPlainTapManaAbilityDef p0 unprojObj unprojDef &&
     !hasUniqueManaPayment gUnprojProp) &&
  mustHoldCheck9 "p57_activeEffectsSpellManaInterest"
    (actEffInterestOk &&
     !hasUniqueManaPayment gActEffProp)

/- Phase 58: `mayPlayLand` cast-only exclusion in `Demo.hasGameStatePriorityAction` and
`Agent.choose`, `Demo.spellManaSpentInterest` `bc.otherFace` & active `.copy` effects,
`advObj` Layer-1 `.copy` immunity in `Demo.hasGameStatePriorityAction` & `Agent.choose`,
and hybrid/twobrid + `{X}` + multi-ability `tapChoicesForSource` + unprojected `CostItem`
mana soundness. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0
  let cause58 : EventCause := .oneShotEffect (some ⟨1⟩) none (some p0)

  -- 1. `mayPlayLand` cast-only exclusion in `Demo.hasGameStatePriorityAction` and `Agent.choose`:
  let elven58Def : CardDef := {
    name := "P58 Check9 ElvenPerm"
    types := #[.enchantment]
    staticAbilities := #[
      .ruleModifying none (.play (.mayPlayFrom .you .library (.hasType .creature) false false false false))
    ]
  }
  let dryad58Def : CardDef := {
    name := "P58 Check9 DryadArbor"
    types := #[.land, .creature]
    subtypes := #["Forest", "Dryad"]
    power := some (.fixed 1)
    toughness := some (.fixed 1)
  }
  let gCastOnlyLib :=
    insertObject (addPermanent gMain elven58Def p0 p0) dryad58Def p0 (.library p0)
  let gCastOnlyEx0 := insertObject gMain forest p0 .exile
  let exLandId := (gCastOnlyEx0.objects.find? (fun o => o.zone == .exile && o.name == forest.name)).get!.id
  let gCastOnlyEx :=
    gCastOnlyEx0.createEffect
      (.permission (some p0) (.playFromExile exLandId { player := p0, withoutManaCost := true })
        .untilEndOfTurn)
      (cause := some cause58)
  let gPlayableEx :=
    gCastOnlyEx0.createEffect
      (.permission (some p0) (.playFromExile exLandId { player := p0 }) .untilEndOfTurn)
      (cause := some cause58)
  let mayPlayLandDemoOk :=
    !hasGameStatePriorityAction gCastOnlyLib p0 &&
    !(match Agent.choose gCastOnlyLib p0 with | some (.playLand _) => true | _ => false) &&
    !hasGameStatePriorityAction gCastOnlyEx p0 &&
    !(match Agent.choose gCastOnlyEx p0 with | some (.playLand _) => true | _ => false) &&
    hasGameStatePriorityAction gPlayableEx p0 &&
    (match Agent.choose gPlayableEx p0 with | some (.playLand id) => id == exLandId | _ => false)

  -- 2. `Demo.spellManaSpentInterest` merges `bc.otherFace` AND active `.layered _ (.copy card) d`:
  let backWatchesTreasureDef : CardDef := {
    creature "P58 Check9 NightWolf" ManaCost.empty #["Wolf"] 3 3 with
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you .anyObject none (some .fromTreasure)) (Effect.gainLife 1)
    ]
  }
  let dfcFront58Def : CardDef := {
    creature "P58 Check9 DayWolf" { symbols := #[.colored .green] } #["Wolf"] 2 2 with
    otherFace := some backWatchesTreasureDef
  }
  let gDfc0 :=
    (insertObject (addPermanent gMain Catalog.treasureToken p0 p0) dfcFront58Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gDfcProp := mustApply gDfc0 p0 (.cast (gDfc0.player p0).hand.back!)
  let dfcInterestOk :=
    match gDfcProp.proposedSpell with
    | some prop => (spellManaSpentInterest gDfcProp (gDfcProp.proposedManaSpend prop) (some prop)).fromTreasure
    | none => false
  let plainGSpell58Def : CardDef := {
    name := "P58 Check9 PlainGSpell"
    manaCost := { symbols := #[.colored .green] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gCopyEff0 :=
    ((insertObject (addPermanent gMain Catalog.treasureToken p0 p0) plainGSpell58Def p0 (.hand p0)).createEffect
      (.layered (.creaturesControlledBy p0) (.copy backWatchesTreasureDef) .untilEndOfTurn)
      (cause := some cause58)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colored .green }])
  let gCopyEffProp := mustApply gCopyEff0 p0 (.cast (gCopyEff0.player p0).hand.back!)
  let copyEffInterestOk :=
    match gCopyEffProp.proposedSpell with
    | some prop => (spellManaSpentInterest gCopyEffProp (gCopyEffProp.proposedManaSpend prop) (some prop)).fromTreasure
    | none => false

  -- 3. `advObj` Layer-1 `.copy` immunity in `Demo.hasGameStatePriorityAction` & `Agent.choose`:
  --    Creature with `{R}` Instant Adventure + Layer-1 `.copy` on `o.id` overwriting it with the
  --    same Creature face + instant/sorcery-only `{R}` mana in pool -> MUST still see the Adventure
  --    as castable (no false auto-pass)!
  let advSub : SubFace := {
    kind := .adventure
    name := "P58 Check9 QuickSpark"
    manaCost := { symbols := #[.colored .red] }
    types := #[.instant]
    subtypes := #["Adventure"]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let advCard58Def : CardDef := {
    creature "P58 Check9 SparkKnight" { symbols := #[.generic 4, .colored .red] } #["Knight"] 3 3 with
    subFaces := #[advSub]
  }
  let gAdv0 :=
    (insertObject gMain advCard58Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0
        #[{ mana := .colored .red, restriction := some ManaSpendRestriction.instantOrSorcery }])
  let advId := (gAdv0.player p0).hand.back!
  let gAdvCopied :=
    gAdv0.createEffect (.layered (.objects #[advId]) (.copy advCard58Def) .indefinite) (cause := some cause58)
  let advLayer1CopyOk :=
    hasGameStatePriorityAction gAdvCopied p0 &&
    (match Agent.choose gAdvCopied p0 with | some (.castAdventure id) => id == advId | _ => false)

  -- 4. Hybrid/twobrid, `{X}` mana ability, and multi-ability plain `{T}` permanent in `Demo`:
  let hybridSpell58Def : CardDef := {
    name := "P58 Check9 HybridBG_B"
    manaCost := { symbols := #[.hybrid .black .green, .colored .black] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gHybrid58 :=
    (insertObject gMain hybridSpell58Def p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0
        #[{ mana := .colored .black }, { mana := .colored .green }])
  let xMana58Def : CardDef := {
    name := "P58 Check9 XMana"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.mana { symbols := #[.x] }, .tapSelf]
      effect := Effect.addMana #[.colored .green]
    }]
  }
  let gXMana58 := addPermanent gMain xMana58Def p0 p0
  let multiTap58Def : CardDef := {
    name := "P58 Check9 MultiTap"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.ofItems #[.tapSelf]
        effect := Effect.addMana #[.colored .green] },
      { cost := CostSpec.ofItems #[.tapSelf]
        effect := { body := .player (.addMana .you {
          spec := ManaSpec.fixed #[.colored .green, .colored .green]
          restriction := some (.onlyForSpells (.hasType .creature))
        }) } }
    ]
  }
  let ggCreat58Def : CardDef :=
    creature "P58 Check9 GGCreat" { symbols := #[.colored .green, .colored .green] } #["Beast"] 2 2
  let gMultiTap58 := insertObject (addPermanent gMain multiTap58Def p0 p0) ggCreat58Def p0 (.hand p0)
  let manaDemo58Ok :=
    hasGameStatePriorityAction gHybrid58 p0 &&
    !hasGameStatePriorityAction gXMana58 p0 &&
    hasGameStatePriorityAction gMultiTap58 p0

  mustHoldCheck9 "p58_mayPlayLandDemo" mayPlayLandDemoOk &&
  mustHoldCheck9 "p58_dfcAndCopyInterest"
    (dfcInterestOk && !hasUniqueManaPayment gDfcProp &&
     copyEffInterestOk && !hasUniqueManaPayment gCopyEffProp) &&
  mustHoldCheck9 "p58_advLayer1Copy" advLayer1CopyOk &&
  mustHoldCheck9 "p58_manaDemo58" manaDemo58Ok

/- Phase 59: `Demo.manaAbilityDefCanChangeOutcome` & `canExtraPlainSourcesChangeOutcome`
`.hybrid` color-`b` check (no false-unique auto-pay on `{2/W}{W/U}`), Layer-6 Improvise
in `Demo`, `PlayPermission.landsAllowed := false`, and synthetic `morphObj` Layer-5
color immunity in `Demo`/`Agent`. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0
  let cause59 : EventCause := .oneShotEffect (some ⟨1⟩) none (some p0)

  -- 1. `Demo.hasUniqueManaPayment` checks hybrid color `b`:
  --    Cost `{2/W}{W/U}` with mana spent amount interest (e.g. a trigger watching mana spent),
  --    pool `{W}{W}`, and an untapped `{U}` source: paying `{W}{W}` spends 2, whereas tapping
  --    `{U}` and paying `{2/W}` with `{W}` + `{W/U}` with `{U}` vs `{2/W}` with 2 + `{U}`
  --    flips spent outcome when `{W}` has a rider (`cantBeCountered`) or `{2/W}` uses `{W}` vs `{2}`!
  let hybridRiderSpell59 : CardDef := {
    name := "P59 Check9 HybridRider"
    manaCost := { symbols := #[.twobrid .white, .hybrid .white .blue] }
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let watchAmt59 : CardDef := {
    name := "P59 Check9 WatchAmt"
    types := #[.enchantment]
    triggeredAbilities := #[
      TriggeredAbility.mkTrigger
        (.castSpell .you (.not (.hasType .creature)))
        { body := .player (.drawCards .you (.manaSpent .triggerSubject)) }
    ]
  }
  let gHyb0 :=
    (insertObject (addPermanent (addPermanent gMain watchAmt59 p0 p0) island p0 p0)
      hybridRiderSpell59 p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0
        #[{ mana := .colored .white }, { mana := .colorless }, { mana := .colorless }])
  let gHybProp := mustApply gHyb0 p0 (.cast (gHyb0.player p0).hand.back!)
  -- Pool `{W}{C}{C}` pays `{2/W}{W/U}` spending 3 (`{C}{C}` for `{2/W}` + `{W}` for `{W/U}`),
  -- while tapping Island for `{U}` lets `{W}` pay `{2/W}` + `{U}` pay `{W/U}` spending 2!
  let hybridColorBOk := !hasUniqueManaPayment gHybProp

  -- 2. `PlayPermission.landsAllowed := false` suppresses `playLand` in `Demo` and `Agent`:
  let gExLand0 := insertObject gMain forest p0 .exile
  let exLandId := (gExLand0.objects.find? (fun o => o.zone == .exile && o.name == forest.name)).get!.id
  let gCastOnlyEx :=
    gExLand0.createEffect
      (.permission (some p0) (.playFromExile exLandId { player := p0, landsAllowed := false })
        .untilEndOfTurn)
      (cause := some cause59)
  let landsAllowedDemoOk :=
    !hasGameStatePriorityAction gCastOnlyEx p0 &&
    !(match Agent.choose gCastOnlyEx p0 with | some (.playLand _) => true | _ => false)

  -- 3. Layer-6 Improvise recognized by `Demo.hasUniqueManaPayment` and `hasGameStatePriorityAction`:
  let impAura59 : CardDef := {
    name := "P59 Check9 ImpStatic"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := .stack, pred := .controlledBy .you }
        (.grantKeywords #[Keyword.improvise])
    ]
  }
  let plainArt59 : CardDef := { name := "P59 Check9 Relic", types := #[.artifact] }
  let plainInst59 : CardDef := {
    name := "P59 Check9 TwoInst"
    manaCost := ManaCost.ofGeneric 2
    types := #[.instant]
    spellAbility := some { effect := Effect.gainLife 1 }
  }
  let gImp0 :=
    (insertObject (addPermanent (addPermanent gMain impAura59 p0 p0) plainArt59 p0 p0)
      plainInst59 p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0 #[{ mana := .colorless }, { mana := .colorless }])
  let gImpProp := mustApply gImp0 p0 (.cast (gImp0.player p0).hand.back!)
  let improviseDemoOk := !hasUniqueManaPayment gImpProp

  -- 4. Synthetic `morphObj` ignores Layer-5 color effects on `o.id` in `Demo.hasGameStatePriorityAction`:
  --    A red-spell tax static (+{5}) must NOT tax a colorless face-down Morph spell even if `o.id`
  --    in hand carries a Layer-5 `.colors .set {red}` effect!
  let redTax59 : CardDef := {
    name := "P59 Check9 RedTax"
    types := #[.enchantment]
    staticAbilities := #[
      .costModifier none (.spells .any (.hasColor (.literal .red)))
        (.increaseGeneric (.const 5))
    ]
  }
  let morphDef59 : CardDef := {
    creature "P59 Check9 MorphCreature" { symbols := #[.generic 5, .colored .green] } #["Beast"] 4 4 with
    keywords := #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])]
  }
  let gMorph0 :=
    (insertObject (addPermanent gMain redTax59 p0 p0) morphDef59 p0 (.hand p0)).record
      (GameEvent.manaAdded gMain.turnNumber p0
        #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let morphHandId := (gMorph0.player p0).hand.back!
  let gMorphColored :=
    gMorph0.createEffect
      (.layered (.objects #[morphHandId]) (.colors .set (ColorSet.ofList [.red])) .indefinite)
      (cause := some cause59)
  let morphColorImmuneOk := hasGameStatePriorityAction gMorphColored p0

  mustHoldCheck9 "p59_hybridColorB" hybridColorBOk &&
  mustHoldCheck9 "p59_landsAllowedDemo" landsAllowedDemoOk &&
  mustHoldCheck9 "p59_improviseDemo" improviseDemoOk &&
  mustHoldCheck9 "p59_morphColorImmune" morphColorImmuneOk

/- Phase 60: Layer-6 hand/graveyard mana abilities in `Demo`, non-mana `crewExcludesSelf`
in `Agent`/`Demo`, `PlayPermission.landsAllowed := true` with `anyManaColor := true`, and
origin-zone Layer-6 Morph + Layer-6 Sneak in `Agent`. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let gMain := emptyHand afterDraw p0
  let cause60 : EventCause := .oneShotEffect (some ⟨1⟩) none (some p0)

  -- 1. Layer-6 granted hand/graveyard mana abilities detected by `Demo.hasGameStatePriorityAction`:
  let handManaGrant60 : CardDef := {
    name := "P60 Check9 HandManaGrant", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantActivated #[{
          cost := CostSpec.ofItems #[.exile (.exact 1) .yourHand .self]
          effect := Effect.addMana #[.colored .red]
        }])
    ]
  }
  let gyManaGrant60 : CardDef := {
    name := "P60 Check9 GyManaGrant", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.graveyard], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantActivated #[{
          cost := CostSpec.ofItems #[.exile (.exact 1) .yourGraveyard .self]
          effect := Effect.addMana #[.colored .black]
        }])
    ]
  }
  let plainVanilla60 : CardDef := creature "P60 Check9 Vanilla" (ManaCost.ofGeneric 9) #["Bear"] 2 2
  let gHandMana60 := insertObject (addPermanent gMain handManaGrant60 p0 p0) plainVanilla60 p0 (.hand p0)
  let gGyMana60 := insertObject (addPermanent gMain gyManaGrant60 p0 p0) plainVanilla60 p0 (.graveyard p0)
  let handGyManaDemoOk :=
    hasGameStatePriorityAction gHandMana60 p0 &&
    hasGameStatePriorityAction gGyMana60 p0

  -- 2. Non-mana `crewExcludesSelf`: a creature whose `.tapObjects (.totalPowerAtLeast 2)` cost
  --    does NOT specify `.otherThan .this` is activatable by `Agent` using itself!
  let selfCrew60 : CardDef := {
    creature "P60 Check9 SelfCrew" ManaCost.zero #["Bear"] 2 2 with
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapObjects (.totalPowerAtLeast (.const 2)) (.all #[.hasType .creature, .tapped false, .controlledBy .you])]
      effect := Effect.gainLife 2
    }]
  }
  let gSelfCrew60 := addPermanent gMain selfCrew60 p0 p0
  let selfCrewId60 := (gSelfCrew60.permanentsOf p0).find? (·.name == selfCrew60.name) |>.get!.id
  let selfCrewAgentOk :=
    hasGameStatePriorityAction gSelfCrew60 p0 &&
    (match Agent.choose gSelfCrew60 p0 with
     | some (.activate sid 0) => sid == selfCrewId60
     | _ => false)

  -- 3. `PlayPermission.landsAllowed := true` with `anyManaColor := true` preserves `playLand` in Demo & Agent:
  let gExLand60 := insertObject gMain forest p0 .exile
  let gExLandPerm60 :=
    gExLand60.applyUnified p0
      { body := .stack (.mayCastOrPlay (.inZones { zones := #[.exile], owner := .any } .anyObject)
          { duration := .untilEndOfTurn, anyManaColor := true, landsAllowed := true, freeCast := false }) } #[]
  let landsAllowedAnyManaOk :=
    hasGameStatePriorityAction gExLandPerm60 p0 &&
    (match Agent.choose gExLandPerm60 p0 with
     | some (.playLand _) => true
     | _ => false)

  -- 4. Origin-zone Layer-6 Morph in `Agent` `.chooseKicker`:
  let morphExLord60 : CardDef := {
    name := "P60 Check9 MorphExLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.exile], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[.morph (CostSpec.ofItems #[.mana (ManaCost.ofGeneric 2)])])
    ]
  }
  let gMorphEx60 :=
    (insertObject (addPermanent gMain morphExLord60 p0 p0) plainVanilla60 p0 .exile).record
      (GameEvent.manaAdded gMain.turnNumber p0
        #[{ mana := .colorless }, { mana := .colorless }, { mana := .colorless }])
  let morphExId60 := (gMorphEx60.objects.find? (fun o => o.zone == .exile && o.name == plainVanilla60.name)).get!.id
  let gMorphExPerm60 :=
    gMorphEx60.createEffect
      (.permission (some p0) (.playFromExile morphExId60 { player := p0 }) .untilEndOfTurn)
      (cause := some cause60)
  let gMorphExProp60 := mustApply gMorphExPerm60 p0 (.cast morphExId60)
  let agentOriginMorphOk :=
    gMorphExProp60.pending == .chooseKicker p0 &&
    (match Agent.choose gMorphExProp60 p0 with
     | some (.announceKicker true) => true
     | _ => false)

  mustHoldCheck9 "p60_handGyManaDemo" handGyManaDemoOk &&
  mustHoldCheck9 "p60_selfCrewAgent" selfCrewAgentOk &&
  mustHoldCheck9 "p60_landsAllowedAnyMana" landsAllowedAnyManaOk &&
  mustHoldCheck9 "p60_agentOriginMorph" agentOriginMorphOk


/- Phase 61: Origin-zone Layer-6 Flash in `Demo`/`Agent`, Aura Layer-3 `TextChange`
in `Demo`/`Agent`, Myriad 3-player planeswalker choice via `Agent`, `ResolutionChoices`
empty-option default action safety, and `flashbackUntilEot` + `freeSelf` CR 118.9a. -/
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let gMain := emptyHand afterDraw p0
  let cause61 : EventCause := .oneShotEffect (some ⟨1⟩) none (some p0)

  -- 1. Origin-zone Layer-6 Flash allows casting a creature during upkeep in Demo & Agent:
  let handFlashLord61 : CardDef := {
    name := "P61 Check9 HandFlashLord", types := #[.enchantment]
    staticAbilities := #[
      .continuous none { zones := { zones := #[.hand], owner := .ofPlayer .you }, pred := .hasType .creature }
        (.grantKeywords #[Keyword.flash])
    ]
  }
  let zeroBear61 : CardDef := creature "P61 Check9 ZeroBear" ManaCost.zero #["Bear"] 2 2
  let gFlashUpkeep61 :=
    (insertObject (addPermanent gMain handFlashLord61 p0 p0) zeroBear61 p0 (.hand p0)).record
      (GameEvent.stepBegan gMain.turnNumber .upkeep)
  let flashHandId61 := (gFlashUpkeep61.player p0).hand.back!
  let originFlashDemoOk :=
    hasGameStatePriorityAction gFlashUpkeep61 p0 &&
    (match Agent.choose gFlashUpkeep61 p0 with
     | some (.cast id) => id == flashHandId61
     | _ => false)

  -- 2. Aura Layer-3 `TextChange` ("Goblin" -> "Bear") recognized by Demo & Agent:
  let gobAura61 : CardDef := {
    name := "P61 Check9 GobAura", manaCost := ManaCost.zero
    types := #[.enchantment], subtypes := #["Aura"]
    staticAbilities := #[.enchantRestriction { domain := .object .battlefield (.hasSubtype (.literal .goblin)) }]
  }
  let gAura61Base := addPermanent (insertObject gMain gobAura61 p0 (.hand p0)) grizzlyBears p0 p0
  let auraId61 := (gAura61Base.player p0).hand.back!
  let gAura61Tc :=
    gAura61Base.createEffect
      (.layered (.objects #[auraId61]) (.text (.replaceCreatureType .goblin .bear)) .indefinite)
      (cause := some cause61)
  let auraTcDemoOk :=
    !hasGameStatePriorityAction gAura61Base p0 &&
    hasGameStatePriorityAction gAura61Tc p0 &&
    (match Agent.choose gAura61Tc p0 with
     | some (.cast id) => id == auraId61
     | _ => false)

  -- 3. Myriad 3-player non-defending opponent planeswalker choice via Agent:
  let myriad61 : CardDef := {
    creature "P61 Check9 Myriad" ManaCost.zero #["Scout"] 2 2 with
    keywords := #[Keyword.myriad]
  }
  let pw61 : CardDef := { name := "P61 Check9 Walker", types := #[.planeswalker], loyalty := some 4 }
  let gMyr3Raw :=
    addPermanent
      (addPermanent (gMain.change (.addPlayer { id := p2, name := "Liliana" })) myriad61 p0 p0)
      pw61 p2 p2
  let pwId61 := (gMyr3Raw.permanentsOf p2).find? (·.name == pw61.name) |>.get!.id
  let gMyr3 := gMyr3Raw.recordPutCounters pwId61 .loyalty 4 (some p2) (cause := some cause61)
  let myrId61 := (gMyr3.permanentsOf p0).find? (·.name == myriad61.name) |>.get!.id
  let gMyrAtk61 := mustApply (gMyr3.beginStep .declareAttackers) p0 (.declareAttackers #[myrId61] (some p1))
  let gMyrMay61 := mustApply (mustApply (mustApply gMyrAtk61 p0 .pass) p1 .pass) p2 .pass
  let gMyrPrompt61 := mustApply gMyrMay61 p0 .accept
  let gMyrAgentDone :=
    match Agent.choose gMyrPrompt61 p0 with
    | some act => mustApply gMyrPrompt61 p0 act
    | none => gMyrPrompt61
  let myrToks61 := (gMyrAgentDone.permanentsOf p0).filter (·.printed.isToken)
  let myriadAgentOk :=
    (match gMyrPrompt61.pending with | .resolutionChoice _ (.chooseEnteringAttackTarget ..) => true | _ => false) &&
    gMyrAgentDone.pending == .none &&
    myrToks61.size == 1 &&
    myrToks61[0]!.status.attacking &&
    (match myrToks61[0]!.status.attackingTarget with
     | some (.player q) => q == p2
     | some (.planeswalker pwId) => (gMyrAgentDone.findObject? pwId).any (gMyrAgentDone.controlledBy · p2)
     | _ => false)

  -- 4. `ResolutionChoices` empty-option default/Agent actions decline & resolve cleanly:
  let staleId61 : ObjectId := ⟨99981⟩
  let emptyChoices61 : Array ResolutionChoice := #[
    .palisadeCreatureType #[],
    .blackGatePlayer staleId61 #[],
    .chooseEnteringAttackTarget #[] #[] none,
    .extrapolatePick p0 #[staleId61],
    .mayRevealToHand #[staleId61] #[staleId61] false
  ]
  let emptyAgentOk :=
    emptyChoices61.all fun ch =>
      let gP := gMain.change (.pending (.resolutionChoice p0 ch))
      match Agent.choose gP p0 with
      | some act =>
        match gP.apply p0 act with
        | .ok gDone => gDone.pending == .none
        | .error _ => false
      | none => false

  -- 5. `flashbackUntilEot` + `freeSelf` does NOT make an unpayable graveyard spell free in Demo:
  let freeSelfFb61 : CardDef := {
    name := "P61 Check9 FreeSelfFb", manaCost := ManaCost.ofGenericAndColor 2 .white
    types := #[.instant]
    staticAbilities := #[.costModifier none .thisSpell .alternativeFree]
    spellAbility := some { effect := Effect.gainLife 2 }
  }
  let gFb61Base := insertObject gMain freeSelfFb61 p0 (.graveyard p0)
  let fbId61 := (gFb61Base.player p0).graveyard.back!
  let gFb61 := gFb61Base.createEffect (ContinuousEffectSpec.flashbackUntilEot fbId61) (cause := some cause61)
  let gFb61Mana :=
    gFb61.record (GameEvent.manaAdded gMain.turnNumber p0
      #[{ mana := .colorless }, { mana := .colorless }, { mana := .colored .white }])
  let fbFreeSelfDemoOk :=
    !hasGameStatePriorityAction gFb61 p0 &&
    hasGameStatePriorityAction gFb61Mana p0

  mustHoldCheck9 "p61_originFlashDemo" originFlashDemoOk &&
  mustHoldCheck9 "p61_auraTcDemo" auraTcDemoOk &&
  mustHoldCheck9 "p61_myriadAgent" myriadAgentOk &&
  mustHoldCheck9 "p61_emptyAgent" emptyAgentOk &&
  mustHoldCheck9 "p61_fbFreeSelfDemo" fbFreeSelfDemoOk
