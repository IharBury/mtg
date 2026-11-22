import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

/-! ### Phase 28 Item 2: Idle-priority & mid-proposal `concede` / `finishConcedePriority`
(`popEmptyContinuationFrames`, `runSba`, `promptTriggerTargetsIfNeeded`) and
`chooseCastFromLooked` / `castAsPartOfResolution` `outerPendingReplacements` stashing -/
section Phase28Item2EventAlignment

private def mustHold28i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase28Item2EventAlignment failed: {label}"

private def replayOk28i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. Mid-proposal `concede` pops trailing empty `ContinuationFrame`s, runs SBAs (`runSba := true`)
--    and calls `promptTriggerTargetsIfNeeded` in `finishConcedePriority`, and
--    `castAsPartOfResolution` / `chooseCastFromLooked` stash `g.pendingReplacement` onto
--    `outerPendingReplacements` (CR 117.3 / 603.3 / 608.2g / 704.3 / 800.4a).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g3 := mkThreePlayer27i1 2821

  -- 1a. Mid-proposal `concede`: `p1` is proposing a spell (`g.proposedSpell.isSome`) with an empty
  --     trailing `ContinuationFrame` (`{}`) while `p0` controls a 2/2 Bear with 2 marked damage AND
  --     a stacked targeted trigger (`triggerNeedingTargets`) is waiting for `p0` to choose targets.
  --     When `p1` concedes, `concedePlayersLoop` aborts the proposal, pops the empty continuation
  --     frame, sets `runSba := true`, destroys the lethally damaged Bear via SBA 704.5g, and
  --     prompts `p0` for the trigger's targets via `promptTriggerTargetsIfNeeded`!
  let gMid0 :=
    insertObject (addPermanent g3 bear p0 p0) bear p1 (.hand p1)
  let p0BearId := (gMid0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1HandId := (gMid0.player p1).hand.back!
  let propP1 : ProposedSpell := {
    caster := p1, cost := default, spellId := p1HandId, original := gMid0.object! p1HandId
  }
  let gMid1 :=
    (((gMid0.markDamageOn (gMid0.object! p0BearId) 2 "lethal" (cause := some testCause)).putReflexiveTrigger
      p0 none { targeting := .of .player, body := Instruction.gainLifeFixed 1, phrase := "Target player gains 1 life" }).change
      (.pushContinuationFrame {})).changes #[
      .pending (.activateManaAbilities p1),
      .proposedSpell (some propP1)
    ]
  let gAfterMidConcede := mustApply gMid1 p1 .concede
  let midProposalConcedeSbaAndTrigOk :=
    (gAfterMidConcede.player p1).leftTheGame &&
    gAfterMidConcede.continuations.isEmpty &&
    (gAfterMidConcede.followMovedToZone? p0BearId (· == .graveyard p0)).isSome &&
    gAfterMidConcede.pending == .chooseTargets p0

  -- 1b. `castAsPartOfResolution` and `chooseCastFromLooked` stash `g.pendingReplacement` onto
  --     `outerPendingReplacements` before entering `proposeCast`:
  let costSpellDef : CardDef := {
    name := "P28i2 Free Sac Bolt"
    manaCost := ⟨#[.colored .red]⟩
    types := #[.instant]
    additionalCosts := #[AdditionalCostSpec.mandatory CostSpec.sacrificeCreature]
    spellEffect := some { body := Instruction.gainLifeFixed 1, phrase := "You gain 1 life" }
  }
  let stashedPr : PendingReplacement := .finishPostStep (.beginScryOne p0)
  let gCastRes0 :=
    ((insertObject (addPermanent afterDraw bear p0 p0) costSpellDef p0 .exile).change
      (.pushContinuationFrame {})).change (.pendingReplacement (some stashedPr))
  let exBoltId := (gCastRes0.objects.filter (fun o => o.zone == .exile && o.name == costSpellDef.name))[0]!.id
  let gCastRes1 := gCastRes0.castAsPartOfResolution p0 exBoltId (withoutManaCost := true)
  let castAsPartOfResStashOk :=
    gCastRes1.pendingReplacement.isNone &&
    gCastRes1.outerPendingReplacements.back? == some stashedPr &&
    gCastRes1.proposedSpell.isSome

  let gLookCast0 :=
    ((insertObject (addPermanent afterDraw bear p0 p0) costSpellDef p0 (.library p0)).change
      (.pushContinuationFrame { pendingReplacement := some stashedPr }))
  let libBoltId := (gLookCast0.player p0).library.back!
  let gLookCast1 := gLookCast0.change (.pending (.mayCastFromLooked p0 #[libBoltId] 5))
  let gLookCast2 :=
    match gLookCast1.chooseCastFromLooked p0 (some libBoltId) with
    | .ok g' => g'
    | .error e => panic! e
  let chooseCastFromLookedStashOk :=
    gLookCast2.pendingReplacement.isNone &&
    gLookCast2.outerPendingReplacements.back? == some stashedPr &&
    gLookCast2.proposedSpell.isSome

  mustHold28i2 "1a.midProposalConcedeSbaAndTrigOk" midProposalConcedeSbaAndTrigOk &&
  mustHold28i2 "1b.castAsPartOfResStashOk" castAsPartOfResStashOk &&
  mustHold28i2 "1b.chooseCastFromLookedStashOk" chooseCastFromLookedStashOk &&
  mustHold28i2 "1.replay" (replayOk28i2 #[gAfterMidConcede, gCastRes1, gLookCast2])

end Phase28Item2EventAlignment

/-! ### Phase 28 Item 3: 2HG `.assignCombatDamage` `redirectPendingAfterLeave` &
remaining `g.stillInGame` (`leftTheGame` vs `.lost`) guards -/
section Phase28Item3EventAlignment

private def mustHold28i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase28Item3EventAlignment failed: {label}"

private def replayOk28i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. 2HG `.assignCombatDamage` `redirectPendingAfterLeave` teammate takeover & defender-stillInGame
--    check, plus `g.stillInGame` guards across `Core`, `Library`, `SacrificeDiscard`, `Choices`,
--    `ResolutionCompat`/`Interpreter`, and `Tokens` when `leftTheGame == true` (CR 510.1c / 800.4a,c–d / 810.7).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g2hg := mkTwoHeadedGiant27i4 2831

  -- 1a. In 2HG, `p1` controls a 3/3 creature attacking `p2`, blocked by two 2/2 Bears controlled
  --     by `p2`. While `g.pending == .assignCombatDamage p0 true`, if `p0` leaves via
  --     `playerLeavesGame p0`, surviving teammate `p1` takes over the prompt
  --     (`g.pending == .assignCombatDamage p1 true`):
  let hillGiant : CardDef := { bear with name := "P28i3 Giant", power := some 3, toughness := some 3 }
  let gCombat0 :=
    addPermanent (addPermanent (addPermanent g2hg hillGiant p1 p1) bear p2 p2) bear p2 p2
  let atkId := (gCombat0.permanentsOf p1).find? (·.name == hillGiant.name) |>.get!.id
  let p2Bears := (gCombat0.permanentsOf p2).filter (·.name == bear.name)
  let blk0 := p2Bears[0]!.id
  let blk1 := p2Bears[1]!.id
  let gCombat1 :=
    (((gCombat0.record
      (GameEvent.attackersDeclared gCombat0.turnNumber p0 #[
        (gCombat0.snapshot (gCombat0.object! atkId), .player p2)
      ])).record
      (GameEvent.blockersDeclared gCombat0.turnNumber p2 #[
        (gCombat0.snapshot (gCombat0.object! blk0), atkId),
        (gCombat0.snapshot (gCombat0.object! blk1), atkId)
      ])).change (.pending (.assignCombatDamage p0 true)))
  let gAfterP0Leave := gCombat1.playerLeavesGame p0
  let teammateTakeoverOk :=
    (gAfterP0Leave.player p0).leftTheGame &&
    gAfterP0Leave.stillInGame p1 &&
    gAfterP0Leave.pending == .assignCombatDamage p1 true

  -- 1b. Remaining `g.stillInGame` guards when `p1` has `leftTheGame == true`:
  let g3 := mkThreePlayer27i1 2832
  let gLeftOnly :=
    g3.record (GameEvent.playerLeftGame g3.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
  let sIdx := gLeftOnly.events.size
  let gRecruit := gLeftOnly.finishBeginRecruit p1
  let gShuffle := gLeftOnly.shuffleLibrary p1
  let gSacCreats := gLeftOnly.beginSacrificeCreatures #[p1]
  let gVillainCon := gLeftOnly.beginMayHaveVillainConnive p1 atkId atkId
  let gSacLeast := gLeftOnly.sacrificeLeastPowerCreature p1
  let gDiscHand := gLeftOnly.discardEntireHand p1
  let gExSub := gLeftOnly.exileTopPlayIfYouControlSubtype p1 2 .elf
  let gRiddles := gLeftOnly.riddlesInTheDark p1 2 false
  let gTreasures := gLeftOnly.createTreasureTokens p1 2
  let gGainLifeSearch := gLeftOnly.applyGainLifeSearchBasicPlusOne p0 #[.player p1] 2 (some atkId)
  let stillInGameGuardsOk :=
    !gLeftOnly.stillInGame p1 &&
    (gLeftOnly.player p1).leftTheGame &&
    !gLeftOnly.defendingPlayers.contains p1 &&
    !gLeftOnly.apnapPlayers.contains p1 &&
    gLeftOnly.nextLiving p0 == p2 &&
    gRecruit.events.size == sIdx &&
    gShuffle.events.size == sIdx &&
    gSacCreats.pending == .none &&
    gSacCreats.battlefield.size == gLeftOnly.battlefield.size &&
    gVillainCon.events.size == sIdx &&
    gSacLeast.events.size == sIdx &&
    gDiscHand.events.size == sIdx &&
    gExSub.events.size == sIdx &&
    gRiddles.events.size == sIdx &&
    gTreasures.battlefield.size == gLeftOnly.battlefield.size &&
    gTreasures.log.back? == some "no token is created (CR 800.4b)" &&
    gGainLifeSearch.log.back? == some "The target is no longer legal"

  mustHold28i3 "1a.teammateTakeoverOk" teammateTakeoverOk &&
  mustHold28i3 "1b.stillInGameGuardsOk" stillInGameGuardsOk &&
  mustHold28i3 "1.replay" (replayOk28i3 #[gAfterP0Leave, gLeftOnly, gSacCreats, gTreasures, gGainLifeSearch])

end Phase28Item3EventAlignment

/-! ### Phase 28 Item 4: *Palantír* `.influence` / Aura & Equipment `attachedHost?` /
`.damageEqualSourcePower` LKI fallbacks and remaining Layer 1 `g.name` / `g.nameWithToken` reads -/
section Phase28Item4EventAlignment

private def mustHold28i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase28Item4EventAlignment failed: {label}"

private def replayOk28i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. CR 608.2h / 613.1a:
--    *Palantír* (`offerPalantirChoice` & `.palantirMayDraw` decline) LKI `.influence` counter
--    reads via `g.damageSourceById?`, Aura & Equipment `attachedTo` LKI fallbacks across
--    `ModeledTriggers.attachedHost?`, `Interpreter` tap-enchanted/unprepare, and
--    `TriggeredAbilities` (`applyAttach` `.enchantedCreature`, `applyTap` `.enchanted`,
--    `applyRemoveCounters` `.all, .enchanted`), `FraAbilities` `.damageEqualSourcePower` LKI
--    power fallback, and Layer 1 `g.name` / `g.nameWithToken` log reads.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1BearId := (gBase.permanentsOf p1).find? (·.name == bear.name) |>.get!.id

  -- 1a. *Palantír* LKI `.influence` counter fallback when *Palantír* left the battlefield with
  --     3 `.influence` counters before `offerPalantirChoice` / `.palantirMayDraw` decline:
  let palDef : CardDef := { name := "Palantír of Orthanc", types := #[.artifact] }
  let gPal0 := addPermanent gBase palDef p0 p0
  let palId := (gPal0.permanentsOf p0).find? (·.name == palDef.name) |>.get!.id
  let (gPalDeparted, _) :=
    (gPal0.recordPutCounters palId .influence 3 (byPlayer := some p0) (cause := some testCause)).move
      palId (.graveyard p0) none (cause := some testCause)
  let gPalOffered := (gPalDeparted.change (.pushContinuationFrame {})).offerPalantirChoice p0 p1 palId
  let palOfferLogOk :=
    gPalOffered.pending == .fraChoice p1 (.palantirMayDraw p0 palId) &&
    gPalOffered.log.any (·.contains "may have")
  let libBefore := (gPalOffered.player p0).library.size
  let gPalDeclined := mustApply gPalOffered p1 .decline
  let palDeclineMillOk :=
    (gPalDeclined.player p0).library.size + 3 == libBefore

  -- 1b. Aura & Equipment LKI `attachedTo` fallback when the Aura/Equipment left the battlefield
  --     while attached to `p0BearId`:
  let auraDef : CardDef := {
    name := "P28i4 Test Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    triggeredAbilities := #[TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }]
  }
  let equipDef : CardDef := { name := "P28i4 Test Equip", types := #[.artifact], subtypes := #["Equipment"] }
  let gAura0 :=
    addPermanent (addPermanent gBase auraDef p0 p0) equipDef p0 p0
  let auraId := (gAura0.permanentsOf p0).find? (·.name == auraDef.name) |>.get!.id
  let equipId := (gAura0.permanentsOf p0).find? (·.name == equipDef.name) |>.get!.id
  let gAuraAttached :=
    (gAura0.record (GameEvent.attached gAura0.turnNumber (gAura0.snapshot (gAura0.object! auraId)) p0BearId (cause := testCause))).recordPutCounters
      p0BearId .plusOnePlusOne 2 (byPlayer := some p0) (cause := some testCause)
  let (gAuraDeparted, _) := gAuraAttached.move auraId (.graveyard p0) none (cause := some testCause)
  -- `attachedHost?` finds `p0BearId` via LKI:
  let attachedHostLkiOk := (gAuraDeparted.attachedHost? (some auraId)).map (·.id) == some p0BearId
  -- Unified tap-enchanted + unprepare taps `p0BearId` via LKI:
  let gFraTapHost :=
    gAuraDeparted.applyAbilityEffect p0
      { body := .seq #[Instruction.tap .attachedHost, .permanent (.setDesignation .attachedHost .prepared false)] }
      #[] (some auraId)
  -- `TriggeredAbilities.applyTap` `.enchanted` taps `p0BearId` via LKI:
  let dummyTrig : TriggeredAbility := auraDef.triggeredAbilities[0]!
  let gTrigTapHost := gAuraDeparted.applyTap p0 dummyTrig (some auraId) #[] .enchanted
  -- `TriggeredAbilities.applyAttach` `.eachEquipment, .enchantedCreature` attaches `equipId` to `p0BearId` via LKI:
  let gTrigAttachHost :=
    gAuraDeparted.applyAttach p0 dummyTrig (some auraId) #[.permanent equipId] .eachEquipment .enchantedCreature
  -- `TriggeredAbilities.applyRemoveCounters` `.all, .enchanted` removes all counters from `p0BearId` via LKI:
  let gTrigRemCntHost :=
    gAuraDeparted.applyRemoveCounters p0 (some auraId) #[] .all .enchanted
  let auraHostLkiFallbacksOk :=
    attachedHostLkiOk &&
    (gFraTapHost.object! p0BearId).status.tapped &&
    (gTrigTapHost.object! p0BearId).status.tapped &&
    (gTrigAttachHost.object! equipId).attachedTo == some p0BearId &&
    (gTrigRemCntHost.object! p0BearId).status.plusOnePlusOne == 0

  -- 1c. Unified `Instruction.dealDamage (.targetSlot 0) (.objectStat .power .this)` uses LKI
  --     when the source left the battlefield with pumped power (2 + 2 = 4) before resolution:
  let (gBearPumpedDeparted, _) :=
    (gBase.recordPutCounters p0BearId .plusOnePlusOne 2 (byPlayer := some p0) (cause := some testCause)).move
      p0BearId (.graveyard p0) none (cause := some testCause)
  let gDmgEqPow :=
    (gBearPumpedDeparted.change
      (.pushContinuationFrame { resolvingAbility := some p0BearId })).applyAbilityEffect
      p0 { targeting := .of .creature, body := Instruction.dealDamage (.targetSlot 0) (.objectStat .power .this) }
      #[.permanent p1BearId] (some p0BearId)
  let dmgEqSourcePowerLkiOk :=
    (gDmgEqPow.object! p1BearId).status.damage == 4

  -- 1d. Layer 1 `g.name` / `g.nameWithToken` reads on copied objects:
  let cloneNameCard : CardDef := { bear with name := "P28i4 Layer1 Copy Name" }
  let gCopiedBear :=
    gBase.createEffect
      (.layered (.objects #[p0BearId]) (.copy cloneNameCard) .indefinite)
      (cause := some testCause)
  let layer1NameOk :=
    gCopiedBear.name (gCopiedBear.object! p0BearId) == "P28i4 Layer1 Copy Name" &&
    gCopiedBear.nameWithToken (gCopiedBear.object! p0BearId) == "P28i4 Layer1 Copy Name"

  mustHold28i4 "1a.palantirLkiOk" (palOfferLogOk && palDeclineMillOk) &&
  mustHold28i4 "1b.auraHostLkiFallbacksOk" auraHostLkiFallbacksOk &&
  mustHold28i4 "1c.dmgEqSourcePowerLkiOk" dmgEqSourcePowerLkiOk &&
  mustHold28i4 "1d.layer1NameOk" layer1NameOk &&
  mustHold28i4 "1.replay"
    (replayOk28i4 #[gPalOffered, gPalDeclined, gFraTapHost, gTrigTapHost, gTrigAttachHost, gTrigRemCntHost, gDmgEqPow, gCopiedBear])

end Phase28Item4EventAlignment

/-! ### Phase 29 Item 1: Co-departing `.chooseReplacement` preservation in `playerLeavesGameCore`,
`redirectPendingAfterLeave` retarget cleanup when `q != p`, and `.crew` / `.zemoBoastExile` /
`.chooseTeamworkCreatures` `.restorePending`, `checkReversal`, & `decline` revalidation -/
section Phase29Item1EventAlignment

private def mustHold29i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase29Item1EventAlignment failed: {label}"

private def replayOk29i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. Co-departing `.chooseReplacement` preservation (`allowLost := true` in `replacementChoiceValid`
--    inside `playerLeavesGameCore`), `redirectPendingAfterLeave` stack-object retarget cleanup
--    when `q != p`, and `.crew` / `.zemoBoastExile` / `.chooseTeamworkCreatures` revalidation
--    across `.restorePending`, `checkReversal`, `decline`, `pickTeamworkCreatures`, `Game.applyIdle`,
--    and `Agent.choose` (CR 601.2b,h / 602.2b / 616.1 / 702.122a / 702.142a / 733.1 / 800.4a).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := mkThreePlayer27i1 2911

  -- 1a. `replacementChoiceValid` `allowLost := true` preserves co-departing `p1`'s
  --     `.chooseReplacement` across `p0`'s departure in `leavePlayersWhoLost`, so `p1`'s
  --     subsequent departure takes the `q == p` branch and runs `runPostCastAndPropCleanup`
  --     to resume `p2`'s outer continuation (`.beginScryOne p2`):
  let rConnive : ReplacementId := { kind := .extraDrawOnConnive, object := none }
  let gCoLost0 :=
    ((g3.change (.pushContinuationFrame {
        pendingReplacement := some (.finishPostStep (.beginScryOne p2))
      })).record
      (GameEvent.playerLost g3.turnNumber p0 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))).record
      (GameEvent.playerLost g3.turnNumber p1 .lifeZeroOrLess (cause := some (.stateBased .lifeZeroOrLess)))
  let allowLostFlagOk :=
    !gCoLost0.replacementChoiceValid p1 #[rConnive] (allowLost := false) &&
    gCoLost0.replacementChoiceValid p1 #[rConnive] (allowLost := true)
  let gCoLost1 := gCoLost0.change (.pending (.chooseReplacement p1 #[rConnive]))
  let (gAfterP0Core, savedAfterP0?) := gCoLost1.playerLeavesGameCore p0 (deferRestore := true)
  let gAfterCoLostLeave :=
    gCoLost0.leavePlayersWhoLost (savedIn := some (.chooseReplacement p1 #[rConnive]))
  let coDepartingChooseReplOk :=
    allowLostFlagOk &&
    savedAfterP0?.1 == some (Pending.chooseReplacement p1 #[rConnive]) &&
    (gAfterCoLostLeave.player p0).leftTheGame &&
    (gAfterCoLostLeave.player p1).leftTheGame &&
    gAfterCoLostLeave.pending == .scry p2 1

  -- 1b. `redirectPendingAfterLeave` retarget cleanup when `q != p`:
  --     * `.mayChangeSpellTarget spellId 0 #[]`: clears when `spellId` left `.stack` during `p1`'s leave,
  --       keeps when `spellId` is still on `.stack`:
  let boltDef : CardDef := {
    name := "P29i1 Bolt", manaCost := ⟨#[.colored .red]⟩, types := #[.instant]
    spellEffect := some { targeting := .of .player, body := Instruction.dealDamageFixed (.targetSlot 0) 3 }
  }
  let gStack0 :=
    insertObject (insertObject g3 boltDef p0 (.hand p0)) boltDef p1 (.hand p1)
  let p0HandBolt := (gStack0.player p0).hand.back!
  let p1HandBolt := (gStack0.player p1).hand.back!
  let (gStack1, p0SpellId) := gStack0.move p0HandBolt .stack (some p0) (cause := some testCause)
  let (gStack2, p1SpellId) := gStack1.move p1HandBolt .stack (some p1) (cause := some testCause)
  let dummyModesRest : ChooseModesRest := {
    controller := p0
    ability := TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }
    sourceId := none, targets := #[], lastKnownPower := none
    sourceName := "Test", modes := [], how := .vision
  }
  let gRetargetStale :=
    ((gStack2.change (.pushContinuationFrame { chooseModesRest := some dummyModesRest })).change
      (.pending (.fraChoice p0 (.mayChangeSpellTarget p1SpellId 0 #[.player p0])))).playerLeavesGame p1
  let gRetargetLive :=
    ((gStack2.change (.pushContinuationFrame { chooseModesRest := some dummyModesRest })).change
      (.pending (.fraChoice p0 (.mayChangeSpellTarget p0SpellId 0 #[.player p0])))).playerLeavesGame p1
  --     * `.newTargetsForCopySlot`:
  --       - all copies gone -> clears `.pending` and `chooseModesRest`;
  --       - `copies[0]` (`p1SpellId`) gone while `copies[1]` (`p0SpellId`) still on `.stack` ->
  --         resets to `.fraChoice p0 (.newTargetsForCopies #[p0SpellId])`;
  --       - `copies[0]` (`p0SpellId`) still on `.stack` while `copies[1]` (`p1SpellId`) gone ->
  --         preserves `.fraChoice p0 (.newTargetsForCopySlot #[p0SpellId] 1 #[.player p0])`:
  let gCopiesAllGone :=
    ((gStack2.change (.pushContinuationFrame { chooseModesRest := some dummyModesRest })).change
      (.pending (.fraChoice p0 (.newTargetsForCopies #[p1SpellId])))).playerLeavesGame p1
  let gCopiesFirstGone :=
    ((gStack2.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.newTargetsForCopySlot #[p1SpellId, p0SpellId] 1 #[.player p0])))).playerLeavesGame p1
  let gCopiesSecondGone :=
    ((gStack2.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.newTargetsForCopySlot #[p0SpellId, p1SpellId] 1 #[.player p0])))).playerLeavesGame p1
  let retargetAfterLeaveOk :=
    gRetargetStale.pending == .none &&
    gRetargetStale.chooseModesRest.isNone &&
    gRetargetLive.pending == .fraChoice p0 (.mayChangeSpellTarget p0SpellId 0 #[.player p0]) &&
    gCopiesAllGone.pending == .none &&
    gCopiesAllGone.chooseModesRest.isNone &&
    gCopiesFirstGone.pending == .fraChoice p0 (.newTargetsForCopies #[p0SpellId]) &&
    gCopiesSecondGone.pending == .fraChoice p0 (.newTargetsForCopySlot #[p0SpellId] 1 #[.player p0])

  -- 1c. `.crew`, `.zemoBoastExile`, and `.chooseTeamworkCreatures` revalidation in `.restorePending`,
  --     `checkReversal`, `decline`, `pickTeamworkCreatures`, `Game.applyIdle`, and `Agent.choose`:
  let wall04 : CardDef := { bear with name := "P29i1 Wall 0/4", power := some 0, toughness := some 4 }
  let vehicleDef : CardDef := {
    name := "P29i1 Skiff", types := #[.artifact], subtypes := #["Vehicle"]
    power := some 4, toughness := some 4
  }
  let blackMv15 : CardDef := {
    name := "P29i1 Fifteen Black"
    manaCost := { symbols := Array.replicate 15 (.colored .black) }
    types := #[.creature], power := some 2, toughness := some 2
  }
  let gCost0 :=
    insertObject (insertObject (addPermanent (addPermanent (addPermanent afterDraw wall04 p0 p0) bear p0 p0) vehicleDef p0 p0)
      blackMv15 p0 (.graveyard p0)) boltDef p0 (.hand p0)
  let wallId := (gCost0.permanentsOf p0).find? (·.name == wall04.name) |>.get!.id
  let bearId := (gCost0.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let vehId := (gCost0.permanentsOf p0).find? (·.name == vehicleDef.name) |>.get!.id
  let handBoltId := (gCost0.player p0).hand.back!
  let (gCost1, stackBoltId) :=
    ((gCost0.changes #[.pushContinuationFrame {}, .saveProposalCheckpoint]).move
      handBoltId .stack (some p0) (cause := some testCause))
  let propCost : ProposedSpell := {
    caster := p0, cost := default, spellId := stackBoltId, original := gCost0.object! handBoltId
  }
  let gWithProp :=
    gCost1.changes #[.pushStack { objectId := stackBoltId, controller := p0, targets := #[] }, .proposedSpell (some propCost)]

  -- `.restorePending` + `checkReversal` inside `.seq`:
  -- Untapped power for `p0` is `0 + 2 = 2`. So `crew` / `chooseTeamworkCreatures` needing `3`
  -- fails revalidation and reverses `proposedSpell`, and `checkReversal` stops `.seq` from running
  -- the second half (`.finishPostStep (.beginScryOne p0)`), whereas needing `2` succeeds and
  -- opens the prompt!
  let gCrewFailSeq :=
    gWithProp.resumePendingReplacement
      (.seq (.restorePending (.fraChoice p0 (.crew vehId vehId 3)) false)
            (.finishPostStep (.beginScryOne p0)))
  let gCrewOk :=
    gWithProp.resumePendingReplacement (.restorePending (.fraChoice p0 (.crew vehId vehId 2)) false)
  let gZemoOk :=
    gWithProp.resumePendingReplacement (.restorePending (.fraChoice p0 (.zemoBoastExile bearId bearId)) false)
  let gZemoFailSeq :=
    let gyId := (gWithProp.player p0).graveyard.back!
    let (gNoGy, _) := gWithProp.move gyId .exile none (cause := some testCause)
    gNoGy.resumePendingReplacement
      (.seq (.restorePending (.fraChoice p0 (.zemoBoastExile bearId bearId)) false)
            (.finishPostStep (.beginScryOne p0)))
  let gTwFailSeq :=
    gWithProp.resumePendingReplacement
      (.seq (.restorePending (.chooseTeamworkCreatures p0 3) false)
            (.finishPostStep (.beginScryOne p0)))
  let gTwOk :=
    gWithProp.resumePendingReplacement (.restorePending (.chooseTeamworkCreatures p0 2) false)
  let restoreCostRevalOk :=
    gCrewFailSeq.proposedSpell.isNone && gCrewFailSeq.pending == .none &&
    gCrewOk.proposedSpell.isSome && gCrewOk.pending == .fraChoice p0 (.crew vehId vehId 2) &&
    gZemoOk.proposedSpell.isSome && gZemoOk.pending == .fraChoice p0 (.zemoBoastExile bearId bearId) &&
    gZemoFailSeq.proposedSpell.isNone && gZemoFailSeq.pending == .none &&
    gTwFailSeq.proposedSpell.isNone && gTwFailSeq.pending == .none &&
    gTwOk.proposedSpell.isSome && gTwOk.pending == .chooseTeamworkCreatures p0 2

  -- `Decisions.decline`, `pickTeamworkCreatures`, `Game.applyIdle`, and `Agent.choose`:
  let wrongPlayerDeclineErr :=
    match gTwOk.apply p1 .decline with
    | .error msg => msg.contains "Only"
    | .ok _ => false
  let mustPayDeclineErr :=
    match gTwOk.apply p0 .decline with
    | .error msg => msg.contains "You must tap creatures with total power 2 or more"
    | .ok _ => false
  let gTwNeed3 := gWithProp.change (.pending (.chooseTeamworkCreatures p0 3))
  let gTwDeclined := mustApply gTwNeed3 p0 .decline
  let pickedNeed2 := gTwOk.pickTeamworkCreatures p0 2
  let gTwIdle := applyIdle gTwNeed3
  let agentActNeed3Ok :=
    match Agent.choose gTwNeed3 p0 with
    | some .decline => true
    | _ => false
  let teamworkDeclineAndPickOk :=
    wrongPlayerDeclineErr &&
    mustPayDeclineErr &&
    gTwDeclined.proposedSpell.isNone &&
    gTwDeclined.pending == .none &&
    pickedNeed2 == #[bearId] &&
    !pickedNeed2.contains wallId &&
    gTwIdle.proposedSpell.isNone &&
    gTwIdle.pending == .none &&
    agentActNeed3Ok

  mustHold29i1 "1a.coDepartingChooseReplOk" coDepartingChooseReplOk &&
  mustHold29i1 "1b.retargetAfterLeaveOk" retargetAfterLeaveOk &&
  mustHold29i1 "1c.restoreCostRevalOk" restoreCostRevalOk &&
  mustHold29i1 "1c.teamworkDeclineAndPickOk" teamworkDeclineAndPickOk &&
  mustHold29i1 "1.replay"
    (replayOk29i1 #[
      gAfterP0Core, gAfterCoLostLeave, gRetargetStale, gRetargetLive,
      gCopiesAllGone, gCopiesFirstGone, gCopiesSecondGone,
      gCrewFailSeq, gCrewOk, gZemoOk, gZemoFailSeq, gTwFailSeq, gTwOk, gTwDeclined, gTwIdle
    ])

end Phase29Item1EventAlignment

/-! ### Phase 29 Item 2: `EventCause` allocation & `ContinuationFrame` pushing in
`Library.moveIdsInOrder`, `ResolutionCompat.offerBottomAnyOrder`, `ResolutionCompat.offerCardChoice`,
`LibrarySearch.beginLibrarySearch`, `ModeledTriggers`, and `ResolutionEffects` -/
section Phase29Item2EventAlignment

private def mustHold29i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase29Item2EventAlignment failed: {label}"

private def replayOk29i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. `Library.moveIdsInOrder` and `ResolutionCompat.offerBottomAnyOrder` allocate a `.oneShotEffect`
--    `EventCause` from `currentResolvingContext?` via `allocDelayedCause`, `offerCardChoice` writes
--    `stashedCause` onto the `ContinuationFrame` pushed by `beginFraChoice`, and `beginLibrarySearch`,
--    `ModeledTriggers`, and `ResolutionEffects` push a `ContinuationFrame` via `beginFraChoice`
--    (including `offerVisionModes` preserving `chooseModesRest`, CR 608.2c / 701.20 / 701.23).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := mkThreePlayer27i1 2921
  let gBase := addPermanent g3 bear p0 p0
  let srcId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- 1a. `Library.moveIdsInOrder` with `cause := none` and `resolvingContext := some (some srcId, p0)`
  --     allocates a `.oneShotEffect` cause and stamps it onto the moved events:
  let gMove0 :=
    insertObject (insertObject (gBase.change (.pushContinuationFrame { resolvingContext := some (some srcId, p0) }))
      bear p0 .exile) bear p0 .exile
  let exIds := (gMove0.objects.filter (·.zone == .exile)).map (·.id)
  let preMoveEv := gMove0.events.size
  let gMovedInOrder := gMove0.moveIdsInOrder exIds (.library p0) (cause := none)
  let moveInOrderEvents := (gMovedInOrder.events.extract preMoveEv gMovedInOrder.events.size).filter fun ev =>
    match ev with
    | .rules _ (.zone (.moved _ _ .exile (.library _) ..)) _ _ => true
    | _ => false
  let moveIdsInOrderCauseOk :=
    moveInOrderEvents.size == 2 &&
    match moveInOrderEvents[0]!, moveInOrderEvents[1]! with
    | .rules _ _ (.oneShotEffect id1 s1 c1) b1, .rules _ _ (.oneShotEffect id2 s2 c2) b2 =>
      id1.isSome && id1 == id2 && s1 == some srcId && c1 == some p0 &&
      s2 == some srcId && c2 == some p0 && b1.isSome && b1 == b2
    | _, _ => false

  -- 1b. `ResolutionCompat.offerBottomAnyOrder` with `cause := none` allocates a fresh
  --     `.oneShotEffect` cause from `currentResolvingContext?` (ignoring any earlier move cause
  --     on the library cards) and stores it in `g.stashedCause`:
  let topTwo := gMovedInOrder.scryLookedIds p0 2
  let gOfferBottom := gMovedInOrder.offerBottomAnyOrder p0 topTwo (cause := none)
  let offerBottomCauseOk :=
    gOfferBottom.pending == .fraChoice p0 (.orderLibraryBottom topTwo) &&
    match gOfferBottom.stashedCause with
    | some (.oneShotEffect (some eid) s c) =>
      s == some srcId && c == some p0 && eid.raw + 1 == gOfferBottom.nextEffectId
    | _ => false

  -- 1c. `ResolutionCompat.offerCardChoice` with `g.continuations == #[]` calls `beginFraChoice`
  --     BEFORE `.change (.stashedCause (some testCause))` so `g.stashedCause == some testCause`:
  let gCardChoice :=
    gBase.offerCardChoice p0 topTwo 1 (.toHand false) "Choose a card" (cause := some testCause)
  let offerCardChoiceCauseOk :=
    !gCardChoice.continuations.isEmpty &&
    gCardChoice.pending == .fraChoice p0 (.chooseCards topTwo 1 (.toHand false)) &&
    gCardChoice.stashedCause == some testCause

  -- 1d. `LibrarySearch.beginLibrarySearch`, `ModeledTriggers`, and `ResolutionEffects` push a
  --     `ContinuationFrame` via `beginFraChoice` when `g.continuations` is empty (and
  --     `offerVisionModes` preserves `g.chooseModesRest.isSome`):
  let boltDef : CardDef := {
    name := "P29i2 Bolt", manaCost := ⟨#[.colored .red]⟩, types := #[.instant]
    spellEffect := some { targeting := .of .player, body := Instruction.dealDamageFixed (.targetSlot 0) 3 }
  }
  let gWithStackAndHand :=
    insertObject (insertObject gBase bear p0 (.hand p0)) boltDef p0 (.hand p0)
  let handBolt := (gWithStackAndHand.player p0).hand.back!
  let (gStack0, spellId) := gWithStackAndHand.move handBolt .stack (some p0) (cause := some testCause)
  let gStack :=
    gStack0.change (.pushStack { objectId := spellId, controller := p0, targets := #[Target.player p1], targetsAnnounced := true })
  let dummyTrig : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }

  let gLibSearch := gBase.beginLibrarySearch p0 (fun _ => true) "a card" .hand
  let gLibMaySearch := gBase.beginLibrarySearch p0 (fun _ => true) "a card" .hand (optional := true)
  let gSacNontoken := gBase.continueNontokenSacrifices #[p0] #[]
  let gWidow := gBase.finishExileLibraryUntilNonland p0 (some srcId) none none
  let gRetarget := gStack.offerSpellRetarget p0 spellId 0
  let gHyde := gBase.offerHydeChoice p0 (some srcId)
  let gDaredevil := gBase.offerExileTopHeroPump p0 (some srcId)
  let gKingpin := gBase.offerPay2LifeToughness p0
  let gVision := gBase.offerVisionModes p0 dummyTrig (some srcId) #[]
  let gWall := gBase.offerMayCreateWall p0
  let gPayRefl := gBase.offerPayForReflexive p0 (some srcId) #[.colored .red] .dealTwoDamage 1
  let gExCasts := gBase.offerExileCasts p0 #[srcId] 1
  let gEntAtk :=
    gBase.promptEnteringAttackItems #[.token p0 .soldier11white true #[.player p1, .player p2] none]
  let gWorlds := gStack.offerWorldsCreatures [p0] #[] #[] (some srcId)

  let allFraPushFrameOk :=
    #[gLibSearch, gLibMaySearch, gSacNontoken, gWidow, gRetarget, gHyde,
      gDaredevil, gKingpin, gVision, gWall, gPayRefl, gExCasts, gEntAtk, gWorlds].all (fun g =>
      !g.continuations.isEmpty &&
      match g.pending with
      | .fraChoice .. => true
      | _ => false) &&
    gVision.chooseModesRest.isSome

  mustHold29i2 "1a.moveIdsInOrderCauseOk" moveIdsInOrderCauseOk &&
  mustHold29i2 "1b.offerBottomCauseOk" offerBottomCauseOk &&
  mustHold29i2 "1c.offerCardChoiceCauseOk" offerCardChoiceCauseOk &&
  mustHold29i2 "1d.allFraPushFrameOk" allFraPushFrameOk &&
  mustHold29i2 "1.replay"
    (replayOk29i2 #[
      gMovedInOrder, gOfferBottom, gCardChoice, gLibSearch, gLibMaySearch,
      gSacNontoken, gWidow, gRetarget, gHyde, gDaredevil, gKingpin, gVision,
      gWall, gPayRefl, gExCasts, gEntAtk, gWorlds
    ])

end Phase29Item2EventAlignment

/-! ### Phase 29 Item 3: Remaining `g.stillInGame` (`!pl.lost && !pl.leftTheGame`) checks and
departed-player entry-point / post-pause guards -/
section Phase29Item3EventAlignment

private def mustHold29i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase29Item3EventAlignment failed: {label}"

private def replayOk29i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. `StateBasedActions.checkSBACounted`, `Targeting.expandEachOpponentEffect`,
--    `Triggers.putTriggeredAbilityOnStack`, `ResolutionEffects` (`queueFollowupReflexive`,
--    `putReflexiveTrigger`, `beginMayCastFromLooked`), `SacrificeDiscard` (`finishConniveDraws`,
--    `applyConnive`), `Choices` (`beholdQuality`, `drawPerSevenCardGraveyard`,
--    `mayDiscardHandDrawThatMany`, `discardHandThenDraw`, `exileTopPlayIfYouControlSubtypeLoop`,
--    `finishGrimaDirectCast`, `exileUntilInstantOrSorceryLoop`, `grimaExileUntilInstantOrSorcery`),
--    `LibrarySearch.resolveExileTopPlayUntilEndOfNextTurn`, and `Decisions.runPostStep`
--    `.grantPlayUntilEndOfNextTurn` check `g.stillInGame` (CR 800.4a).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g3 := mkThreePlayer27i1 2931
  let gBase := addPermanent (insertObject g3 bear p1 (.hand p1)) bear p0 p0
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- Synthetic state where `p1` has `leftTheGame == true` (while `lost == false`):
  let gLeft0 :=
    gBase.record (GameEvent.playerLeftGame gBase.turnNumber p1 (cause := some (.gameRule .playerLeftGame)))
  -- Record a spell proposal after `p1` left so `expandEachOpponentEffect` exercises its `some idx` branch:
  let gLeft :=
    gLeft0.record
      (GameEvent.proposed gLeft0.turnNumber p0BearId p0 (.hand p0) .normal)
  let sIdx := gLeft.events.size

  -- 1a. `Targeting.expandEachOpponentEffect` skips `p1` (`!g.stillInGame p1`) and includes only `p2`:
  let effOpp : Effect := {
    targeting := .of (.forEachOpponentControlled (.hasType .creature) (.exact 1))
    body := Instruction.dealDamageFixed (.targetSlot 0) 2
  }
  let expandedEff := gLeft.expandEachOpponentEffect p0 effOpp (some p0BearId)
  let expandOppOk := expandedEff.maxTargets == 1

  -- 1b. `Triggers.putTriggeredAbilityOnStack` and `ResolutionEffects` (`queueFollowupReflexive`,
  --     `putReflexiveTrigger`, `beginMayCastFromLooked`) are no-ops when `!g.stillInGame p1`:
  let gTrigStack :=
    gLeft.putTriggeredAbilityOnStack p1 (gLeft.object! p0BearId)
      (TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }) "enters"
  let gQueueRefl := gLeft.queueFollowupReflexive p1 (some p0BearId) (.gainLife 1)
  let gPutRefl := gLeft.putReflexiveTrigger p1 (some p0BearId) { body := Instruction.gainLifeFixed 1 }
  let gLookCast := gLeft.beginMayCastFromLooked p1 6 5

  -- 1c. `SacrificeDiscard` (`finishConniveDraws`, `applyConnive`), `Choices` (`beholdQuality`,
  --     `drawPerSevenCardGraveyard`, `mayDiscardHandDrawThatMany`, `discardHandThenDraw`,
  --     `exileTopPlayIfYouControlSubtypeLoop`, `finishGrimaDirectCast`, `exileUntilInstantOrSorceryLoop`,
  --     `grimaExileUntilInstantOrSorcery`), `LibrarySearch.resolveExileTopPlayUntilEndOfNextTurn`,
  --     and `Decisions.runPostStep` `.grantPlayUntilEndOfNextTurn`:
  let gFinConnive := gLeft.finishConniveDraws p1 #[] none
  let gAppConnive := gLeft.applyConnive p1 (some p0BearId)
  let gBehold := gLeft.beholdQuality p1 .bear
  let gDraw7 := gLeft.drawPerSevenCardGraveyard p1
  let gMayWheel := gLeft.mayDiscardHandDrawThatMany p1 true
  let gWheel := gLeft.discardHandThenDraw p1 3
  let gExSubLoop := gLeft.exileTopPlayIfYouControlSubtypeLoop p1 .bear 2 none
  let gFinGrima := gLeft.finishGrimaDirectCast p1 p1 p0BearId #[p0BearId] none
  let gExLoop := gLeft.exileUntilInstantOrSorceryLoop p1 (.directCastOrBottom p0 false) none #[p0BearId]
  let gGrimaEntry := gLeft.grimaExileUntilInstantOrSorcery p0 p1 false
  let gExPlayNext := gLeft.resolveExileTopPlayUntilEndOfNextTurn p1
  let gGrantPost := gLeft.runPostStep (.grantPlayUntilEndOfNextTurn p1 p0BearId none)

  -- Also verify `exileUntilInstantOrSorceryLoop` with `.impulseState` when `victim` (`p1`) left
  -- after a replacement pause: it skips the `while` loop (`p1`'s library is untouched) and still
  -- finishes `.impulseState` (`grimaImpulseReady == true`):
  let gExImpulse := gLeft.exileUntilInstantOrSorceryLoop p1 .impulseState none #[]

  let allDepartedNoOpsOk :=
    expandOppOk &&
    #[gTrigStack, gQueueRefl, gPutRefl, gLookCast, gFinConnive, gAppConnive,
      gBehold, gDraw7, gMayWheel, gWheel, gExSubLoop, gFinGrima, gExLoop,
      gGrimaEntry, gExPlayNext, gGrantPost].all (fun g => g.events.size == sIdx) &&
    gExImpulse.grimaImpulseReady &&
    (gExImpulse.player p1).library.size == (gLeft.player p1).library.size

  mustHold29i3 "1.allDepartedNoOpsOk" allDepartedNoOpsOk &&
  mustHold29i3 "1.replay" (replayOk29i3 #[gLeft, gExImpulse])

end Phase29Item3EventAlignment

/-! ### Phase 29 Item 4: CR 608.2h `sourcePTAtResolution` LKI fallback and remaining
Layer 1 `g.name` / `g.isCreature` / `g.isInstantOrSorcery` / `!g.isLand` / `g.objectManaValue` reads -/
section Phase29Item4EventAlignment

private def mustHold29i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase29Item4EventAlignment failed: {label}"

private def replayOk29i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

-- 1. `ResolutionEffects.sourcePTAtResolution` falls back to `lastKnownPowerOf?` /
--    `lastKnownToughnessOf?` and `snapshotPower` / `snapshotToughness` (CR 608.2h), and
--    `Decisions`, `Triggers`, `ResolutionEffects`, `Casting`, `FraChoices`, `Movement`, and
--    `TriggeredAbilities` read Layer 1–6 characteristics (`g.name`, `g.isCreature`,
--    `g.isInstantOrSorcery`, `!g.isLand`, `g.objectManaValue`, CR 613.1a,d,f).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- 1a. `sourcePTAtResolution` LKI fallback when `p0BearId` had two +1/+1 counters (4/4) before
  --     leaving the battlefield to `.graveyard p0` (`newGyId`, printed 2/2):
  let (gDeparted, newGyId) :=
    (gBase.recordPutCounters p0BearId .plusOnePlusOne 2 (byPlayer := some p0) (cause := some testCause)).move
      p0BearId (.graveyard p0) none (cause := some testCause)
  let ptLki := gDeparted.sourcePTAtResolution (some p0BearId)
  let ptSnap := gDeparted.sourcePTAtResolution (some newGyId)
  let ptNone := gDeparted.sourcePTAtResolution none
  let sourcePTLkiOk :=
    ptLki == (4, 4) &&
    ptSnap == (2, 2) &&
    ptNone == (0, 0)

  -- 1b. Layer 1 `g.name` reads when a continuous copy effect renames an object:
  let renamedDef : CardDef := {
    name := "P29i4 Layer1 Renamed Card"
    manaCost := ⟨#[.generic 2]⟩
    types := #[.creature]
    power := some 3, toughness := some 3
  }
  let gRenamed :=
    gBase.createEffect
      (.layered (.objects #[p0BearId]) (.copy renamedDef) .indefinite)
      (cause := some testCause)
  -- `withSourceOnBattlefield`, `incrementPlanSource`, and `sacrificePlanIfOnBattlefield`
  -- log `g.name o` when `o` is no longer on the battlefield (`o` moved to `.exile`, with Layer 1 copy effect on `exId`):
  let (gEx0, exId) := gBase.move p0BearId .exile none (cause := some testCause)
  let gExRenamed :=
    gEx0.createEffect
      (.layered (.objects #[exId]) (.copy renamedDef) .indefinite)
      (cause := some testCause)
  let gWithSrcLog := gExRenamed.withSourceOnBattlefield (some exId) (fun g _ => g)
  let gIncPlanLog := gExRenamed.incrementPlanSource p0 (some exId)
  let gSacPlanLog := gExRenamed.sacrificePlanIfOnBattlefield (some exId)
  let layer1ResolutionNameLogsOk :=
    gRenamed.name (gRenamed.object! p0BearId) == renamedDef.name &&
    gWithSrcLog.log.back? == some s!"{renamedDef.name} is no longer on the battlefield" &&
    gIncPlanLog.log.back? == some s!"{renamedDef.name} is no longer on the battlefield" &&
    gSacPlanLog.log.back? == some s!"{renamedDef.name} is no longer on the battlefield"

  -- 1c. `TriggeredAbilities.revealLibrary` `.untilCreature` / `.revealedManaValueAtMostLands`
  --     uses `g.isCreature o` and `g.objectManaValue o` (Layer 1 copy effect turning a 0-MV
  --     artifact in `.library p0` into a 2-MV creature):
  let relic0Def : CardDef := { name := "P29i4 Relic", types := #[.artifact] }
  let gLib0 := insertObject gBase relic0Def p0 (.library p0)
  let topRelicId := (gLib0.player p0).library.back!
  let gLibCopiedAsCreature :=
    gLib0.createEffect
      (.layered (.objects #[topRelicId]) (.copy renamedDef) .indefinite)
      (cause := some testCause)
  -- `p0` controls 0 lands (`landsYouControl p0 == 0`), while `g.objectManaValue` of the Layer 1
  -- copy is `2` (`> 0`), so `.untilCreature` finds `topRelicId` via `g.isCreature` and puts it into
  -- `p0`'s hand (rather than onto the battlefield as a 0-MV card):
  let gAfterRevealUntilCreature :=
    match gLibCopiedAsCreature.applyRevealLibrary p0 (some p0BearId) #[]
      .untilCreature
      (.ifElse .revealedManaValueAtMostLands (.put .revealed .asPrinted .none) (.returnToHand .revealed .none))
      .you with
    | some g' => g'
    | none => panic! "expected applyRevealLibrary some"
  let layer1RevealLibraryOk :=
    (gAfterRevealUntilCreature.followMovedToZone? topRelicId (· == .hand p0)).isSome

  mustHold29i4 "1a.sourcePTLkiOk" sourcePTLkiOk &&
  mustHold29i4 "1b.layer1ResolutionNameLogsOk" layer1ResolutionNameLogsOk &&
  mustHold29i4 "1c.layer1RevealLibraryOk" layer1RevealLibraryOk &&
  mustHold29i4 "1.replay"
    (replayOk29i4 #[gDeparted, gRenamed, gExRenamed, gWithSrcLog, gIncPlanLog, gSacPlanLog, gAfterRevealUntilCreature])

end Phase29Item4EventAlignment

/-! ### Phase 30 Item 1: `Leaving.redirectPendingAfterLeave` and `Decisions.resumePendingReplacement` `.restorePending` revalidation -/
section Phase30Item1EventAlignment

private def mustHold30i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase30Item1EventAlignment failed: {label}"

private def replayOk30i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g3 := mkThreePlayer27i1 3011
  let gBase := addPermanent (addPermanent g3 bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1BearId := (gBase.permanentsOf p1).find? (·.name == bear.name) |>.get!.id

  -- 1a. `.chooseSacrificeCreature q chosen remaining`: when `p1` leaves while `p0` (`q != leaver`)
  --     has no sacrificeable creatures (`gNoP0Bear`), `redirectPendingAfterLeave` filters `p1` from
  --     `remaining` and finishes the batch via `finishChosenSacrifices`!
  let (gNoP0Bear, _) := gBase.move p0BearId (.graveyard p0) none (cause := some testCause)
  let gPendChooseSac :=
    gNoP0Bear.changes #[
      .pushContinuationFrame {},
      .pending (.chooseSacrificeCreature p0 #[] #[p1])]
  let gAfterChooseSacLeave := gPendChooseSac.concede p1
  let chooseSacNonLeaverOk :=
    gAfterChooseSacLeave.pending != Pending.chooseSacrificeCreature p0 #[] #[] &&
    gAfterChooseSacLeave.continuations.isEmpty

  -- 1b. `.fraChoice p0 (.sacrificeCreatureEach p0 #[p1] #[])` and `.sacrificeNontokenEach #[p1] #[]`:
  --     when `p1` leaves while `p0` (`q != leaver`) has no sacrificeable creatures (`gNoP0Bear`),
  --     `redirectPendingAfterLeave` filters `p1` from `rest` and runs `finishChosenSacrifices`:
  let gPendSacEach :=
    gNoP0Bear.beginFraChoice p0 (.sacrificeCreatureEach p0 #[p1] #[])
  let gAfterSacEachLeave := gPendSacEach.concede p1
  let gPendSacNontoken :=
    gNoP0Bear.beginFraChoice p0 (.sacrificeNontokenEach #[p1] #[])
  let gAfterSacNontokenLeave := gPendSacNontoken.concede p1
  let sacEachNonLeaverOk :=
    gAfterSacEachLeave.pending != Pending.fraChoice p0 (.sacrificeCreatureEach p0 #[] #[]) &&
    gAfterSacEachLeave.continuations.isEmpty &&
    gAfterSacNontokenLeave.pending != Pending.fraChoice p0 (.sacrificeNontokenEach #[] #[]) &&
    gAfterSacNontokenLeave.continuations.isEmpty

  -- 1c. `.fraChoice p0 (.sacrificeDamager #[p1BearId] #[] p0 #[])` and
  --     `.fraChoice p0 (.tricksterLibrary p0 p1BearId none)`:
  --     when `p1` leaves and `p1BearId` leaves the battlefield with `p1`, `redirectPendingAfterLeave`
  --     finishes the stale `fraChoice` for `p0`:
  let gPendDamager := gBase.beginFraChoice p0 (.sacrificeDamager #[p1BearId] #[] p0 #[])
  let gAfterDamagerLeave := gPendDamager.concede p1
  let gPendTrickster := gBase.beginFraChoice p0 (.tricksterLibrary p0 p1BearId none)
  let gAfterTricksterLeave := gPendTrickster.concede p1
  let damagerAndTricksterLeaveOk :=
    gAfterDamagerLeave.pending != Pending.fraChoice p0 (.sacrificeDamager #[] #[] p0 #[]) &&
    gAfterDamagerLeave.continuations.isEmpty &&
    gAfterTricksterLeave.pending != Pending.fraChoice p0 (.tricksterLibrary p0 p1BearId none) &&
    gAfterTricksterLeave.continuations.isEmpty

  -- 1d. `.fraChoice p0 (.sacrificeLeastPower #[p0BearId, p1BearId])`: when `p1` (`q != leaver`)
  --     leaves and only `p0BearId` remains tied for least power under `p0`'s control
  --     (`liveTied.size <= 1`), `redirectPendingAfterLeave` delegates to
  --     `sacrificeLeastPowerCreature p0` via `clearPending` inside `withOuterContStashed`,
  --     sacrificing `p0BearId` without journaling `.chooseModesRest none`:
  let gPendLeastPower := gBase.beginFraChoice p0 (.sacrificeLeastPower #[p0BearId, p1BearId])
  let gAfterLeastPowerLeave := gPendLeastPower.concede p1
  let leastPowerLeaveOk :=
    (gAfterLeastPowerLeave.followMovedToZone? p0BearId (· == .graveyard p0)).isSome &&
    !gAfterLeastPowerLeave.events.any (fun e => e.change == .engine (.chooseModesRest none)) &&
    gAfterLeastPowerLeave.continuations.isEmpty

  -- 1e. `.fraChoice p0 (.hydeRemoveCounter #[p0BearId, p1BearId])`: when `p1` (`q != leaver`)
  --     leaves while `p0BearId` has a `+1/+1` counter (`live.size == 1 <= 1`),
  --     `redirectPendingAfterLeave` runs `(clearPending g).applyHydeMode p0 none 1 #[Target.permanent p0BearId]`
  --     inside `withOuterContStashed` (removing the `+1/+1` counter from `p0BearId` without
  --     journaling `.chooseModesRest none`):
  let gWithCounter := gBase.addPlusOnePlusOneTo (gBase.object! p0BearId) 1 (cause := some testCause)
  let gPendHyde := gWithCounter.beginFraChoice p0 (.hydeRemoveCounter #[p0BearId, p1BearId])
  let gAfterHydeLeave := gPendHyde.concede p1
  let hydeLeaveOk :=
    (gAfterHydeLeave.object! p0BearId).status.plusOnePlusOne == 0 &&
    !gAfterHydeLeave.events.any (fun e => e.change == .engine (.chooseModesRest none)) &&
    gAfterHydeLeave.continuations.isEmpty

  -- 1f. `.sacrificeCreature p0`: when `p1` leaves while `p0` (`q != leaver`) has no remaining
  --     creatures (`gNoP0Bear`), `redirectPendingAfterLeave` advances priority instead of stranding
  --     `.sacrificeCreature p0`:
  let gPendSacCreature := gNoP0Bear.change (.pending (.sacrificeCreature p0))
  let gAfterSacCreatureLeave := gPendSacCreature.concede p1
  let sacCreatureNonLeaverOk :=
    gAfterSacCreatureLeave.pending != Pending.sacrificeCreature p0

  -- 1g. `Decisions.resumePendingReplacement` `.restorePending` for `.assignCombatDamage p0 true`
  --     (when no combat damage assignment is needed) and
  --     `.fraChoice p0 (.tricksterLibrary p0 p1BearId none)` (when `p1BearId` left the battlefield):
  let (gBlockersGone, _) := gBase.move p1BearId (.graveyard p1) none (cause := some testCause)
  let gRestoreCombat :=
    gBlockersGone.resumePendingReplacement (.restorePending (.assignCombatDamage p0 true) false)
  let gRestoreTrickster :=
    gBlockersGone.resumePendingReplacement
      (.restorePending (.fraChoice p0 (.tricksterLibrary p0 p1BearId none)) false)
  let restorePendingOk :=
    gRestoreCombat.pending != Pending.assignCombatDamage p0 true &&
    gRestoreTrickster.pending != Pending.fraChoice p0 (.tricksterLibrary p0 p1BearId none) &&
    gRestoreTrickster.log.back? == some "The target is no longer legal"

  mustHold30i1 "1a.chooseSacNonLeaverOk" chooseSacNonLeaverOk &&
  mustHold30i1 "1b.sacEachNonLeaverOk" sacEachNonLeaverOk &&
  mustHold30i1 "1c.damagerAndTricksterLeaveOk" damagerAndTricksterLeaveOk &&
  mustHold30i1 "1d.leastPowerLeaveOk" leastPowerLeaveOk &&
  mustHold30i1 "1e.hydeLeaveOk" hydeLeaveOk &&
  mustHold30i1 "1f.sacCreatureNonLeaverOk" sacCreatureNonLeaverOk &&
  mustHold30i1 "1g.restorePendingOk" restorePendingOk &&
  mustHold30i1 "1.replay"
    (replayOk30i1 #[gAfterChooseSacLeave, gAfterSacEachLeave, gAfterSacNontokenLeave,
      gAfterDamagerLeave, gAfterTricksterLeave, gAfterLeastPowerLeave, gAfterHydeLeave,
      gAfterSacCreatureLeave, gRestoreCombat, gRestoreTrickster])

end Phase30Item1EventAlignment

/-! ### Phase 30 Item 2: `Core.beginFraChoice` frame-push invariant across all `.fraChoice` writers -/
section Phase30Item2EventAlignment

private def mustHold30i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase30Item2EventAlignment failed: {label}"

private def replayOk30i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- 1a. `g.beginFraChoice p choice` (default `msg := ""`) pushes a continuation frame when
  --     `g.continuations.isEmpty` and does not log an empty message:
  let logSize0 := gBase.log.size
  let gSilentChoice := gBase.beginFraChoice p0 (.hydeRemoveCounter #[p0BearId])
  let gSilentFinished := (gSilentChoice.change (.pending .none)).finishFraChoice
  let silentBeginFraChoiceOk :=
    gBase.continuations.isEmpty &&
    gSilentChoice.continuations.size == 1 &&
    gSilentChoice.log.size == logSize0 &&
    gSilentChoice.pending == Pending.fraChoice p0 (.hydeRemoveCounter #[p0BearId]) &&
    gSilentFinished.continuations.isEmpty &&
    gSilentFinished.pending == .none

  -- 1b. Direct calls to `ResolutionCompat.beginVisionQuest` and `ResolutionCompat.offerBottomAnyOrder`
  --     when `g.continuations.isEmpty` push a frame via `beginFraChoice`:
  let gLib2 := insertObject (insertObject gBase bear p0 (.library p0)) bear p0 (.library p0)
  let topTwo := (gLib2.player p0).library.extract ((gLib2.player p0).library.size - 2) (gLib2.player p0).library.size
  let gBottomChoice := gLib2.offerBottomAnyOrder p0 topTwo
  let directWritersPushFrameOk :=
    gBottomChoice.continuations.size == 1 &&
    gBottomChoice.pending == Pending.fraChoice p0 (.orderLibraryBottom topTwo)

  mustHold30i2 "1a.silentBeginFraChoiceOk" silentBeginFraChoiceOk &&
  mustHold30i2 "1b.directWritersPushFrameOk" directWritersPushFrameOk &&
  mustHold30i2 "1.replay"
    (replayOk30i2 #[gSilentChoice, gSilentFinished, gLib2, gBottomChoice])

end Phase30Item2EventAlignment

/-! ### Phase 30 Item 3: Unified `stillInGame` checks and departed-player guards -/
section Phase30Item3EventAlignment

private def mustHold30i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase30Item3EventAlignment failed: {label}"

private def replayOk30i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let gLeft := gBase.playerLeavesGame p1
  let sIdx := gLeft.events.size

  -- 1. All departed-player entrypoints / loops / PostSteps return `gLeft` without emitting new events:
  let gCascadeLoop := gLeft.resolveCascadeLoop p1 3 testCause #[] none
  let gCascade := gLeft.resolveCascade p1 3
  let gMayCastLooked := gLeft.beginMayCastFromLooked p1 3 3
  let gMill := gLeft.mill p1 2
  let gMillLoop := gLeft.millCardsLoop p1 #[] (freshCount := some 2)
  let gMovePubHand := gLeft.movePublicCardsToHandLoop p1 #[p0BearId] 1 true none
  let gMoveOrder := gLeft.moveIdsInOrderLoop #[p0BearId] (.library p1) "ordered"
  let gReqOrder := gLeft.requestOrderInto #[p0BearId] (.library p1) "ordered"
  let gWidowCast := gLeft.grantWidowCast p1 (some p0BearId)
  let gFinWidow := gLeft.finishExileLibraryUntilNonland p1 (some p0BearId) (some p0BearId) none
  let gPostNick := gLeft.runPostStep (.nickFuryMayTransformOrBottom p1 p0BearId #[] none)
  let gPostOppDraw := gLeft.runPostStep (.opponentsDrawOneLoop p1 #[p1] none)
  let gPostLoseMill := gLeft.runPostStep (.loseLifeForMilledManaValue p1 #[p0BearId] none)
  let gPostShuffle := gLeft.runPostStep (.logShuffleIntoLibrary p1 p0BearId)
  let gPostPutMill := gLeft.runPostStep (.offerPutMilledPermanentOrGainLife p1 #[p0BearId] 3)

  -- 2. Verify pending-arrival logs in `millCardsLoop`, `movePublicCardsToHandLoop`, and
  --    `.logShuffleIntoLibrary` still emit when the card already arrived before `p1` left,
  --    then return before further departed-player actions:
  let gMillWithLog := gLeft.millCardsLoop p1 #[p0BearId] (logCard := some bear.name)
  let gMovedToP1Hand := (gBase.move p0BearId (.hand p1) none (cause := some testCause)).1.playerLeavesGame p1
  let sIdxHand := gMovedToP1Hand.events.size
  let gMovePubWithPending :=
    gMovedToP1Hand.movePublicCardsToHandLoop p1 #[p0BearId] 1 true none
      (pendingCard := some (p0BearId, bear.name))
  let gMovedToP1Lib := (gBase.move p0BearId (.library p1) none (cause := some testCause)).1.playerLeavesGame p1
  let sIdxLib := gMovedToP1Lib.events.size
  let gPostShuffleArrived := gMovedToP1Lib.runPostStep (.logShuffleIntoLibrary p1 p0BearId)
  let pendingArrivalLogsOk :=
    gMillWithLog.log.back? == some s!"{(gLeft.player p1).name} mills {bear.name}" &&
    gMillWithLog.events.size == sIdx + 1 &&
    gMovePubWithPending.log.back? == some s!"{(gLeft.player p1).name} puts {bear.name} into their hand" &&
    gMovePubWithPending.events.size == sIdxHand + 1 &&
    gPostShuffleArrived.log.back? == some s!"{(gLeft.player p1).name} shuffles {bear.name} into their library" &&
    gPostShuffleArrived.events.size == sIdxLib + 1 &&
    gPostShuffleArrived.pending == .none

  -- 3. Also verify `.grantAdventureExilePermission` when `controller` (`p1`) has left the game:
  --    logs `"{name} is exiled"` without creating a `.playPermission` effect for `p1`:
  let (gExBear, exBearId) := gLeft.move p0BearId .exile none (cause := some testCause)
  let effCountBefore := gExBear.activeEffects.size
  let gAdvGone := gExBear.runPostStep (.grantAdventureExilePermission p1 p0BearId (some testCause))
  let advGoneOk :=
    gAdvGone.activeEffects.size == effCountBefore &&
    gAdvGone.log.back? == some s!"{gExBear.name (gExBear.object! exBearId)} is exiled"

  let departedGuardsOk :=
    #[gCascadeLoop, gCascade, gMayCastLooked, gMill, gMillLoop, gMovePubHand,
      gMoveOrder, gReqOrder, gWidowCast, gFinWidow, gPostNick, gPostOppDraw,
      gPostLoseMill, gPostShuffle, gPostPutMill].all (fun g => g.events.size == sIdx) &&
    pendingArrivalLogsOk &&
    advGoneOk

  mustHold30i3 "1.departedGuardsOk" departedGuardsOk &&
  mustHold30i3 "1.replay"
    (replayOk30i3 #[gLeft, gMillWithLog, gMovedToP1Hand, gMovePubWithPending,
      gMovedToP1Lib, gPostShuffleArrived, gExBear, gAdvGone])

end Phase30Item3EventAlignment

/-! ### Phase 30 Item 4: Single `Core.snapshot` constructor and Layer 1–6 characteristic reads -/
section Phase30Item4EventAlignment

private def mustHold30i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase30Item4EventAlignment failed: {label}"

private def replayOk30i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let gBase := addPermanent afterDraw bear p0 p0
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id

  -- 1a. `ActivationCosts.costPickAllows` `.discardLegendaryCard` and `.discardLegendarySameName`
  --     use `g.isLegendary` and `g.name`:
  let legBearDef : CardDef := {
    bear with
    name := "P30i4 Legendary Bear"
    supertypes := #[.legendary]
  }
  let gWithHandBear := insertObject gBase bear p0 (.hand p0)
  let handBearId := (gWithHandBear.player p0).hand.back!
  let gCopiedLeg :=
    (gWithHandBear.createEffect
      (.layered (.objects #[p0BearId]) (.copy legBearDef) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[handBearId]) (.copy legBearDef) .indefinite)
      (cause := some testCause)
  let handObj := gCopiedLeg.object! handBearId
  let costPickLayerOk :=
    gCopiedLeg.costPickAllows p0 none .discardLegendaryCard handObj &&
    gCopiedLeg.costPickAllows p0 none .discardLegendarySameName handObj

  -- 1b. `Costs.returnToHand`, `ResolutionEffects.revealHand`, and `Decisions` `.logMovedToExile`
  --     log `g.name` (Layer 1 copy name):
  let gRevealed := gCopiedLeg.revealHand p0
  let gReturned := gCopiedLeg.returnToHand p0BearId p0 (cause := some testCause)
  let (gMovedEx, _) := gCopiedLeg.move p0BearId .exile none (cause := some testCause)
  let exId := (gMovedEx.followMovedToZone? p0BearId (· == .exile)).get!.id
  let gExCopied :=
    gMovedEx.createEffect
      (.layered (.objects #[exId]) (.copy legBearDef) .indefinite)
      (cause := some testCause)
  let gLogMovedEx := gExCopied.runPostStep (.logMovedToExile p0BearId)
  let layer1NamesOk :=
    (gRevealed.log.back?.getD "").endsWith s!"{legBearDef.name})" &&
    gReturned.log.back? == some s!"{legBearDef.name} is returned to {(gReturned.player p0).name}'s hand" &&
    gLogMovedEx.log.back? == some s!"{legBearDef.name} is exiled"

  mustHold30i4 "1a.costPickLayerOk" costPickLayerOk &&
  mustHold30i4 "1b.layer1NamesOk" layer1NamesOk &&
  mustHold30i4 "1.replay"
    (replayOk30i4 #[gCopiedLeg, gRevealed, gReturned, gMovedEx, gExCopied, gLogMovedEx])

end Phase30Item4EventAlignment

/-! ### Phase 31 Item 1: `redirectPendingAfterLeave` `q != p` revalidation, `mayThenDrop > 0` `declineMayThenCore` cleanup, and `resumePendingReplacement` `.restorePending` (`departed`) revalidation -/
section Phase31Item1EventAlignment

private def mustHold31i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase31Item1EventAlignment failed: {label}"

private def replayOk31i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent g3 bear p0 p0) bear p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1BearId := (gBase.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let gNoP0Bear := addPermanent g3 bear p1 p1
  let eqDef : CardDef := { name := "P31 Spear", manaCost := ManaCost.empty, types := #[.artifact], subtypes := #["Equipment"] }
  let gWithEq := addPermanent gBase eqDef p0 p0
  let eqId := (gWithEq.permanentsOf p0).find? (·.name == "P31 Spear") |>.get!.id

  -- 1a. `redirectPendingAfterLeave` (`q != p`) on `.sacrificeCreature p0`, `.chooseLegend p0`,
  --     `.mayAttachEquipment p0`, `.maySacrificeAnotherBolg p0`, and `.chooseLibraryPlacement p0`:
  let gP0ControlsP1Bear := gNoP0Bear.giveControlUntilEot (gNoP0Bear.object! ((gNoP0Bear.permanentsOf p1)[0]!.id)) p0
  let gPendSacCr := gP0ControlsP1Bear.change (.pending (.sacrificeCreature p0))
  let gAfterSacCr := gPendSacCr.concede p1
  let gPendLegend :=
    (gBase.giveControlUntilEot (gBase.object! p1BearId) p0).change
      (.pending (.chooseLegend p0 bear.name #[p0BearId, p1BearId]))
  let gAfterLegend := gPendLegend.concede p1
  let gPendMayAttachEq := gWithEq.change (.pending (.mayAttachEquipment p0 p1BearId (some eqId)))
  let gAfterMayAttachEq := gPendMayAttachEq.concede p1
  let gPendMayBolg := gP0ControlsP1Bear.change (.pending (.maySacrificeAnotherBolg p0 p0BearId))
  let gAfterMayBolg := gPendMayBolg.concede p1
  let gPendLibPlace :=
    (gBase.change (.pushContinuationFrame { spellOrLibrary := true })).change
      (.pending (.chooseLibraryPlacement p0 (some p1BearId)))
  let gAfterLibPlace := gPendLibPlace.concede p1

  let nonFraLeaveRevalOk :=
    gAfterSacCr.pending != Pending.sacrificeCreature p0 &&
    gAfterLegend.pending != Pending.chooseLegend p0 bear.name #[p0BearId, p1BearId] &&
    gAfterMayAttachEq.pending != Pending.mayAttachEquipment p0 p1BearId (some eqId) &&
    gAfterMayBolg.pending != Pending.maySacrificeAnotherBolg p0 p0BearId &&
    gAfterLibPlace.pending != Pending.chooseLibraryPlacement p0 (some p1BearId)

  -- 1b. `redirectPendingAfterLeave` (`q != p`) on `.fraChoice p0`:
  --     `.chooseCards (.amassArmy ...)`, `.attachAnyEquipment`, `.maySacrificeAnotherCreatureForPower`,
  --     `.maySacrificeAnotherForDrawTreasure`, `.maySacrificeThese`, `.sheHulkMayDamage`,
  --     `.widowMayCounter`, and `.sacrificeLeastPower`:
  let armyDef : CardDef := { bear with name := "P31 Army", subtypes := #["Orc", "Army"] }
  let gTwoArmies :=
    let g := addPermanent (addPermanent g3 armyDef p0 p0) armyDef p1 p1
    let p1Army := (g.permanentsOf p1).find? (·.name == "P31 Army") |>.get!
    g.giveControlUntilEot p1Army p0
  let p0ArmyId := (gTwoArmies.battlefield.filter (fun o => o.owner == p0 && o.name == "P31 Army"))[0]!.id
  let p1ArmyId := (gTwoArmies.battlefield.filter (fun o => o.owner == p1 && o.name == "P31 Army"))[0]!.id
  let gPendAmass :=
    (gTwoArmies.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.chooseCards #[p0ArmyId, p1ArmyId] 1 (.amassArmy .orc 2 none))))
  let gAfterAmassLeave := gPendAmass.concede p1
  let gPendAttachAny :=
    (gWithEq.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.attachAnyEquipment p1BearId #[eqId])))
  let gAfterAttachAnyLeave := gPendAttachAny.concede p1
  let gPendSacPow :=
    (gP0ControlsP1Bear.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.maySacrificeAnotherCreatureForPower p1BearId)))
  let gAfterSacPowLeave := gPendSacPow.concede p1
  let gPendSacDraw :=
    (gP0ControlsP1Bear.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.maySacrificeAnotherForDrawTreasure p1BearId)))
  let gAfterSacDrawLeave := gPendSacDraw.concede p1
  let gPendSacThese :=
    (gP0ControlsP1Bear.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.maySacrificeThese 1 #[p1BearId])))
  let gAfterSacTheseLeave := gPendSacThese.concede p1
  let gPendSheHulk :=
    (gBase.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.sheHulkMayDamage 2 (.permanent p1BearId) (some p0BearId))))
  let gAfterSheHulkLeave := gPendSheHulk.concede p1
  let gPendWidow :=
    (gBase.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.widowMayCounter (some p1BearId) none)))
  let gAfterWidowLeave := gPendWidow.concede p1
  let gPendLeastPow :=
    (gBase.giveControlUntilEot (gBase.object! p1BearId) p0).change
      (.pending (.fraChoice p0 (.sacrificeLeastPower #[p0BearId, p1BearId])))
  let gAfterLeastPowLeave := gPendLeastPow.concede p1

  let fraChoiceLeaveRevalOk :=
    (gAfterAmassLeave.object! p0ArmyId).status.plusOnePlusOne == 2 &&
    gAfterAttachAnyLeave.pending != Pending.fraChoice p0 (.attachAnyEquipment p1BearId #[eqId]) &&
    gAfterSacPowLeave.pending != Pending.fraChoice p0 (.maySacrificeAnotherCreatureForPower p1BearId) &&
    gAfterSacDrawLeave.pending != Pending.fraChoice p0 (.maySacrificeAnotherForDrawTreasure p1BearId) &&
    gAfterSacTheseLeave.pending != Pending.fraChoice p0 (.maySacrificeThese 1 #[p1BearId]) &&
    gAfterSheHulkLeave.pending != Pending.fraChoice p0 (.sheHulkMayDamage 2 (.permanent p1BearId) (some p0BearId)) &&
    gAfterWidowLeave.pending != Pending.fraChoice p0 (.widowMayCounter (some p1BearId) none) &&
    (gAfterLeastPowLeave.followMovedToZone? p0BearId (· == .graveyard p0)).isSome

  -- 1c. `mayThenDrop > 0` in `redirectPendingAfterLeave` calls `declineMayThenCore` cleanly
  --     when `p1` concedes during `.mayPutLandFromHand p1`:
  let gPendMayLand :=
    (gBase.change (.pushContinuationFrame {
      mayThenDrop := 1
      mayThenConditional := some (.draw (.fixed 1) .you)
    })).change (.pending (.mayPutLandFromHand p1))
  let gAfterMayLandLeave := gPendMayLand.concede p1
  let mayThenDropLeaveOk :=
    gAfterMayLandLeave.mayThenDrop == 0 &&
    gAfterMayLandLeave.mayThenConditional.isNone

  -- 1d. `Decisions.resumePendingReplacement` `.restorePending saved checkSBA promptLog departed`:
  --     revalidates `saved` after post-leave exile / SBA and routes `departed` through
  --     `redirectPendingAfterLeave`:
  let (gP1BearGone, _) := gBase.move p1BearId (.graveyard p1) none (cause := some testCause)
  let gRestoreLegend :=
    gP1BearGone.resumePendingReplacement
      (.restorePending (.chooseLegend p0 bear.name #[p0BearId, p1BearId]) false)
  let gLeftP1 := gBase.playerLeavesGame p1
  let gRestoreDeparted :=
    (gLeftP1.change (.pushContinuationFrame {
      mayThenDrop := 1
      mayThenConditional := some (.draw (.fixed 1) .you)
    })).resumePendingReplacement
      (.restorePending (.mayPutLandFromHand p1) false none #[p1])
  let restorePendingRevalOk :=
    gRestoreLegend.pending == .none &&
    gRestoreDeparted.mayThenDrop == 0 &&
    gRestoreDeparted.mayThenConditional.isNone &&
    gRestoreDeparted.pending == .none

  mustHold31i1 "1a.nonFraLeaveRevalOk" nonFraLeaveRevalOk &&
  mustHold31i1 "1b.fraChoiceLeaveRevalOk" fraChoiceLeaveRevalOk &&
  mustHold31i1 "1c.mayThenDropLeaveOk" mayThenDropLeaveOk &&
  mustHold31i1 "1d.restorePendingRevalOk" restorePendingRevalOk &&
  mustHold31i1 "1.replay"
    (replayOk31i1 #[gAfterSacCr, gAfterLegend, gAfterMayAttachEq, gAfterMayBolg,
      gAfterLibPlace, gAfterAmassLeave, gAfterAttachAnyLeave, gAfterSacPowLeave,
      gAfterSacDrawLeave, gAfterSacTheseLeave, gAfterSheHulkLeave, gAfterWidowLeave,
      gAfterLeastPowLeave, gAfterMayLandLeave, gRestoreLegend, gRestoreDeparted])

end Phase31Item1EventAlignment

/-! ### Phase 31 Item 2: `ContinuationFrame` entry and exit guards across Scry, Surveil, May, SpellOr, UnlessPays, Saga chapters, `Interpreter`, and `finishAndGrantPriority` -/
section Phase31Item2EventAlignment

private def mustHold31i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase31Item2EventAlignment failed: {label}"

private def replayOk31i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let gBase := insertObject (insertObject afterDraw bear p0 (.library p0)) bear p0 (.library p0)
  let topId := (gBase.player p0).library.back!

  -- 2a. Direct calls when `gBase.continuations.isEmpty`:
  --     `beginScry`, `scryThenDraw`, `beginSurveil`, `beginMay`, `beginSpellOr`, and `beginUnlessPays`
  --     each push a `ContinuationFrame` on entry (`continuations.size == 1`) and pop it on exit (`continuations.isEmpty`):
  let gScry0 := gBase.beginScry p0 1
  let gScry1 := mustApply gScry0 p0 (.scry #[topId] #[])
  let gScryDraw0 := gBase.scryThenDraw p0 1 1
  let gScryDraw1 := mustApply gScryDraw0 p0 (.scry #[topId] #[])
  let gSurv0 := gBase.beginSurveil p0 1
  let gSurv1 := mustApply gSurv0 p0 (.surveil #[topId] #[])
  let gMay0 := gBase.beginMay p0 default #[] (Instruction.drawFixed 1)
  let gMay1 := mustApply gMay0 p0 .decline
  let gOr0 := gBase.beginSpellOr p0 default #[] [Instruction.drawFixed 1, Instruction.gainLifeFixed 2]
  let gOr1 :=
    match gOr0.chooseSpellOr p0 1 with
    | .ok g => g
    | .error _ => gOr0
  let gUnless0 := gBase.beginUnlessPays p0 default #[Target.player p0] (Instruction.drawFixed 1) 1
  let gUnless1 := mustApply gUnless0 p0 .decline

  let directFramesOk :=
    gBase.continuations.isEmpty &&
    gScry0.continuations.size == 1 && gScry1.continuations.isEmpty &&
    gScryDraw0.continuations.size == 1 && gScryDraw1.continuations.isEmpty &&
    gSurv0.continuations.size == 1 && gSurv1.continuations.isEmpty &&
    gMay0.continuations.size == 1 && gMay1.continuations.isEmpty &&
    gOr0.continuations.size == 1 && gOr1.continuations.isEmpty &&
    gUnless0.continuations.size == 1 && gUnless1.continuations.isEmpty

  -- 2b. Direct calls to `applyAbilityEffect` (chapter mana, each-player damage, monarch token) when
  --     `gBase.continuations.isEmpty` wrap cleanly and leave no stray `ContinuationFrame` when finished:
  let gChap0 := gBase.applyAbilityEffect p0 (Effect.chapterAddMana (.colored .green)) #[] none
  let gFra0 := gBase.applyAbilityEffect p0 { body := Instruction.dealDamageFixed (.players .eachPlayer) 1 } #[] none
  let gFrc0 :=
    gBase.applyAbilityEffect p0
      { body := Instruction.ifThen (.playerPred .you .isMonarch) (Instruction.createTokensFixed .gingerbrute 1) } #[] none

  let entrypointsFramesOk :=
    gChap0.continuations.isEmpty &&
    gFra0.continuations.isEmpty && (gFra0.player p0).life == 19 &&
    gFrc0.continuations.isEmpty

  mustHold31i2 "2a.directFramesOk" directFramesOk &&
  mustHold31i2 "2b.entrypointsFramesOk" entrypointsFramesOk &&
  mustHold31i2 "2.replay"
    (replayOk31i2 #[gScry0, gScry1, gScryDraw0, gScryDraw1, gSurv0, gSurv1,
      gMay0, gMay1, gOr0, gOr1, gUnless0, gUnless1,
      gChap0, gFra0, gFrc0])

end Phase31Item2EventAlignment

/-! ### Phase 31 Item 3: Post-pause arrival logging order and departed-player `stillInGame` guards -/
section Phase31Item3EventAlignment

private def mustHold31i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase31Item3EventAlignment failed: {label}"

private def replayOk31i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) bear p1 p1
  let p0Hand0 := (gBase.player p0).hand[0]!
  let p0Hand1 := (gBase.player p0).hand[1]!

  -- 3a. `Library.moveIdsInOrderLoop` with `prevMoved := some (p0Hand0, .library p0)` counts `p0Hand0`
  --     when it arrived in `.library p0` and logs the arrival message after moving `p0Hand1`:
  let (gMoved0, _) := gBase.move p0Hand0 (.library p0) none (libraryPosition := some .bottom) (cause := some testCause)
  let gLoopDone :=
    gMoved0.runPostStep
      (.moveIdsInOrderLoop #[p0Hand1] (.library p0) "puts cards on bottom" (some testCause) 0 (some (p0Hand0, .library p0)))
  let moveOrderPrevOk :=
    gLoopDone.log.back? == some "puts cards on bottom" &&
    (gLoopDone.followMovedToZone? p0Hand1 (· == .library p0)).isSome

  -- 3b. Departed-player `stillInGame` guards across `Library`, `ResolutionEffects`,
  --     `Tokens`, `Interpreter`, `TriggeredAbilities`, and `Decisions`:
  let gLeft := gBase.playerLeavesGame p1
  let sIdx := gLeft.events.size
  let gReqShuf := gLeft.requestShuffle p1
  let gExTopPlay := gLeft.exileTopForPlay p1 p1 2 (fun o c => s!"{o} {c}") false
  let gEmpJace := gLeft.empowerJace p1 2
  let gHandDisc := gLeft.runFrcPostStep (.discardHand p1)
  let gHandBot := gLeft.runFrcPostStep (.handDiscardToBottom p1)
  let gFrcPutDrawn := gLeft.runFrcPostStep (.putDrawnBackOnTop p1 2)
  let gFrcPolyRev := gLeft.runFrcPostStep (.polymorphRevealCreatures p1 1 none #[])
  let gFrcPolySingle := gLeft.runFrcPostStep (.polymorphSingleTargetReveal p1 p0 none)
  let gFrcOptPoly := gLeft.runFrcPostStep (.optionalOncePolymorphReveal p1 none)
  let gFrcRevCr := gLeft.runFrcPostStep (.revealCreatureOrPlaneswalker p1 none)
  let gTrigExLoop := gLeft.runTriggerExileLoop p1 none .playThisTurn #[p0Hand0] #[] (some testCause)
  let gSurvLoop := gLeft.surveilMoveLoop p1 #[p0Hand0] none

  let departedStillInGameOk :=
    #[gReqShuf, gExTopPlay, gEmpJace, gHandDisc, gHandBot,
      gFrcPutDrawn, gFrcPolyRev, gFrcPolySingle, gFrcOptPoly,
      gFrcRevCr, gTrigExLoop, gSurvLoop].all (fun g => g.events.size == sIdx)

  mustHold31i3 "3a.moveOrderPrevOk" moveOrderPrevOk &&
  mustHold31i3 "3b.departedStillInGameOk" departedStillInGameOk &&
  mustHold31i3 "3.replay"
    (replayOk31i3 #[gMoved0, gLoopDone, gLeft])

end Phase31Item3EventAlignment

/-! ### Phase 31 Item 4: CR 608.2h `.equalSourceToughness` LKI propagation and Layer 1–6 characteristic reads -/
section Phase31Item4EventAlignment

private def mustHold31i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase31Item4EventAlignment failed: {label}"

private def replayOk31i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  -- 4a. CR 608.2h `.equalSourceToughness` LKI propagation:
  --     When a creature with toughness 5 leaves the battlefield before its trigger resolves,
  --     `applyGainLife` / `TriggerRead` uses `lastKnownToughness` (`wallSnap.toughness == some 5`)
  --     so `p0` gains 5 life!
  let wallDef : CardDef := {
    bear with
    name := "P31 Wall"
    power := some 1
    toughness := some 5
  }
  let gWall0 := addPermanent afterDraw wallDef p0 p0
  let wallObj := (gWall0.permanentsOf p0).find? (·.name == "P31 Wall") |>.get!
  let wallSnap := gWall0.snapshot wallObj
  let (gWallGone, _) := gWall0.move wallObj.id (.graveyard p0) none (cause := some testCause)
  let lifeBefore := (gWallGone.player p0).life
  let gWallResolved :=
    gWallGone.applyGainLife p0 default (some wallObj.id) #[] .equalSourceToughness none
      (lastKnownPower := wallSnap.power) (cause := some testCause)
      (lastKnownToughness := wallSnap.toughness)
  let lkiToughnessOk :=
    wallSnap.toughness == some 5 &&
    (gWallResolved.player p0).life == lifeBefore + 5

  -- 4b. Layer 1–4 graveyard queries (`gyCreatureCards`, `graveyardCardTypeCount`,
  --     `instantSorceryInGraveyard`, and `.fra .powerPerCreatureAndPlaneswalkerCard`):
  --     An artifact card in `p0`'s graveyard with an active Layer 1 `.copy` effect copying a creature
  --     or an instant is counted by `gyCreatureCards`, `graveyardCardTypeCount`,
  --     `instantSorceryInGraveyard`, and `.fra .powerPerCreatureAndPlaneswalkerCard`:
  let relicDef : CardDef := { name := "P31 Relic", manaCost := ManaCost.empty, types := #[.artifact] }
  let boltDef : CardDef := { name := "P31 Bolt", manaCost := ManaCost.empty, types := #[.instant] }
  let goyfDef : CardDef := {
    bear with
    name := "P31 Goyf"
    power := some 0
    toughness := some 1
    staticAbilities := #[.powerPerCreatureAndPlaneswalkerCard]
  }
  let gGy0 := insertObject (addPermanent afterDraw goyfDef p0 p0) relicDef p0 (.graveyard p0)
  let relicGyId := (gGy0.player p0).graveyard.back!
  let goyfId := (gGy0.permanentsOf p0).find? (·.name == "P31 Goyf") |>.get!.id
  let gGyAsCreature :=
    gGy0.createEffect (.layered (.objects #[relicGyId]) (.copy bear) .indefinite)
      (cause := some testCause)
  let gGyAsInstant :=
    gGy0.createEffect (.layered (.objects #[relicGyId]) (.copy boltDef) .indefinite)
      (cause := some testCause)
  let layeredGyReadsOk :=
    gGy0.gyCreatureCards p0 == 0 &&
    gGyAsCreature.gyCreatureCards p0 == 1 &&
    gGyAsCreature.power (gGyAsCreature.object! goyfId) == 1 &&
    gGy0.instantSorceryInGraveyard p0 == 0 &&
    gGyAsInstant.instantSorceryInGraveyard p0 == 1 &&
    gGyAsInstant.graveyardCardTypeCount == 1

  mustHold31i4 "4a.lkiToughnessOk" lkiToughnessOk &&
  mustHold31i4 "4b.layeredGyReadsOk" layeredGyReadsOk &&
  mustHold31i4 "4.replay"
    (replayOk31i4 #[gWallGone, gWallResolved, gGy0, gGyAsCreature, gGyAsInstant])

end Phase31Item4EventAlignment

/-! ### Phase 32 Item 1: `ContinuationFrame` exit cleanup and game-over resolution teardown -/
section Phase32Item1EventAlignment

private def mustHold32i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase32Item1EventAlignment failed: {label}"

private def replayOk32i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) hero p1 p1
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!

  -- 1a. `finishFraChoice` pops an empty `ContinuationFrame {}` pushed by `beginFraChoice`
  --     before `promptTriggerTargetsIfNeeded` opens `Pending.chooseTargets`:
  let gHkStack :=
    gBase.putReflexiveTrigger p0 (some p0Bear.id)
      { resolution? := some (.mshReflexive .trickArrows 1), phrase := "Choose up to 1 Trick Arrows mode" }
  let gHkChoseNet := mustApply gHkStack p0 (.chooseMode 0)
  let emptyFramePoppedBeforeTargetsOk :=
    gBase.continuations.isEmpty &&
    gHkStack.continuations.size == 1 &&
    (match gHkStack.pending with | .fraChoice q (.hawkeyeModes 1 #[] (some _)) => q == p0 | _ => false) &&
    gHkChoseNet.pending == .chooseTargets p0 &&
    gHkChoseNet.continuations.isEmpty

  -- 1b. `finishFraChoice` and `finishAndGrantPriority` tear down active resolving stack entries
  --     and pop all `ContinuationFrame`s when `g.over` becomes true during `drainPendingContinuations`:
  let simpleAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gWithAbOnStack := gBase.putTriggeredAbilityOnStack p0 p0Bear simpleAb "triggers" (eventCause := some testCause)
  let abObjId := gWithAbOnStack.stack.back!.objectId
  let abSnap := gWithAbOnStack.snapshot (gWithAbOnStack.object! abObjId)
  let gResolvingLethal :=
    (((gWithAbOnStack.loseLife p1 20 (cause := some testCause)).change
      (.pushContinuationFrame {
        resolutionFinish := some (.ability abObjId abSnap p0 (some p0Bear.id) none)
      })).change (.pushContinuationFrame {})).change (.pendingReplacement (some .checkSBA))
  let gFraGameOver := gResolvingLethal.finishFraChoice
  let gPrioGameOver := gResolvingLethal.finishAndGrantPriority p0
  let gameOverTeardownOk :=
    gFraGameOver.over &&
    gFraGameOver.continuations.isEmpty &&
    gFraGameOver.stack.isEmpty &&
    (gFraGameOver.findObject? abObjId).isNone &&
    gPrioGameOver.over &&
    gPrioGameOver.continuations.isEmpty &&
    gPrioGameOver.stack.isEmpty &&
    (gPrioGameOver.findObject? abObjId).isNone

  -- 1c. `ResolutionCompat.finishChooseCards` `.landsTappedGainLife` and
  --     `Decisions.runPostStep` `.shuffleThenGainLife` pop their `ContinuationFrame` when
  --     `(g.player p0).library.size ≤ 1` and `g.continuations.isEmpty`:
  let gOneCardLib := gBase.mill p0 ((gBase.player p0).library.size - 1) (cause := some testCause)
  let gTwoCardWithForest := insertObject gOneCardLib forest p0 (.library p0)
  let forestId := (gTwoCardWithForest.player p0).library.back!
  let lifeBefore := (gTwoCardWithForest.player p0).life
  let gAfterLandsGain :=
    gTwoCardWithForest.finishChooseCards p0 #[forestId] (.landsTappedGainLife 3) (cause := some testCause)
  let gAfterShuffleGain :=
    gOneCardLib.runPostStep (.shuffleThenGainLife p0 4)
  let smallLibShuffleFrameOk :=
    (gOneCardLib.player p0).library.size == 1 &&
    gOneCardLib.continuations.isEmpty &&
    gAfterLandsGain.pending == .none &&
    gAfterLandsGain.afterRandom == .none &&
    gAfterLandsGain.continuations.isEmpty &&
    (gAfterLandsGain.player p0).life == lifeBefore + 3 &&
    (gAfterLandsGain.permanentsOf p0).any (fun o => o.name == forest.name && o.status.tapped) &&
    gAfterShuffleGain.pending == .none &&
    gAfterShuffleGain.afterRandom == .none &&
    gAfterShuffleGain.continuations.isEmpty &&
    (gAfterShuffleGain.player p0).life == (gOneCardLib.player p0).life + 4

  mustHold32i1 "1a.emptyFramePoppedBeforeTargetsOk" emptyFramePoppedBeforeTargetsOk &&
  mustHold32i1 "1b.gameOverTeardownOk" gameOverTeardownOk &&
  mustHold32i1 "1c.smallLibShuffleFrameOk" smallLibShuffleFrameOk &&
  mustHold32i1 "1.replay"
    (replayOk32i1 #[gHkStack, gHkChoseNet, gResolvingLethal, gFraGameOver, gPrioGameOver,
      gOneCardLib, gTwoCardWithForest, gAfterLandsGain, gAfterShuffleGain])

end Phase32Item1EventAlignment

/-! ### Phase 32 Item 2: Stack-placed modal trigger prompt revalidation and unified `.restorePending` departed-player revalidation -/
section Phase32Item2EventAlignment

private def mustHold32i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase32Item2EventAlignment failed: {label}"

private def replayOk32i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent g3 bear p0 p0) hero p1 p1
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!

  -- 2a. `.upToTriggerModes` revalidation on `q != p` and `q == p`:
  --     (i) Re-opens `.upToTriggerModes` when remaining choosable modes still exist;
  --     (ii) Finalizes `chosen == #[]` (recording `announced #[]` and `targetsAnnounced := true`)
  --          when no choosable mode remains after `p1` leaves;
  --     (iii) Finalizes non-empty `chosen == #[0]` when no further mode is choosable after `p1` leaves;
  --     (iv) Clears pending when `q == p` (`p0` concedes).
  let upToAb : TriggeredAbility := TriggeredAbility.mkTrigger .thisEnters Effect.enterChooseUpToXModes
  let xTwoSrc : GameObject := { p0Bear with chosenX := some 2 }
  let gUpToReopen0 := gBase.putTriggeredAbilityOnStack p0 xTwoSrc upToAb "enters" (eventCause := some testCause)
  let upToObjId1 := gUpToReopen0.stack.back!.objectId
  let gUpToReopen1 := gUpToReopen0.concede p1
  let gUpToLeaverConcede := gUpToReopen0.concede p0

  let tokenOnlyUpToAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters
      { Effect.enterChooseUpToXModes with
        body := .chooseModes {
          modes := #[
            { targeting := .of (.ofDomain (.object .battlefield (.isToken true)))
              body := Instruction.destroy (.target 0)
              phrase := "Destroy target token" }
          ] } }
  let tokenOnlyModesDef : CardDef := {
    bear with
    name := "P32 UpTo Token Modal"
    triggeredAbilities := #[tokenOnlyUpToAb]
  }
  let (gWithP1Tok0, _) := (addPermanent g3 tokenOnlyModesDef p0 p0).createOneToken p1
    { bear with name := "P32 Token", isToken := true } (cause := some testCause)
  let tokModalSrc := { (gWithP1Tok0.permanentsOf p0).find? (·.name == "P32 UpTo Token Modal") |>.get! with chosenX := some 1 }
  let gUpToEmpty0 := gWithP1Tok0.putTriggeredAbilityOnStack p0 tokModalSrc tokenOnlyUpToAb "enters" (eventCause := some testCause)
  let upToEmptyId := gUpToEmpty0.stack.back!.objectId
  let preEmptyLeaveIdx := gUpToEmpty0.events.size
  let gUpToEmptyAfterLeave := gUpToEmpty0.concede p1
  let emptyFinalizedAnnounced :=
    (gUpToEmptyAfterLeave.events.extract preEmptyLeaveIdx gUpToEmptyAfterLeave.events.size).any fun e =>
      match e.change with
      | .rules (.cast (.announced oid #[] _ _)) => oid == upToEmptyId
      | _ => false

  let twoModesUpToAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters
      { Effect.enterChooseUpToXModes with
        body := .chooseModes {
          modes := #[
            { body := Instruction.gainLifeFixed 2, phrase := "Gain 2 life" },
            { targeting := .of (.ofDomain (.object .battlefield (.isToken true)))
              body := Instruction.destroy (.target 0)
              phrase := "Destroy target token" }
          ] } }
  let twoModesDef : CardDef := {
    bear with
    name := "P32 UpTo Two Modal"
    triggeredAbilities := #[twoModesUpToAb]
  }
  let (gWithTwoModal0, _) := (addPermanent g3 twoModesDef p0 p0).createOneToken p1
    { bear with name := "P32 Token 2", isToken := true } (cause := some testCause)
  let twoModalSrc := { (gWithTwoModal0.permanentsOf p0).find? (·.name == "P32 UpTo Two Modal") |>.get! with chosenX := some 2 }
  let gUpToChosen0 := gWithTwoModal0.putTriggeredAbilityOnStack p0 twoModalSrc twoModesUpToAb "enters" (eventCause := some testCause)
  let upToChosenId := gUpToChosen0.stack.back!.objectId
  let gUpToPicked0 := mustApply gUpToChosen0 p0 (.chooseMode 0)
  let preChosenLeaveIdx := gUpToPicked0.events.size
  let gUpToChosenAfterLeave := gUpToPicked0.concede p1
  let nonEmptyFinalizedAnnounced :=
    (gUpToChosenAfterLeave.events.extract preChosenLeaveIdx gUpToChosenAfterLeave.events.size).any fun e =>
      match e.change with
      | .rules (.cast (.announced oid #[0] _ _)) => oid == upToChosenId
      | _ => false

  let upToModesLeaveOk :=
    gUpToReopen1.pending == .fraChoice p0 (.upToTriggerModes upToObjId1 2 #[]) &&
    gUpToLeaverConcede.pending == .none &&
    gUpToEmptyAfterLeave.pending == .none &&
    emptyFinalizedAnnounced &&
    (gUpToEmptyAfterLeave.stack.find? (·.objectId == upToEmptyId)).any (·.targetsAnnounced) &&
    gUpToChosenAfterLeave.pending == .none &&
    nonEmptyFinalizedAnnounced &&
    (gUpToChosenAfterLeave.stack.find? (·.objectId == upToChosenId)).any (·.targetsAnnounced)

  -- 2b. `.hawkeyeModes` revalidation on `q != p`:
  --     (i) Re-opens `.hawkeyeModes` when modes remain choosable;
  --     (ii) Finalizes `chosen == #[1, 2]` (when `left == 3` and mode 0 `Net — Target creature`
  --          loses the only creature on the battlefield with `p1`), announcing `#[1, 2]` and
  --          transitioning to `Pending.chooseTargets p0` for mode 1 (`Explosive`);
  --     (iii) Clears `.hawkeyeModes` when `objId? == none`.
  let gHkReopen0 :=
    gBase.putReflexiveTrigger p0 (some p0Bear.id)
      { resolution? := some (.mshReflexive .trickArrows 2), phrase := "Choose up to 2 Trick Arrows modes" }
  let hkObjId1 := gHkReopen0.stack.back!.objectId
  let gHkReopen1 := gHkReopen0.concede p1

  let gNoP0Creature := addPermanent g3 hero p1 p1
  let gHkFin0 :=
    gNoP0Creature.putReflexiveTrigger p0 none
      { resolution? := some (.mshReflexive .trickArrows 3), phrase := "Choose up to 3 Trick Arrows modes" }
  let hkFinObjId := gHkFin0.stack.back!.objectId
  let gHkPicked12 := mustApply (mustApply gHkFin0 p0 (.chooseMode 1)) p0 (.chooseMode 2)
  let preHkLeaveIdx := gHkPicked12.events.size
  let gHkAfterP1Leave := gHkPicked12.concede p1
  let hkFinalizedAnnounced :=
    (gHkAfterP1Leave.events.extract preHkLeaveIdx gHkAfterP1Leave.events.size).any fun e =>
      match e.change with
      | .rules (.cast (.announced oid #[1, 2] _ _)) => oid == hkFinObjId
      | _ => false
  let gHkNoneObj :=
    ((gBase.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.hawkeyeModes 2 #[] none)))).concede p1

  let hawkeyeLeaveOk :=
    gHkReopen1.pending == .fraChoice p0 (.hawkeyeModes 2 #[] (some hkObjId1)) &&
    hkFinalizedAnnounced &&
    gHkAfterP1Leave.pending == .chooseTargets p0 &&
    gHkAfterP1Leave.continuations.isEmpty &&
    gHkNoneObj.pending == .none

  -- 2c. `.stackHydeMode` and `.stackTriggerUnusedMode` on `q != p` (on-stack vs off-stack) and `q == p`:
  let unusedAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.ofTrigger .gollumMode)
  let gUnused0 := gBase.putTriggeredAbilityOnStack p0 p0Bear unusedAb "triggers" (eventCause := some testCause)
  let unusedObjId := gUnused0.stack.back!.objectId
  let gUnusedKeep := gUnused0.concede p1
  let gUnusedGone := (gUnused0.ceaseToExist unusedObjId (cause := some testCause)).concede p1
  let gHydeOnStack :=
    ((gBase.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.stackHydeMode unusedObjId))))
  let gHydeGone := gHydeOnStack.concede p1
  let stackHydeAndUnusedOk :=
    (match gUnusedKeep.pending with | .fraChoice q (.stackTriggerUnusedMode oid ..) => q == p0 && oid == unusedObjId | _ => false) &&
    gUnusedGone.pending == .none &&
    gHydeGone.pending == .none

  -- 2d. `Pending.promptPlayer?` and unified `Decisions.resumePendingReplacement` `.restorePending`:
  let promptPlayerHelperOk :=
    Pending.none.promptPlayer? == none &&
    Pending.declareAttackers.promptPlayer? == none &&
    Pending.declareBlockers.promptPlayer? == none &&
    (Pending.resolveRandom (.chooseIndex 2)).promptPlayer? == none &&
    (Pending.chooseMode p0).promptPlayer? == some p0 &&
    (Pending.chooseTargets p0).promptPlayer? == some p0 &&
    (Pending.mayDiscardDraw p1 2).promptPlayer? == some p1 &&
    (Pending.resolveRandom (.shuffleLibrary p1)).promptPlayer? == some p1 &&
    (Pending.resolveRandom (.orderInto #[] (.library p1) none)).promptPlayer? == some p1 &&
    (Pending.resolveRandom (.orderInto #[] (.hand p1) none)).promptPlayer? == some p1 &&
    (Pending.resolveRandom (.orderInto #[] (.graveyard p1) none)).promptPlayer? == some p1 &&
    (Pending.resolveRandom (.orderInto #[] (.outside p1) none)).promptPlayer? == some p1

  -- When `p0` is still in game and `p1` departed (`departed == #[p1]`), `.restorePending (.chooseTargets p0)`
  -- runs `redirectPendingAfterLeave p1` -> `.resumeChooseTargetsAfterLeave p0`, removing `p0`'s targetless
  -- stack trigger (CR 603.3d) rather than short-circuiting to `openPrompt`:
  let oppCreatureTrig : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you) { targeting := .of .oppCreature, body := Instruction.tap (.target 0), phrase := "Tap target opponent creature" }
  let gTrigOnP1 := gBase.putTriggeredAbilityOnStack p0 p0Bear oppCreatureTrig "triggers" (eventCause := some testCause)
  let trigTargetId := gTrigOnP1.stack.back!.objectId
  let gP1Gone := gTrigOnP1.playerLeavesGame p1
  let gRestoreTargetsAfterDep :=
    (gP1Gone.resumePendingReplacement (.restorePending (.chooseTargets p0) false none #[p1])).drainPendingContinuations
  -- When `p1` ALREADY left the game before `.restorePending` was queued (`departed == #[]`),
  -- `effectiveDeparted` prepends `p1` from `p.promptPlayer?` so `.mayDiscardDraw p1 1` is declined:
  let gLeftP1 := gBase.playerLeavesGame p1
  let gRestorePreDeparted :=
    gLeftP1.resumePendingReplacement (.restorePending (.mayDiscardDraw p1 1) false none #[])
  let gLeftP0 := gBase.playerLeavesGame p0
  let gRestorePreDepartedAttackers :=
    gLeftP0.resumePendingReplacement (.restorePending .declareAttackers false none #[])

  let unifiedRestorePendingOk :=
    promptPlayerHelperOk &&
    gRestoreTargetsAfterDep.pending != .chooseTargets p0 &&
    (gRestoreTargetsAfterDep.findObject? trigTargetId).isNone &&
    gRestorePreDeparted.pending == .none &&
    gRestorePreDeparted.log.back? == some s!"{(gLeftP1.player p1).name} declines (CR 800.4f)" &&
    gRestorePreDepartedAttackers.pending != .declareAttackers

  mustHold32i2 "2a.upToModesLeaveOk" upToModesLeaveOk &&
  mustHold32i2 "2b.hawkeyeLeaveOk" hawkeyeLeaveOk &&
  mustHold32i2 "2c.stackHydeAndUnusedOk" stackHydeAndUnusedOk &&
  mustHold32i2 "2d.unifiedRestorePendingOk" unifiedRestorePendingOk &&
  mustHold32i2 "2.replay"
    (replayOk32i2 #[gUpToReopen0, gUpToReopen1, gUpToLeaverConcede,
      gUpToEmpty0, gUpToEmptyAfterLeave, gUpToChosen0, gUpToPicked0, gUpToChosenAfterLeave,
      gHkReopen0, gHkReopen1, gHkFin0, gHkPicked12, gHkAfterP1Leave, gHkNoneObj,
      gUnused0, gUnusedKeep, gUnusedGone, gHydeGone,
      gTrigOnP1, gP1Gone, gRestoreTargetsAfterDep, gLeftP1, gRestorePreDeparted,
      gLeftP0, gRestorePreDepartedAttackers])

end Phase32Item2EventAlignment

/-! ### Phase 32 Item 3: `redirectPendingAfterLeave` `q != p` `.mayCastExiledElseDamage` & object-referencing `FraChoice` revalidation, and `stillInGame` entry guards -/
section Phase32Item3EventAlignment

private def mustHold32i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase32Item3EventAlignment failed: {label}"

private def replayOk32i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let dfcDef : CardDef := { bear with name := "P32 DFC", otherFace := some { hero with name := "P32 Back" } }
  let gBase :=
    addPermanent
      (addPermanent (addPermanent g3 bear p0 p0) bear p1 p1)
      dfcDef p1 p1
  let p0BearId := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!.id
  let p1BearId := (gBase.permanentsOf p1).find? (·.name == bear.name) |>.get!.id
  let p1DfcId := (gBase.permanentsOf p1).find? (·.name == "P32 DFC") |>.get!.id

  -- 3a. `.mayCastExiledElseDamage`:
  --     (i) `q != p` when `cardId` (owned by `p1` in `.exile`) leaves the game with `p1`:
  --         clears the prompt and deals `n` damage to remaining opponent `p2`;
  --     (ii) `q != p` when `cardId` is owned by `p0` (still in `.exile`): keeps the prompt open;
  --     (iii) `q == p` when `mayThenDrop > 0`: clears `mayThenDrop` via `declineMayThenCore`, logs
  --         `"declines (CR 800.4f)"`, and deals `n` damage to remaining opponents.
  let gWithP1Exiled := insertObject gBase bear p1 .exile
  let p1ExiledId := (gWithP1Exiled.objects.filter (fun o => o.owner == p1 && o.zone == .exile))[0]!.id
  let p2LifeBefore := (gWithP1Exiled.player p2).life
  let gCastExP1Card :=
    ((gWithP1Exiled.change (.pushContinuationFrame {})).change
      (.pending (.mayCastExiledElseDamage p0 p1ExiledId 3 (some p0BearId)))).concede p1

  let gWithP0Exiled := insertObject gBase bear p0 .exile
  let p0ExiledId := (gWithP0Exiled.objects.filter (fun o => o.owner == p0 && o.zone == .exile))[0]!.id
  let gCastExP0Card :=
    ((gWithP0Exiled.change (.pushContinuationFrame {})).change
      (.pending (.mayCastExiledElseDamage p0 p0ExiledId 3 (some p0BearId)))).concede p1

  let gCastExSelfLeave :=
    ((gWithP0Exiled.change (.pushContinuationFrame {
      mayThenDrop := 1
      mayThenConditional := some (.draw (.fixed 1) .you)
    })).change (.pending (.mayCastExiledElseDamage p1 p0ExiledId 2 none))).concede p1

  let mayCastExiledLeaveOk :=
    gCastExP1Card.pending != .mayCastExiledElseDamage p0 p1ExiledId 3 (some p0BearId) &&
    (gCastExP1Card.player p2).life == p2LifeBefore - 3 &&
    gCastExP0Card.pending == .mayCastExiledElseDamage p0 p0ExiledId 3 (some p0BearId) &&
    gCastExSelfLeave.mayThenDrop == 0 &&
    gCastExSelfLeave.mayThenConditional.isNone &&
    gCastExSelfLeave.log.any (·.endsWith "declines (CR 800.4f)") &&
    (gCastExSelfLeave.player p0).life == (gWithP0Exiled.player p0).life - 2 &&
    (gCastExSelfLeave.player p2).life == (gWithP0Exiled.player p2).life - 2

  -- 3b. Object-referencing `FraChoice` prompts on `q != p` when `p1`'s permanent leaves with `p1`:
  let gTopBot := (gBase.beginFraChoice p0 (.topOrBottomDamage p1BearId 2 none)).concede p1
  let gChooseKw := (gBase.beginFraChoice p0 (.chooseKeyword p1BearId #[.trample, .deathtouch])).concede p1
  let gBecomePT := (gBase.beginFraChoice p0 (.mayBecomeBasePT p1BearId 4 4)).concede p1
  let gPlusOne :=
    ((gBase.addPlusOnePlusOneTo (gBase.object! p1BearId) 1 (cause := some testCause)).beginFraChoice
      p0 (.mayMovePlusOne p1BearId)).concede p1
  let gMoveAll := (gBase.beginFraChoice p0 (.mayMoveAllCounters p0BearId p1BearId)).concede p1
  let gTapSrc := (gBase.beginFraChoice p0 (.mayTapSourceThen (.gainLife 2) p1BearId)).concede p1

  let gWithRestCard := insertObject gBase hero p0 .exile
  let restCardId := (gWithRestCard.objects.filter (fun o => o.owner == p0 && o.zone == .exile && o.name == hero.name))[0]!.id
  let gNickFury :=
    (gWithRestCard.beginFraChoice p0 (.nickFuryMayTransform p1DfcId #[restCardId])).concede p1
  let gWithTwoRestCards := insertObject gWithRestCard forest p0 .exile
  let restCard2Id := (gWithTwoRestCards.objects.filter (fun o => o.owner == p0 && o.zone == .exile && o.name == forest.name))[0]!.id
  let gNickFuryTwoRest :=
    (gWithTwoRestCards.beginFraChoice p0 (.nickFuryMayTransform p1DfcId #[restCardId, restCard2Id])).concede p1
  let nickFuryTwoRestRandomOk :=
    match gNickFuryTwoRest.pending with
    | .resolveRandom (.orderInto ids (.library q) _) =>
      q == p0 && ids == #[restCardId, restCard2Id]
    | _ => false

  let objFraChoicesLeaveOk :=
    gTopBot.pending == .none && gTopBot.continuations.isEmpty &&
    gChooseKw.pending == .none && gChooseKw.continuations.isEmpty &&
    gBecomePT.pending == .none && gBecomePT.continuations.isEmpty &&
    gPlusOne.pending == .none && gPlusOne.continuations.isEmpty &&
    gMoveAll.pending == .none && gMoveAll.continuations.isEmpty &&
    gTapSrc.pending == .none && gTapSrc.continuations.isEmpty &&
    gNickFury.pending == .none && gNickFury.continuations.isEmpty &&
    (gNickFury.followMovedToZone? restCardId (· == .library p0)).isSome &&
    (gNickFury.player p0).library[0]? == (gNickFury.followMovedToZone? restCardId (· == .library p0)).map (·.id) &&
    nickFuryTwoRestRandomOk

  -- 3c. Departed-player `stillInGame` guards on `beginMayDiscardDraw`, `beginSacrificeCreature`,
  --     and `sacrificeGreatestManaValue`:
  let gLeft := gBase.playerLeavesGame p1
  let sIdx := gLeft.events.size
  let gMayDisc := gLeft.beginMayDiscardDraw p1 2
  let gSacCr := gLeft.beginSacrificeCreature p1
  let gSacGreatest := gLeft.sacrificeGreatestManaValue p1
  let stillInGameGuardsOk :=
    #[gMayDisc, gSacCr, gSacGreatest].all (fun g => g.events.size == sIdx && g.pending == .none)

  mustHold32i3 "3a.mayCastExiledLeaveOk" mayCastExiledLeaveOk &&
  mustHold32i3 "3b.objFraChoicesLeaveOk" objFraChoicesLeaveOk &&
  mustHold32i3 "3c.stillInGameGuardsOk" stillInGameGuardsOk &&
  mustHold32i3 "3.replay"
    (replayOk32i3 #[gCastExP1Card, gCastExP0Card, gCastExSelfLeave,
      gTopBot, gChooseKw, gBecomePT, gPlusOne, gMoveAll, gTapSrc, gNickFury, gNickFuryTwoRest, gLeft])

end Phase32Item3EventAlignment

/-! ### Phase 33 Item 1: Game-over active-resolution teardown, ward `outerCont?` ordering, `Core.clearMay`, and `redirectPendingAfterLeave` scratch cleanup -/
section Phase33Item1EventAlignment

private def mustHold33i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase33Item1EventAlignment failed: {label}"

private def replayOk33i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustApply33i1 (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! s!"Phase33Item1EventAlignment apply failed: {e}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent afterDraw bear p0 p0) hero p1 p1
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let g3Base := addPermanent (addPermanent (addPermanent g3 bear p0 p0) hero p1 p1) bear p2 p2
  let p0Bear3 := (g3Base.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p1Hero3 := (g3Base.permanentsOf p1).find? (·.name == hero.name) |>.get!

  -- 1a. Game-over active-resolution & transient prompt/proposal/continuation teardown across
  --     `completeActiveResolutions`, `concede`, `receivePriority`, `finishConcedePriority`,
  --     `concedePlayersLoop`, and `finishHostRandom`:
  let simpleAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gAbStack := gBase.putTriggeredAbilityOnStack p0 p0Bear simpleAb "triggers" (eventCause := some testCause)
  let abObjId := gAbStack.stack.back!.objectId
  let abSnap := gAbStack.snapshot (gAbStack.object! abObjId)
  let dummyProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abObjId
    original := gAbStack.object! abObjId
    originalSnapshot := abSnap
  }
  let gMidResDirty :=
    (gAbStack.change (.pushContinuationFrame {
      resolutionFinish := some (.ability abObjId abSnap p0 (some p0Bear.id) none)
    })).changes #[
      .pending (.chooseMode p0),
      .afterRandom (.gainLife p0 1),
      .proposedSpell (some dummyProp),
      .saveProposalCheckpoint,
      .pendingReplacement (some .checkSBA),
      .pushOuterPendingReplacement .checkSBA ]
  let isTornDown (g : Game) : Bool :=
    g.over &&
    g.continuations.isEmpty &&
    g.stack.isEmpty &&
    (g.findObject? abObjId).isNone &&
    g.pending == .none &&
    g.afterRandom == .none &&
    g.proposedSpell.isNone &&
    g.proposalCheckpoint.isNone &&
    g.pendingReplacement.isNone &&
    g.outerPendingReplacements.isEmpty

  let gConcedeOver := gMidResDirty.concede p1
  let gLethalMidRes := gMidResDirty.loseLife p1 20 (cause := some testCause)
  let gReceivePrioEntryOver := gLethalMidRes.checkSBA.receivePriority p0
  let gReceivePrioSbaOver :=
    (gLethalMidRes.changes #[.pending .none, .afterRandom .none, .pendingReplacement none]).receivePriority p0
  let gFinishConcedeOver :=
    gLethalMidRes.checkSBA.finishConcedePriority false none
  let gConcedeLoopOver :=
    gLethalMidRes.checkSBA.concedePlayersLoop #[p1] false true false none none none false #[]
  let gHostRandomOver := gLethalMidRes.checkSBA.finishHostRandom

  let gameOverTeardownOk :=
    isTornDown gConcedeOver &&
    isTornDown gReceivePrioEntryOver &&
    isTornDown gReceivePrioSbaOver &&
    isTornDown gFinishConcedeOver &&
    isTornDown gConcedeLoopOver &&
    isTornDown gHostRandomOver

  -- 1b. `popEmptyTopContinuationFrames` in `drainPendingContinuations` and `.restorePending`
  --     (and `openPromptWith` frame push for `.fraChoice`):
  let gEmptyFrameBeforeTargets :=
    ((gBase.change (.pushContinuationFrame {})).change
      (.pendingReplacement (some (.restorePending (.chooseTargets p0))))).drainPendingContinuations
  let gRestoreFraPushesFrame :=
    ((gBase.change (.pushContinuationFrame {})).change
      (.pendingReplacement (some (.restorePending (.fraChoice p0 (.mayCreateTokens .treasure 1)))))).drainPendingContinuations
  let emptyTopFrameOk :=
    gBase.continuations.isEmpty &&
    gEmptyFrameBeforeTargets.pending == .chooseTargets p0 &&
    gEmptyFrameBeforeTargets.continuations.isEmpty &&
    gRestoreFraPushesFrame.pending == .fraChoice p0 (.mayCreateTokens .treasure 1) &&
    gRestoreFraPushesFrame.continuations.size == 1

  -- 1c. Ward `outerCont?` ordering (`finishWardAndDrain`, `sacrificeForActivation` `.payWard`,
  --     and `afterWardResolved` guard):
  --     Paying ward with an outer `PendingReplacement` runs `outerCont?` (which pauses on a
  --     prompt) BEFORE `afterWardResolved` grants idle priority or pops frames prematurely:
  let gWithForest := addPermanent gBase forest p0 p0
  let fId := (gWithForest.permanentsOf p0).find? (·.name == forest.name) |>.get!.id
  let gWithMana := mustApply33i1 gWithForest p0 (.tapForMana fId (.colored .green))
  let gWardStack1 := gWithMana.putTriggeredAbilityOnStack p0 p0Bear simpleAb "triggers" (eventCause := some testCause)
  let wardAbId1 := gWardStack1.stack.back!.objectId
  let gWardSetup :=
    ((gWardStack1.change (.pushContinuationFrame {})).changes #[
      .pending (.payWard p0 wardAbId1 (CostSpec.ofGeneric 1)),
      .pendingReplacement (some (.restorePending (.mayDiscardDraw p0 1))) ])
  let gWardPaidMana := mustApply33i1 gWardSetup p0 .payGeneric
  let gWardStack2 := gBase.putTriggeredAbilityOnStack p0 p0Bear simpleAb "triggers" (eventCause := some testCause)
  let wardAbId2 := gWardStack2.stack.back!.objectId
  let gWardSacSetup :=
    ((gWardStack2.change (.pushContinuationFrame {})).changes #[
      .pending (.payWard p0 wardAbId2 (CostSpec.sacrificePermanents 1) #[]),
      .pendingReplacement (some (.restorePending (.mayDiscardDraw p0 1))) ])
  let gWardPaidSac := mustApply33i1 gWardSacSetup p0 (.sacrifice p0Bear.id)
  let wardOuterOrderOk :=
    gWardPaidMana.pending == .mayDiscardDraw p0 1 &&
    gWardPaidMana.pendingReplacement == some .afterWardResolved &&
    gWardPaidSac.pending == .mayDiscardDraw p0 1 &&
    gWardPaidSac.pendingReplacement == some .afterWardResolved

  -- 1d. `Core.clearMay`, `ResolutionCompat.beginMay`, and `redirectPendingAfterLeave`
  --     `.mayResolve` (`.ifYouDont` decline & `sequenceAllTargetsIllegal`), `.chooseCards`
  --     `.stashedCause none`, `.orderLibraryBottom`, and `.searchLibrary` (`plusOneAfterSearch`):
  let trigCtx : TriggerSequenceRest := {
    controller := p1
    ability := simpleAb
    sourceId := some p1Hero3.id
    targets := #[]
    dividedDamage := #[]
    lastKnownPower := none
    lastKnownToughness := none
    sourceName := hero.name
    cardPower := none
    steps := []
  }
  let gStaleMay :=
    (g3Base.change (.pushContinuationFrame {})).changes #[
      .mayOnAccept (some (.gainLife (.fixed 1))),
      .mayOnDecline (some (.gainLife (.fixed 5))),
      .mayContext (some trigCtx) ]
  let gClearedMay := gStaleMay.clearMay
  let tapEff : Effect := {
    targeting := .of .creature
    body := Instruction.tap (.target 0)
    phrase := "Tap target creature"
  }
  let gBeginMayAfterStale :=
    gStaleMay.beginMay p0 tapEff #[Target.permanent p1Hero3.id] (Instruction.tap (.target 0))
  -- `q != p` on `.mayResolve` cancels when all targets in `mayTargets` became illegal:
  let gMayTargetGone := gBeginMayAfterStale.concede p1
  -- `q == p` on `.mayResolve` with `mayOnDecline` + `mayContext` resumes `.ifYouDont` branch:
  let oppLoseFollow : TriggeredAbility.TriggerResolution := .loseLife (.fixed 3) .eachOpponent
  let gMayIfYouDont :=
    ((g3Base.change (.pushContinuationFrame {})).changes #[
      .pending (.mayResolve p1),
      .mayOnAccept (some (.gainLife (.fixed 1))),
      .mayOnDecline (some oppLoseFollow),
      .mayContext (some trigCtx) ]).concede p1
  -- `.chooseCards` (`q == p`) clears `.stashedCause none`:
  let gChooseCardsLeave :=
    ((g3Base.change (.pushContinuationFrame { stashedCause := some testCause })).change
      (.pending (.fraChoice p1 (.chooseCards #[] 1 (.toHand false))))).concede p1
  -- `.orderLibraryBottom` (`q != p` with `liveIds.size == 1` moves remaining card to bottom):
  let p0TopId := (g3Base.player p0).library.back!
  let p1TopId := (g3Base.player p1).library.back!
  let gOrderBotSingle :=
    ((g3Base.change (.pushContinuationFrame { stashedCause := some testCause })).change
      (.pending (.fraChoice p0 (.orderLibraryBottom #[p0TopId, p1TopId])))).concede p1
  -- `.searchLibrary` (`q == p` with `plusOneAfterSearch` for surviving `p0` places +1/+1 on `p0Bear3`;
  -- and `q != p` filters vanished `eligible` cards and drops departed `plusOneAfterSearch`):
  let gSearchTargetLeaves :=
    ((g3Base.change (.pushContinuationFrame {
      plusOneAfterSearch := some (p0Bear3.id, p0, none)
    })).change (.pending (.fraChoice p1 (.searchLibrary #[p1TopId] 1 .hand none "a card")))).concede p1
  let gSearchOtherLeaves :=
    ((g3Base.change (.pushContinuationFrame {
      plusOneAfterSearch := some (p1Hero3.id, p1, none)
    })).change (.pending (.fraChoice p0 (.maySearchLibrary #[p0TopId, p1TopId] 1 .hand none "a card")))).concede p1

  let mayAndScratchCleanupOk :=
    gClearedMay.mayOnAccept.isNone &&
    gClearedMay.mayOnDecline.isNone &&
    gClearedMay.mayContext.isNone &&
    gBeginMayAfterStale.mayOnAccept.isNone &&
    gBeginMayAfterStale.mayOnDecline.isNone &&
    gBeginMayAfterStale.mayContext.isNone &&
    gMayTargetGone.pending == .none &&
    gMayTargetGone.mayEffect.isNone &&
    gMayTargetGone.continuations.isEmpty &&
    gMayTargetGone.log.any (· == "The target is no longer legal") &&
    gMayIfYouDont.pending == .none &&
    gMayIfYouDont.continuations.isEmpty &&
    gMayIfYouDont.log.any (·.endsWith "declines (CR 800.4f)") &&
    (gMayIfYouDont.player p0).life == (g3Base.player p0).life - 3 &&
    gChooseCardsLeave.stashedCause.isNone &&
    gOrderBotSingle.pending == .none &&
    gOrderBotSingle.continuations.isEmpty &&
    (gOrderBotSingle.player p0).library[0]? == (gOrderBotSingle.followMovedToZone? p0TopId (· == .library p0)).map (·.id) &&
    (gSearchTargetLeaves.object! p0Bear3.id).status.plusOnePlusOne == 1 &&
    gSearchOtherLeaves.plusOneAfterSearch.isNone &&
    gSearchOtherLeaves.pending == .fraChoice p0 (.maySearchLibrary #[p0TopId] 1 .hand none "a card")

  mustHold33i1 "1a.gameOverTeardownOk" gameOverTeardownOk &&
  mustHold33i1 "1b.emptyTopFrameOk" emptyTopFrameOk &&
  mustHold33i1 "1c.wardOuterOrderOk" wardOuterOrderOk &&
  mustHold33i1 "1d.mayAndScratchCleanupOk" mayAndScratchCleanupOk &&
  mustHold33i1 "1.replay"
    (replayOk33i1 #[gConcedeOver, gReceivePrioEntryOver, gReceivePrioSbaOver, gFinishConcedeOver, gConcedeLoopOver,
      gHostRandomOver, gEmptyFrameBeforeTargets, gRestoreFraPushesFrame,
      gWardPaidMana, gWardPaidSac, gClearedMay, gBeginMayAfterStale, gMayTargetGone,
      gMayIfYouDont, gChooseCardsLeave, gOrderBotSingle, gSearchTargetLeaves, gSearchOtherLeaves])

end Phase33Item1EventAlignment

/-! ### Phase 33 Item 2: Modal `chosen` revalidation & departed-seat guards in `runPostStep`, and `.restorePending` cost/2HG-combat/`unlessPaysDue` completion -/
section Phase33Item2EventAlignment

private def mustHold33i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase33Item2EventAlignment failed: {label}"

private def replayOk33i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustApply33i2 (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! s!"Phase33Item2EventAlignment apply failed: {e}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent g3 bear p0 p0) hero p1 p1
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!

  -- 2a. Departed-seat `!g.stillInGame p` and controller/caster guards in `Decisions.runPostStep`:
  let gLeftP1 := gBase.playerLeavesGame p1
  let oppTrig : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you) { targeting := .of .creature, body := Instruction.tap (.target 0), phrase := "Tap target creature" }
  let gP0TrigAwaiting := gLeftP1.putTriggeredAbilityOnStack p0 p0Bear oppTrig "triggers" (eventCause := some testCause)
  let p0TrigId := gP0TrigAwaiting.stack.back!.objectId
  -- Calling `.resumeChooseTargetsAfterLeave p1` (departed) or `.resumeChooseTargetsAfterLeave p2`
  -- (living non-controller) prompts `p0` via `afterTriggerTargetsChosen` instead of removing `p0`'s trigger:
  let gTargetPostDeparted := (gP0TrigAwaiting.change (.pending .none)).runPostStep (.resumeChooseTargetsAfterLeave p1)
  let gTargetPostWrongSeat := (gP0TrigAwaiting.change (.pending .none)).runPostStep (.resumeChooseTargetsAfterLeave p2)
  -- When `p0` has an open `proposedSpell`, `.resumeChooseTargetsAfterLeave p2` neither reverses/grants priority
  -- when `prop.spellId` is gone nor leaves `p0`'s live targeted proposal without `.chooseTargets p0`:
  let tapSpellDef : CardDef := {
    name := "P33 Tap Spell"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some { targeting := .of .creature, body := Instruction.tap (.target 0), phrase := "Tap target creature" }
  }
  let gTap0 := insertObject gLeftP1 tapSpellDef p0 (.hand p0)
  let gTapCast := mustApply33i2 gTap0 p0 (.cast (gTap0.player p0).hand.back!)
  let gTargetOtherPropLive := (gTapCast.change (.pending .none)).runPostStep (.resumeChooseTargetsAfterLeave p2)
  let vanishedProp : ProposedSpell := { gTapCast.proposedSpell.get! with spellId := ⟨999999⟩ }
  let vanishedPropP2 : ProposedSpell := { vanishedProp with caster := p2 }
  let gVanishedOnCastP2 := gTapCast.changes #[.proposedSpell (some vanishedPropP2), .pending .none]
  let gTargetOwnPropGone := gVanishedOnCastP2.runPostStep (.resumeChooseTargetsAfterLeave p2)
  let gTargetOtherPropGone := gVanishedOnCastP2.runPostStep (.resumeChooseTargetsAfterLeave p0)
  -- Queued waiting trigger proves whether `receivePriority` ran (which stacks waiting triggers):
  let probeWt : WaitingTrigger := {
    controller := p0
    source := p0Bear
    ability := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
    pattern := .thisEnters
    checked := true
    eventCause := some testCause
  }
  let gTrigWithProbe := (gP0TrigAwaiting.change (.pending .none)).change (.waitingTriggers #[probeWt])
  let gOwnVanishedWithTrig := gTrigWithProbe.changes #[.saveProposalCheckpoint, .proposedSpell (some vanishedProp)]
  let gOtherCasterVanishedWithTrig :=
    gTrigWithProbe.changes #[.pendingPriority (some p0), .saveProposalCheckpoint, .proposedSpell (some vanishedPropP2)]
  -- (1) Own vanished proposal (`caster == p2` while `activePlayer == p0` and `ckpt.pendingPriority == some p0`, plus `caster == p0`)
  --     + `p0`'s trigger: reverses the proposal, overwrites `pendingPriority`, prompts `.chooseTargets p0`, and returns priority to caster:
  let gTargetOwnSeatWithTrig := gOwnVanishedWithTrig.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gTargetOwnSeatAnnounced := mustApply33i2 gTargetOwnSeatWithTrig p0 (.target (.permanent p0Bear.id))
  let gTargetOwnP2SeatWithTrig := gOtherCasterVanishedWithTrig.runPostStep (.resumeChooseTargetsAfterLeave p2)
  let gTargetOwnP2SeatAnnounced := mustApply33i2 gTargetOwnP2SeatWithTrig p0 (.target (.permanent p0Bear.id))
  -- (2) Other player's vanished proposal (`caster != p` on both `p == p2` and `caster == p2, p == p0`) + `p0`'s trigger:
  --     prompts `.chooseTargets p0` first, and once `p0Bear.id` is announced, `afterTriggerTargetsChosen` reverses the
  --     vanished proposal (preserving `p0TrigId`'s target) and runs `receivePriority` for the vanished caster:
  let gTargetOtherPropGoneWithTrig := gOwnVanishedWithTrig.runPostStep (.resumeChooseTargetsAfterLeave p2)
  let gTargetOtherAnnouncedA := mustApply33i2 gTargetOtherPropGoneWithTrig p0 (.target (.permanent p0Bear.id))
  let gTargetOtherCasterSameSeat := gOtherCasterVanishedWithTrig.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gTargetOtherAnnouncedB := mustApply33i2 gTargetOtherCasterSameSeat p0 (.target (.permanent p0Bear.id))
  -- (3) No-legal-target trigger (`ceaseToExist` CR 603.3d) alongside own vs other vanished `proposedSpell`:
  let tokOnlyTrig : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you)
      { targeting := .of (.ofDomain (.object .battlefield (.isToken true)))
        body := Instruction.tap (.target 0)
        phrase := "Tap target token" }
  let gNoLegalTrig0 :=
    ((gLeftP1.putTriggeredAbilityOnStack p0 p0Bear tokOnlyTrig "triggers" (eventCause := some testCause)).change
      (.pending .none)).change (.waitingTriggers #[probeWt])
  let noLegalTrigId := gNoLegalTrig0.stack.back!.objectId
  let gNoLegalOwnRemoved :=
    (gNoLegalTrig0.changes #[.pendingPriority (some p0), .saveProposalCheckpoint, .proposedSpell (some vanishedPropP2)]).runPostStep
      (.resumeChooseTargetsAfterLeave p2)
  let gNoLegalOtherRemoved :=
    (gNoLegalTrig0.changes #[.pendingPriority (some p0), .saveProposalCheckpoint, .proposedSpell (some vanishedPropP2)]).runPostStep
      (.resumeChooseTargetsAfterLeave p0)
  -- (4) Plain `reverseProposedSpell` (`alwaysGrantPriority == false`) while `p0TrigId` still needs targets:
  --     both with a post-checkpoint kept stack entry + `probeWt` (stacks `waitingTriggers` via `receivePriority` and prompts `.chooseTargets p0`)
  --     and with no waiting triggers / kept events (prompts `.chooseTargets p0` and stashes `pendingPriority = some p2`):
  let gPlainRevWithTrig :=
    (gOtherCasterVanishedWithTrig.change (.stackEntry p0TrigId .clearChosenModes)).reverseProposedSpell
  let gPlainRevAnnounced := mustApply33i2 gPlainRevWithTrig p0 (.target (.permanent p0Bear.id))
  let gPlainRevNoWt :=
    (gP0TrigAwaiting.changes #[.pending .none, .pendingPriority (some p0),
      .saveProposalCheckpoint, .proposedSpell (some vanishedPropP2)]).reverseProposedSpell
  -- (5) Proposal reversal when a kept `.player (.gameEnded ..)` event is replayed while a non-proposal
  --     stacked trigger still needs targets (`triggerNeedingTargets.isSome`): both `alwaysGrantPriority`
  --     (`.resumeChooseTargetsAfterLeave` and `afterTriggerTargetsChosen`) and plain `reverseProposedSpell`
  --     tear down continuation frames / resolving entries via `receivePriority` without opening `.chooseTargets`:
  let simpleResAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gResAbStack := gLeftP1.putTriggeredAbilityOnStack p0 p0Bear simpleResAb "triggers" (eventCause := some testCause)
  let resAbId := gResAbStack.stack.back!.objectId
  let resAbSnap := gResAbStack.snapshot (gResAbStack.object! resAbId)
  let gOverStackCont :=
    (((gResAbStack.change (.pushContinuationFrame {
      resolutionFinish := some (.ability resAbId resAbSnap p0 (some p0Bear.id) none)
    })).putTriggeredAbilityOnStack p0 p0Bear oppTrig "triggers" (eventCause := some testCause)).change (.pending .none))
  let overTrigId := gOverStackCont.stack.back!.objectId
  let gOverBaseCont :=
    ((gOverStackCont.changes #[.saveProposalCheckpoint, .proposedSpell (some vanishedProp)]).playerLeavesGame
      p2).decideGameIfFinished.get!
  let gOverBaseFlat :=
    ((gP0TrigAwaiting.changes #[.pending .none, .saveProposalCheckpoint, .proposedSpell (some vanishedProp)]).playerLeavesGame
      p2).decideGameIfFinished.get!
  let gOverAlwaysGrantCont := gOverBaseCont.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gOverAlwaysGrantFlat := gOverBaseFlat.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gOverPlainRevCont := gOverBaseCont.reverseProposedSpell
  let gOverPlainRevFlat := gOverBaseFlat.reverseProposedSpell
  let gOverOtherSeatLeave := gOverBaseCont.runPostStep (.resumeChooseTargetsAfterLeave p2)
  let gOverAfterTrigBracketed :=
    (((gOverStackCont.changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some vanishedProp),
      .beginProposalAction .costAction,
      .stackEntry overTrigId (.targetsAnnounced true),
      .endProposalAction]).playerLeavesGame p2).decideGameIfFinished.get!).afterTriggerTargetsChosen
  let gOverAfterTrigDirect := gOverBaseCont.afterTriggerTargetsChosen
  let gModePostDeparted :=
    ((gLeftP1.change (.pushContinuationFrame {})).runPostStep (.resumeTriggerModesAfterLeave p1 p0TrigId 1 #[]))
  let gUpToPostDeparted :=
    ((gLeftP1.change (.pushContinuationFrame {})).runPostStep (.resumeUpToTriggerModesAfterLeave p1 p0TrigId 1 #[]))
  let gHkPostDeparted :=
    ((gLeftP1.change (.pushContinuationFrame {})).runPostStep (.resumeHawkeyeModesAfterLeave p1 p0TrigId 1 #[]))
  let departedSeatGuardsOk :=
    (gTargetPostDeparted.findObject? p0TrigId).any (·.zone == .stack) &&
    gTargetPostDeparted.pending == .chooseTargets p0 &&
    (gTargetPostWrongSeat.findObject? p0TrigId).any (·.zone == .stack) &&
    gTargetPostWrongSeat.pending == .chooseTargets p0 &&
    gTargetOtherPropLive.pending == .chooseTargets p0 &&
    gTargetOtherPropLive.proposedSpell.isSome &&
    gTargetOwnPropGone.pending == .none &&
    gTargetOwnPropGone.proposedSpell.isNone &&
    gTargetOwnPropGone.priority == p2 &&
    gTargetOtherPropGone.pending == .none &&
    gTargetOtherPropGone.proposedSpell.isNone &&
    gTargetOtherPropGone.priority == p2 &&
    gTargetOwnSeatWithTrig.proposedSpell.isNone &&
    gTargetOwnSeatWithTrig.pending == .chooseTargets p0 &&
    gTargetOwnSeatAnnounced.pending == .none &&
    gTargetOwnSeatAnnounced.proposedSpell.isNone &&
    gTargetOwnSeatAnnounced.priority == p0 &&
    (gTargetOwnSeatAnnounced.stack.find? (·.objectId == p0TrigId)).any (fun se =>
      se.targetsAnnounced && se.targets == #[.permanent p0Bear.id]) &&
    gTargetOwnSeatAnnounced.waitingTriggers.isEmpty &&
    gTargetOwnP2SeatWithTrig.proposedSpell.isNone &&
    gTargetOwnP2SeatWithTrig.pending == .chooseTargets p0 &&
    gTargetOwnP2SeatWithTrig.pendingPriority == some p2 &&
    gTargetOwnP2SeatAnnounced.pending == .none &&
    gTargetOwnP2SeatAnnounced.proposedSpell.isNone &&
    gTargetOwnP2SeatAnnounced.priority == p2 &&
    (gTargetOwnP2SeatAnnounced.stack.find? (·.objectId == p0TrigId)).any (fun se =>
      se.targetsAnnounced && se.targets == #[.permanent p0Bear.id]) &&
    gTargetOwnP2SeatAnnounced.waitingTriggers.isEmpty &&
    gTargetOtherPropGoneWithTrig.proposedSpell.isSome &&
    gTargetOtherPropGoneWithTrig.pending == .chooseTargets p0 &&
    gTargetOtherAnnouncedA.pending == .none &&
    gTargetOtherAnnouncedA.proposedSpell.isNone &&
    gTargetOtherAnnouncedA.priority == p0 &&
    (gTargetOtherAnnouncedA.stack.find? (·.objectId == p0TrigId)).any (fun se =>
      se.targetsAnnounced && se.targets == #[.permanent p0Bear.id]) &&
    gTargetOtherAnnouncedA.waitingTriggers.isEmpty &&
    gTargetOtherCasterSameSeat.proposedSpell.isSome &&
    gTargetOtherCasterSameSeat.pending == .chooseTargets p0 &&
    gTargetOtherAnnouncedB.pending == .none &&
    gTargetOtherAnnouncedB.proposedSpell.isNone &&
    gTargetOtherAnnouncedB.priority == p2 &&
    (gTargetOtherAnnouncedB.stack.find? (·.objectId == p0TrigId)).any (fun se =>
      se.targetsAnnounced && se.targets == #[.permanent p0Bear.id]) &&
    gTargetOtherAnnouncedB.waitingTriggers.isEmpty &&
    gNoLegalOwnRemoved.proposedSpell.isNone &&
    gNoLegalOwnRemoved.pending == .none &&
    gNoLegalOwnRemoved.priority == p2 &&
    (gNoLegalOwnRemoved.findObject? noLegalTrigId).isNone &&
    gNoLegalOwnRemoved.waitingTriggers.isEmpty &&
    gNoLegalOtherRemoved.proposedSpell.isNone &&
    gNoLegalOtherRemoved.pending == .none &&
    gNoLegalOtherRemoved.priority == p2 &&
    (gNoLegalOtherRemoved.findObject? noLegalTrigId).isNone &&
    gNoLegalOtherRemoved.waitingTriggers.isEmpty &&
    gPlainRevWithTrig.proposedSpell.isNone &&
    gPlainRevWithTrig.pending == .chooseTargets p0 &&
    gPlainRevWithTrig.pendingPriority == some p2 &&
    gPlainRevAnnounced.waitingTriggers.isEmpty &&
    gPlainRevAnnounced.pending == .none &&
    gPlainRevAnnounced.priority == p2 &&
    gPlainRevNoWt.proposedSpell.isNone &&
    gPlainRevNoWt.pending == .chooseTargets p0 &&
    gPlainRevNoWt.pendingPriority == some p2 &&
    gOverAlwaysGrantCont.over && gOverAlwaysGrantCont.pending == .none &&
    gOverAlwaysGrantCont.continuations.isEmpty && gOverAlwaysGrantCont.proposedSpell.isNone &&
    (gOverAlwaysGrantCont.findObject? resAbId).isNone &&
    gOverAlwaysGrantFlat.over && gOverAlwaysGrantFlat.pending == .none &&
    gOverAlwaysGrantFlat.continuations.isEmpty && gOverAlwaysGrantFlat.proposedSpell.isNone &&
    gOverPlainRevCont.over && gOverPlainRevCont.pending == .none &&
    gOverPlainRevCont.continuations.isEmpty && gOverPlainRevCont.proposedSpell.isNone &&
    (gOverPlainRevCont.findObject? resAbId).isNone &&
    gOverPlainRevFlat.over && gOverPlainRevFlat.pending == .none &&
    gOverPlainRevFlat.continuations.isEmpty && gOverPlainRevFlat.proposedSpell.isNone &&
    gOverOtherSeatLeave.over && gOverOtherSeatLeave.pending == .none &&
    gOverOtherSeatLeave.continuations.isEmpty && gOverOtherSeatLeave.proposedSpell.isNone &&
    (gOverOtherSeatLeave.findObject? resAbId).isNone &&
    gOverAfterTrigBracketed.over && gOverAfterTrigBracketed.pending == .none &&
    gOverAfterTrigBracketed.continuations.isEmpty && gOverAfterTrigBracketed.proposedSpell.isNone &&
    (gOverAfterTrigBracketed.findObject? resAbId).isNone &&
    gOverAfterTrigDirect.over && gOverAfterTrigDirect.pending == .none &&
    gOverAfterTrigDirect.continuations.isEmpty && gOverAfterTrigDirect.proposedSpell.isNone &&
    (gOverAfterTrigDirect.findObject? resAbId).isNone &&
    gModePostDeparted.pending == .none && gModePostDeparted.continuations.isEmpty &&
    gUpToPostDeparted.pending == .none && gUpToPostDeparted.continuations.isEmpty &&
    gHkPostDeparted.pending == .none && gHkPostDeparted.continuations.isEmpty

  -- 2b. Revalidation of already-selected modes in `chosen` across `.resumeChooseModeAfterLeave`,
  --     `.resumeTriggerModesAfterLeave`, `.resumeUpToTriggerModesAfterLeave`, and `.resumeHawkeyeModesAfterLeave`:
  -- (i) Modal spell (`Choose one or both` `ModalSpec`) where mode 0 targets a token (only `p1` controls one)
  --     and mode 1 gains 2 life: `p0` picks mode 0 while `chooseMode` stays open for the optional second mode;
  --     then `p1` concedes, removing the only token! `validChosen` drops mode 0 via `StackEntryChange.clearChosenModes`
  --     and re-opens `Pending.chooseMode p0` with `chosenModesOf == #[]`!
  let modalBothSpell : CardDef := {
    name := "P33 Modal Both"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      body := .chooseModes {
        maxModes := .const 2
        modes := #[
          { targeting := .of (.ofDomain (.object .battlefield (.isToken true)))
            body := Instruction.destroy (.target 0)
            phrase := "Destroy target token" },
          { body := Instruction.gainLifeFixed 2, phrase := "Gain 2 life" }
        ]
      }
    }
  }
  let (gModal0, _) := (insertObject g3 modalBothSpell p0 (.hand p0)).createOneToken p1
    { bear with name := "P33 Token", isToken := true } (cause := some testCause)
  let modalSpellId := (gModal0.player p0).hand.back!
  let gModalCast := mustApply33i2 gModal0 p0 (.cast modalSpellId)
  let stackModalId := gModalCast.stack.back!.objectId
  let gModalPicked0 := mustApply33i2 gModalCast p0 (.chooseMode 0)
  let gModalAfterLeave := gModalPicked0.concede p1
  let modalSpellClearedOk :=
    gModalPicked0.chosenModesOf (gModalPicked0.object! stackModalId) == #[0] &&
    gModalAfterLeave.pending == .chooseMode p0 &&
    gModalAfterLeave.chosenModesOf (gModalAfterLeave.object! stackModalId) == #[]

  -- (ii) `.resumeTriggerModesAfterLeave`: source with 3 modes (mode 0 token-only, mode 1 gain 2 life,
  --      mode 2 draw 1), choosing 2 modes: `p0` picks mode 0 (`remaining == 1, chosen == #[0]`), then
  --      `p1` leaves removing the token -> `validChosen == #[]` and `needed == 2`!
  --      Also verify `needed == 0` finalizes `validChosen == #[1]` when `remaining == 0`:
  let chooseTwoTrigAb : TriggeredAbility :=
    TriggeredAbility.mkModal .thisEnters #[
      { targeting := .of (.ofDomain (.object .battlefield (.isToken true)))
        body := Instruction.destroy (.target 0)
        phrase := "Destroy target token" },
      { body := Instruction.gainLifeFixed 2, phrase := "Gain 2 life" },
      { body := Instruction.drawFixed 1, phrase := "Draw a card" }
    ] (headerPhrase := "Choose two") (minModes := .const 2) (maxModes := .const 2)
  let threeModesDef : CardDef := {
    bear with
    name := "P33 Three Modes"
    triggeredAbilities := #[chooseTwoTrigAb]
  }
  let (gTrigModes0, _) := (addPermanent g3 threeModesDef p0 p0).createOneToken p1
    { bear with name := "P33 Tok2", isToken := true } (cause := some testCause)
  let threeSrc := (gTrigModes0.permanentsOf p0).find? (·.name == "P33 Three Modes") |>.get!
  let gTrigModesStack := gTrigModes0.putTriggeredAbilityOnStack p0 threeSrc chooseTwoTrigAb "enters" (eventCause := some testCause)
  let trigModesObjId := gTrigModesStack.stack.back!.objectId
  let gTrigModesPicked0 := mustApply33i2 gTrigModesStack p0 (.chooseMode 0)
  let gTrigModesAfterLeave := gTrigModesPicked0.concede p1
  let gTrigModesFinalize0 :=
    (gTrigModesAfterLeave.change (.pending .none)).runPostStep
      (.resumeTriggerModesAfterLeave p0 trigModesObjId 0 #[1, 2])
  let trigModesRevalOk :=
    gTrigModesAfterLeave.pending == .fraChoice p0 (.triggerModes trigModesObjId 2 #[]) &&
    gTrigModesFinalize0.pending == .none &&
    (gTrigModesFinalize0.stack.find? (·.objectId == trigModesObjId)).any (·.targetsAnnounced)

  -- (iii) `.resumeUpToTriggerModesAfterLeave` and `.resumeHawkeyeModesAfterLeave`:
  --       when `chosen` contained invalidated mode `0`, `validChosen` filters out `0` (re-opening when
  --       another legal mode remains choosable, or finalizing `validChosen` when none remain):
  let gUpToReopen :=
    ((gTrigModesAfterLeave.change (.pushContinuationFrame {})).change (.pending .none)).runPostStep
      (.resumeUpToTriggerModesAfterLeave p0 trigModesObjId 0 #[0, 1])
  let gUpToFilter :=
    ((gTrigModesAfterLeave.change (.pushContinuationFrame {})).change (.pending .none)).runPostStep
      (.resumeUpToTriggerModesAfterLeave p0 trigModesObjId 0 #[0, 1, 2])
  let gHkNoCreatures := g3
  let gHkStack :=
    gHkNoCreatures.putReflexiveTrigger p0 none
      { resolution? := some (.mshReflexive .trickArrows 2), phrase := "Choose up to 2 Trick Arrows modes" }
  let hkObjId := gHkStack.stack.back!.objectId
  -- Mode 0 (`Net — target creature`) is illegal on empty battlefield while mode 2 (`Boomerang`) is legal:
  let gHkFiltered :=
    (gHkStack.change (.pending .none)).runPostStep (.resumeHawkeyeModesAfterLeave p0 hkObjId 1 #[0, 2])
  let upToAndHkFilterOk :=
    gUpToReopen.pending == .fraChoice p0 (.upToTriggerModes trigModesObjId 1 #[1]) &&
    gUpToFilter.pending == .none &&
    gUpToFilter.chosenModesOf (gUpToFilter.object! trigModesObjId) == #[1, 2] &&
    gHkFiltered.pending == .none &&
    gHkFiltered.chosenModesOf (gHkFiltered.object! hkObjId) == #[2]

  -- 2c. `.restorePending` proposal-cost `proposalCostPromptStillPayable`, 2HG attacker
  --     `.assignCombatDamage`, and `unlessPaysDue` flushing:
  let gRestoreDeadCost :=
    gLeftP1.resumePendingReplacement (.restorePending (.discardForAdditionalCost p1) false none #[])
  -- `.assignCombatDamage q true`: departed `q` with no living teammate needing assignment clears
  -- `pendingBlockerAssignments` and logs CR 800.4j, whereas living `q` without needing assignment
  -- keeps `pendingBlockerAssignments` untouched and does NOT log CR 800.4j:
  let p0BearId := p0Bear.id
  let dummyAsgn : CreatureCombatAssignment := { source := p0BearId, toCreatures := #[], toPlayer := 2 }
  let gWithAsgnLiving := gBase.change (.pendingBlockerAssignments #[dummyAsgn])
  let gRestoreLivingAtk :=
    gWithAsgnLiving.resumePendingReplacement (.restorePending (.assignCombatDamage p0 true) false none #[])
  let gWithAsgnDead := (gWithAsgnLiving.playerLeavesGame p0).change (.pendingBlockerAssignments #[dummyAsgn])
  let gRestoreDeadAtk :=
    gWithAsgnDead.resumePendingReplacement (.restorePending (.assignCombatDamage p0 true) false none #[])
  -- 2HG (`areTeammates p0 p1`): when `p0` departed and living teammate `p1` controls a multi-blocked
  -- attacker needing assignment, `.restorePending (.assignCombatDamage p0 true)` hands off to `p1` (CR 800.4h):
  let g2HG0 := mkTwoHeadedGiant18 3302
  let g2HG1 :=
    addPermanent (addPermanent (addPermanent g2HG0 bear p1 p1) bear p2 p2) hero p2 p2
  let p1AtkId := (g2HG1.permanentsOf p1)[0]!.id
  let b1Id := (g2HG1.permanentsOf p2)[0]!.id
  let b2Id := (g2HG1.permanentsOf p2)[1]!.id
  let g2HGCombat :=
    (((g2HG1.record (GameEvent.attacked g2HG1.turnNumber p1 (g2HG1.snapshot (g2HG1.object! p1AtkId)) p2)).record
      (GameEvent.blockersDeclared g2HG1.turnNumber p2
        #[(g2HG1.snapshot (g2HG1.object! b1Id), p1AtkId), (g2HG1.snapshot (g2HG1.object! b2Id), p1AtkId)])).record
      (GameEvent.becameBlocked g2HG1.turnNumber (g2HG1.snapshot (g2HG1.object! p1AtkId)) #[b1Id, b2Id])).playerLeavesGame p0
  let g2HGHandoff :=
    g2HGCombat.resumePendingReplacement (.restorePending (.assignCombatDamage p0 true) false none #[])
  -- `unlessPaysDue` flushing in `.restorePending` when `p1` left via `playerLeavesGame`:
  let gUnless0 :=
    ((gBase.change (.pushContinuationFrame {
      unlessPaysInstead := some (Effect.gainLife 3)
      unlessPaysController := p0
    })).change (.pending (.payOrLetCounter p1 2 none)))
  let p0LifeBefore := (gUnless0.player p0).life
  let gUnlessLeft := (gUnless0.change (.pending .none)).playerLeavesGame p1
  let gUnlessRestored :=
    gUnlessLeft.resumePendingReplacement (.restorePending (.payOrLetCounter p1 2 none) false none #[p1])

  let restorePendingCompleteOk :=
    gRestoreDeadCost.pending == .none &&
    gRestoreLivingAtk.pending == .none &&
    gRestoreLivingAtk.pendingBlockerAssignments == #[dummyAsgn] &&
    !gRestoreLivingAtk.log.any (·.endsWith "(CR 800.4j)") &&
    gRestoreDeadAtk.pending == .none &&
    gRestoreDeadAtk.pendingBlockerAssignments.isEmpty &&
    gRestoreDeadAtk.log.any (· == "no active player assigns combat damage (CR 800.4j)") &&
    g2HGHandoff.pending == .assignCombatDamage p1 true &&
    g2HGHandoff.log.any (·.endsWith "assigns combat damage (CR 800.4h)") &&
    gUnlessRestored.pending == .none &&
    !gUnlessRestored.unlessPaysDue &&
    (gUnlessRestored.player p0).life == p0LifeBefore + 3

  mustHold33i2 "2a.departedSeatGuardsOk" departedSeatGuardsOk &&
  mustHold33i2 "2b.modalSpellClearedOk" modalSpellClearedOk &&
  mustHold33i2 "2b.trigModesRevalOk" trigModesRevalOk &&
  mustHold33i2 "2b.upToAndHkFilterOk" upToAndHkFilterOk &&
  mustHold33i2 "2c.restorePendingCompleteOk" restorePendingCompleteOk &&
  mustHold33i2 "2.replay"
    (replayOk33i2 #[gLeftP1, gP0TrigAwaiting, gTargetPostDeparted, gTargetPostWrongSeat,
      gTargetOtherPropLive, gTargetOwnPropGone, gTargetOtherPropGone,
      gTargetOwnSeatWithTrig, gTargetOwnSeatAnnounced,
      gTargetOwnP2SeatWithTrig, gTargetOwnP2SeatAnnounced,
      gTargetOtherPropGoneWithTrig, gTargetOtherAnnouncedA,
      gTargetOtherCasterSameSeat, gTargetOtherAnnouncedB,
      gNoLegalOwnRemoved, gNoLegalOtherRemoved,
      gPlainRevWithTrig, gPlainRevAnnounced, gPlainRevNoWt,
      gOverAlwaysGrantCont, gOverAlwaysGrantFlat, gOverPlainRevCont, gOverPlainRevFlat,
      gOverOtherSeatLeave, gOverAfterTrigBracketed, gOverAfterTrigDirect,
      gModePostDeparted, gUpToPostDeparted, gHkPostDeparted,
      gModal0, gModalCast, gModalPicked0, gModalAfterLeave,
      gTrigModes0, gTrigModesStack, gTrigModesPicked0, gTrigModesAfterLeave, gTrigModesFinalize0,
      gUpToReopen, gUpToFilter, gHkStack, gHkFiltered,
      gRestoreDeadCost, gRestoreLivingAtk, gRestoreDeadAtk, g2HGCombat, g2HGHandoff, gUnlessRestored])

end Phase33Item2EventAlignment

/-! ### Phase 33 Item 3: `redirectPendingAfterLeave` `q != p` proposal-cost, `.mayAttachEquipment`, `.payWard`, staged-retarget, and `--norandom` `AfterRandom` revalidation -/
section Phase33Item3EventAlignment

private def mustHold33i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase33Item3EventAlignment failed: {label}"

private def replayOk33i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustApply33i3 (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! s!"Phase33Item3EventAlignment apply failed: {e}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent (addPermanent g3 bear p0 p0) hero p1 p1) bear p2 p2
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p1Hero := (gBase.permanentsOf p1).find? (·.name == hero.name) |>.get!
  let p2Bear := (gBase.permanentsOf p2).find? (·.name == bear.name) |>.get!

  -- 3a. `redirectPendingAfterLeave` `q != p` proposal-cost revalidation (`.crew` / `.chooseTeamworkCreatures`):
  --     `p0` steals `p1`'s Vehicle (`crew := some 2`) and activates Crew; while `Pending.fraChoice p0 (.crew ...)`
  --     is open, `p1` concedes, removing the Vehicle! `resumeProposalCostAfterLeave` reverses `p0`'s proposal!
  --     Conversely, if `p0` owns the Vehicle and still controls `p0Bear` (power 2), `p1` conceding keeps `.crew` open!
  let vehicleDef : CardDef := {
    name := "P33 Skiff"
    manaCost := ManaCost.empty
    types := #[.artifact]
    subtypes := #["Vehicle"]
    power := some 3
    toughness := some 3
    keywords := #[.crew 2]
  }
  let gStolenVeh0 := addPermanent gBase vehicleDef p1 p0
  let stolenVehId := (gStolenVeh0.permanentsOf p0).find? (·.name == "P33 Skiff") |>.get!.id
  let gCrewStolen := mustApply33i3 gStolenVeh0 p0 (.activate stolenVehId 0)
  let gCrewStolenAfterLeave := gCrewStolen.concede p1
  -- When `.resumeProposalCostAfterLeave` reverses a living caster's proposal inside `.seq first rest`,
  -- `checkReversal` stops un-checkpointed proposal tails (`gCrewSeqTail`), while a pre-proposal
  -- continuation saved in `proposalCheckpoint` (`gCrewCkptAfterLeave`) runs once via `reverseProposedSpell`:
  let gStolenVehWithCont :=
    gStolenVeh0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.finishPostStep (.applyPlusOneAfterSearch p0Bear.id p0 none))) ]
  let gCrewCkptAfterLeave := (mustApply33i3 gStolenVehWithCont p0 (.activate stolenVehId 0)).concede p1
  let savedCrewPending := gCrewStolen.pending
  let (gCrewVehGone, _) := (gCrewStolen.change (.pending .none)).move stolenVehId .exile none (cause := some testCause)
  let gCrewSeqTail :=
    gCrewVehGone.resumePendingReplacement
      (.seq (.finishPostStep (.resumeProposalCostAfterLeave p0 savedCrewPending))
            (.finishPostStep (.applyPlusOneAfterSearch p0Bear.id p0 none)))

  let gOwnVeh0 := addPermanent gBase vehicleDef p0 p0
  let ownVehId := (gOwnVeh0.permanentsOf p0).find? (·.name == "P33 Skiff") |>.get!.id
  let gCrewOwn := mustApply33i3 gOwnVeh0 p0 (.activate ownVehId 0)
  let gCrewOwnAfterLeave := gCrewOwn.concede p1

  let proposalCostLeaveOk :=
    (match gCrewStolen.pending with | .fraChoice q (.crew _ vid 2) => q == p0 && vid == stolenVehId | _ => false) &&
    gCrewStolenAfterLeave.pending == .none &&
    gCrewStolenAfterLeave.proposedSpell.isNone &&
    gCrewStolenAfterLeave.stack.isEmpty &&
    gCrewCkptAfterLeave.proposedSpell.isNone &&
    (gCrewCkptAfterLeave.object! p0Bear.id).status.plusOnePlusOne == 1 &&
    gCrewSeqTail.proposedSpell.isNone &&
    (gCrewSeqTail.object! p0Bear.id).status.plusOnePlusOne == 0 &&
    (match gCrewOwnAfterLeave.pending with | .fraChoice q (.crew _ vid 2) => q == p0 && vid == ownVehId | _ => false) &&
    gCrewOwnAfterLeave.proposedSpell.isSome

  -- 3b. `.mayAttachEquipment`, `.payWard`, and multi-slot staged target reversion (`q != p`):
  let equipDef : CardDef := {
    name := "P33 Blade"
    manaCost := ManaCost.empty
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  -- (i) `.mayAttachEquipment`: when `p0` only controls a stolen Equipment owned by `p1`, `p1` leaving cancels;
  --     when `p0` controls their own Equipment and `hostId` is `p2`'s creature (`!g.controlledBy o p0`), it stays open!
  let gEquipStolen :=
    ((addPermanent gBase equipDef p1 p0).change (.pushContinuationFrame {})).change
      (.pending (.mayAttachEquipment p0 p0Bear.id none))
  let gEquipStolenGone := gEquipStolen.concede p1
  let gEquipOwnOnP2 :=
    ((addPermanent gBase equipDef p0 p0).change (.pushContinuationFrame {})).change
      (.pending (.mayAttachEquipment p0 p2Bear.id none))
  let gEquipOwnKept := gEquipOwnOnP2.concede p1

  -- (ii) `.payWard` (`q != p`):
  --      - when `spellId` left the stack with `p1`, `.payWard p0 spellId ...` clears to `.none`;
  --      - when `cost == .sacrificePermanents 1 1 #[p0Bear.id]` (`paid > 0`) and `p0`'s only other permanent
  --        was stolen from `p1`, `p1` leaving logs `"cannot finish paying ward"` and counters `spellId`!
  let simpleAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gP1AbStack := gBase.putTriggeredAbilityOnStack p1 p1Hero simpleAb "triggers" (eventCause := some testCause)
  let p1AbId := gP1AbStack.stack.back!.objectId
  let gWardSpellGone :=
    ((gP1AbStack.change (.pushContinuationFrame {})).change
      (.pending (.payWard p0 p1AbId (CostSpec.ofGeneric 1)))).concede p1

  let gP0AbStack := (addPermanent gBase bear p1 p0).putTriggeredAbilityOnStack p0 p0Bear simpleAb "triggers" (eventCause := some testCause)
  let p0AbId := gP0AbStack.stack.back!.objectId
  let gWardPartialUnpayable :=
    ((gP0AbStack.change (.pushContinuationFrame {})).change
      (.pending (.payWard p0 p0AbId (CostSpec.sacrificePermanents 2) #[p0Bear.id]))).concede p1

  -- (iii) Multi-slot staged target reversion on `.mayChangeSpellTarget` and `.newTargetsForCopySlot`:
  let twoTargetSpell : CardDef := {
    name := "P33 Twin Tap"
    manaCost := ManaCost.empty
    types := #[.sorcery]
    spellEffect := some {
      body := .chooseModes {
        maxModes := .const 2
        modes := #[
          { targeting := .of .creature, body := Instruction.tap (.target 0), phrase := "Tap first creature" },
          { targeting := .of .creature, body := Instruction.tap (.target 0), phrase := "Tap second creature" }
        ]
      }
    }
  }
  let gTwin0 := insertObject gBase twoTargetSpell p0 (.hand p0)
  let handTwinId := (gTwin0.player p0).hand.back!
  let (gTwin1, twinId) := gTwin0.move handTwinId .stack (some p0) (cause := some testCause)
  let gTwinOnStack :=
    gTwin1.change (.pushStack {
      objectId := twinId
      controller := p0
      targets := #[Target.permanent p0Bear.id, Target.permanent p2Bear.id]
      targetsAnnounced := true
    })
  -- Staged slot 0 was retargeted to `p1Hero.id` (which leaves with `p1`), while slot 1 is still `p2Bear.id`:
  let stagedBefore := #[Target.permanent p1Hero.id, Target.permanent p2Bear.id]
  let gRetargetAfterLeave :=
    ((gTwinOnStack.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.mayChangeSpellTarget twinId 1 stagedBefore)))).concede p1
  let gCopySlotAfterLeave :=
    ((gTwinOnStack.change (.pushContinuationFrame {})).change
      (.pending (.fraChoice p0 (.newTargetsForCopySlot #[twinId] 1 stagedBefore)))).concede p1

  let equipWardAndRetargetOk :=
    gEquipStolenGone.pending == .none && gEquipStolenGone.continuations.isEmpty &&
    gEquipOwnKept.pending == .mayAttachEquipment p0 p2Bear.id none &&
    gWardSpellGone.pending == .none && gWardSpellGone.continuations.isEmpty &&
    gWardPartialUnpayable.pending == .none &&
    (gWardPartialUnpayable.findObject? p0AbId).isNone &&
    gWardPartialUnpayable.log.any (·.endsWith "cannot finish paying ward") &&
    gRetargetAfterLeave.pending == .fraChoice p0
      (.mayChangeSpellTarget twinId 1 #[Target.permanent p0Bear.id, Target.permanent p2Bear.id]) &&
    gCopySlotAfterLeave.pending == .fraChoice p0
      (.newTargetsForCopySlot #[twinId] 1 #[Target.permanent p0Bear.id, Target.permanent p2Bear.id])

  -- 3c. `AfterRandom.player?`, `--norandom` `.resolveRandom` (`PostStep.runAfterRandom` &
  --     `autoResolveSingleChooseObject`), `resolveRandomCreatureReveal`, and `Actions.rawActor` `.outside`:
  let afterRandomPlayerOk :=
    AfterRandom.none.player? == Option.none &&
    (AfterRandom.draw p0 1).player? == some p0 &&
    (AfterRandom.gainLife p1 2).player? == some p1 &&
    (AfterRandom.revealRandomCreatureThenBottom p0 #[]).player? == some p0 &&
    (AfterRandom.putOnTop p1 #[]).player? == some p1 &&
    (AfterRandom.beholdUntap p0 p0Bear.id .elf).player? == some p0 &&
    (AfterRandom.plusOne p0Bear.id p2 none).player? == some p2 &&
    (AfterRandom.discardRandom p1).player? == some p1
  -- `.shuffleLibrary p1` with `afterRandom == .plusOne p0Bear.id p0 none`: when `p1` concedes (`q == p`),
  -- `PostStep.runAfterRandom` runs `.plusOne` so `p0Bear` gets `+1/+1` and `afterRandom == .none`!
  let gShufRunAfter :=
    ((gBase.change (.pushContinuationFrame {})).changes #[
      .pending (.resolveRandom (.shuffleLibrary p1)),
      .afterRandom (.plusOne p0Bear.id p0 none) ]).concede p1
  -- `.shuffleLibrary p0` with `afterRandom == .draw p1 1`: when `p1` concedes (`q != p`),
  -- `afterRandom` is cleared to `.none` while `shuffleLibrary p0` stays open:
  let gShufDropAfter :=
    ((gBase.change (.pushContinuationFrame {})).changes #[
      .pending (.resolveRandom (.shuffleLibrary p0)),
      .afterRandom (.draw p1 1) ]).concede p1
  -- `.chooseObject #[p0HandId, p1HandId]` with `afterRandom == .discardRandom p0`: when `p1` concedes,
  -- `liveIds` shrinks to `#[p0HandId]` (`size == 1`) and `autoResolveSingleChooseObject` discards `p0HandId`!
  let p0HandId := (gBase.player p0).hand[0]!
  let p1HandId := (gBase.player p1).hand[0]!
  let gChooseObjAuto :=
    ((gBase.change (.pushContinuationFrame {})).changes #[
      .pending (.resolveRandom (.chooseObject #[p0HandId, p1HandId])),
      .afterRandom (.discardRandom p0) ]).concede p1
  -- `resolveRandomCreatureReveal` filters vanished cards owned by departed `p1` out of `revealed`:
  let p0LibTop := (gBase.player p0).library.back!
  let p1LibTop := (gBase.player p1).library.back!
  let gLeftP1 := gBase.playerLeavesGame p1
  let gRevealFiltered := gLeftP1.resolveRandomCreatureReveal p0 #[p0Bear.id, p0LibTop, p1LibTop] p0Bear.id
  -- Surviving creature (`p0Bear`) still gets its `.plusOne` counter when former controller `p1` left,
  -- in both `finishAfterRandom` and `PostStep.runAfterRandom`, while `PostStep.runAfterRandom` skips
  -- `.gainLife` for departed `p1`:
  let gFinishPlusOneDeparted :=
    ((gLeftP1.change (.pushContinuationFrame {})).change
      (.afterRandom (.plusOne p0Bear.id p1 none))).finishAfterRandom false
  let gPostRunPlusOneDeparted :=
    gLeftP1.runPostStep (.runAfterRandom (.plusOne p0Bear.id p1 none))
  let p1LifeDeadBefore := (gLeftP1.player p1).life
  let gPostRunGainDeparted :=
    gLeftP1.runPostStep (.runAfterRandom (.gainLife p1 5))
  -- `Actions.rawActor` on `.resolveRandom (.orderInto #[] (.outside p2) none)` returns `some p2`:
  let gOrderOutside := gBase.change (.pending (.resolveRandom (.orderInto #[] (.outside p2) none)))

  let norandomRevalOk :=
    afterRandomPlayerOk &&
    gShufRunAfter.pending == .none &&
    gShufRunAfter.afterRandom == .none &&
    (gShufRunAfter.object! p0Bear.id).status.plusOnePlusOne == 1 &&
    (gFinishPlusOneDeparted.object! p0Bear.id).status.plusOnePlusOne == 1 &&
    (gPostRunPlusOneDeparted.object! p0Bear.id).status.plusOnePlusOne == 1 &&
    (gPostRunGainDeparted.player p1).life == p1LifeDeadBefore &&
    gShufDropAfter.pending == .resolveRandom (.shuffleLibrary p0) &&
    gShufDropAfter.afterRandom == .none &&
    gChooseObjAuto.pending == .none &&
    gChooseObjAuto.afterRandom == .none &&
    !(gChooseObjAuto.player p0).hand.contains p0HandId &&
    !(gRevealFiltered.player p0).library.contains p1LibTop &&
    gOrderOutside.rawActor == some p2

  mustHold33i3 "3a.proposalCostLeaveOk" proposalCostLeaveOk &&
  mustHold33i3 "3b.equipWardAndRetargetOk" equipWardAndRetargetOk &&
  mustHold33i3 "3c.norandomRevalOk" norandomRevalOk &&
  mustHold33i3 "3.replay"
    (replayOk33i3 #[gCrewStolen, gCrewStolenAfterLeave, gCrewCkptAfterLeave, gCrewSeqTail, gCrewOwn, gCrewOwnAfterLeave,
      gEquipStolenGone, gEquipOwnKept, gWardSpellGone, gWardPartialUnpayable,
      gTwinOnStack, gRetargetAfterLeave, gCopySlotAfterLeave,
      gShufRunAfter, gFinishPlusOneDeparted, gPostRunPlusOneDeparted, gPostRunGainDeparted,
      gShufDropAfter, gChooseObjAuto, gRevealFiltered, gOrderOutside])

end Phase33Item3EventAlignment

/-! ### Phase 33 Item 4: `stillInGame` guards (`playerCanBeTargetedBy`, `emptyManaPools`, `finishProliferate`, `canPayLife`) and Layer 1 `g.name` / `originalSnapshot.name` reads -/
section Phase33Item4EventAlignment

private def mustHold33i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase33Item4EventAlignment failed: {label}"

private def replayOk33i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def mustApply33i4 (g : Game) (p : PlayerId) (a : Action) : Game :=
  match g.apply p a with
  | .ok g' => g'
  | .error e => panic! s!"Phase33Item4EventAlignment apply failed: {e}"

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent (addPermanent g3 bear p0 p0) forest p1 p1) bear p2 p2

  -- 4a. `g.stillInGame` guards in `playerCanBeTargetedBy`, `playerLeavesGameCore` + `emptyManaPools`,
  --     `finishProliferate` + `finishProliferateLoop`, and `canPayLife`:
  let gP1WithMana :=
    (gBase.addMana p1 (.colored .green) 1).addPlayerCounters p1 .poison 1
  let preLeaveEvents := gP1WithMana.events.size
  let gP1Departed := gP1WithMana.concede p1
  let emptiedOnLeave :=
    (gP1Departed.events.extract preLeaveEvents gP1Departed.events.size).any fun e =>
      match e.change with
      | .rules (.player (.manaEmptied pid _)) => pid == p1
      | _ => false
  let preStepEmptyIdx := gP1Departed.events.size
  let gAfterEmptyPools := gP1Departed.emptyManaPools
  let noRepeatDepartedEmpty :=
    !(gAfterEmptyPools.events.extract preStepEmptyIdx gAfterEmptyPools.events.size).any fun e =>
      match e.change with
      | .rules (.player (.manaEmptied pid _)) => pid == p1
      | _ => false

  let gProlifPrompt :=
    (gP1Departed.change (.pushContinuationFrame {})).change (.pending (.chooseProliferate p0 1))
  let prolifRejectsDeparted :=
    match gProlifPrompt.finishProliferate p0 #[Target.player p1] with
    | .error msg => mentions msg "is no longer in the game (CR 701.34a / 800.4a)"
    | .ok _ => false
  let p1PoisonBefore := (gP1Departed.player p1).poison
  let gProlifLoopSkips :=
    gP1Departed.withBatch (some testCause) fun g =>
      g.finishProliferateLoop p0 #[Target.player p1] #[] #[] false 0 (some testCause)

  let stillInGameChecksOk :=
    gBase.playerCanBeTargetedBy p0 p1 none &&
    !gP1Departed.playerCanBeTargetedBy p0 p1 none &&
    emptiedOnLeave &&
    (gP1Departed.player p1).manaPool.isEmpty &&
    noRepeatDepartedEmpty &&
    prolifRejectsDeparted &&
    (gProlifLoopSkips.player p1).poison == p1PoisonBefore &&
    gBase.canPayLife p1 0 &&
    !gP1Departed.canPayLife p1 0

  -- 4b. Layer 1 `g.name` / `pr.originalSnapshot.name` queries in `FraHelpers`, `CastExtras`,
  --     `ResolutionHelpers`, `StateBasedActions`, and `FraChoices`:
  let sphinxCopyDef : CardDef := { bear with name := "Sphinx's Approach" }
  let cloneCardDef : CardDef := { bear with name := "Cloned Illusion" }
  let gGy0 := insertObject gBase bear p0 (.graveyard p0)
  let gyId := (gGy0.player p0).graveyard.back!
  let gGySphinx := gGy0.createEffect (ContinuousEffectSpec.copy gyId sphinxCopyDef) (cause := some testCause)

  let p0BearId := (gBase.permanentsOf p0)[0]!.id
  let gSrcCopied := gBase.createEffect (ContinuousEffectSpec.copy p0BearId cloneCardDef) (cause := some testCause)

  let gHand0 := insertObject gBase bear p2 (.hand p2)
  let p2HandId := (gHand0.player p2).hand.back!
  let gHandCopied := gHand0.createEffect (ContinuousEffectSpec.copy p2HandId cloneCardDef) (cause := some testCause)
  let gDiscRevealed := gHandCopied.discardNonlandFrom p0 p2

  let p0TopLibId := (gBase.player p0).library.back!
  let gLibCopied := gBase.createEffect (ContinuousEffectSpec.copy p0TopLibId cloneCardDef) (cause := some testCause)
  let gMilled := gLibCopied.mill p0 1 (cause := some testCause)

  let gExile0 := insertObject gBase bear p0 .exile
  let exId := (gExile0.objects.filter (fun o => o.owner == p0 && o.zone == .exile))[0]!.id
  let gExCopied := gExile0.createEffect (ContinuousEffectSpec.copy exId cloneCardDef) (cause := some testCause)
  let gMovedToHand :=
    gExCopied.withBatch (some testCause) fun g =>
      g.movePublicCardsToHandLoop p0 #[exId] 1 true (some testCause)

  -- Token outside battlefield (`CR 704.5d`) logs its Layer 1 copy name before `ceaseToExist`:
  let (gTok0, tok) := gBase.createOneToken p0 { bear with name := "Printed Cub", isToken := true } (cause := some testCause)
  let gTokCopied := gTok0.createEffect (ContinuousEffectSpec.copy tok.id cloneCardDef) (cause := some testCause)
  let (gTokGy, tokGyId) := gTokCopied.move tok.id (.graveyard p0) none (cause := some testCause)
  let gTokGyCopied := gTokGy.createEffect (ContinuousEffectSpec.copy tokGyId cloneCardDef) (cause := some testCause)
  let gAfterSba := gTokGyCopied.checkSBA

  -- `FraChoices` `.zemoBoastExile`: when `sourceId` left the battlefield before choosing exiled cards,
  -- `pr.originalSnapshot.name` supplies the Layer 1 name (`"Cloned Zemo"`) to the activated ability log!
  let blackCardDef : CardDef := {
    bear with
    name := "Black Fuel"
    manaCost := { symbols := Array.replicate 15 (.colored .black) }
  }
  let gZemo00 :=
    insertObject (addPermanent gBase bear p2 p1) blackCardDef p0 (.graveyard p0)
  let zemoSrc := (gZemo00.permanentsOf p1).back!
  let blackGyId := (gZemo00.player p0).graveyard.back!
  let cloneZemoDef : CardDef := { bear with name := "Cloned Zemo" }
  let gZemo0 :=
    (gZemo00.createEffect
      (.layered (.objects #[zemoSrc.id]) (.control p0) (.whileInZone blackGyId (.graveyard p0)))
      (cause := some testCause)).concede p1
  let gZemoCopied := gZemo0.createEffect (ContinuousEffectSpec.copy zemoSrc.id cloneZemoDef) (cause := some testCause)
  let zemoObj := gZemoCopied.object! zemoSrc.id
  let zemoSnap := gZemoCopied.snapshot zemoObj
  let (gZemoStack, abObj) := gZemoCopied.putStackAbility zemoObj p0
    (abilityEffect := some ActivatedAbility.zemoBoastAbility.effect)
  let abId := abObj.id
  let zemoProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abId
    original := zemoObj
    originalSnapshot := zemoSnap
    kind := .activatedAbility
    sourceId := some zemoSrc.id
    activation := some ActivatedAbility.zemoBoastAbility
  }
  let gZemoPrompt :=
    (gZemoStack.change (.pushContinuationFrame {})).changes #[
      .saveProposalCheckpoint,
      .proposedSpell (some zemoProp),
      .pending (.fraChoice p0 (.zemoBoastExile abId zemoSrc.id)) ]
  let gZemoActivated := mustApply33i4 gZemoPrompt p0 (.choosePermanents #[blackGyId])

  let layeredNameReadsOk :=
    gGy0.sphinxsApproachesInGraveyard p0 == #[] &&
    gGySphinx.sphinxsApproachesInGraveyard p0 == #[gyId] &&
    gSrcCopied.fraSourceName (some p0BearId) == "Cloned Illusion" &&
    gDiscRevealed.log.any (fun s => mentions s "Cloned Illusion") &&
    gMilled.log.any (·.endsWith "mills Cloned Illusion") &&
    gMovedToHand.log.any (·.endsWith "puts Cloned Illusion into their hand") &&
    gAfterSba.log.any (· == "Cloned Illusion ceases to exist (token left the battlefield)") &&
    gZemoActivated.log.any (fun s => mentions s "Cloned Zemo")

  mustHold33i4 "4a.stillInGameChecksOk" stillInGameChecksOk &&
  mustHold33i4 "4b.layeredNameReadsOk" layeredNameReadsOk &&
  mustHold33i4 "4.replay"
    (replayOk33i4 #[gP1WithMana, gP1Departed, gAfterEmptyPools, gProlifLoopSkips,
      gGySphinx, gSrcCopied, gDiscRevealed, gMilled, gMovedToHand, gAfterSba, gZemoActivated])

end Phase33Item4EventAlignment

/-! ### Phase 34 Item 1: `reverseToProposalCheckpointCore?` non-proposal modal trigger preservation, `finishFraChoice` / `finishAndGrantPriority` / `afterWardResolved` proposal reversal & `mayThenResume` / `triggerSequenceRest` ordering -/
section Phase34Item1EventAlignment

private def mustHold34i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase34Item1EventAlignment failed: {label}"

private def replayOk34i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase :=
    addPermanent
      (addPermanent
        (addPermanent (insertObject g3 bear p0 (.hand p0)) bear p0 p0)
        hero p1 p1)
      bear p2 p2
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p1Hero := (gBase.permanentsOf p1).find? (·.name == hero.name) |>.get!
  let handBoltId := (gBase.player p0).hand.back!

  -- 1a. `Core.reverseToProposalCheckpointCore?` preserves:
  --     - non-proposal modal trigger `.abilityEffect` and `TriggerQueueEvent.modeChosen` on stack, and
  --     - non-proposal modal trigger `.noLegalMode` stack removal (`ZoneEvent.moved _ .stack .command`).
  let simpleTrigAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gWithTrigs0 :=
    (gBase.putTriggeredAbilityOnStack p0 p0Bear simpleTrigAb "triggers" (eventCause := some testCause)).putTriggeredAbilityOnStack
      p0 p0Bear simpleTrigAb "triggers" (eventCause := some testCause)
  let modalTrigId := gWithTrigs0.stack[0]!.objectId
  let noLegalTrigId := gWithTrigs0.stack[1]!.objectId
  let gModalCp0 := gWithTrigs0.change .saveProposalCheckpoint
  let (gModalCp1, modalStackBoltId) := gModalCp0.move handBoltId .stack (some p0) (cause := some testCause)
  let modalBoltProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofColor .red
    spellId := modalStackBoltId
    original := gBase.object! handBoltId
    originalSnapshot := gBase.snapshot (gBase.object! handBoltId)
  }
  let gModalWithProp :=
    gModalCp1.changes #[
      .pushStack { objectId := modalStackBoltId, controller := p0, targets := #[] },
      .proposedSpell (some modalBoltProp),
      .pending (.activateManaAbilities p0) ]
  -- Install `.abilityEffect (some (Effect.gainLife 2))` and record `triggerModeChosen` on `modalTrigId`,
  -- and remove `noLegalTrigId` with `.gameRule .noLegalMode` after the checkpoint:
  let gWithModalTrig :=
    (gModalWithProp.changeObject modalTrigId (.abilityEffect (some (Effect.gainLife 2)))).record
      (GameEvent.triggerModeChosen gModalWithProp.turnNumber p0Bear.id 1 (lifetime := true)
        (cause := some (.gameRule .triggeredAbility)))
  let gWithBothModalTrigs :=
    gWithModalTrig.ceaseToExist noLegalTrigId (cause := some (.gameRule .noLegalMode))
  -- Reverse the spell proposal:
  let gReversedModal := gWithBothModalTrigs.reverseProposedSpell (resumeContinuation := false)
  let hasModeChosenEvent :=
    gReversedModal.events.any fun e =>
      match e.change with
      | .rules (.triggerQueue (.modeChosen src m lt)) => src == p0Bear.id && m == 1 && lt
      | _ => false
  let checkpointPreservationOk :=
    mustHold34i1 "1a.propNone" gReversedModal.proposedSpell.isNone &&
    mustHold34i1 "1a.handBolt" ((gReversedModal.player p0).hand.contains handBoltId) &&
    mustHold34i1 "1a.modalOnStack" (gReversedModal.stack.any (·.objectId == modalTrigId)) &&
    mustHold34i1 "1a.modalAbEff" ((gReversedModal.object! modalTrigId).abilityEffect == some (Effect.gainLife 2)) &&
    mustHold34i1 "1a.modeChosenEv" hasModeChosenEvent &&
    mustHold34i1 "1a.noLegalRemoved" (!gReversedModal.stack.any (·.objectId == noLegalTrigId)) &&
    mustHold34i1 "1a.noLegalGone" (gReversedModal.findObject? noLegalTrigId).isNone

  let gCp0 := gBase.change .saveProposalCheckpoint
  let (gCp1, stackBoltId) := gCp0.move handBoltId .stack (some p0) (cause := some testCause)
  let boltProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofColor .red
    spellId := stackBoltId
    original := gBase.object! handBoltId
    originalSnapshot := gBase.snapshot (gBase.object! handBoltId)
  }
  let gWithProp :=
    gCp1.changes #[
      .pushStack { objectId := stackBoltId, controller := p0, targets := #[] },
      .proposedSpell (some boltProp),
      .pending (.activateManaAbilities p0) ]

  -- 1b. `finishFraChoice` and `finishAndGrantPriority`:
  -- (i) Game-over (`g.over`) with an orphaned `proposedSpell` reverses the proposal to hand BEFORE
  --     `completeActiveResolutions.clearTransientPromptsOnGameOver`:
  let (gVanishedProp0, _) := gWithProp.move stackBoltId (.graveyard p0) none (cause := some testCause)
  let gVanishedProp := (gVanishedProp0.change (.removeStackEntry stackBoltId)).change (.pending .none)
  let gOverWithProp :=
    gVanishedProp.record (GameEvent.gameEnded gVanishedProp.turnNumber (.won p0))
  let gFinishFraOver := gOverWithProp.finishFraChoice
  let gFinishGrantOver := gOverWithProp.finishAndGrantPriority p0
  -- (ii) `triggerNeedingTargets` is prompted before `waitingTriggers`:
  let targTrigAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you) {
      targeting := .of .creature
      body := Instruction.tap (.target 0)
      phrase := "Tap target creature"
    }
  let gUnannouncedTrig :=
    (gBase.putTriggeredAbilityOnStack p0 p0Bear targTrigAb "triggers" (eventCause := some testCause)).changes #[
      .waitingTriggers #[{ controller := p0, source := p0Bear, ability := simpleTrigAb },
                         { controller := p0, source := p0Bear, ability := simpleTrigAb }],
      .pushContinuationFrame {},
      .pending .none ]
  let gFraPromptsTarg := gUnannouncedTrig.finishFraChoice
  let gGrantPromptsTarg := gUnannouncedTrig.finishAndGrantPriority p0
  -- (iii) Vanished `proposedSpell` (`spellId` no longer on `.stack`) is reversed by both
  --       `finishFraChoice` and `finishAndGrantPriority` (and live `proposedSpell` in
  --       `finishAndGrantPriority` pops empty top continuation frames without granting idle priority):
  let gFraRevVanished := gVanishedProp.finishFraChoice
  let gGrantRevVanished := gVanishedProp.finishAndGrantPriority p0
  let gLivePropGrant :=
    ((gWithProp.change (.pushContinuationFrame {})).change (.pending .none)).finishAndGrantPriority p0

  let finishFraAndGrantOk :=
    gFinishFraOver.over && gFinishFraOver.proposedSpell.isNone &&
    (gFinishFraOver.player p0).hand.contains handBoltId &&
    gFinishGrantOver.over && gFinishGrantOver.proposedSpell.isNone &&
    (gFinishGrantOver.player p0).hand.contains handBoltId &&
    gFraPromptsTarg.pending == .chooseTargets p0 &&
    gFraPromptsTarg.continuations.isEmpty &&
    gGrantPromptsTarg.pending == .chooseTargets p0 &&
    gGrantPromptsTarg.continuations.isEmpty &&
    gFraRevVanished.proposedSpell.isNone &&
    (gFraRevVanished.player p0).hand.contains handBoltId &&
    gGrantRevVanished.proposedSpell.isNone &&
    (gGrantRevVanished.player p0).hand.contains handBoltId &&
    gLivePropGrant.proposedSpell.isSome &&
    gLivePropGrant.continuations.isEmpty &&
    gLivePropGrant.pending == .none

  -- 1c. `Casting.afterWardResolved`:
  --     - Game-over (`g.over`) reverses orphaned `proposedSpell` before `completeActiveResolutions`;
  --     - Live `proposedSpell` returns without granting idle priority;
  --     - Vanished `proposedSpell` reverses via `reverseProposedSpell`;
  --     - `mayThenResume` + `triggerSequenceRest` drains `acceptMayThenCore` + `resumeTriggerSequence`
  --       before popping the continuation frame;
  --     - `triggerSequenceRest` resumes `resumeTriggerSequence` and drains `pendingReplacement` before popping.
  let gWardOver := gOverWithProp.afterWardResolved
  let gWardLiveProp :=
    ((gWithProp.change (.pushContinuationFrame {})).change (.pending .none)).afterWardResolved
  let gWardVanishedProp := gVanishedProp.afterWardResolved
  let trigCtx : TriggerSequenceRest := {
    controller := p0
    ability := simpleTrigAb
    sourceId := some p0Bear.id
    targets := #[]
    dividedDamage := #[]
    lastKnownPower := none
    lastKnownToughness := none
    sourceName := bear.name
    cardPower := none
    steps := [.gainLife (.fixed 4)]
  }
  let gWardMayResume :=
    ((gBase.change (.pushContinuationFrame {
      mayThenResume := true
      triggerSequenceRest := some trigCtx
    })).change (.pending .none)).afterWardResolved
  let gWardTrigSeqResume :=
    ((gBase.change (.pushContinuationFrame {
      triggerSequenceRest := some trigCtx
    })).change (.pending .none)).afterWardResolved

  let afterWardOk :=
    gWardOver.over && gWardOver.proposedSpell.isNone &&
    (gWardOver.player p0).hand.contains handBoltId &&
    gWardLiveProp.proposedSpell.isSome &&
    gWardLiveProp.continuations.isEmpty &&
    gWardLiveProp.pending == .none &&
    gWardVanishedProp.proposedSpell.isNone &&
    (gWardVanishedProp.player p0).hand.contains handBoltId &&
    (gWardMayResume.player p0).life == (gBase.player p0).life + 4 &&
    !gWardMayResume.mayThenResume &&
    gWardMayResume.continuations.isEmpty &&
    (gWardTrigSeqResume.player p0).life == (gBase.player p0).life + 4 &&
    gWardTrigSeqResume.continuations.isEmpty &&
    (gBase.object! p1Hero.id).zone == .battlefield

  mustHold34i1 "1a.checkpointPreservationOk" checkpointPreservationOk &&
  mustHold34i1 "1b.finishFraAndGrantOk" finishFraAndGrantOk &&
  mustHold34i1 "1c.afterWardOk" afterWardOk &&
  mustHold34i1 "1.replay"
    (replayOk34i1 #[gWithBothModalTrigs, gReversedModal, gFinishFraOver, gFinishGrantOver,
      gFraPromptsTarg, gGrantPromptsTarg, gFraRevVanished, gGrantRevVanished, gLivePropGrant,
      gWardOver, gWardLiveProp, gWardVanishedProp, gWardMayResume, gWardTrigSeqResume])

end Phase34Item1EventAlignment

/-! ### Phase 34 Item 2: `proposalCostPromptStillPayable`, `.restorePending` departed-seat ordering, and `.resume*AfterLeave` game-over / vanished-proposal guards -/
section Phase34Item2EventAlignment

private def mustHold34i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase34Item2EventAlignment failed: {label}"

private def replayOk34i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase :=
    addPermanent
      (addPermanent (insertObject g3 bear p0 (.hand p0)) bear p0 p0)
      bear p1 p1
  let handBoltId := (gBase.player p0).hand.back!
  let p0Bear := (gBase.permanentsOf p0)[0]!

  -- 2a. `proposalCostPromptStillPayable`:
  --     Requires `!g.over && g.stillInGame caster` and a matching `g.proposedSpell` whose `spellId`
  --     is still on `.stack` (or on `.battlefield` for `.turnFaceUp`).
  let gCp0 := gBase.change .saveProposalCheckpoint
  let (gCp1, stackBoltId) := gCp0.move handBoltId .stack (some p0) (cause := some testCause)
  let boltProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.ofColor .red
    spellId := stackBoltId
    original := gBase.object! handBoltId
    originalSnapshot := gBase.snapshot (gBase.object! handBoltId)
  }
  let gLiveProp :=
    gCp1.changes #[
      .pushStack { objectId := stackBoltId, controller := p0, targets := #[] },
      .proposedSpell (some boltProp) ]
  let gOverLiveProp := gLiveProp.record (GameEvent.gameEnded gLiveProp.turnNumber (.won p0))
  let (gVanished0, _) := gLiveProp.move stackBoltId (.graveyard p0) none (cause := some testCause)
  let gVanishedProp := gVanished0.change (.removeStackEntry stackBoltId)
  let gOverProp := gVanishedProp.record (GameEvent.gameEnded gVanishedProp.turnNumber (.won p0))
  let gTurnFaceUpProp :=
    gBase.change (.proposedSpell (some {
      caster := p0
      cost := ManaCost.empty
      spellId := p0Bear.id
      original := p0Bear
      originalSnapshot := gBase.snapshot p0Bear
      kind := .turnFaceUp
    }))
  let (gTurnFaceUpGone0, _) := gTurnFaceUpProp.move p0Bear.id (.graveyard p0) none (cause := some testCause)
  let gRestoreVanishedCost :=
    gVanishedProp.resumePendingReplacement (.restorePending (.discardForAdditionalCost p0) false none #[])

  let proposalCostPayableOk :=
    gLiveProp.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    !gLiveProp.proposalCostPromptStillPayable p1 (.discardForAdditionalCost p1) &&
    !gBase.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    !gOverLiveProp.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    !gVanishedProp.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    gTurnFaceUpProp.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    !gTurnFaceUpGone0.proposalCostPromptStillPayable p0 (.discardForAdditionalCost p0) &&
    gRestoreVanishedCost.proposedSpell.isNone &&
    (gRestoreVanishedCost.player p0).hand.contains handBoltId

  -- 2b. `resumePendingReplacement` `.restorePending` departed-seat ordering:
  --     When `saved` has `promptSeat? == some p1` and `!g.stillInGame p1`, `effectiveDeparted`
  --     prepends `p1` (`#[p1] ++ departed.filter (· != p1)`) even when `departed` was `#[p2]`!
  let gLeftP1 := gBase.playerLeavesGame p1
  let gRestoreDepartedSeat :=
    ((gLeftP1.change (.pushContinuationFrame {})).change (.pending .none)).resumePendingReplacement
      (.restorePending (.mayDiscardDraw p1 1) false none #[p2])
  let departedSeatOrderOk :=
    gRestoreDepartedSeat.pending == .none &&
    gRestoreDepartedSeat.continuations.isEmpty &&
    gRestoreDepartedSeat.log.any (·.endsWith "declines (CR 800.4f)")

  -- 2c. `runPostStep` (`.resumeChooseModeAfterLeave`, `.resumeChooseTargetsAfterLeave`,
  --     `.resumeTriggerModesAfterLeave`, `.resumeUpToTriggerModesAfterLeave`,
  --     `.resumeHawkeyeModesAfterLeave`, and `.resumeProposalCostAfterLeave`):
  --     - Game-over (`g.over`) reverses any orphaned `proposedSpell` before `completeActiveResolutions`;
  --     - Departed `p1` tears down via `finishFraChoice` without re-opening `.fraChoice` or emitting
  --       post-departure announcements or stack removals;
  --     - Living `p0` with vanished `proposedSpell` reverses in `.resumeChooseModeAfterLeave`,
  --       `.resumeChooseTargetsAfterLeave`, and `.resumeProposalCostAfterLeave`.
  let gOverModePost := gOverProp.runPostStep (.resumeChooseModeAfterLeave p0)
  let gOverTargPost := gOverProp.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gOverTrigModePost := gOverProp.runPostStep (.resumeTriggerModesAfterLeave p0 stackBoltId 1 #[])
  let gOverUpToModePost := gOverProp.runPostStep (.resumeUpToTriggerModesAfterLeave p0 stackBoltId 1 #[])
  let gOverHkModePost := gOverProp.runPostStep (.resumeHawkeyeModesAfterLeave p0 stackBoltId 1 #[])
  let gOverCostPost := gOverProp.runPostStep (.resumeProposalCostAfterLeave p0 (.discardForAdditionalCost p0))

  let simpleTrigAb : TriggeredAbility := TriggeredAbility.mkTrigger (.gainLife .you) (Effect.gainLife 1)
  let gP1TrigStack :=
    gBase.putTriggeredAbilityOnStack p1 (gBase.permanentsOf p1)[0]! simpleTrigAb "triggers" (eventCause := some testCause)
  let p1TrigId := gP1TrigStack.stack.back!.objectId
  let gP1TrigLeft :=
    (gP1TrigStack.record (GameEvent.playerLeftGame gP1TrigStack.turnNumber p1)).changes #[
      .pushContinuationFrame {},
      .pending .none ]
  let gDepartedTrigModes :=
    gP1TrigLeft.runPostStep (.resumeTriggerModesAfterLeave p1 p1TrigId 1 #[])
  let gDepartedUpToModes :=
    gP1TrigLeft.runPostStep (.resumeUpToTriggerModesAfterLeave p1 p1TrigId 1 #[])
  let gDepartedHkModes :=
    gP1TrigLeft.runPostStep (.resumeHawkeyeModesAfterLeave p1 p1TrigId 1 #[])

  let gVanishedModePost := gVanishedProp.runPostStep (.resumeChooseModeAfterLeave p0)
  let gVanishedTargPost := gVanishedProp.runPostStep (.resumeChooseTargetsAfterLeave p0)
  let gVanishedCostPost := gVanishedProp.runPostStep (.resumeProposalCostAfterLeave p0 (.discardForAdditionalCost p0))

  let resumePostStepsOk :=
    mustHold34i2 "2c.overPostSteps"
      ((#[gOverModePost, gOverTargPost, gOverTrigModePost, gOverUpToModePost, gOverHkModePost, gOverCostPost]).all
        (fun g => g.over && g.proposedSpell.isNone && (g.player p0).hand.contains handBoltId)) &&
    mustHold34i2 "2c.departedTrigModes"
      ((#[gDepartedTrigModes, gDepartedUpToModes, gDepartedHkModes]).all
        (fun g => g.pending == .none && g.continuations.isEmpty && g == gP1TrigLeft.finishFraChoice)) &&
    mustHold34i2 "2c.vanishedPostSteps"
      ((#[gVanishedModePost, gVanishedTargPost, gVanishedCostPost]).all
        (fun g => g.proposedSpell.isNone && (g.player p0).hand.contains handBoltId))

  mustHold34i2 "2a.proposalCostPayableOk" proposalCostPayableOk &&
  mustHold34i2 "2b.departedSeatOrderOk" departedSeatOrderOk &&
  mustHold34i2 "2c.resumePostStepsOk" resumePostStepsOk &&
  mustHold34i2 "2.replay"
    (replayOk34i2 #[gLiveProp, gOverLiveProp, gOverProp, gVanishedProp, gRestoreVanishedCost, gRestoreDepartedSeat,
      gOverModePost, gOverTargPost, gOverTrigModePost, gOverUpToModePost, gOverHkModePost, gOverCostPost,
      gDepartedTrigModes, gDepartedUpToModes, gDepartedHkModes,
      gVanishedModePost, gVanishedTargPost, gVanishedCostPost])

end Phase34Item2EventAlignment

/-! ### Phase 34 Item 3: `sourceStillPayable` (`removePlusOneX`), `isProposalAbortedByLeave` (`sourceId`), and `redirectPendingAfterLeave` cleanup -/
section Phase34Item3EventAlignment

private def mustHold34i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase34Item3EventAlignment failed: {label}"

private def replayOk34i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase :=
    addPermanent
      (addPermanent
        (addPermanent (insertObject g3 bear p0 (.hand p0)) bear p0 p0)
        hero p1 p1)
      bear p2 p2
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p1Hero := (gBase.permanentsOf p1).find? (·.name == hero.name) |>.get!
  let handBoltId := (gBase.player p0).hand.back!

  -- 3a. `Choices.sourceStillPayable` (`removePlusOneX`) & `Leaving.isProposalAbortedByLeave` (`sourceId`):
  let (gAbStack0, abObj) := gBase.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let abId := abObj.id
  let gAbX2 := gAbStack0.record (GameEvent.announced gAbStack0.turnNumber abId #[] (some 2) #[])
  let removeXProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abId
    original := abObj
    originalSnapshot := gAbX2.snapshot abObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
    removePlusOneX := true
  }
  let gBear1Counter := gAbX2.addCounters (gAbX2.object! p0Bear.id) .plusOnePlusOne 1 (cause := some testCause)
  let gBear2Counters := gBear1Counter.addCounters (gBear1Counter.object! p0Bear.id) .plusOnePlusOne 1 (cause := some testCause)
  let gBearStolen :=
    gBear2Counters.createEffect (.control p0Bear.id p1) (cause := some testCause)
  -- `p0` proposes an activated ability from `p1Hero` (`sourceId == some p1Hero.id`) while at `.chooseX p0`:
  -- when `p1` concedes, `isProposalAbortedByLeave p1 == true` immediately reverses `p0`'s proposal
  -- (rolling back journaled proposal actions and not emitting `.ceasedToExist` for `p0`'s stack ability)!
  let gCpChooseX0 := gBase.change .saveProposalCheckpoint
  let (gCpChooseX1, p1SrcAbObj) := gCpChooseX0.putStackAbility p1Hero p0 (abilityEffect := some (Effect.gainLife 1))
  let gCpChooseX2 :=
    gCpChooseX1.withProposalAction .costAction fun g =>
      g.becomeTapped (g.object! p0Bear.id) (cause := some testCause)
  let p1SrcProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := p1SrcAbObj.id
    original := p1SrcAbObj
    originalSnapshot := gCpChooseX2.snapshot p1SrcAbObj
    kind := .activatedAbility
    sourceId := some p1Hero.id
  }
  let gChooseXBorrowedSrc :=
    gCpChooseX2.changes #[
      .proposedSpell (some p1SrcProp),
      .pending (.chooseX p0) ]
  let gChooseXAfterP1Leave := gChooseXBorrowedSrc.concede p1
  let p1SrcAbCeasedOnP1Leave :=
    gChooseXAfterP1Leave.events.any fun ev =>
      match ev with
      | .rules _ (.zone (.ceasedToExist snap)) _ _ => snap.id == some p1SrcAbObj.id
      | _ => false
  -- Outer non-proposal continuation preserved across unpaused leave rewind (`Comment 1`):
  let gWithOuter0 :=
    gBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint ]
  let (gWithOuter1, outerSrcAbObj) :=
    gWithOuter0.putStackAbility p1Hero p0 (abilityEffect := some (Effect.gainLife 1))
  let outerSrcProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := outerSrcAbObj.id
    original := outerSrcAbObj
    originalSnapshot := gWithOuter1.snapshot outerSrcAbObj
    kind := .activatedAbility
    sourceId := some p1Hero.id
  }
  let gChooseXWithOuter :=
    gWithOuter1.changes #[
      .proposedSpell (some outerSrcProp),
      .pending (.chooseX p0) ]
  let gChooseXWithOuterAfterLeave := gChooseXWithOuter.playerLeavesGame p1
  -- Deferred rewind (`rewindProposal := true`) still rewinds when `p1` only controlled `p0Bear`
  -- and control returned to `p0` during `p1`'s departure (`Comment 2`):
  let gStolenSrc0 := gBearStolen.change .saveProposalCheckpoint
  let (gStolenSrc1, stolenSrcAbObj) :=
    gStolenSrc0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let stolenSrcProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := stolenSrcAbObj.id
    original := stolenSrcAbObj
    originalSnapshot := gStolenSrc1.snapshot stolenSrcAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
  }
  let gStolenSrcChooseX :=
    gStolenSrc1.changes #[
      .proposedSpell (some stolenSrcProp),
      .pending (.chooseX p0) ]
  let (gStolenLeaveCore, savedStolen?, popOuterStolen, _) :=
    gStolenSrcChooseX.playerLeavesGameCore p1 (deferRestore := true)
  -- Also test `restorePending .none` with `rewindProposal := true` after `p1` left (when `sourceStillPayable` is true again):
  let gStolenDeferred0 :=
    (gBearStolen.concede p1).change .saveProposalCheckpoint
  let (gStolenDeferred1, stolenDefAbObj) :=
    gStolenDeferred0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let stolenDefProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := stolenDefAbObj.id
    original := stolenDefAbObj
    originalSnapshot := gStolenDeferred1.snapshot stolenDefAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
  }
  let gStolenDeferred2 :=
    gStolenDeferred1.change (.proposedSpell (some stolenDefProp))
  let gStolenDeferredRewound :=
    gStolenDeferred2.resumePendingReplacement
      (.restorePending .none false (departed := #[p1]) (rewindProposal := some false))
  -- Unrelated `restorePending .none` (`rewindProposal := none`) does NOT reverse a legal `{T}` activation
  -- whose `{T}` cost was already paid (`Comment 2`):
  let gTapPaid0 := gBase.change .saveProposalCheckpoint
  let (gTapPaid1, tapPaidAbObj) :=
    gTapPaid0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let gTapPaid2 :=
    gTapPaid1.withProposalAction .costAction fun g =>
      g.becomeTapped (g.object! p0Bear.id) (cause := some testCause)
  let tapPaidProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := tapPaidAbObj.id
    original := tapPaidAbObj
    originalSnapshot := gTapPaid2.snapshot tapPaidAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
    tapSource := true
  }
  let gTapPaid3 := gTapPaid2.change (.proposedSpell (some tapPaidProp))
  let gTapPaidAfterUnrelatedRestore :=
    gTapPaid3.resumePendingReplacement
      (.restorePending .none false (departed := #[p1]) (rewindProposal := none))
  -- Deferred rewind on a `castAsPartOfResolution` checkpoint (`ckpt.pendingReplacement == some (.gainLife p0 2 ...)`
  -- moved to `outerPendingReplacements` after `saveProposalCheckpoint`, so `hadPreBodyCont == false` at leave time)
  -- when the departure also pushed a leave-built outer continuation (`popOuter == true`, `+3` life) preserves both
  -- the checkpoint's resolution continuation AND the leave-built outer continuation (`Review #3 Comment 1`):
  let gResCastCkpt0 :=
    gBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pendingReplacement none ]
  let (gResCastCkpt1, resCastAbObj) :=
    gResCastCkpt0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let resCastProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := resCastAbObj.id
    original := resCastAbObj
    originalSnapshot := gResCastCkpt1.snapshot resCastAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
    resolutionCast := true
  }
  let gResCastWithLeaveOuter :=
    gResCastCkpt1.changes #[
      .proposedSpell (some resCastProp),
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)) ]
  let gResCastDeferredRestore :=
    gResCastWithLeaveOuter.resumePendingReplacement
      (.restorePending .none true (departed := #[p1]) (rewindProposal := some false))
  -- Chaining `runPostCastCleanup`'s `.resolveRandom (.orderInto ...)` with an already-saved departure prompt
  -- (`saved? == some (.scry p0 ...)`) keeps both prompts instead of dropping `.orderInto` (`Review #3 Comment 2`):
  let gCasc2 :=
    insertObject
      (insertObject
        (insertObject gBase bear p0 .exile)
        bear p0 .exile)
      bear p0 .exile
  let cascExIds := (gCasc2.objects.filter (fun o => o.zone == .exile && o.owner == p0)).map (·.id)
  let cascCard0 := cascExIds[0]!
  let cascCard1 := cascExIds[1]!
  let cascCard2 := cascExIds[2]!
  let gCascCkpt :=
    gCasc2.changes #[
      .pushContinuationFrame {},
      .postCastCleanup (some (.cascadeBottom p0 cascCard0 #[cascCard1, cascCard2])),
      .saveProposalCheckpoint ]
  let (gCascStack0, cascStackId) := gCascCkpt.move cascCard0 .stack (some p0) (cause := some testCause)
  let cascProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := cascStackId
    original := gCascCkpt.object! cascCard0
    originalSnapshot := gCascCkpt.snapshot (gCascCkpt.object! cascCard0)
    kind := .spell
    resolutionCast := true
  }
  let savedScryPrompt : Pending := .scry p0 1
  let gCascWithProp := gCascStack0.change (.proposedSpell (some cascProp))
  let gCascRestored :=
    gCascWithProp.resumePendingReplacement
      (.restorePending savedScryPrompt false (departed := #[p1]) (rewindProposal := some false))
  let cascOpenedOrderInto :=
    match gCascRestored.pending with
    | .resolveRandom (.orderInto ids (.library q) _) =>
      q == p0 && ids.size == 3 && ids.contains cascCard0 && ids.contains cascCard1 && ids.contains cascCard2
    | _ => false
  let gCascAfterOrder :=
    match gCascRestored.supplyOrder #[cascCard0, cascCard1, cascCard2] with
    | .ok g' => g'
    | .error _ => gCascRestored
  -- A second departure in `leavePlayersWhoLostCore` while `rewindProposalIn == some false`
  -- and `popOuterIn == true` keeps `hadPreBodyCont = false` instead of flipping to `true`
  -- from the popped outer continuation (`Review #4`):
  let gMultiLeave0 :=
    (gResCastWithLeaveOuter.createEffect (.control p0Bear.id p2) (cause := some testCause)).record
      (GameEvent.playerLost gResCastWithLeaveOuter.turnNumber p2 .conceded)
  let (gMultiAfter, sMulti, poMulti, depMulti, rwMulti) :=
    gMultiLeave0.withBatchReturn none fun g =>
      let (g', s', po', dep', rw') :=
        g.leavePlayersWhoLostCore none true #[p1] (some false)
      (g', (s', po', dep', rw'))
  let gMultiRestored :=
    gMultiAfter.restoreSavedPostLeave sMulti poMulti (departed := depMulti) (rewindProposal := rwMulti)

  let sourceAndLeaveAbortOk :=
    !gBear1Counter.sourceStillPayable removeXProp &&
    gBear2Counters.sourceStillPayable removeXProp &&
    !gBearStolen.sourceStillPayable removeXProp &&
    gChooseXAfterP1Leave.proposedSpell.isNone &&
    gChooseXAfterP1Leave.proposalCheckpoint.isNone &&
    gChooseXAfterP1Leave.pending == .none &&
    (gChooseXAfterP1Leave.findObject? p1SrcAbObj.id).isNone &&
    !(gChooseXAfterP1Leave.object! p0Bear.id).status.tapped &&
    !p1SrcAbCeasedOnP1Leave &&
    gChooseXAfterP1Leave.log.any (·.contains "the activation is reversed (CR 602.2 / 733.1)") &&
    gChooseXWithOuterAfterLeave.proposedSpell.isNone &&
    gChooseXWithOuterAfterLeave.proposalCheckpoint.isNone &&
    (gChooseXWithOuterAfterLeave.player p0).life == (gBase.player p0).life + 2 &&
    gStolenLeaveCore.proposedSpell.isNone &&
    gStolenLeaveCore.proposalCheckpoint.isNone &&
    savedStolen?.isNone &&
    !popOuterStolen &&
    gStolenDeferred2.sourceStillPayable stolenDefProp &&
    gStolenDeferredRewound.proposedSpell.isNone &&
    gStolenDeferredRewound.proposalCheckpoint.isNone &&
    !gTapPaid3.sourceStillPayable tapPaidProp &&
    gTapPaidAfterUnrelatedRestore.proposedSpell.isSome &&
    gTapPaidAfterUnrelatedRestore.proposalCheckpoint.isSome &&
    gResCastDeferredRestore.proposedSpell.isNone &&
    gResCastDeferredRestore.proposalCheckpoint.isNone &&
    (gResCastDeferredRestore.player p0).life == (gBase.player p0).life + 5 &&
    cascOpenedOrderInto &&
    gCascAfterOrder.pending == savedScryPrompt &&
    poMulti &&
    gMultiRestored.proposedSpell.isNone &&
    gMultiRestored.proposalCheckpoint.isNone &&
    (gMultiRestored.player p0).life == (gBase.player p0).life + 5

  -- 3b. `redirectPendingAfterLeave`:
  -- (i) `.payOrLetCounter`:
  --     - `q == p1` with `p0`'s spell on stack counters `p0`'s spell (unless `controlledBy o p1`);
  --     - `q == p0` when `spellId` left `.stack` clears `.payOrLetCounter` & `clearUnlessPays`;
  --     - `q == p0` with `spellId == none` and `unlessPaysInstead` whose target left (or controller left)
  --       clears `.payOrLetCounter` & `clearUnlessPays`.
  let (gBoltStack0, stackBoltId) := gBase.move handBoltId .stack (some p0) (cause := some testCause)
  let gBoltOnStack :=
    gBoltStack0.change (.pushStack {
      objectId := stackBoltId
      controller := p0
      targets := #[Target.player p2]
      targetsAnnounced := true
    })
  let gPayOrCounterP1Leaves :=
    ((gBoltOnStack.change (.pushContinuationFrame { unlessPaysController := p0 })).change
      (.pending (.payOrLetCounter p1 2 (some stackBoltId)))).concede p1
  let gPayOrCounterSpellGone :=
    ((gBase.change (.pushContinuationFrame {
      unlessPaysController := p1
      unlessPaysInstead := some (Effect.gainLife 1)
    })).change (.pending (.payOrLetCounter p0 2 (some stackBoltId)))).concede p1
  let tapCreatureEff : Effect := {
    targeting := .of .creature
    body := Instruction.tap (.target 0)
    phrase := "Tap target creature"
  }
  let gPayOrCounterInsteadIllegal :=
    ((gBase.change (.pushContinuationFrame {
      unlessPaysController := p0
      unlessPaysInstead := some tapCreatureEff
      unlessPaysTargets := #[Target.permanent p1Hero.id]
    })).change (.pending (.payOrLetCounter p0 2 none))).concede p1

  -- (ii) `.castCopiesFree`, `.mayCastCopy`, and `.mayCastCascade`:
  let dummyModesRest : ChooseModesRest := {
    controller := p0
    ability := TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }
    sourceName := "Test"
    how := .vision
  }
  let dummyTrigOr : TriggerOrRest := {
    controller := p1
    alternatives := #[.gainLife (.fixed 2)]
    ability := TriggeredAbility.mkTrigger .thisEnters { body := Instruction.gainLifeFixed 1 }
    sourceId := some p0Bear.id
    targets := #[]
    dividedDamage := #[]
    lastKnownPower := none
    lastKnownToughness := none
    sourceName := "Test"
    cardPower := none
  }
  let (gCopy0, exCopyId1) := gBase.move handBoltId .exile none (isCopy := some true) (cause := some testCause)
  let gCopiesFreeP1Leaves :=
    ((gCopy0.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
      pendingFreeCopies := some (p1, #[exCopyId1], 3, 1)
    })).change (.pending (.fraChoice p1 (.castCopiesFree #[exCopyId1] 3 1)))).concede p1
  let gCopiesFreeUnpayable :=
    ((gCopy0.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
      pendingFreeCopies := some (p0, #[exCopyId1], 0, 0)
    })).change (.pending (.fraChoice p0 (.castCopiesFree #[exCopyId1] 0 0)))).concede p1
  let gMayCastCopyP1Leaves :=
    ((gCopy0.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
    })).change (.pending (.fraChoice p1 (.mayCastCopy exCopyId1)))).concede p1
  let gMayCastCopyGone :=
    ((gBase.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
    })).change (.pending (.fraChoice p0 (.mayCastCopy handBoltId)))).concede p1
  let p0TopLibId := (gBase.player p0).library.back!
  let (gCasc0, exOtherId) := gBase.move p0TopLibId .exile none (cause := some testCause)
  let gCascadeCardGone :=
    ((gCasc0.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
    })).change (.pending (.fraChoice p0 (.mayCastCascade handBoltId #[exOtherId, p1Hero.id])))).concede p1

  -- (iii) `.chooseTriggerOr`, `.tapHumans`, and `.mayPutArtifactFromHand`:
  let gTrigOrP1Leaves :=
    ((gBase.change (.pushContinuationFrame {
      triggerOr := some dummyTrigOr
      chooseModesRest := some dummyModesRest
    })).change (.pending (.chooseTriggerOr p1))).concede p1
  let gTapHumansP1Leaves :=
    ((gBase.change (.pushContinuationFrame {
      chooseModesRest := some dummyModesRest
    })).changes #[
      .humansTappedThisWay 2,
      .pending (.tapHumans p1) ]).concede p1
  let gPutArtP1Leaves :=
    ((gBase.change (.pushContinuationFrame {
      putArtifactThisWay := some (p0Bear.id, p0Bear.id)
      chooseModesRest := some dummyModesRest
    })).change (.pending (.mayPutArtifactFromHand p1 (some p0Bear.id)))).concede p1

  let redirectCleanupOk :=
    mustHold34i3 "3b.payOrCounterP1" (gPayOrCounterP1Leaves.pending == .none &&
      (gPayOrCounterP1Leaves.player p0).graveyard.size == 1) &&
    mustHold34i3 "3b.payOrCounterSpellGone" (gPayOrCounterSpellGone.pending == .none &&
      gPayOrCounterSpellGone.continuations.isEmpty) &&
    mustHold34i3 "3b.payOrCounterInsteadIllegal" (gPayOrCounterInsteadIllegal.pending == .none &&
      gPayOrCounterInsteadIllegal.continuations.isEmpty) &&
    mustHold34i3 "3b.copiesFreeP1" (gCopiesFreeP1Leaves.pending == .none &&
      (gCopiesFreeP1Leaves.findObject? exCopyId1).isNone &&
      gCopiesFreeP1Leaves.continuations.isEmpty) &&
    mustHold34i3 "3b.copiesFreeUnpayable" (gCopiesFreeUnpayable.pending == .none &&
      (gCopiesFreeUnpayable.findObject? exCopyId1).isNone &&
      gCopiesFreeUnpayable.continuations.isEmpty) &&
    mustHold34i3 "3b.mayCastCopyP1" (gMayCastCopyP1Leaves.pending == .none &&
      (gMayCastCopyP1Leaves.findObject? exCopyId1).isNone &&
      gMayCastCopyP1Leaves.log.any (·.endsWith "ceases to exist")) &&
    mustHold34i3 "3b.mayCastCopyGone" (gMayCastCopyGone.pending == .none &&
      gMayCastCopyGone.continuations.isEmpty) &&
    mustHold34i3 "3b.cascadeCardGone" (gCascadeCardGone.pending == .none &&
      (gCascadeCardGone.findObject? exOtherId).isNone &&
      (gCascadeCardGone.player p0).library.size == (gCasc0.player p0).library.size + 1 &&
      gCascadeCardGone.continuations.isEmpty) &&
    mustHold34i3 "3b.trigOrP1" (gTrigOrP1Leaves.pending == .none && gTrigOrP1Leaves.continuations.isEmpty) &&
    mustHold34i3 "3b.tapHumansP1" (gTapHumansP1Leaves.pending == .none && gTapHumansP1Leaves.continuations.isEmpty) &&
    mustHold34i3 "3b.putArtP1" (gPutArtP1Leaves.pending == .none && gPutArtP1Leaves.continuations.isEmpty)

  mustHold34i3 "3a.sourceAndLeaveAbortOk" sourceAndLeaveAbortOk &&
  mustHold34i3 "3b.redirectCleanupOk" redirectCleanupOk &&
  mustHold34i3 "3.replay"
    (replayOk34i3 #[gBear1Counter, gBear2Counters, gBearStolen, gChooseXAfterP1Leave,
      gChooseXWithOuterAfterLeave, gStolenLeaveCore, gStolenDeferredRewound,
      gTapPaidAfterUnrelatedRestore,
      gPayOrCounterP1Leaves, gPayOrCounterSpellGone, gPayOrCounterInsteadIllegal,
      gCopiesFreeP1Leaves, gCopiesFreeUnpayable, gMayCastCopyP1Leaves, gMayCastCopyGone,
      gCascadeCardGone, gTrigOrP1Leaves, gTapHumansP1Leaves, gPutArtP1Leaves])

end Phase34Item3EventAlignment

/-! ### Phase 34 Item 4: `stillInGame` guards (`addManaUnits`, `addManaLogged`, `temptWithTheRing`, `createCommandObject`, `.emblemCastSpellDamage`, `.elspethEmblem`, `registerDelayedTrigger`, `setPlayerControl`, `shuffleThen`, `.fblthpSearch`) and Layer 1–6 characteristic queries (`Interpreter`, `Turns`, `SpellResolution`) -/
section Phase34Item4EventAlignment

private def mustHold34i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase34Item4EventAlignment failed: {label}"

private def replayOk34i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let gBase := addPermanent (addPermanent g3 bear p0 p0) bear p2 p2
  let p0Bear := (gBase.permanentsOf p0)[0]!
  let gLeftP1 := gBase.concede p1

  -- 4a. `g.stillInGame` guards on departed `p1`:
  let gAddManaDead := gLeftP1.addMana p1 (.colored .green) 2
  let gAddManaLoggedDead := gLeftP1.addManaLogged p1 #[.colored .red]
  let gTemptDead := gLeftP1.temptWithTheRing p1
  let gCmdObjDead := gLeftP1.createCommandObject p1 { name := "Dead Emblem", types := #[] }
  let gChandraEmblemDead :=
    gLeftP1.applyAbilityEffect p1 (Effect.emblemCastSpellDamage 2) #[] none
  let gElspethEmblemDead :=
    gLeftP1.applyAbilityEffect p1 elspethSunsChampion.activatedAbilities[2]!.effect #[] none
  let gDelayTrigDead :=
    gLeftP1.registerDelayedTrigger {
      controller := p1
      source := some p0Bear
      kind := .endStepExile p0Bear.id
      cause := testCause
    }
  let gCtrlTargetDead := gLeftP1.setPlayerControl p1 p0
  let gCtrlByDead := gLeftP1.setPlayerControl p0 p1
  -- `shuffleThen` on departed `p1` skips `shuffleLibrary p1` and runs `PostStep.runAfterRandom`
  -- so `p0Bear` receives its `+1/+1` counter without opening `.resolveRandom (.shuffleLibrary p1)`:
  let gShuffleThenDead := gLeftP1.shuffleThen p1 (.plusOne p0Bear.id p0 none)
  let gFblthpDead :=
    gLeftP1.applyAbilityEffect p1 fblthpKnowsTheWay.triggeredAbilities[0]!.effect #[] (some p0Bear.id)

  let stillInGameGuardsOk :=
    mustHold34i4 "4a.addMana" (gAddManaDead == gLeftP1) &&
    mustHold34i4 "4a.addManaLogged" (gAddManaLoggedDead == gLeftP1) &&
    mustHold34i4 "4a.tempt" (gTemptDead == gLeftP1) &&
    mustHold34i4 "4a.cmdObj" (gCmdObjDead == gLeftP1) &&
    mustHold34i4 "4a.chandra" (gChandraEmblemDead == gLeftP1) &&
    mustHold34i4 "4a.elspeth" (gElspethEmblemDead.objects == gLeftP1.objects && gElspethEmblemDead.log == gLeftP1.log) &&
    mustHold34i4 "4a.delayTrig" (gDelayTrigDead == gLeftP1) &&
    mustHold34i4 "4a.ctrlTarget" (gCtrlTargetDead == gLeftP1) &&
    mustHold34i4 "4a.ctrlBy" (gCtrlByDead == gLeftP1) &&
    mustHold34i4 "4a.shufflePending" (gShuffleThenDead.pending == .none) &&
    mustHold34i4 "4a.shuffleCounter" ((gShuffleThenDead.object! p0Bear.id).status.plusOnePlusOne == 1) &&
    mustHold34i4 "4a.fblthp" (gFblthpDead.objects == gLeftP1.objects && gFblthpDead.log == gLeftP1.log && gFblthpDead.pending == .none)

  -- 4b. Layer 1–6 characteristic queries in `Interpreter`, `Turns`, and `SpellResolution`:
  -- (i) `Interpreter` Fblthp distinct-name search: checks `g.hasSupertype o .basic && g.isLand o`:
  --     Insert a non-land card (`bear`) into `p0`'s library and apply Layer 1 copy effects so
  --     `targetLibId` becomes a basic land (`mountain`) while all other library cards become `bear`;
  --     Fblthp's trigger with `X = 1` finds `targetLibId` and puts it into `p0`'s hand!
  let gFblthpLib := insertObject gBase bear p0 (.library p0)
  let libIds := (gFblthpLib.player p0).library
  let targetLibId := libIds.back!
  let otherLibIds := libIds.pop
  let gFblthp0 :=
    otherLibIds.foldl
      (fun g id => g.createEffect (ContinuousEffectSpec.copy id bear) (cause := some testCause))
      ((gFblthpLib.record (GameEvent.announced gFblthpLib.turnNumber p0Bear.id #[] (some 1) #[])).createEffect
        (ContinuousEffectSpec.copy targetLibId mountain) (cause := some testCause))
  let gFblthp1 :=
    gFblthp0.applyAbilityEffect p0 fblthpKnowsTheWay.triggeredAbilities[0]!.effect #[] (some p0Bear.id)
  let fblthpLayeredOk :=
    mustHold34i4 "4b.fblthp" ((gFblthp1.followMovedToZone? targetLibId (· == .hand p0)).isSome)

  -- (ii) `Turns.expireEffectsByDuration`: logs `{acc.name o} is no longer a copy of {printed.name}`
  --      using the remaining Layer 1 name (`"Indefinite Clone"`) after the `.untilEndOfTurn` copy expires:
  let cloneIndefDef : CardDef := { bear with name := "Indefinite Clone" }
  let cloneEotDef : CardDef := { bear with name := "EOT Clone" }
  let gExpire0 :=
    (gBase.createEffect (ContinuousEffectSpec.copy p0Bear.id cloneIndefDef) (cause := some testCause)).createEffect
      (ContinuousEffectSpec.copy p0Bear.id cloneEotDef (untilEot := true))
      (cause := some testCause)
  let gExpired := gExpire0.expireEffectsByDuration (fun _ d => d == .untilEndOfTurn) (some testCause)
  let expireLogOk :=
    mustHold34i4 "4b.expire"
      (gExpired.log.any (· == "Indefinite Clone is no longer a copy of EOT Clone"))

  -- (iii) `Turns.discardCleanupIds`: logs `g.name card` (`"Cloned Cleanup Card"`) when discarding:
  let p0HandId := (gBase.player p0).hand.back!
  let cloneCleanupDef : CardDef := { bear with name := "Cloned Cleanup Card" }
  let gCleanup0 := gBase.createEffect (ContinuousEffectSpec.copy p0HandId cloneCleanupDef) (cause := some testCause)
  let gCleanedUp := gCleanup0.discardCleanupIds p0 #[p0HandId]
  let cleanupLogOk :=
    mustHold34i4 "4b.cleanup"
      (gCleanedUp.log.any (·.endsWith "discards Cloned Cleanup Card (cleanup)"))

  -- (iv) `SpellResolution.resolveTop`: computes `srcName := (g.name obj).replace "'s ability" ""`
  --      from the stack ability's Layer 1 name (`"Cloned Trigger Source's ability"` -> `"Cloned Trigger Source"`):
  let pauseRes : TriggeredAbility.TriggerResolution :=
    .may (.draw (.fixed 1) .you) (.sequence []) .ifYouDont
  let pauseTrigAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.gainLife .you) {
      resolution? := some pauseRes
      phrase := "You may draw a card"
    }
  let gTrigStack0 :=
    gBase.putTriggeredAbilityOnStack p0 p0Bear pauseTrigAb "triggers"
      (eventCause := some testCause) (reflexiveResolution := some pauseRes)
  let stackTrigId := gTrigStack0.stack.back!.objectId
  let cloneAbDef : CardDef := { bear with name := "Cloned Trigger Source's ability" }
  let gTrigCopied :=
    gTrigStack0.createEffect (ContinuousEffectSpec.copy stackTrigId cloneAbDef) (cause := some testCause)
  let gTrigResolving := gTrigCopied.resolveTop
  let resolveTopSrcNameOk :=
    mustHold34i4 "4b.resolveTop"
      (gTrigResolving.mayContext.map (·.sourceName) == some "Cloned Trigger Source")

  let layeredQueriesOk :=
    fblthpLayeredOk && expireLogOk && cleanupLogOk && resolveTopSrcNameOk

  mustHold34i4 "4a.stillInGameGuardsOk" stillInGameGuardsOk &&
  mustHold34i4 "4b.layeredQueriesOk" layeredQueriesOk &&
  mustHold34i4 "4.replay"
    (replayOk34i4 #[gLeftP1, gShuffleThenDead, gFblthp1, gExpired, gCleanedUp, gTrigResolving])

end Phase34Item4EventAlignment

/-! ### Phase 35 Item 1: Preserve `proposalCheckpoint` resolution continuations across multi-player departures when an earlier non-aborting departure precedes an aborting departure -/
section Phase35Item1EventAlignment

private def mustHold35i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase35Item1EventAlignment failed: {label}"

private def replayOk35i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana", teammate := some p3 })).change
      (.addPlayer { id := p3, name := "Jace", teammate := some p2 })
  let gBase := addPermanent (addPermanent g4 bear p0 p0) bear p3 p3
  let p0Bear := (gBase.permanentsOf p0)[0]!
  let baseLife := (gBase.player p0).life
  let leaveCause : EventCause := .gameRule .playerLeftGame

  -- Shared `castAsPartOfResolution` checkpoint where `ckpt.pendingReplacement == some (.gainLife p0 2 ...)`
  -- is moved to `outerPendingReplacements` right after `saveProposalCheckpoint` (`ckptMovedToOuter == true`):
  let gResCast0 :=
    gBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pendingReplacement none ]
  let (gResCast1, resCastAbObj) :=
    gResCast0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let resCastProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := resCastAbObj.id
    original := resCastAbObj
    originalSnapshot := gResCast1.snapshot resCastAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
    resolutionCast := true
  }
  -- `p3` controls `p0Bear` (so `p2` leaving first does NOT abort `resCastProp`, while `p3` leaving second DOES abort it),
  -- and `g.pendingReplacement` holds `.gainLife p0 3` when `p2` departs (`p2` sets `popOuter = true`, `rewindProposal = none`):
  let gMultiSetup :=
    (gResCast1.createEffect (.control p0Bear.id p3) (cause := some testCause)).changes #[
      .proposedSpell (some resCastProp),
      .pending (.chooseX p0),
      .pendingReplacement (some (.gainLife p0 3 (some testCause))) ]

  -- 1a. `leavePlayersWhoLostCore` across `#[p2, p3]`:
  --     `p2` leaves without aborting (`rewindProposal = none`, `popOuter = true`), then `p3` leaves and aborts
  --     (`prePopCont? = some none` -> `hadPreBodyCont = false`, `ckptMovedToOuter = true`):
  --     both `ckpt`'s `+2` life AND `p2`'s `+3` life run (`+5` life total)!
  let gLostBoth :=
    (gMultiSetup.record (GameEvent.playerLost gMultiSetup.turnNumber p2 .conceded (cause := some leaveCause))).record
      (GameEvent.playerLost gMultiSetup.turnNumber p3 .conceded (cause := some leaveCause))
  let (gLpwlAfter, sLpwl, poLpwl, depLpwl, rwLpwl) := gLostBoth.leavePlayersWhoLostCore
  let gLpwlRestored :=
    gLpwlAfter.restoreSavedPostLeave sLpwl poLpwl (departed := depLpwl) (rewindProposal := rwLpwl)
  let gLpwlDirect := gLostBoth.leavePlayersWhoLost

  -- 1b. Team `concede p2` (`concedePlayersLoop #[p2, p3]`) across the same `castAsPartOfResolution` setup:
  let gConcedeBoth := gMultiSetup.concede p2

  -- 1c. `prePopCont?` with `.seq (.completeActivation ..) keeper` strips `.completeActivation` to `some keeper`
  --     (`hadPreBodyCont = true`), AND `ckptMovedToOuter == true` still preserves `ckpt`'s moved `+2` life
  --     alongside `keeper` (`+4` life) and `p2`'s popped outer continuation (`+3` life) -> `+9` life total!
  let gStripKeeper0 :=
    (((gResCast1.createEffect (.control p0Bear.id p3) (cause := some testCause)).changes #[
      .proposedSpell (some resCastProp),
      .pending (.chooseX p0),
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)),
      .pendingReplacement
        (some (.seq (.completeActivation false false) (.gainLife p0 4 (some testCause)))) ]).record
      (GameEvent.playerLost gResCast1.turnNumber p3 .conceded (cause := some leaveCause)))
  let (gStripAfter, sStrip, poStrip, depStrip, rwStrip) :=
    gStripKeeper0.leavePlayersWhoLostCore none true #[p2] none
  let gStripRestored :=
    gStripAfter.restoreSavedPostLeave sStrip poStrip (departed := depStrip) (rewindProposal := rwStrip)

  -- 1d. Non-moved pre-proposal `ckpt.pendingReplacement` (`!ckptMovedToOuter`, stayed in `g.pendingReplacement`
  --     across `saveProposalCheckpoint`) is NOT duplicated across either `#[p3, p2]` or `#[p2, p3]` departure:
  let gNonMoved0 :=
    gBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint ]
  let (gNonMoved1, nonMovedAbObj) :=
    gNonMoved0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let nonMovedProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := nonMovedAbObj.id
    original := nonMovedAbObj
    originalSnapshot := gNonMoved1.snapshot nonMovedAbObj
    kind := .activatedAbility
    sourceId := some p0Bear.id
  }
  let gNonMoved2 :=
    (gNonMoved1.createEffect (.control p0Bear.id p3) (cause := some testCause)).changes #[
      .proposedSpell (some nonMovedProp),
      .pending (.chooseX p0) ]
  let gNonMovedAbortFirst := gNonMoved2.concede p3
  let gNonMovedNonAbortFirst := gNonMoved2.concede p2

  mustHold35i1 "1a.lpwl"
    ((gLpwlRestored.player p2).leftTheGame &&
      (gLpwlRestored.player p3).leftTheGame &&
      gLpwlRestored.proposedSpell.isNone &&
      gLpwlRestored.proposalCheckpoint.isNone &&
      (gLpwlRestored.player p0).life == baseLife + 5 &&
      (gLpwlDirect.player p0).life == baseLife + 5) &&
  mustHold35i1 "1b.concedePlayersLoop"
    ((gConcedeBoth.player p2).leftTheGame &&
      (gConcedeBoth.player p3).leftTheGame &&
      gConcedeBoth.proposedSpell.isNone &&
      gConcedeBoth.proposalCheckpoint.isNone &&
      (gConcedeBoth.player p0).life == baseLife + 5) &&
  mustHold35i1 "1c.stripKeeperAndMovedCkpt"
    (gStripRestored.proposedSpell.isNone &&
      gStripRestored.proposalCheckpoint.isNone &&
      (gStripRestored.player p0).life == baseLife + 9) &&
  mustHold35i1 "1d.nonMovedNotDuplicated"
    (gNonMovedAbortFirst.proposedSpell.isNone &&
      (gNonMovedAbortFirst.player p0).life == baseLife + 2 &&
      gNonMovedNonAbortFirst.proposedSpell.isNone &&
      (gNonMovedNonAbortFirst.player p0).life == baseLife + 2) &&
  mustHold35i1 "1.replay"
    (replayOk35i1 #[gLpwlAfter, gLpwlRestored, gLpwlDirect, gConcedeBoth, gStripAfter, gStripRestored,
      gNonMovedAbortFirst, gNonMovedNonAbortFirst])

end Phase35Item1EventAlignment

/-! ### Phase 35 Item 2: Preserve live non-proposal `savedPausedBatch?` across `Leaving.playerLeavesGameCore` when `shouldRewindProposal` is true -/
section Phase35Item2EventAlignment

private def mustHold35i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase35Item2EventAlignment failed: {label}"

private def replayOk35i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let b0EtbDef : CardDef := {
    bear with
    name := "P35i2 Returned Bear"
    triggeredAbilities := #[.onEnterDraw 1]
  }
  let b1RetDef : CardDef := { bear with name := "P35i2 Trailing Bear" }
  let b3DualAsEnters : CardDef := {
    bear with
    name := "P35i2 Dual Choice Bear"
    staticAbilities := #[.asEntersChooseCreatureType, .asEntersChooseOddEven]
  }
  let p0DualAsEnters : CardDef := {
    bear with
    name := "P35i2 P0 Dual Choice Bear"
    staticAbilities := #[.asEntersChooseCreatureType, .asEntersChooseOddEven]
  }
  let oringDef : CardDef := { name := "P35i2 O-Ring", types := #[.enchantment] }
  let gSetup0 :=
    insertObject
      (insertObject
        (insertObject
          (addPermanent (addPermanent g4 oringDef p2 p2) bear p3 p3)
          b0EtbDef p0 .exile)
        b3DualAsEnters p3 .exile)
      b1RetDef p1 .exile
  let oringId := (gSetup0.permanentsOf p2).find? (·.name == oringDef.name) |>.get!.id
  let p3PropSrc := (gSetup0.permanentsOf p3).find? (·.name == bear.name) |>.get!
  let b0ExId := (gSetup0.objects.find? (·.name == b0EtbDef.name)).get!.id
  let b3ExId := (gSetup0.objects.find? (·.name == b3DualAsEnters.name)).get!.id
  let b1ExId := (gSetup0.objects.find? (·.name == b1RetDef.name)).get!.id
  let gLinkedP3 := gSetup0.changeObject oringId (.linkedExile #[b0ExId, b3ExId, b1ExId])

  -- 2a. Non-proposal `origBid` paused by `p2`'s departure (`p2Oring` returning `#[b0ExId, b3ExId, b1ExId]`
  --     and pausing on `.chooseReplacement p3` with `.closeBatch origBid` queued) while `p0` has an active
  --     proposal whose source (`p3PropSrc`) is owned by `p3`:
  --     - `playerLeavesGameCore p3 (deferRestore := true)` retains `origBid` in `g.currentBatch`
  --       and defers `rewindAbortedProposalOnLeave` (`rw == some true`, `popOuter == true`);
  --     - `restoreSavedPostLeave` and `concede p3` finish returning `b1ExId`, close `origBid`
  --       (queuing/stacking `P35i2 Returned Bear`'s `.onEnterDraw 1` trigger), clear `g.currentBatch`,
  --       dismiss `p0`'s stale `.chooseX` prompt, and rewind `p0`'s proposal!
  let gCkptP3 := gLinkedP3.change .saveProposalCheckpoint
  let (gPropStackP3, abObjP3) :=
    gCkptP3.putStackAbility p3PropSrc p0 (abilityEffect := some (Effect.gainLife 1))
  let propOnP3 : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abObjP3.id
    original := abObjP3
    originalSnapshot := gPropStackP3.snapshot abObjP3
    kind := .activatedAbility
    sourceId := some p3PropSrc.id
  }
  let gPropActiveP3 :=
    gPropStackP3.changes #[.proposedSpell (some propOnP3), .pending (.chooseX p0)]
  let gPausedP3 := gPropActiveP3.concede p2
  let origBidP3? := gPausedP3.currentBatch.map Prod.fst
  let (gCoreP3, savedCoreP3?, popOuterCoreP3, rwCoreP3) :=
    gPausedP3.playerLeavesGameCore p3 (deferRestore := true)
  let gRestoredCoreP3 :=
    gCoreP3.restoreSavedPostLeave savedCoreP3? popOuterCoreP3 (departed := #[p3]) (rewindProposal := rwCoreP3)
  let gConcedeP3 := gPausedP3.concede p3
  let etbTriggered (g : Game) : Bool :=
    (g.permanentsOf p0).any (·.name == b0EtbDef.name) &&
      (g.permanentsOf p1).any (·.name == b1RetDef.name) &&
      (g.waitingTriggers.any (fun wt => wt.source.name == b0EtbDef.name) ||
        g.stack.any (fun se => (g.findObject? se.objectId).any (fun o => (g.name o).contains b0EtbDef.name)))

  -- 2b. Non-proposal `origBid` paused by `p2`'s departure on `.chooseReplacement p0` (living chooser `p0`)
  --     while `p3` concedes and aborts `p0`'s proposal: `p3` leaving retains `origBid` AND keeps
  --     `.chooseReplacement p0` open; when `p0` finishes choosing replacement options (`"Bear"` + `odd`),
  --     `origBid` closes with `p0DualAsEnters` on the battlefield and `p0`'s proposal is rewound!
  let gSetupP0 :=
    insertObject (addPermanent (addPermanent g4 oringDef p2 p2) bear p3 p3) p0DualAsEnters p0 .exile
  let oringIdP0 := (gSetupP0.permanentsOf p2).find? (·.name == oringDef.name) |>.get!.id
  let p3PropSrcP0 := (gSetupP0.permanentsOf p3).find? (·.name == bear.name) |>.get!
  let p0ExId := (gSetupP0.objects.find? (·.name == p0DualAsEnters.name)).get!.id
  let gLinkedP0 := gSetupP0.changeObject oringIdP0 (.linkedExile #[p0ExId])
  let gCkptP0 := gLinkedP0.change .saveProposalCheckpoint
  let (gPropStackP0, abObjP0) :=
    gCkptP0.putStackAbility p3PropSrcP0 p0 (abilityEffect := some (Effect.gainLife 1))
  let propOnP0 : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abObjP0.id
    original := abObjP0
    originalSnapshot := gPropStackP0.snapshot abObjP0
    kind := .activatedAbility
    sourceId := some p3PropSrcP0.id
  }
  let gPausedP0 :=
    (gPropStackP0.changes #[.proposedSpell (some propOnP0), .pending (.chooseX p0)]).concede p2
  let origBidP0? := gPausedP0.currentBatch.map Prod.fst
  let gAfterP3LeaveOnP0Prompt := gPausedP0.concede p3
  let gAfterP0Type := mustApply gAfterP3LeaveOnP0Prompt p0 (.chooseName "Bear")
  let gAfterP0Done := mustApply gAfterP0Type p0 (.chooseMode 1)

  -- 2c. Checkpoint-only `ckpt.currentBatch` without any queued `.closeBatch` is NOT passed to
  --     `restorePausedBatch` (which would close it via `finishOpenBatchAndLinkedExile`), so
  --     `reverseToProposalCheckpoint?` restores `ckpt.currentBatch` intact:
  let ckptOnlyBid : BatchId := ⟨gSetup0.nextBatchId⟩
  let gCkptBatch0 :=
    (gSetup0.change
      (.pauseBatch ckptOnlyBid (some testCause) gSetup0.objects gSetup0.players
        gSetup0.activeEffects gSetup0.pending gSetup0.stack)).change
      .saveProposalCheckpoint
  let (gCkptBatch1, abCkptBatch) :=
    gCkptBatch0.putStackAbility p3PropSrc p0 (abilityEffect := some (Effect.gainLife 1))
  let propCkptBatch : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := abCkptBatch.id
    original := abCkptBatch
    originalSnapshot := gCkptBatch1.snapshot abCkptBatch
    kind := .activatedAbility
    sourceId := some p3PropSrc.id
  }
  let gCkptBatch2 :=
    gCkptBatch1.changes #[.proposedSpell (some propCkptBatch), .pending (.chooseX p0)]
  let gAfterCkptOnlyLeave := gCkptBatch2.playerLeavesGame p3

  mustHold35i2 "2a.coreRetainsBatchAndDefersRewind"
    (origBidP3?.isSome &&
      gCoreP3.currentBatch.map Prod.fst == origBidP3? &&
      popOuterCoreP3 &&
      rwCoreP3 == some true &&
      gCoreP3.proposedSpell.isSome) &&
  mustHold35i2 "2a.restoredClosesBatchAndRewinds"
    (gRestoredCoreP3.currentBatch.isNone &&
      gRestoredCoreP3.pending == .none &&
      gRestoredCoreP3.proposedSpell.isNone &&
      gRestoredCoreP3.proposalCheckpoint.isNone &&
      etbTriggered gRestoredCoreP3) &&
  mustHold35i2 "2a.concedeClosesBatchAndRewinds"
    (gConcedeP3.currentBatch.isNone &&
      gConcedeP3.pending == .none &&
      gConcedeP3.proposedSpell.isNone &&
      gConcedeP3.proposalCheckpoint.isNone &&
      etbTriggered gConcedeP3) &&
  mustHold35i2 "2b.livingChooserKeepsPromptThenRewinds"
    (origBidP0?.isSome &&
      gAfterP3LeaveOnP0Prompt.currentBatch.map Prod.fst == origBidP0? &&
      gAfterP3LeaveOnP0Prompt.proposedSpell.isSome &&
      gAfterP0Done.currentBatch.isNone &&
      gAfterP0Done.proposedSpell.isNone &&
      gAfterP0Done.proposalCheckpoint.isNone &&
      gAfterP0Done.pending == .none &&
      (gAfterP0Done.permanentsOf p0).any (fun o =>
        o.name == p0DualAsEnters.name &&
        o.status.chosenOdd == some true &&
        o.status.chosenCreatureType.isSome)) &&
  mustHold35i2 "2c.ckptOnlyBatchPreserved"
    (gAfterCkptOnlyLeave.proposedSpell.isNone &&
      gAfterCkptOnlyLeave.proposalCheckpoint.isNone &&
      gAfterCkptOnlyLeave.currentBatch.map Prod.fst == some ckptOnlyBid) &&
  mustHold35i2 "2.replay"
    (replayOk35i2 #[gPausedP3, gCoreP3, gRestoredCoreP3, gConcedeP3,
      gPausedP0, gAfterP3LeaveOnP0Prompt, gAfterP0Type, gAfterP0Done, gAfterCkptOnlyLeave])

end Phase35Item2EventAlignment

/-! ### Phase 35 Item 3: Thread `savedPending`, `popOuter`, `departed`, and `rewindProposal` with `deferRestore` across `Decisions.finishConcedePriority` and `StateBasedActions.checkSBACounted` / `checkSBACountedWithLeavesCore` -/
section Phase35Item3EventAlignment

private def mustHold35i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase35Item3EventAlignment failed: {label}"

private def replayOk35i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

private def hasLeaveOrCheckSbaCont : PendingReplacement → Bool
  | .leavePlayersWhoLost .. | .checkSBA => true
  | .seq a b => hasLeaveOrCheckSbaCont a || hasLeaveOrCheckSbaCont b
  | _ => false

private def countFinishConcedeCont : PendingReplacement → Nat
  | .finishConcede .. => 1
  | .seq a b => countFinishConcedeCont a + countFinishConcedeCont b
  | _ => 0

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let baseLife := (g4.player p0).life

  -- 3a(i). `finishConcedePriority` SBA pass pauses on `.chooseLegend` (both direct with `popOuter`
  --        continuation AND end-to-end `concede p1` with `savedPending` from `midResolutionOrBatch == false`):
  --        chains a SINGLE `.finishConcede` carrying `savedPending`, `popOuter`, `departed`, `rewindProposal`
  --        (with NO `.leavePlayersWhoLost` / `.checkSBA`), restores `savedPending` when `keepLegend` resolves,
  --        and runs the outer continuation once (`+3` life) when `savedPending` completes!
  let legDef : CardDef := { bear with name := "P35i3 Legend", supertypes := #[.legendary] }
  let gLeg0 := addPermanent (addPermanent g4 legDef p0 p0) legDef p0 p0
  let legIds := (gLeg0.permanentsOf p0).filter (·.name == legDef.name) |>.map (·.id)
  let gLegDirect :=
    (gLeg0.logLookAtTop p0 1 (looked := gLeg0.scryLookedIds p0 1)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)) ]
  let gLegDirectPaused :=
    gLegDirect.finishConcedePriority false (some p0) none (some (.scry p0 1)) true
      (runSba := true) (departed := #[p1])
  let gLegDirectResolved := mustApply gLegDirectPaused p0 (.keepLegend legIds[0]!)
  let gLegDirectAfterScry :=
    mustApply gLegDirectResolved p0 (.scry (gLegDirectResolved.scryLookedIds p0 1) #[])

  let gLegE2e0 :=
    (gLeg0.changeControl (gLeg0.object! legIds[1]!) p1 (untilEot := true) (cause := some testCause)).change
      .saveProposalCheckpoint
  let (gLegE2e1, legAbObj) :=
    gLegE2e0.putStackAbility (gLegE2e0.object! legIds[0]!) p0 (abilityEffect := some (Effect.gainLife 1))
  let legProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := legAbObj.id, original := legAbObj
    originalSnapshot := gLegE2e1.snapshot legAbObj, kind := .activatedAbility
    sourceId := some legIds[0]!
  }
  let gLegE2e2 := gLegE2e1.changes #[.proposedSpell (some legProp), .pending (.chooseX p0)]
  let gLegE2ePaused := gLegE2e2.concede p1
  let gLegE2eResolved := mustApply gLegE2ePaused p0 (.keepLegend legIds[0]!)

  let legPausedContOk :=
    gLegDirectPaused.legendChoicePending? &&
    gLegDirectPaused.pendingReplacement.any (fun pr =>
      !hasLeaveOrCheckSbaCont pr && countFinishConcedeCont pr == 1) &&
    gLegE2ePaused.legendChoicePending? &&
    gLegE2ePaused.pendingReplacement.any (fun pr =>
      !hasLeaveOrCheckSbaCont pr && countFinishConcedeCont pr == 1)

  -- 3a(ii). `finishConcedePriority` SBA pass pauses on `.chooseReplacement` (0/0 creature dying with two
  --         replacement choices on `p0` while `savedPending = some (.scry p0 1)` and `popOuter = true`):
  let zeroDef : CardDef := { bear with name := "P35i3 Zero", power := some 0, toughness := some 0 }
  let leyA3 : CardDef := { name := "P35i3 LeyA", types := #[.enchantment] }
  let leyB3 : CardDef := { name := "P35i3 LeyB", types := #[.enchantment] }
  let gSbaRepl0 :=
    addPermanent (addPermanent (addPermanent g4 zeroDef p0 p0) leyA3 p0 p0) leyB3 p0 p0
  let zeroId := (gSbaRepl0.permanentsOf p0).find? (·.name == zeroDef.name) |>.get!.id
  let leyA3Id := (gSbaRepl0.permanentsOf p0).find? (·.name == leyA3.name) |>.get!.id
  let leyB3Id := (gSbaRepl0.permanentsOf p0).find? (·.name == leyB3.name) |>.get!.id
  let rid3A : ReplacementId := { kind := .exileOppDeath, object := some leyA3Id }
  let rid3B : ReplacementId := { kind := .exileOppDeath, object := some leyB3Id }
  let gSbaRepl1 :=
    (((gSbaRepl0.logLookAtTop p0 1 (looked := gSbaRepl0.scryLookedIds p0 1)).createEffect
      (.replacement { id := rid3A, source := some leyA3Id, controller := some p0, affectedPlayer := p0,
                      kind := .exileInsteadOfGraveyard (some zeroId) false })
      (cause := some testCause)).createEffect
      (.replacement { id := rid3B, source := some leyB3Id, controller := some p0, affectedPlayer := p0,
                      kind := .exileInsteadOfGraveyard (some zeroId) false })
      (cause := some testCause)).changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)) ]
  let gSbaReplPaused :=
    gSbaRepl1.finishConcedePriority false (some p0) none (some (.scry p0 1)) true
      (runSba := true) (departed := #[p1])
  let sbaReplPausedOk :=
    (match gSbaReplPaused.pending with
     | .chooseReplacement q cs => q == p0 && cs == #[rid3A, rid3B]
     | _ => false) &&
    gSbaReplPaused.pendingReplacement.any (fun pr =>
      !hasLeaveOrCheckSbaCont pr && countFinishConcedeCont pr == 1)
  let gSbaReplResolved := mustApply gSbaReplPaused p0 (.chooseReplacement rid3A)
  let gSbaReplAfterScry :=
    mustApply gSbaReplResolved p0 (.scry (gSbaReplResolved.scryLookedIds p0 1) #[])

  -- 3b. Secondary loser `p2` loses during `finishConcedePriority`'s SBA pass (`p2` is at 0 life):
  --     (i) Direct `finishConcedePriority` with `castAsPartOfResolution` (`+2` life in `ckpt` moved to outer)
  --         plus `p1`'s `+3` life in `outerPendingReplacements` (`popOuter = true`, `departed = #[p1]`):
  --         `checkSBACountedWithLeavesCore (deferRestore := true)` threads `popOuter` / `departed` into
  --         `leavePlayersWhoLostCore` without premature `restoreSavedPostLeave`, and `finishConcedePriority`
  --         runs both `+2` and `+3` life (`baseLife + 5`)!
  --     (ii) End-to-end `concede p1` from `midResolutionOrBatch == false` while `p0` is at `.chooseX p0`
  --          on `secBear` (controlled by `p2` at 0 life): `p1` leaves with `saved? = some (.chooseX p0)`,
  --          `finishConcedePriority` runs SBAs, `p2` loses and aborts `p0`'s proposal, clearing `saved?`
  --          and rewinding `proposedSpell` / `proposalCheckpoint` cleanly!
  let gSec0 := addPermanent g4 bear p0 p0
  let secBear := (gSec0.permanentsOf p0)[0]!
  let gSec1 :=
    gSec0.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p0 2 (some testCause))),
      .saveProposalCheckpoint,
      .pushOuterPendingReplacement (.gainLife p0 2 (some testCause)),
      .pendingReplacement none ]
  let (gSec2, secAbObj) :=
    gSec1.putStackAbility secBear p0 (abilityEffect := some (Effect.gainLife 1))
  let secProp : ProposedSpell := {
    caster := p0
    cost := ManaCost.empty
    spellId := secAbObj.id
    original := secAbObj
    originalSnapshot := gSec2.snapshot secAbObj
    kind := .activatedAbility
    sourceId := some secBear.id
    resolutionCast := true
  }
  let gSec3 :=
    ((gSec2.createEffect (.control secBear.id p2) (cause := some testCause)).loseLife p2 20
      (cause := some testCause)).changes #[
      .proposedSpell (some secProp),
      .pushOuterPendingReplacement (.gainLife p0 3 (some testCause)) ]
  let gSecFcp :=
    gSec3.finishConcedePriority false (some p0) none (some (.chooseX p0)) true
      (runSba := true) (departed := #[p1])

  let gSecE2e0 :=
    ((gSec0.createEffect (.control secBear.id p2) (cause := some testCause)).loseLife p2 20
      (cause := some testCause)).change .saveProposalCheckpoint
  let (gSecE2e1, secE2eAbObj) :=
    gSecE2e0.putStackAbility secBear p0 (abilityEffect := some (Effect.gainLife 1))
  let secE2eProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := secE2eAbObj.id, original := secE2eAbObj
    originalSnapshot := gSecE2e1.snapshot secE2eAbObj, kind := .activatedAbility
    sourceId := some secBear.id
  }
  let gSecE2e2 := gSecE2e1.changes #[.proposedSpell (some secE2eProp), .pending (.chooseX p0)]
  let gSecAfterConcedeP1 := gSecE2e2.concede p1

  mustHold35i3 "3a.legendPause" legPausedContOk &&
  mustHold35i3 "3a.legendResolved"
    (gLegDirectResolved.pending == .scry p0 1 &&
      (gLegDirectAfterScry.player p0).life == baseLife + 3 &&
      gLegE2eResolved.pending == .chooseX p0 &&
      gLegE2eResolved.proposedSpell.isSome) &&
  mustHold35i3 "3a.sbaReplPause" sbaReplPausedOk &&
  mustHold35i3 "3a.sbaReplResolved"
    (gSbaReplResolved.pending == .scry p0 1 &&
      (gSbaReplAfterScry.player p0).life == baseLife + 3) &&
  mustHold35i3 "3b.secondaryLoserThreadsAndRewinds"
    ((gSecFcp.player p2).leftTheGame &&
      gSecFcp.proposedSpell.isNone &&
      gSecFcp.proposalCheckpoint.isNone &&
      (gSecFcp.player p0).life == baseLife + 5 &&
      (gSecAfterConcedeP1.player p1).leftTheGame &&
      (gSecAfterConcedeP1.player p2).leftTheGame &&
      gSecAfterConcedeP1.proposedSpell.isNone &&
      gSecAfterConcedeP1.proposalCheckpoint.isNone &&
      gSecAfterConcedeP1.pending == .none) &&
  mustHold35i3 "3.replay"
    (replayOk35i3 #[gLegDirectPaused, gLegDirectResolved, gLegDirectAfterScry,
      gLegE2ePaused, gLegE2eResolved, gSbaReplPaused, gSbaReplResolved, gSbaReplAfterScry,
      gSecFcp, gSecAfterConcedeP1])

end Phase35Item3EventAlignment

/-! ### Phase 35 Item 4: Complete `Choices.sourceStillPayable`, `Leaving.isProposalAbortedByLeave` indirect control-loss detection, `Decisions.proposalCostPromptStillPayable`, and `Decisions.runPostStep` `.resumeChooseModeAfterLeave` / `.resumeChooseTargetsAfterLeave` source-payability checks -/
section Phase35Item4EventAlignment

private def mustHold35i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase35Item4EventAlignment failed: {label}"

private def replayOk35i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })
  let auraDef : CardDef := { name := "P35i4 Mind Lease", types := #[.enchantment] }
  let vehicleDef : CardDef := {
    name := "P35i4 Skiff", types := #[.artifact], subtypes := #["Vehicle"]
    power := some 4, toughness := some 4
  }
  let pwDef : CardDef := {
    name := "P35i4 Walker", types := #[.planeswalker], loyalty := some 3
  }
  let blackMv15 : CardDef := {
    name := "P35i4 Fifteen Black"
    manaCost := { symbols := Array.replicate 15 (.colored .black) }
    types := #[.creature], power := some 2, toughness := some 2
  }
  let gBase0 :=
    insertObject
      (insertObject
        (addPermanent
          (addPermanent
            (addPermanent
              (addPermanent
                (addPermanent g3 bear p0 p0)
                bear p2 p2)
              auraDef p1 p1)
            vehicleDef p0 p0)
          pwDef p0 p0)
        blackMv15 p0 (.graveyard p0))
      bear p0 (.hand p0)
  let pwInitId := (gBase0.permanentsOf p0).find? (·.name == pwDef.name) |>.get!.id
  let gBase := gBase0.recordPutCounters pwInitId .loyalty 3 (some p0) (cause := some testCause)
  let p0Bear := (gBase.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let p2Bear := (gBase.permanentsOf p2).find? (·.name == bear.name) |>.get!
  let p1Aura := (gBase.permanentsOf p1).find? (·.name == auraDef.name) |>.get!
  let p0Veh := (gBase.permanentsOf p0).find? (·.name == vehicleDef.name) |>.get!
  let p0Pw := (gBase.permanentsOf p0).find? (·.name == pwDef.name) |>.get!

  -- 4a. `Choices.sourceStillPayable`: `removeStoryCounter` and `removeIndestructibleCounter`:
  let (gAb0, ab0) := gBase.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let storyAb : ActivatedAbility := { cost := CostSpec.ofItems #[.removeCounters (.exact 1) (some .story) .self], effect := Effect.gainLife 1 }
  let indestAb : ActivatedAbility := { cost := CostSpec.ofItems #[.removeCounters (.exact 1) (some .indestructible) .self], effect := Effect.gainLife 1 }
  let storyProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := ab0.id, original := ab0
    originalSnapshot := gAb0.snapshot ab0, kind := .activatedAbility
    sourceId := some p0Bear.id, activation := some storyAb
  }
  let indestProp : ProposedSpell := { storyProp with activation := some indestAb }
  let gWithStory := gAb0.recordPutCounters p0Bear.id .story 1 (some p0) (cause := some testCause)
  let gStoryStolen := gWithStory.createEffect (.control p0Bear.id p2) (cause := some testCause)
  let gWithIndest := gAb0.recordPutCounters p0Bear.id .indestructible 1 (some p0) (cause := some testCause)
  let gIndestStolen := gWithIndest.createEffect (.control p0Bear.id p2) (cause := some testCause)
  let sourceCountersPayableOk :=
    !gAb0.sourceStillPayable storyProp &&
    gWithStory.sourceStillPayable storyProp &&
    !gStoryStolen.sourceStillPayable storyProp &&
    !gAb0.sourceStillPayable indestProp &&
    gWithIndest.sourceStillPayable indestProp &&
    !gIndestStolen.sourceStillPayable indestProp

  -- 4b. `Leaving.isProposalAbortedByLeave` indirect Layer 2 control-loss detection:
  --     (i) `p1`'s `p1Aura` (`.whileSourceOnBattlefield p1Aura.id`) grants `p0` control of `p2Bear`;
  --         `p0` proposes an `{X}` ability of `p2Bear` at `.chooseX p0`; when `p1` concedes OR leaves,
  --         `p0` loses control of `p2Bear` and `p0`'s proposal immediately aborts and rewinds!
  let mkIndirectGame (dur : EffectDuration) : Game :=
    let g0 :=
      (gBase.createEffect (.layered (.objects #[p2Bear.id]) (.control p0) dur)
        (cause := some testCause)).change .saveProposalCheckpoint
    let (g1, abObj) := g0.putStackAbility p2Bear p0 (abilityEffect := some (Effect.gainLife 1))
    let prop : ProposedSpell := {
      caster := p0, cost := ManaCost.empty, spellId := abObj.id, original := abObj
      originalSnapshot := g1.snapshot abObj, kind := .activatedAbility, sourceId := some p2Bear.id
    }
    g1.changes #[.proposedSpell (some prop), .pending (.chooseX p0)]
  let gIndWhileBf := mkIndirectGame (.whileSourceOnBattlefield p1Aura.id)
  let gIndUntilLeaves := mkIndirectGame (.untilSourceLeaves p1Aura.id)
  let gIndWhileInZone := mkIndirectGame (.whileInZone p1Aura.id .battlefield)
  let gIndWhileCnt :=
    (gBase.recordPutCounters p1Aura.id .charge 1 (some p1) (cause := some testCause)) |> fun gC =>
      let g0 :=
        (gC.createEffect (.layered (.objects #[p2Bear.id]) (.control p0) (.whileSourceHasCounter p1Aura.id .charge))
          (cause := some testCause)).change .saveProposalCheckpoint
      let (g1, abObj) := g0.putStackAbility p2Bear p0 (abilityEffect := some (Effect.gainLife 1))
      let prop : ProposedSpell := {
        caster := p0, cost := ManaCost.empty, spellId := abObj.id, original := abObj
        originalSnapshot := g1.snapshot abObj, kind := .activatedAbility, sourceId := some p2Bear.id
      }
      g1.changes #[.proposedSpell (some prop), .pending (.activateManaAbilities p0)]
  let gIndConceded := gIndWhileBf.concede p1
  let gIndLeftDirect := gIndWhileBf.playerLeavesGame p1
  let gIndCntConceded := gIndWhileCnt.concede p1
  --     (ii) CR 613.8 dependency via `.creaturesControlledBy p1`: `p1` controls `p2Bear` and `p0` has
  --          `.layered (.creaturesControlledBy p1) (.control p0) .indefinite`; when `p1` concedes,
  --          `p1`'s control effect ends, `.creaturesControlledBy p1` stops matching `p2Bear`, and `p0`'s
  --          proposal aborts and rewinds!
  let gDep0 :=
    ((gBase.createEffect (.control p2Bear.id p1) (cause := some testCause)).createEffect
      (.layered (.creaturesControlledBy p1) (.control p0) .indefinite)
      (cause := some testCause)).change .saveProposalCheckpoint
  let (gDep1, depAbObj) := gDep0.putStackAbility p2Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let depProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := depAbObj.id, original := depAbObj
    originalSnapshot := gDep1.snapshot depAbObj, kind := .activatedAbility, sourceId := some p2Bear.id
  }
  let gDep2 := gDep1.changes #[.proposedSpell (some depProp), .pending (.activateManaAbilities p0)]
  let gDepConceded := gDep2.concede p1
  --     (iii) Negative check: `p0Bear` (owned by `p0`) was stolen by `p1` and reclaimed by `p0` via `p1Aura`;
  --           when `p1` concedes, `p0` STILL controls `p0Bear`, so `p0`'s proposal is NOT aborted!
  let gReclaimed0 :=
    ((gBase.createEffect (.control p0Bear.id p1) (cause := some testCause)).createEffect
      (.layered (.objects #[p0Bear.id]) (.control p0) (.whileSourceOnBattlefield p1Aura.id))
      (cause := some testCause)).change .saveProposalCheckpoint
  let (gReclaimed1, recAbObj) := gReclaimed0.putStackAbility p0Bear p0 (abilityEffect := some (Effect.gainLife 1))
  let recProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := recAbObj.id, original := recAbObj
    originalSnapshot := gReclaimed1.snapshot recAbObj, kind := .activatedAbility, sourceId := some p0Bear.id
  }
  let gReclaimed2 := gReclaimed1.changes #[.proposedSpell (some recProp), .pending (.chooseX p0)]
  let gReclaimedAfterP1 := gReclaimed2.concede p1

  let indirectAbortOk :=
    gIndWhileBf.isProposalAbortedByLeave p1 &&
    gIndUntilLeaves.isProposalAbortedByLeave p1 &&
    gIndWhileInZone.isProposalAbortedByLeave p1 &&
    gIndWhileCnt.isProposalAbortedByLeave p1 &&
    gIndConceded.proposedSpell.isNone &&
    gIndConceded.proposalCheckpoint.isNone &&
    gIndConceded.pending == .none &&
    gIndLeftDirect.proposedSpell.isNone &&
    gIndLeftDirect.proposalCheckpoint.isNone &&
    gIndCntConceded.proposedSpell.isNone &&
    gDep2.isProposalAbortedByLeave p1 &&
    gDepConceded.proposedSpell.isNone &&
    gDepConceded.proposalCheckpoint.isNone &&
    !gReclaimed2.isProposalAbortedByLeave p1 &&
    gReclaimedAfterP1.proposedSpell.isSome &&
    gReclaimedAfterP1.pending == .chooseX p0

  -- 4c. `Decisions.proposalCostPromptStillPayable`:
  --     - `.costPicks`, `.crew`, `.zemoBoastExile` require `g.sourceStillPayable prop`;
  --     - `prop.kind == .turnFaceUp` requires `g.sourceStillPayable prop` (`faceDown` & controlled by `caster`);
  --     - `.sacrificePermanent` on `.activatedAbility` allows an already-tapped non-loyalty source,
  --       while checking loyalty payability (`controlledBy`, `!loyaltyActivatedThisTurn`, counter count / `minusX`).
  let gCostPicksOk := gAb0.change (.proposedSpell (some { storyProp with activation := none, tapSource := true }))
  let gCostPicksTapped := gCostPicksOk.becomeTapped (gCostPicksOk.object! p0Bear.id) (cause := some testCause)
  let costPicksPrompt : Pending := .fraChoice p0 (.costPicks p0Bear.id #[.discardACard] false)

  let (gCrew0, crewAbObj) := gBase.putStackAbility p0Veh p0 (abilityEffect := some (Effect.gainLife 1))
  let crewProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := crewAbObj.id, original := crewAbObj
    originalSnapshot := gCrew0.snapshot crewAbObj, kind := .activatedAbility, sourceId := some p0Veh.id
  }
  let gCrewOk := gCrew0.change (.proposedSpell (some crewProp))
  let gCrewStolen := gCrewOk.createEffect (.control p0Veh.id p2) (cause := some testCause)
  let crewPrompt : Pending := .fraChoice p0 (.crew crewAbObj.id p0Veh.id 2)

  let zemoPrompt : Pending := .fraChoice p0 (.zemoBoastExile ab0.id p0Bear.id)
  let gZemoOk := gAb0.change (.proposedSpell (some { storyProp with activation := none }))
  let gZemoStolen := gZemoOk.createEffect (.control p0Bear.id p2) (cause := some testCause)

  let morphDef : CardDef := { creature "P35i4 Morph" ManaCost.empty #["Human"] 3 3 with keywords := #[.morph CostSpec.empty] }
  let gMorphAdded := addPermanent gBase morphDef p0 p0
  let gMorph0 := setFaceDown gMorphAdded
    (gMorphAdded.permanentsOf p0 |>.find? (·.name == morphDef.name) |>.get!.id) true
  let morphObj := (gMorph0.permanentsOf p0).find? (·.status.faceDown) |>.get!
  let morphProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := morphObj.id, sourceId := some morphObj.id
    original := morphObj, originalSnapshot := gMorph0.snapshot morphObj
    kind := .turnFaceUp, needsDiscardCard := true
  }
  let gMorphOk := gMorph0.change (.proposedSpell (some morphProp))
  let gMorphFaceUp := setFaceDown gMorphOk morphObj.id false
  let gMorphStolen := gMorphOk.createEffect (.control morphObj.id p2) (cause := some testCause)
  let morphDiscardPrompt : Pending := .discardForAdditionalCost p0

  -- `.sacrificePermanent` on `.activatedAbility`:
  let gSacTapPaid :=
    gCostPicksTapped.change
      (.proposedSpell (some { storyProp with activation := none, tapSource := true, needsSacrificeOther := true }))
  let sacNonLoyaltyPrompt : Pending := .sacrificePermanent p0 p0Bear.id
  let (gPw0, pwAbObj) := gBase.putStackAbility p0Pw p0 (abilityEffect := some (Effect.gainLife 1))
  let pwMinus3Ab : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty (.minus 3)], effect := Effect.gainLife 1
  }
  let pwMinus4Ab : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty (.minus 4)], effect := Effect.gainLife 1
  }
  let pwMinusXAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.loyalty .minusX], effect := Effect.gainLife 1
  }
  let mkPwProp (ab : ActivatedAbility) : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := pwAbObj.id, original := pwAbObj
    originalSnapshot := gPw0.snapshot pwAbObj, kind := .activatedAbility
    sourceId := some p0Pw.id, activation := some ab, needsSacrificeOther := true
  }
  let sacPwPrompt : Pending := .sacrificePermanent p0 p0Pw.id
  let gPwOk := gPw0.change (.proposedSpell (some (mkPwProp pwMinus3Ab)))
  let gPwTooLow := gPw0.change (.proposedSpell (some (mkPwProp pwMinus4Ab)))
  let gPwStolen := gPwOk.createEffect (.control p0Pw.id p2) (cause := some testCause)
  let gPwAlreadyUsed :=
    gPwOk.record
      (GameEvent.abilityActivated gPwOk.turnNumber p0Pw.id (gPwOk.snapshot (gPwOk.object! p0Pw.id)) p0
        (.nonMana (some (-1)) false false false none false) (cause := some testCause))
  let gPwMinusX3Ok :=
    (gPw0.record (GameEvent.announced gPw0.turnNumber pwAbObj.id #[] (some 3) #[])).change
      (.proposedSpell (some (mkPwProp pwMinusXAb)))
  let gPwMinusX4Fail :=
    (gPw0.record (GameEvent.announced gPw0.turnNumber pwAbObj.id #[] (some 4) #[])).change
      (.proposedSpell (some (mkPwProp pwMinusXAb)))

  let costPromptPayableOk :=
    gCostPicksOk.proposalCostPromptStillPayable p0 costPicksPrompt &&
    !gCostPicksTapped.proposalCostPromptStillPayable p0 costPicksPrompt &&
    gCrewOk.proposalCostPromptStillPayable p0 crewPrompt &&
    !gCrewStolen.proposalCostPromptStillPayable p0 crewPrompt &&
    gZemoOk.proposalCostPromptStillPayable p0 zemoPrompt &&
    !gZemoStolen.proposalCostPromptStillPayable p0 zemoPrompt &&
    gMorphOk.proposalCostPromptStillPayable p0 morphDiscardPrompt &&
    !gMorphFaceUp.proposalCostPromptStillPayable p0 morphDiscardPrompt &&
    !gMorphStolen.proposalCostPromptStillPayable p0 morphDiscardPrompt &&
    gSacTapPaid.proposalCostPromptStillPayable p0 sacNonLoyaltyPrompt &&
    gPwOk.proposalCostPromptStillPayable p0 sacPwPrompt &&
    !gPwTooLow.proposalCostPromptStillPayable p0 sacPwPrompt &&
    !gPwStolen.proposalCostPromptStillPayable p0 sacPwPrompt &&
    !gPwAlreadyUsed.proposalCostPromptStillPayable p0 sacPwPrompt &&
    gPwMinusX3Ok.proposalCostPromptStillPayable p0 sacPwPrompt &&
    !gPwMinusX4Fail.proposalCostPromptStillPayable p0 sacPwPrompt

  -- 4d. `Decisions.runPostStep` `.resumeChooseModeAfterLeave` and `.resumeChooseTargetsAfterLeave`:
  let mode1 : Effect := Effect.gainLife 1
  let mode2 : Effect := Effect.gainLife 2
  let gModeCkpt := gBase.change .saveProposalCheckpoint
  let (gMode1, modeAbObj) := gModeCkpt.putStackAbility p0Bear p0 (abilityEffect := some mode1)
  let modalAbProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := modeAbObj.id, original := modeAbObj
    originalSnapshot := gMode1.snapshot modeAbObj, kind := .activatedAbility
    sourceId := some p0Bear.id, abilityModes := #[mode1, mode2], tapSource := true
  }
  let gModalAbLegal :=
    (gMode1.change (.proposedSpell (some modalAbProp))).runPostStep (.resumeChooseModeAfterLeave p0)
  let gModalAbStolen :=
    ((gMode1.createEffect (.control p0Bear.id p2) (cause := some testCause)).change
      (.proposedSpell (some modalAbProp))).runPostStep (.resumeChooseModeAfterLeave p0)

  let gMorphCkpt := gMorph0.change .saveProposalCheckpoint
  let gMorphModeLegal :=
    (gMorphCkpt.changes #[.proposedSpell (some morphProp), .pending (.chooseMode p0)]).runPostStep
      (.resumeChooseModeAfterLeave p0)
  let gMorphModeStolen :=
    ((gMorphCkpt.createEffect (.control morphObj.id p2) (cause := some testCause)).changes #[
      .proposedSpell (some morphProp), .pending (.chooseMode p0) ]).runPostStep
      (.resumeChooseModeAfterLeave p0)

  let targEff : Effect := { targeting := .of .player, body := Instruction.gainLifeFixed 1, phrase := "Target player" }
  let (gTarg1, targAbObj) := gModeCkpt.putStackAbility p0Bear p0 (abilityEffect := some targEff)
  let targAbProp : ProposedSpell := {
    caster := p0, cost := ManaCost.empty, spellId := targAbObj.id, original := targAbObj
    originalSnapshot := gTarg1.snapshot targAbObj, kind := .activatedAbility
    sourceId := some p0Bear.id, tapSource := true
  }
  let gTargLegal :=
    (gTarg1.changes #[.proposedSpell (some targAbProp), .pending (.chooseTargets p0)]).runPostStep
      (.resumeChooseTargetsAfterLeave p0)
  let gTargStolen :=
    ((gTarg1.createEffect (.control p0Bear.id p2) (cause := some testCause)).changes #[
      .proposedSpell (some targAbProp), .pending (.chooseTargets p0) ]).runPostStep
      (.resumeChooseTargetsAfterLeave p0)

  let postStepPayabilityOk :=
    gModalAbLegal.proposedSpell.isSome && gModalAbLegal.pending == .chooseMode p0 &&
    gModalAbStolen.proposedSpell.isNone && gModalAbStolen.proposalCheckpoint.isNone &&
    gMorphModeLegal.proposedSpell.isSome &&
    gMorphModeStolen.proposedSpell.isNone && gMorphModeStolen.proposalCheckpoint.isNone &&
    gTargLegal.proposedSpell.isSome && gTargLegal.pending == .chooseTargets p0 &&
    gTargStolen.proposedSpell.isNone && gTargStolen.proposalCheckpoint.isNone

  mustHold35i4 "4a.sourceCountersPayable" sourceCountersPayableOk &&
  mustHold35i4 "4b.indirectAbort" indirectAbortOk &&
  mustHold35i4 "4c.costPromptPayable" costPromptPayableOk &&
  mustHold35i4 "4d.postStepPayability" postStepPayabilityOk &&
  mustHold35i4 "4.replay"
    (replayOk35i4 #[gWithStory, gStoryStolen, gWithIndest, gIndestStolen,
      gIndConceded, gIndLeftDirect, gIndCntConceded, gDepConceded, gReclaimedAfterP1,
      gPwAlreadyUsed, gModalAbLegal, gModalAbStolen, gMorphModeLegal, gMorphModeStolen,
      gTargLegal, gTargStolen])

end Phase35Item4EventAlignment

end Mtg.Engine.EventTests
