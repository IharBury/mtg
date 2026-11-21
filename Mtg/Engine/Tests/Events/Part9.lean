import Mtg.Engine.Tests.Events.Base

namespace Mtg.Engine.EventTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

section Phase41Item1EventAlignment

private def mustHold41i1 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase41Item1EventAlignment failed: {label}"

private def replayOk41i1 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let legBearDef : CardDef := { bear with supertypes := #[.legendary] }
  let legHeroDef : CardDef := { hero with supertypes := #[.legendary] }
  let fragileLordDef : CardDef := creature "P41i1 FragileLord" ManaCost.empty #["Wizard"] 1 0
  let zeroToughDef : CardDef := creature "P41i1 ZeroTough" ManaCost.empty #["Human"] 1 0
  let p2LandDef : CardDef := { name := "P41i1 Forest", types := #[.land] }
  let auraBaseDef : CardDef := {
    name := "P41i1 PlainAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
  }
  let legAuraDef : CardDef := {
    name := "P41i1 LegendAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedCreatureGetsHasAndTypes 1 1 {} #[.hero]]
  }
  let nonLegSubAuraDef : CardDef := {
    name := "P41i1 SpiritAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedIsOnlySubtypeCantAttackOrBlock .spirit]
  }
  let constructAuraDef : CardDef := {
    name := "P41i1 ConstructAura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantedIsConstruct55]
  }

  -- 1a. Legend-affecting attachment departure (`ceasedToExist` & CR 800.4a `moved`) and
  --     expired `.copy` / `.text` / `.types` / `.abilities` on prompt attachments invalidate
  --     `Leaving.preBatchLegendSnapshotValid`, while non-legendary subtype/Construct Auras and
  --     Layer 7 attachment effects remain allowlisted:
  let gAuraCease0 :=
    addPermanent (addPermanent (addPermanent g4 bear p0 p0) legBearDef p0 p0) legAuraDef p2 p2
  let acB1 := (gAuraCease0.permanentsOf p0).find? (fun o => o.printed.supertypes.isEmpty) |>.get!
  let acB2 := (gAuraCease0.permanentsOf p0).find? (fun o => !o.printed.supertypes.isEmpty) |>.get!
  let acAura := (gAuraCease0.permanentsOf p2)[0]!
  let gAuraCeasePaused :=
    (gAuraCease0.record
      (GameEvent.attached gAuraCease0.turnNumber (gAuraCease0.snapshot acAura) acB1.id (cause := testCause))).checkSBA
  let gAuraCeaseAfter := mustApply gAuraCeasePaused p2 .concede
  let auraCeaseInvalidatedOk :=
    gAuraCeasePaused.pending == .chooseLegend p0 bear.name #[acB1.id, acB2.id] &&
    gAuraCeaseAfter.pending == .none &&
    gAuraCeaseAfter.currentBatch.isNone &&
    (gAuraCeaseAfter.permanentsOf p0).size == 2

  -- Legend-granting Aura leaving via CR 800.4a `.moved` to `.exile`:
  let gAuraMove0 :=
    addPermanent (addPermanent (addPermanent g4 bear p0 p0) legBearDef p0 p0) legAuraDef p0 p2
  let amB1 := (gAuraMove0.permanentsOf p0).find? (fun o => o.printed.supertypes.isEmpty) |>.get!
  let amB2 := (gAuraMove0.permanentsOf p0).find? (fun o => !o.printed.supertypes.isEmpty) |>.get!
  let amAura := (gAuraMove0.permanentsOf p2)[0]!
  let gAuraMovePaused :=
    (gAuraMove0.record
      (GameEvent.attached gAuraMove0.turnNumber (gAuraMove0.snapshot amAura) amB1.id (cause := testCause))).checkSBA
  let gAuraMoveAfter := mustApply gAuraMovePaused p2 .concede
  let auraMoveInvalidatedOk :=
    gAuraMovePaused.pending == .chooseLegend p0 bear.name #[amB1.id, amB2.id] &&
    (gAuraMoveAfter.followMovedToZone? amAura.id (· == .exile)).isSome &&
    gAuraMoveAfter.pending == .none &&
    gAuraMoveAfter.currentBatch.isNone &&
    (gAuraMoveAfter.permanentsOf p0).size == 2

  -- Helper setup where `b1` & `b2` are legendary only in Pass 1's pre-batch snapshot (`fragileLordDef` dies in Pass 1),
  -- with a `p0`-owned face-up Aura attached to `b1` and `p2`'s `p2LandDef` sourcing an attachment effect:
  let mkAttSnapGame (attEff : ObjectId → ObjectId → ContinuousEffect) : Game × ObjectId × ObjectId :=
    let g0 :=
      addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0)
            fragileLordDef p0 p0)
          auraBaseDef p0 p0)
        p2LandDef p2 p2
    let bs := (g0.permanentsOf p0).filter (·.name == bear.name)
    let b1 := bs[0]!
    let b2 := bs[1]!
    let lord := (g0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
    let att := (g0.permanentsOf p0).find? (·.name == auraBaseDef.name) |>.get!
    let src := (g0.permanentsOf p2)[0]!
    let gReady :=
      (((g0.record (GameEvent.attached g0.turnNumber (g0.snapshot att) b1.id (cause := testCause))).createEffect
        (attEff att.id src.id) (cause := some testCause)).createEffect
        (.layered (.objects #[b1.id, b2.id]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield lord.id))
        (cause := some testCause)).checkSBA
    (gReady, b1.id, b2.id)

  let (gAttCopy0, acp1, acp2) :=
    mkAttSnapGame (fun attId srcId =>
      .layered (.objects #[attId]) (.copy legAuraDef) (.whileSourceOnBattlefield srcId))
  let gAttCopyAfter := mustApply gAttCopy0 p2 .concede
  let (gAttText0, atx1, atx2) :=
    mkAttSnapGame (fun attId srcId =>
      .layered (.objects #[attId]) (.text (.replaceCreatureType .bear .goblin)) (.whileSourceOnBattlefield srcId))
  let gAttTextAfter := mustApply gAttText0 p2 .concede
  let (gAttTypes0, aty1, aty2) :=
    mkAttSnapGame (fun attId srcId =>
      .layered (.objects #[attId]) (.types .add #[.artifact] #[] #[]) (.whileSourceOnBattlefield srcId))
  let gAttTypesAfter := mustApply gAttTypes0 p2 .concede
  let (gAttAbil0, aab1, aab2) :=
    mkAttSnapGame (fun attId srcId =>
      .layered (.objects #[attId])
        (.abilities { staticAbilities := #[.enchantedCreatureGetsHasAndTypes 1 1 {} #[.hero]] } .none)
        (.whileSourceOnBattlefield srcId))
  let gAttAbilAfter := mustApply gAttAbil0 p2 .concede
  let (gAttL70, al71, al72) :=
    mkAttSnapGame (fun attId srcId =>
      .layered (.objects #[attId]) (.ptModify 2 2) (.whileSourceOnBattlefield srcId))
  let gAttL7WithCol :=
    let src := (gAttL70.permanentsOf p2)[0]!
    let att := (gAttL70.permanentsOf p0).find? (·.name == auraBaseDef.name) |>.get!
    -- Add `.colors` before `checkSBA` on a fresh fixture so it is in `openBatchEffects`:
    let g0 :=
      addPermanent
        (addPermanent
          (addPermanent
            (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0)
            fragileLordDef p0 p0)
          auraBaseDef p0 p0)
        p2LandDef p2 p2
    let bs := (g0.permanentsOf p0).filter (·.name == bear.name)
    let b1 := bs[0]!; let b2 := bs[1]!
    let lord := (g0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
    let att0 := (g0.permanentsOf p0).find? (·.name == auraBaseDef.name) |>.get!
    let src0 := (g0.permanentsOf p2)[0]!
    let _ := (src, att)
    ((((g0.record (GameEvent.attached g0.turnNumber (g0.snapshot att0) b1.id (cause := testCause))).createEffect
      (.layered (.objects #[att0.id]) (.ptModify 2 2) (.whileSourceOnBattlefield src0.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[att0.id]) (.colors .add { red := true }) (.whileSourceOnBattlefield src0.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[b1.id, b2.id]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield lord.id))
      (cause := some testCause)).checkSBA
  let l7Ids := match gAttL7WithCol.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let gAttL7After := mustApply gAttL7WithCol p2 .concede
  let _ := (al71, al72)

  -- Non-legendary subtype Aura & Construct Aura owned by departing `p2` preserve `preBatchLegendSnapshotValid`:
  let mkP2AuraSnap (aDef : CardDef) : Game × Array ObjectId :=
    let g0 :=
      addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 bear p0 p0) bear p0 p0)
          fragileLordDef p0 p0)
        aDef p2 p2
    let bs := (g0.permanentsOf p0).filter (·.name == bear.name)
    let b1 := bs[0]!; let b2 := bs[1]!
    let lord := (g0.permanentsOf p0).find? (·.name == fragileLordDef.name) |>.get!
    let p2Aura := (g0.permanentsOf p2)[0]!
    let gPaused :=
      ((g0.record (GameEvent.attached g0.turnNumber (g0.snapshot p2Aura) b1.id (cause := testCause))).createEffect
        (.layered (.objects #[b1.id, b2.id]) (.types .add #[] #[] #[.legendary]) (.whileSourceOnBattlefield lord.id))
        (cause := some testCause)).checkSBA
    (gPaused, #[b1.id, b2.id])
  let (gSubAura0, subIds) := mkP2AuraSnap nonLegSubAuraDef
  let gSubAuraAfter := mustApply gSubAura0 p2 .concede
  let (gConAura0, conIds) := mkP2AuraSnap constructAuraDef
  let gConAuraAfter := mustApply gConAura0 p2 .concede

  let attEffectsAndAllowlistOk :=
    gAttCopy0.pending == .chooseLegend p0 bear.name #[acp1, acp2] &&
    gAttCopyAfter.pending == .none &&
    gAttText0.pending == .chooseLegend p0 bear.name #[atx1, atx2] &&
    gAttTextAfter.pending == .none &&
    gAttTypes0.pending == .chooseLegend p0 bear.name #[aty1, aty2] &&
    gAttTypesAfter.pending == .none &&
    gAttAbil0.pending == .chooseLegend p0 bear.name #[aab1, aab2] &&
    gAttAbilAfter.pending == .none &&
    l7Ids.size == 2 &&
    gAttL7After.pending == .chooseLegend p0 bear.name l7Ids &&
    gSubAura0.pending == .chooseLegend p0 bear.name subIds &&
    gSubAuraAfter.pending == .chooseLegend p0 bear.name subIds &&
    gConAura0.pending == .chooseLegend p0 bear.name conIds &&
    gConAuraAfter.pending == .chooseLegend p0 bear.name conIds
  let item1aOk := auraCeaseInvalidatedOk && auraMoveInvalidatedOk && attEffectsAndAllowlistOk

  -- 1b. Pass-1-before-Pass-2 SBA batch draining (`tokensOutsideBf` & `.closeBatch origBid` before Pass 2 batch),
  --     `savedIn` preservation, `wasPaused` / `.leavePlayersWhoLost`, `g.over`, and mid-flush second-group pause:
  let tokDef : CardDef := { bear with name := "P41i1 GyToken", isToken := true }
  let gDrain0 :=
    insertObject
      (addPermanent
        (addPermanent
          (addPermanent
            (addPermanent g4 bear p0 p0)
            legBearDef p0 p0)
          zeroToughDef p0 p0)
        p2LandDef p2 p2)
      tokDef p0 (.graveyard p0)
  let drB1 := (gDrain0.permanentsOf p0).find? (fun o => o.name == bear.name && o.printed.supertypes.isEmpty) |>.get!
  let drB2 := (gDrain0.permanentsOf p0).find? (fun o => o.name == bear.name && !o.printed.supertypes.isEmpty) |>.get!
  let drZero := (gDrain0.permanentsOf p0).find? (·.name == zeroToughDef.name) |>.get!
  let drP2Src := (gDrain0.permanentsOf p2)[0]!
  let drTokId := (gDrain0.player p0).graveyard.back!
  let gDrain1 :=
    addPermanent gDrain0 legAuraDef p2 p2
  let drAura := (gDrain1.permanentsOf p2).find? (·.name == legAuraDef.name) |>.get!
  let gDrainPaused :=
    (((gDrain1.record (GameEvent.attached gDrain1.turnNumber (gDrain1.snapshot drAura) drB1.id (cause := testCause))).createEffect
      (.layered (.objects #[drZero.id]) (.ptModify 0 1) (.whileSourceOnBattlefield drP2Src.id))
      (cause := some testCause))).checkSBA
  let origBid := gDrainPaused.currentBatch.get!.1
  -- Token is still in graveyard while Pass 1 paused at `legendGroups`:
  let tokStillInGyAtPause := (gDrainPaused.findObject? drTokId).any (·.zone == .graveyard p0)
  let preConcedeEvIdx := gDrainPaused.events.size
  let gDrainAfterConcede := mustApply gDrainPaused p2 .concede
  let drainSlice := gDrainAfterConcede.events.extract preConcedeEvIdx gDrainAfterConcede.events.size
  let tokCeaseIdx? := drainSlice.findIdx? fun ev =>
    match ev with
    | .rules _ (.zone (.ceasedToExist eo)) _ b => eo.id == some drTokId && b == some origBid
    | _ => false
  let closeOrigIdx? :=
    tokCeaseIdx?.bind fun ti =>
      (drainSlice.extract ti drainSlice.size).findIdx? (fun ev =>
        match ev with
        | .engine _ .clearPausedBatch _ => true
        | _ => false) |>.map (· + ti)
  let zeroDeathIdxAndBatch? := Id.run do
    for idx in [0:drainSlice.size] do
      if let .rules _ (.zone (.moved before _ .battlefield (.graveyard _) ..)) _ (some b) := drainSlice[idx]! then
        if before.id == some drZero.id then return some (idx, b)
    return none
  let pass1BeforePass2Ok :=
    tokStillInGyAtPause &&
    (match tokCeaseIdx?, closeOrigIdx?, zeroDeathIdxAndBatch? with
     | some ti, some ci, some (zi, pass2Bid) => ti < ci && ci < zi && pass2Bid != origBid
     | _, _, _ => false) &&
    gDrainAfterConcede.currentBatch.isNone &&
    gDrainAfterConcede.pending == .none

  -- Direct `checkSBACounted` AND `checkSBACountedWithLeavesCore` with `savedIn := some (.mayPayGeneric p0 1)` + `p1` at 0 life:
  let (gDirInv0, _) := gDrainPaused.move drB2.id .exile none (cause := some testCause)
  let (gDirCounted, dirDid) := gDirInv0.checkSBACounted
  let gSavedInv0 := gDirInv0.setLifeTotal p1 0
  let (gSavedLeaves, savedDid, savedOut?, popOut, depOut, rwOut) :=
    gSavedInv0.checkSBACountedWithLeavesCore (savedIn := some (.mayPayGeneric p0 1)) (deferRestore := false)
  let savedAndLeavesOk :=
    dirDid &&
    (gDirCounted.findObject? drTokId).isNone &&
    gDirCounted.currentBatch.isNone &&
    savedDid &&
    savedOut?.isNone &&
    !popOut &&
    depOut == #[p1] &&
    rwOut.isNone &&
    (gSavedLeaves.player p1).leftTheGame &&
    (gSavedLeaves.findObject? drTokId).isNone &&
    gSavedLeaves.pending == .mayPayGeneric p0 1 &&
    gSavedLeaves.pendingReplacement.isNone

  -- `g.over` during flush in a 2-player game returns `(g, true)` without opening a post-game Pass 2 batch:
  let g2p0 :=
    insertObject
      (addPermanent (addPermanent afterDraw legBearDef p0 p0) legBearDef p0 p0)
      tokDef p0 (.graveyard p0)
  let g2pPaused := g2p0.checkSBA
  let g2pOrigBid := g2pPaused.currentBatch.get!.1
  let g2pIds := match g2pPaused.pending with | .chooseLegend _ _ ids => ids | _ => #[]
  let (g2pExiled, _) := g2pPaused.move g2pIds[0]! .exile none (cause := some testCause)
  let g2pOppLost :=
    (g2pExiled.record (GameEvent.playerLost g2pExiled.turnNumber p1 .conceded (cause := some testCause))).record
      (GameEvent.playerLeftGame g2pExiled.turnNumber p1 (cause := some testCause))
  let preOverEvIdx := g2pOppLost.events.size
  let (g2pFlushedOver, overDid) := g2pOppLost.checkSBACounted
  let noPostOverOpenBatch :=
    !(g2pFlushedOver.events.extract preOverEvIdx g2pFlushedOver.events.size).any fun ev =>
      (ev.batch.isSome && ev.batch != some g2pOrigBid) ||
        match ev with | .engine _ (.pauseBatch ..) _ => true | _ => false

  -- Mid-flush pause on a second legend group (`restGroups`) stays in `origBid` without opening a new batch:
  let gTwoGrp0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 legBearDef p0 p0) legBearDef p0 p0)
        legHeroDef p0 p0)
      legHeroDef p0 p0
  let gTwoGrpPaused := gTwoGrp0.checkSBA
  let twoGrpOrigBid := gTwoGrpPaused.currentBatch.get!.1
  let (firstGrpName, firstGrpIds) :=
    match gTwoGrpPaused.pending with | .chooseLegend _ nm ids => (nm, ids) | _ => ("", #[])
  let secondGrpName := if firstGrpName == bear.name then hero.name else bear.name
  let (gTwoGrpInv, _) := gTwoGrpPaused.move firstGrpIds[0]! .exile none (cause := some testCause)
  let (gTwoGrpMid, midDid) := gTwoGrpInv.checkSBACounted
  let midFlushPauseOk :=
    midDid &&
    gTwoGrpMid.currentBatch.map Prod.fst == some twoGrpOrigBid &&
    (match gTwoGrpMid.pending with | .chooseLegend q nm ids => q == p0 && nm == secondGrpName && ids.size == 2 | _ => false) &&
    g2pFlushedOver.over && overDid && noPostOverOpenBatch
  let item1bOk := pass1BeforePass2Ok && savedAndLeavesOk && midFlushPauseOk

  -- 1c. `hasFollowingSeq` propagation across `.seq` (even when `g0.pendingReplacement.isSome`) and `.restorePending`:
  let gManaSeqBase := (addPermanent g4 p2LandDef p0 p0).change (.priority p2)
  let seqLand := (gManaSeqBase.permanentsOf p0)[0]!
  let manaPostSac : PendingReplacement :=
    .finishActivateManaAbilityPostSac p0 seqLand.id seqLand.printed.name
      (gManaSeqBase.snapshot seqLand) #[.colorless] false (some 0) .none 0 false .none
  -- (i) `.seq` when `g0.pendingReplacement.isSome`: `first` still gets `hasFollowingSeq == true` and does NOT grant priority to `p0`!
  let gSeqWithPending0 :=
    gManaSeqBase.changes #[
      .pushContinuationFrame {},
      .pendingReplacement (some (.gainLife p1 2 (some testCause))) ]
  let gSeqWithPendingDone :=
    (gSeqWithPending0.resumePendingReplacement
      (.seq manaPostSac (.gainLife p0 4 (some testCause)))).drainPendingContinuations
  -- (ii) `.restorePending` (`resumePoppedIfNoPrompt`) inside `.seq`:
  let gRpNoPrompt0 :=
    gManaSeqBase.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement manaPostSac ]
  let gRpNoPromptDone :=
    gRpNoPrompt0.resumePendingReplacement
      (.seq (.restorePending .none true none #[] none) (.gainLife p0 5 (some testCause)))
  -- (iii) `.restorePending` (`shouldSplitBatch`) inside `.seq`:
  let splitBid : BatchId := ⟨gManaSeqBase.nextBatchId⟩
  let gRpSplit0 :=
    gManaSeqBase.changes #[
      .pauseBatch splitBid (some testCause) gManaSeqBase.objects gManaSeqBase.players
        gManaSeqBase.activeEffects .none gManaSeqBase.stack,
      .pushContinuationFrame {},
      .pushOuterPendingReplacement (.seq (.closeBatch splitBid gManaSeqBase.events.size) manaPostSac) ]
  let gRpSplitDone :=
    gRpSplit0.resumePendingReplacement
      (.seq (.restorePending .none true none #[] none) (.gainLife p0 6 (some testCause)))
  -- (iv) `.restorePending` (`poppedTail?` on proposal reversal) inside `.seq`:
  let (gRpTail0, rpAb) := gManaSeqBase.putStackAbility seqLand p0 (abilityEffect := some (Effect.gainLife 1))
  let rpProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := rpAb.id, original := rpAb
    originalSnapshot := gRpTail0.snapshot rpAb, kind := .activatedAbility, sourceId := some seqLand.id
  }
  let gRpTailReady :=
    gRpTail0.changes #[
      .pushContinuationFrame {},
      .pushOuterPendingReplacement manaPostSac,
      .saveProposalCheckpoint,
      .proposedSpell (some rpProp) ]
  let gRpTailDone :=
    gRpTailReady.resumePendingReplacement
      (.seq (.restorePending (.activateManaAbilities p1) true none #[p1] none) (.gainLife p0 7 (some testCause)))
  -- (v) `.restorePending` (`ckptWasRandom` with `restored?.isSome`) preserves `restored?` without premature priority:
  let gRpRnd0 :=
    gManaSeqBase.changes #[
      .pushContinuationFrame { afterRandom := .draw p0 1 },
      .pending (.resolveRandom (.shuffleLibrary p0)),
      .pendingReplacement (some (.gainLife p0 8 (some testCause))),
      .saveProposalCheckpoint ]
  let (gRpRnd1, rndAb) := gRpRnd0.putStackAbility seqLand p0 (abilityEffect := some (Effect.gainLife 1))
  let rndProp : ProposedSpell := {
    caster := p0, cost := ManaCost.ofGeneric 1, spellId := rndAb.id, original := rndAb
    originalSnapshot := gRpRnd1.snapshot rndAb, kind := .activatedAbility, sourceId := some seqLand.id
  }
  let gRpRndDone :=
    (gRpRnd1.change (.proposedSpell (some rndProp))).resumePendingReplacement
      (.restorePending (.activateManaAbilities p1) false none #[p1] none)
  let baseP0Life := (gManaSeqBase.player p0).life
  let item1cOk :=
    gSeqWithPendingDone.priority == p2 &&
    (gSeqWithPendingDone.player p0).life == baseP0Life + 4 &&
    (gSeqWithPendingDone.player p1).life == (gManaSeqBase.player p1).life + 2 &&
    gRpNoPromptDone.priority == p2 &&
    (gRpNoPromptDone.player p0).life == baseP0Life + 5 &&
    gRpSplitDone.priority == p2 &&
    gRpSplitDone.currentBatch.isNone &&
    (gRpSplitDone.player p0).life == baseP0Life + 6 &&
    gRpTailDone.priority == p2 &&
    gRpTailDone.proposedSpell.isNone &&
    (gRpTailDone.player p0).life == baseP0Life + 7 &&
    gRpRndDone.pending == .resolveRandom (.shuffleLibrary p0) &&
    gRpRndDone.pendingReplacement == some (.gainLife p0 8 (some testCause))

  mustHold41i1 "1a.legendAttSnapshot" item1aOk &&
  mustHold41i1 "1b.sbaBatchDrain" item1bOk &&
  mustHold41i1 "1c.hasFollowingSeq" item1cOk &&
  mustHold41i1 "1.replay"
    (replayOk41i1 #[gAuraCeaseAfter, gAuraMoveAfter, gAttCopyAfter, gAttTextAfter,
      gAttTypesAfter, gAttAbilAfter, gAttL7After, gSubAuraAfter, gConAuraAfter,
      gDrainAfterConcede, gDirCounted, gSavedLeaves, g2pFlushedOver, gTwoGrpMid,
      gSeqWithPendingDone, gRpNoPromptDone, gRpSplitDone, gRpTailDone, gRpRndDone])

end Phase41Item1EventAlignment

section Phase41Item2EventAlignment

private def mustHold41i2 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase41Item2EventAlignment failed: {label}"

private def replayOk41i2 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let stealerDef : CardDef := { name := "P41i2 Stealer", types := #[.artifact] }
  let leyADef : CardDef := { name := "P41i2 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P41i2 LeyB", types := #[.enchantment] }
  let embDef : CardDef := { name := "P41i2 FraEmblem", types := #[] }

  -- 2a. Simultaneous outer-`pre` `playerLeavesGameCore` owned-object + `.control` reconciliation:
  --     (i) Unchanged survivor controller keeps `.ringBearer` & combat without departed return logs;
  --     (ii) Empty `activeEids` / `ctrlEids` with `pre`-vs-post-`preExpire` control changes emits `"reverts to ..."`
  --          and exiles CR 800.4c orphans;
  --     (iii) `linkedExile` & `bodyExileCont?` CR 800.4c exile queues are deduplicated.
  let gSim0 :=
    addPermanent
      (addPermanent (addPermanent g4 bear p0 p0) hero p0 p0)
      stealerDef p2 p2
  let rbBear := (gSim0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let revHero := (gSim0.permanentsOf p0).find? (·.name == hero.name) |>.get!
  let p2Stealer := (gSim0.permanentsOf p2)[0]!
  let gSim1 :=
    ((((((gSim0.createEffect
      (.layered (.objects #[rbBear.id]) (.control p2) (.untilSourceLeaves p2Stealer.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[rbBear.id]) (.control p0) .indefinite)
      (cause := some testCause)).createEffect
      (.layered (.objects #[revHero.id]) (.control p2) (.untilSourceLeaves p2Stealer.id))
      (cause := some testCause)).record
      (GameEvent.designation gSim0.turnNumber (gSim0.snapshot rbBear) .ringBearer true (cause := testCause))).record
      (GameEvent.attacked gSim0.turnNumber p0 (gSim0.snapshot rbBear) p1 (cause := testCause))))
  let preSimLogIdx := gSim1.log.size
  let gSimAfter := mustApply gSim1 p2 .concede
  let simLogs := gSimAfter.log.extract preSimLogIdx gSimAfter.log.size
  let p2Name := (g4.player p2).name
  let p0Name := (g4.player p0).name
  let simSurvivorOk :=
    (gSimAfter.player p0).ringBearerId == some rbBear.id &&
    (gSimAfter.object! rbBear.id).status.attacking &&
    !simLogs.any (fun s => (s.splitOn s!"returns to {p2Name}'s control").length > 1) &&
    !simLogs.any (fun s => (s.splitOn rbBear.name).length > 1) &&
    -- `revHero` was controlled ONLY via `.untilSourceLeaves p2Stealer.id` (`activeEids` is empty after `preExpire`!),
    -- yet `pre`-vs-post-`preExpire` diffing puts `revHero` in `candidates` and logs `"reverts to Chandra's control"`!
    simLogs.any (fun s => s == s!"{revHero.name} reverts to {p0Name}'s control")

  -- Empty `ctrlEids` (`c == p0 != p2`) where `p2`'s leaving source expires `.untilSourceLeaves` `.control p0`
  -- on departed `p1`'s permanent `p1Orph` -> exiled under CR 800.4c via `pre`-vs-post-`preExpire` `candidates`:
  let gEmptyCtrl0 :=
    addPermanent (addPermanent g4 bear p0 p1) stealerDef p2 p2
  let p1Orph := (gEmptyCtrl0.permanentsOf p1)[0]!
  let p2Src := (gEmptyCtrl0.permanentsOf p2)[0]!
  let gEmptyCtrl1 :=
    (gEmptyCtrl0.createEffect
      (.layered (.objects #[p1Orph.id]) (.control p0) (.untilSourceLeaves p2Src.id))
      (cause := some testCause)).concede p1
  let gEmptyCtrlAfterP2 := mustApply gEmptyCtrl1 p2 .concede
  let emptyCtrlOrphExiledOk :=
    (gEmptyCtrl1.permanentsOf p0).any (·.id == p1Orph.id) &&
    (gEmptyCtrlAfterP2.followMovedToZone? p1Orph.id (· == .exile)).isSome

  -- Deduplicated `linkedExile` & `bodyExileCont?` CR 800.4c exile queues when replacement choice is open:
  let gDedup0 :=
    addPermanent
      (addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 bear p0 p0) hero p0 p1)
          stealerDef p2 p2)
        leyADef p0 p0)
      leyBDef p0 p0
  let cagedBear := (gDedup0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let bodyOrph := (gDedup0.permanentsOf p1)[0]!
  let p2Cage := (gDedup0.permanentsOf p2)[0]!
  let dLeyA := (gDedup0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let dLeyB := (gDedup0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some dLeyA, counterKind := some .plusOnePlusOne }
  let dRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some dLeyB, counterKind := some .plusOnePlusOne }
  let gDedup1 :=
    (((((gDedup0.exileUntilSourceLeaves (some p2Cage.id) cagedBear (cause := some testCause)).createEffect
      (.layered (.objects #[bodyOrph.id]) (.control p2) .indefinite) (cause := some testCause)).concede p1).createEffect
      (.replacement {
        id := dRidA, source := some dLeyA, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some dLeyB, controller := some p0, affectedPlayer := p0,
        kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
  -- Open a `.chooseReplacement` pause on `p0`, then have `p2` concede while paused:
  let (gDedupOpen, _) := gDedup1.createOneToken p0 hero (cause := some testCause)
  let preDedupLogIdx := gDedupOpen.log.size
  let gDedupAfterP2 := mustApply gDedupOpen p2 .concede
  -- Resolve token's replacement choice AND `cagedBear`'s `linkedExile` return replacement choice:
  let gDedupRes1 := mustApply gDedupAfterP2 p0 (.chooseReplacement dRidA)
  let gDedupRes2 := mustApply gDedupRes1 p0 (.chooseReplacement dRidA)
  let dedupLogs := gDedupRes2.log.extract preDedupLogIdx gDedupRes2.log.size
  let bearReturnLogs := dedupLogs.filter (· == s!"{bear.name} returns to the battlefield")
  let orphExileLogs := dedupLogs.filter (fun s => (s.splitOn bodyOrph.name).length > 1 && (s.splitOn "is exiled").length > 1)
  let dedupQueuesOk :=
    gDedupRes2.pending == .none &&
    gDedupRes2.queuedLinkedExile.isEmpty &&
    ((gDedupRes2.permanentsOf p0).filter (·.name == bear.name)).size == 1 &&
    (gDedupRes2.followMovedToZone? bodyOrph.id (· == .exile)).isSome &&
    bearReturnLogs.size == 1 &&
    orphExileLogs.size == 1
  let item2aOk := simSurvivorOk && emptyCtrlOrphExiledOk && dedupQueuesOk

  -- 2b. Unified outer-`pre` `Turns.expireFraUntilTurnEffects` (`skipControl := false`) with command-zone FRA emblem:
  let gFra0 :=
    insertObject (addPermanent g4 bear p0 p0) embDef p2 .command (some p2)
  let fraBear := (gFra0.permanentsOf p0)[0]!
  let fraEmb := (gFra0.objects.filter (·.zone == .command))[0]!
  let gFra1 :=
    (((((gFra0.createEffect (.gameRule (.fraEmblem fraEmb.id) (.untilNextTurnOf p0))
      (cause := some testCause)).createEffect
      (.layered (.objects #[fraBear.id]) (.control p2) (.whileInZone fraEmb.id .command))
      (cause := some testCause)).createEffect
      (.layered (.objects #[fraBear.id]) (.control p0) (.untilNextTurnOf p0))
      (cause := some testCause)).record
      (GameEvent.designation gFra0.turnNumber (gFra0.snapshot fraBear) .ringBearer true (cause := testCause))).record
      (GameEvent.attacked gFra0.turnNumber p0 (gFra0.snapshot fraBear) p1 (cause := testCause)))
  let preFraLogIdx := gFra1.log.size
  let gFraAfter := gFra1.expireFraUntilTurnEffects p0 (skipControl := false)
  let fraLogs := gFraAfter.log.extract preFraLogIdx gFraAfter.log.size
  let item2bOk :=
    (gFraAfter.findObject? fraEmb.id).isNone &&
    gFraAfter.activeEffects.isEmpty &&
    (gFraAfter.player p0).ringBearerId == some fraBear.id &&
    (gFraAfter.object! fraBear.id).status.attacking &&
    !fraLogs.any (fun s => (s.splitOn p2Name).length > 1)

  mustHold41i2 "2a.simLeaveAndDedup" item2aOk &&
  mustHold41i2 "2b.unifiedFraUntilTurn" item2bOk &&
  mustHold41i2 "2.replay"
    (replayOk41i2 #[gSimAfter, gEmptyCtrlAfterP2, gDedupAfterP2, gDedupRes2, gFraAfter])

end Phase41Item2EventAlignment

section Phase41Item3EventAlignment

private def mustHold41i3 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase41Item3EventAlignment failed: {label}"

private def replayOk41i3 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let p3 : PlayerId := ⟨3⟩
  let g4 :=
    (afterDraw.change (.addPlayer { id := p2, name := "Liliana" })).change
      (.addPlayer { id := p3, name := "Jace" })
  let srcDefA : CardDef := creature "P41i3 SrcA" ManaCost.empty #["Construct"] 3 3
  let srcDefB : CardDef := creature "P41i3 SrcB" ManaCost.empty #["Construct"] 3 3
  let cageDef : CardDef := { name := "P41i3 Cage", types := #[.artifact] }
  let leyADef : CardDef := { name := "P41i3 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P41i3 LeyB", types := #[.enchantment] }
  let noTrampleScope : ObjectScope := .creaturesWithout #[Keyword.trample]

  -- 3a. `Core.effectPhasingAllows` enforces `durationActiveAt` for `EventCause.oneShotEffect` dynamic durations
  --     (`.whileSourceOnBattlefield`, `.whileSourceHasCounter`) while preserving `.untilSourceLeaves`/clock durations & `lockOk`:
  let gDur0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g4 bear p0 p0) hero p0 p0)
        srcDefA p0 p0)
      srcDefB p0 p0
  let phBear := (gDur0.permanentsOf p0).find? (·.name == bear.name) |>.get!
  let phHero := (gDur0.permanentsOf p0).find? (·.name == hero.name) |>.get!
  let srcA := (gDur0.permanentsOf p0).find? (·.name == srcDefA.name) |>.get!
  let srcB := (gDur0.permanentsOf p0).find? (·.name == srcDefB.name) |>.get!
  -- Phase `srcA` out FIRST (`srcA` is phased out when `phBear` & `phHero` phase out at `pIdx`; `srcB` has 0 `.charge` counters at `pIdx`):
  let gSrcAOut := gDur0.phaseOut srcA (cause := some testCause)
  let gDurCreated :=
    (((gSrcAOut.createEffect
      (.layered (.objects #[phBear.id]) (.control p2) (.whileSourceOnBattlefield srcA.id))
      (cause := some testCause)).createEffect
      (.layered (.objects #[phBear.id]) (.copy srcDefB) (.whileSourceHasCounter srcB.id .charge))
      (cause := some testCause)).createEffect
      (.layered (.objects #[phHero.id]) (.control p1) (.untilSourceLeaves srcA.id))
      (cause := some testCause))
  let gBothPhOut :=
    (gDurCreated.phaseOut (gDurCreated.object! phBear.id) (cause := some testCause)).phaseOut
      (gDurCreated.object! phHero.id) (cause := some testCause)
  -- Activate `srcA` (phase in) and `srcB` (add `.charge` counter) + create a one-shot non-explicit effect while `phBear` is phased out:
  let gActivatedWhileOut :=
    (((gBothPhOut.phaseIn (gBothPhOut.object! srcA.id) (cause := some testCause)).recordPutCounters
      srcB.id .charge 1 (some p0) (cause := some testCause)).createEffect
      (.layered noTrampleScope (.ptModify 4 4) .untilEndOfTurn) (cause := some testCause))
  let excludedWhilePhasedOut :=
    gActivatedWhileOut.controllerOf (gActivatedWhileOut.object! phBear.id) == some p0 &&
    gActivatedWhileOut.name (gActivatedWhileOut.object! phBear.id) == bear.name &&
    -- `.untilSourceLeaves` (`isTimedResolvingDuration == true`) keeps its short-circuit:
    gActivatedWhileOut.controllerOf (gActivatedWhileOut.object! phHero.id) == some p1
  let gBearPhIn := gActivatedWhileOut.phaseIn (gActivatedWhileOut.object! phBear.id) (cause := some testCause)
  let bearIn := gBearPhIn.object! phBear.id
  let item3aOk :=
    excludedWhilePhasedOut &&
    gBearPhIn.controllerOf bearIn == some p2 &&
    gBearPhIn.name bearIn == srcDefB.name &&
    -- `lockOk` still excludes the non-explicit `oneShotEffect` `.ptModify 4 4` created while `phBear` was phased out:
    gBearPhIn.power bearIn == 3 &&
    gBearPhIn.toughness bearIn == 3

  -- 3b. Phasing-aware `Core.hasSummoningSickness` across initial (`o0At.status.phasedOut`) & forward (`oAt.status.phasedOut`) checks:
  let gSick0 := addPermanent (addPermanent g4 bear p1 p1) srcDefA p0 p0
  let stBear := (gSick0.permanentsOf p1)[0]!
  let stSrc := (gSick0.permanentsOf p0)[0]!
  let gSick1 :=
    readyControlledForTurn
      (gSick0.createEffect (.layered (.objects #[stBear.id]) (.control p0) (.whileSourceOnBattlefield stSrc.id))
        (cause := some testCause)) p0
  let readyBeforePhaseToggle := !gSick1.hasSummoningSickness (gSick1.object! stBear.id)
  -- Phasing `stSrc` out and back in mid-turn briefly returns `stBear` to `p1` and re-steals it -> summoning sick!
  let gSrcPhOut := gSick1.phaseOut (gSick1.object! stSrc.id) (cause := some testCause)
  let gSrcPhBackIn := gSrcPhOut.phaseIn (gSrcPhOut.object! stSrc.id) (cause := some testCause)
  let sickAfterSrcToggle := gSrcPhBackIn.hasSummoningSickness (gSrcPhBackIn.object! stBear.id)

  -- Forward check: `p0Bear` phases out mid-turn, `.control p1` is created & expires while `p0Bear` is phased out
  -- (never affecting phased-out `p0Bear`!), then `p0Bear` phases in -> NOT summoning sick!
  let gFwdPh0 := readyControlledForTurn (addPermanent g4 bear p0 p0) p0
  let fwdBear := (gFwdPh0.permanentsOf p0)[0]!
  let gFwdOut := gFwdPh0.phaseOut fwdBear (cause := some testCause)
  let gFwdCtrlCreated :=
    gFwdOut.createEffect (.layered (.objects #[fwdBear.id]) (.control p1) .untilEndOfTurn) (cause := some testCause)
  let fwdCtrlEid := gFwdCtrlCreated.activeEffects.back!.1
  let gFwdCtrlExpired := gFwdCtrlCreated.expireEffectById fwdCtrlEid (cause := some testCause)
  let gFwdBackIn := gFwdCtrlExpired.phaseIn (gFwdCtrlExpired.object! fwdBear.id) (cause := some testCause)
  let notSickAcrossPhasedOutCtrl := !gFwdBackIn.hasSummoningSickness (gFwdBackIn.object! fwdBear.id)

  -- Initial check (`effStartIdx? == none` via `quiet`): stolen creature already phased out at start of log
  -- (`o0At.status.phasedOut == true`, `g0At.initialControllerOf o0At == some p1 != some p0`) phases in under `p0` -> NOT summoning sick!
  let gInitPhQuiet := quiet (gSick1.phaseOut (gSick1.object! stBear.id) (cause := some testCause))
  let gInitPhIn := gInitPhQuiet.phaseIn (gInitPhQuiet.object! stBear.id) (cause := some testCause)
  let initPhasedSkipOk := !gInitPhIn.hasSummoningSickness (gInitPhIn.object! stBear.id)
  let item3bOk :=
    readyBeforePhaseToggle &&
    sickAfterSrcToggle &&
    notSickAcrossPhasedOutCtrl &&
    initPhasedSkipOk

  -- 3c. `inProgressExtraSeats` queued-extra-turn phase-in in `Phasing.departedNextTurnWouldHaveBegunSince`
  --     and materialized / entered / token-created phased-out controller lookup in `Phasing.phaseInControlled`:
  let cfg3Teams : StartConfig := {
    seats := #[
      { name := "A0", deck := testRedDeck, teammate := some ⟨1⟩ },
      { name := "A1", deck := testGreenDeck, teammate := some ⟨0⟩ },
      { name := "B0", deck := testRedDeck, teammate := some ⟨3⟩ },
      { name := "B1", deck := testGreenDeck, teammate := some ⟨2⟩ },
      { name := "C0", deck := testRedDeck, teammate := some ⟨5⟩ },
      { name := "C1", deck := testGreenDeck, teammate := some ⟨4⟩ }
    ]
    format := .constructed
    seed := 413
    startingPlayer := some 0
  }
  let gTeams0 : Game :=
    match Start.start cfg3Teams with
    | .ok g => (keepOpeningHands g 30).advanceStep
    | .error e => panic! e
  -- Finish `⟨0⟩`'s seat into `⟨1⟩`'s seat, add a first extra turn for Team A, and advance into BOTH seats (`⟨0⟩` then `⟨1⟩`) of that extra turn:
  let gRegA1 := gTeams0.startNextTurnAndBegin
  let gWithEx1 := gRegA1.record (GameEvent.extraTurnAdded gRegA1.turnNumber ⟨0⟩ (cause := testCause))
  let gExSeat0 := gWithEx1.startNextTurnAndBegin
  let gExSeat1 := gExSeat0.startNextTurnAndBegin
  -- Now on `⟨1⟩` (final seat of current extra turn, `inProgressExtraSeats == 0`), Team A earns a SECOND queued extra turn,
  -- steals Team B's `qBear` and phases it out, then concedes:
  let gExSeat1WithBear := addPermanent gExSeat1 bear ⟨2⟩ ⟨2⟩
  let qBear := (gExSeat1WithBear.permanentsOf ⟨2⟩)[0]!
  let gQueuedEx :=
    ((gExSeat1WithBear.record (GameEvent.extraTurnAdded gExSeat1WithBear.turnNumber ⟨0⟩ (cause := testCause))).createEffect
      (.layered (.objects #[qBear.id]) (.control ⟨1⟩) .indefinite) (cause := some testCause))
  let gQueuedPhOut := gQueuedEx.phaseOut (gQueuedEx.object! qBear.id) (cause := some testCause)
  let gTeamAConceded := mustApply gQueuedPhOut ⟨0⟩ .concede
  let gNextAfterQueuedSkip := gTeamAConceded.startNextTurnAndBegin
  let queuedExtraPhaseInOk :=
    gNextAfterQueuedSkip.activePlayer == ⟨2⟩ &&
    !(gNextAfterQueuedSkip.object! qBear.id).status.phasedOut

  -- Materialized, `.moved`, and `.created` phased-out permanents phase in when departed phase-out controller `p1`'s turn would have begun:
  let gMat0 :=
    insertObject
      (insertObject g4 hero p0 .exile)
      bear p0 .battlefield (some p0) { summoningSick := false, phasedOut := false }
  let preBear := (gMat0.permanentsOf p0)[0]!
  let exHero := (gMat0.objects.filter (·.zone == .exile))[0]!
  -- Create `.control p1` on all permanents of `p0`? Use `.creaturesWithout { trample := true }` `.control p1` (static) so newly materialized/entered/created creatures are controlled by `p1` when they arrive phased out!
  let gMatCtrl :=
    gMat0.createEffect (.layered noTrampleScope (.control p1) .indefinite)
      (cause := some (.gameRule .staticAbility))
  let gMat1 :=
    insertObject gMatCtrl bear p0 .battlefield (some p1) { summoningSick := false, phasedOut := true }
  let matPhId := gMat1.objects.back!.id
  let exSnap := gMat1.snapshot exHero
  let gMat2 :=
    gMat1.record (GameEvent.moved gMat1.turnNumber exSnap .exile .battlefield
      (after := some { exSnap with zone := .battlefield, controller := some p1, phasedOut := true, summoningSick := true })
      (cause := testCause))
  let movedPhId := exHero.id
  let (_, sampleTok) := gMat2.createOneToken p1 srcDefA (cause := some testCause)
  let tokSnap : EventObject := {
    id := some sampleTok.id
    name := srcDefA.name
    types := srcDefA.types
    subtypes := CardSubtype.ofSubtypes srcDefA.subtypes
    power := srcDefA.power
    toughness := srcDefA.toughness
    printed := some { srcDefA with isToken := true }
    owner := p1
    controller := some p1
    zone := .battlefield
    token := true
    phasedOut := true
    summoningSick := true
  }
  let gMat3 := gMat2.record (GameEvent.created gMat2.turnNumber p1 tokSnap (cause := testCause))
  let createdPhId := sampleTok.id
  let _ := preBear
  -- Also materialize a `p1`-defaultController phased-out permanent and drop `p1` via `playerLost`+`playerLeftGame` so `g.controllerOf` is `none` (testing `fallbackCtrlOf`):
  let gMat4 :=
    insertObject gMat3 srcDefB p0 .battlefield (some p1) { summoningSick := false, phasedOut := true }
  let fallbackPhId := gMat4.objects.back!.id
  let gP1DepartedRaw :=
    ((gMat4.expireMatching (fun _ => true) (cause := some testCause)).record
      (GameEvent.playerLost gMat4.turnNumber p1 .conceded (cause := some testCause))).record
      (GameEvent.playerLeftGame gMat4.turnNumber p1 (cause := some testCause))
  let preSkipP1Idx := gP1DepartedRaw.events.size
  let gAfterSkipP1 := gP1DepartedRaw.startNextTurnAndBegin
  let skipP1Events := gAfterSkipP1.events.extract preSkipP1Idx gAfterSkipP1.events.size
  let phasedInAndExiled8004c (oid : ObjectId) : Bool :=
    skipP1Events.any (fun ev =>
      match ev.change with
      | .rules (.permanent (.phasedIn eo _)) => eo.id == some oid
      | _ => false) &&
    skipP1Events.any (fun ev =>
      match ev.change with
      | .rules (.zone (.moved before _ .battlefield .exile ..)) =>
        before.id == some oid && !before.phasedOut
      | _ => false)
  let matMovedCreatedPhaseInOk :=
    gAfterSkipP1.activePlayer == p2 &&
    phasedInAndExiled8004c matPhId &&
    (gAfterSkipP1.followMovedToZone? matPhId (· == .exile)).isSome &&
    phasedInAndExiled8004c movedPhId &&
    (gAfterSkipP1.followMovedToZone? movedPhId (· == .exile)).isSome &&
    phasedInAndExiled8004c createdPhId &&
    (gAfterSkipP1.findObject? createdPhId).isNone &&
    phasedInAndExiled8004c fallbackPhId &&
    (gAfterSkipP1.followMovedToZone? fallbackPhId (· == .exile)).isSome
  let item3cOk := queuedExtraPhaseInOk && matMovedCreatedPhaseInOk

  -- 3d. Multi-extra-turn mid-pause departure expiry in `Turns.continueStartNextTurn`
  --     (both `nextExtra?.isSome` and `nextExtra?.isNone` with multiple dead extra turns):
  let mkPausedTurnStart (extraSeats : Array PlayerId) : Game × ReplacementId :=
    let g0 :=
      addPermanent
        (addPermanent
          (addPermanent (addPermanent g4 cageDef p0 p1) bear p0 p0)
          leyADef p0 p0)
        leyBDef p0 p0
    let p1Cage := (g0.permanentsOf p1)[0]!
    let cBear := (g0.permanentsOf p0).find? (·.name == bear.name) |>.get!
    let tLeyA := (g0.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
    let tLeyB := (g0.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
    let tRidA : ReplacementId := { kind := .entersWithExtraCounters, object := some tLeyA, counterKind := some .plusOnePlusOne }
    let tRidB : ReplacementId := { kind := .entersWithExtraCounters, object := some tLeyB, counterKind := some .plusOnePlusOne }
    let g1 :=
      extraSeats.foldr (fun ep acc => acc.record (GameEvent.extraTurnAdded acc.turnNumber ep (cause := testCause))) g0
    let g2 :=
      (((((((g1.exileUntilSourceLeaves (some p1Cage.id) cBear (cause := some testCause)).createEffect
        (.layered (.objects #[p1Cage.id]) (.control p0) (.untilNextTurnOf p1))
        (cause := some testCause)).createEffect
        (.layered noTrampleScope (.ptModify 1 1) (.untilNextTurnOf p2))
        (cause := some testCause)).createEffect
        (.layered noTrampleScope (.ptModify 2 2) (.untilNextTurnOf p3))
        (cause := some testCause)).concede p1).createEffect
        (.replacement {
          id := tRidA, source := some tLeyA, controller := some p0, affectedPlayer := p0,
          kind := .entersWithExtraCounters none .plusOnePlusOne 1 }) (cause := some testCause)).createEffect
        (.replacement {
          id := tRidB, source := some tLeyB, controller := some p0, affectedPlayer := p0,
          kind := .entersWithExtraCounters none .plusOnePlusOne 2 }) (cause := some testCause))
    (g2, tRidA)

  -- Branch (i) `nextExtra?.isSome`: `extraTurns == #[p2, p3]`, `continueStartNextTurn p2 #[p1] true` pauses on `p1`'s CR 800.4c `linkedExile` return;
  -- while paused, `p2` concedes (`!g.stillInGame p2`, `nextExtra? == some p3`), then `p0` resolves replacement -> `p2`'s effect expires AND `p3`'s extra turn begins!
  let (gExSome0, ridSome) := mkPausedTurnStart #[p2, p3]
  let gExSomePaused := gExSome0.continueStartNextTurn p2 #[p1] true
  let gExSomeP2Gone := mustApply gExSomePaused p2 .concede
  let gExSomeResumed := mustApply gExSomeP2Gone p0 (.chooseReplacement ridSome)
  let nextExtraSomeOk :=
    gExSomeResumed.activePlayer == p3 &&
    !gExSomeResumed.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf p2) &&
    -- `p3`'s `.untilNextTurnOf p3` also expired as `p3`'s turn began (`beginTurn`), or verify `p2`'s expired before `p3` began:
    gExSomeResumed.events.any (fun ev =>
      match ev.change with
      | .rules (.continuousEffect (.expired ..)) => true
      | _ => false)

  -- Also verify with `runBeginTurn := false` so `p3`'s `.untilNextTurnOf p3` stays active while `p2`'s `.untilNextTurnOf p2` expires!
  let gExSomeNoBeginPaused := gExSome0.continueStartNextTurn p2 #[p1] false
  let gExSomeNoBeginResumed :=
    mustApply (mustApply gExSomeNoBeginPaused p2 .concede) p0 (.chooseReplacement ridSome)
  let nextExtraSomeExactOk :=
    gExSomeNoBeginResumed.activePlayer == p3 &&
    !gExSomeNoBeginResumed.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf p2) &&
    gExSomeNoBeginResumed.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf p3)

  -- Branch (ii) `nextExtra?.isNone` with MULTIPLE dead extra turns (`extraTurns == #[p2, p3]`):
  -- Add a 5th player `p4` so the game doesn't end when `p1, p2, p3` all concede!
  let p4 : PlayerId := ⟨4⟩
  let (gExNone0a, ridNone) := mkPausedTurnStart #[p2, p3]
  let gExNone0 := gExNone0a.change (.addPlayer { id := p4, name := "Ajani" })
  let gExNonePaused := gExNone0.continueStartNextTurn p2 #[p1] false
  let gExNoneBothGone := mustApply (mustApply gExNonePaused p2 .concede) p3 .concede
  let gExNoneResumed := mustApply gExNoneBothGone p0 (.chooseReplacement ridNone)
  let nextExtraNoneMultiOk :=
    gExNoneResumed.activePlayer == p4 &&
    !gExNoneResumed.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf p2) &&
    !gExNoneResumed.activeEffects.any (fun (_, e) => e.duration == .untilNextTurnOf p3)
  let item3dOk := nextExtraSomeOk && nextExtraSomeExactOk && nextExtraNoneMultiOk

  mustHold41i3 "3a.phasingDurationActiveAt" item3aOk &&
  mustHold41i3 "3b.phasingSummoningSick" item3bOk &&
  mustHold41i3 "3c.queuedExtraAndMatPhaseIn" item3cOk &&
  mustHold41i3 "3d.multiExtraMidPause" item3dOk &&
  mustHold41i3 "3.replay"
    (replayOk41i3 #[gActivatedWhileOut, gBearPhIn, gSrcPhBackIn, gFwdBackIn,
      gNextAfterQueuedSkip, gAfterSkipP1, gExSomeResumed, gExSomeNoBeginResumed, gExNoneResumed])

end Phase41Item3EventAlignment

section Phase41Item4EventAlignment

private def mustHold41i4 (label : String) (ok : Bool) : Bool :=
  if ok then true else panic! s!"Phase41Item4EventAlignment failed: {label}"

private def replayOk41i4 (gs : Array Game) : Bool :=
  gs.all (fun g => Game.replayEvents g.events == g && allRulesEventsClassified g)

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let p2 : PlayerId := ⟨2⟩
  let g3 := afterDraw.change (.addPlayer { id := p2, name := "Liliana" })

  -- 4a. Proposal/activation `sinceIdx` + `CounterKind`-accurate `ActivationCosts.source*ForCost`
  --     and `resolvingForObj <|> sourceId` in `FraChoices.mayPayPickThen`:
  let multiCntAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[
      .removeCounters (.exact 1) (some .story) .self,
      .removeCounters (.exact 1) (some .indestructible) .self,
      .removeCounters .anyNumber (some .plusOnePlusOne) .self
    ]
    effect := Effect.plusOneX
  }
  let multiCntDef : CardDef := {
    creature "P41i4 MultiCounter" ManaCost.empty #["Construct"] 2 2 with
    types := #[.artifact, .creature]
    activatedAbilities := #[multiCntAb]
  }
  let gMc0 := addPermanent g3 multiCntDef p0 p0
  let mcObj := (gMc0.permanentsOf p0)[0]!
  let gMcReady :=
    (((gMc0.recordPutCounters mcObj.id .story 1 (some p0) (cause := some testCause)).recordPutCounters
      mcObj.id .indestructible 1 (some p0) (cause := some testCause)).recordPutCounters
      mcObj.id .plusOnePlusOne 2 (some p0) (cause := some testCause))
  -- Direct `payActivationExtraCosts` pays `.story`, `.indestructible`, AND `.plusOnePlusOne` (none skipped after `.story`!):
  let gMcPaidDirect : Game :=
    match gMcReady.payActivationExtraCosts p0 mcObj.id false false 0 false (some multiCntAb) (removePlusOnes := 2) with
    | .ok g => g
    | .error e => panic! e
  let mcDirectObj := gMcPaidDirect.object! mcObj.id
  let multiCounterDirectOk :=
    mcDirectObj.status.counters.count .story == 0 &&
    mcDirectObj.status.counters.count .indestructible == 0 &&
    mcDirectObj.status.counters.count .plusOnePlusOne == 0 &&
    gMcPaidDirect.sourceCounterCostPaidFor mcObj.id (some mcObj.id) .removeCounters (some .story) &&
    gMcPaidDirect.sourceCounterCostPaidFor mcObj.id (some mcObj.id) .removeCounters (some .indestructible) &&
    gMcPaidDirect.sourceCounterCostPaidFor mcObj.id (some mcObj.id) .removeCounters (some .plusOnePlusOne) &&
    !gMcPaidDirect.sourceCounterCostPaidFor mcObj.id (some mcObj.id) .removeCounters (some .loyalty) &&
    !gMcPaidDirect.sourceCounterCostPaidFor mcObj.id (some mcObj.id) .removeCounters (some .stun)

  -- Full proposal activation (`activate` -> `chooseX 2`) through `Choices` / `Casting` / `ActivationCosts`:
  let gMcAct := mustApply (mustApply gMcReady p0 (.activate mcObj.id 0)) p0 (.chooseX 2)
  let mcActObj := gMcAct.object! mcObj.id
  let multiCounterProposalOk :=
    mcActObj.status.counters.count .story == 0 &&
    mcActObj.status.counters.count .indestructible == 0 &&
    mcActObj.status.counters.count .plusOnePlusOne == 0 &&
    gMcAct.stack.size == 1

  -- Prior-turn `{T}` mana ability / cost payment on `sid` (`sinceIdx` bound across standalone `payActivationExtraCosts`,
  -- standalone `payCostPick`, `.turnFaceUp`, and `FraChoices.mayPayPickThen` `resolvingForObj <|> sourceId`):
  let dorkManaAb : ActivatedAbility := {
    cost := CostSpec.ofItems #[.tapSelf]
    effect := { resolution := .addMana #[.colored .green] }
  }
  let morphDorkDef : CardDef := {
    creature "P41i4 MorphDork" ManaCost.empty #["Elf", "Druid"] 2 2 with
    keywords := #[Keyword.haste, .morph CostSpec.empty]
    activatedAbilities := #[dorkManaAb]
  }
  let gPrior0 := addPermanent g3 morphDorkDef p0 p0
  let dorkObj := (gPrior0.permanentsOf p0)[0]!
  -- Record a real `{T}` cost-payment event with `forObject == some dorkObj.id` on Turn 1, then advance/untap:
  let prePriorTapIdx := gPrior0.events.size
  let gTappedTurn1 :=
    gPrior0.becomeTapped dorkObj (cause := some (.costPayment .tap p0 (some dorkObj.id)))
  let gUntappedLater :=
    setTapped (readyControlledForTurn gTappedTurn1 p0) dorkObj.id false
  let sinceIdxHelperOk :=
    gUntappedLater.sourceTappedForCost dorkObj.id (some dorkObj.id) 0 &&
    !gUntappedLater.sourceTappedForCost dorkObj.id (some dorkObj.id) gUntappedLater.events.size &&
    gUntappedLater.sourceTappedForCost dorkObj.id (some dorkObj.id) prePriorTapIdx

  -- (i) Standalone `payActivationExtraCosts` (`forObject? == none`, `proposedSpell == none`) taps `dorkObj`:
  let gStandaloneExtra : Game :=
    match gUntappedLater.payActivationExtraCosts p0 dorkObj.id true false with
    | .ok g => g
    | .error e => panic! e
  -- (ii) Standalone `payCostPick` (`abilityId == none`) with `.tapUntappedCreature` taps `dorkObj`:
  let gStandalonePick : Game :=
    match gUntappedLater.payCostPick p0 none (some dorkObj.id) .tapUntappedCreature #[dorkObj.id] with
    | .ok g => g
    | .error e => panic! e
  -- (iii) `FraChoices.mayPayPickThen` with `resolvingAbility := some trigAb.id` AND an outer `proposalCheckpoint` from before the tap (`eventsSize == prePriorTapIdx`):
  let gWithOldCkpt :=
    setTapped
      (readyControlledForTurn
        ((gPrior0.change .saveProposalCheckpoint).becomeTapped dorkObj
          (cause := some (.costPayment .tap p0 (some dorkObj.id)))) p0)
      dorkObj.id false
  let (gFraTrig0, trigAb) := gWithOldCkpt.allocStackAbility (gWithOldCkpt.object! dorkObj.id) p0
  let gFraPrompt :=
    gFraTrig0.changes #[
      .pushContinuationFrame { resolvingAbility := some trigAb.id },
      .pending (.fraChoice p0 (.mayPayPickThen .tapUntappedCreature (.gainLife 2) (some dorkObj.id))) ]
  let gFraPaid := mustApply gFraPrompt p0 (.choosePermanents #[dorkObj.id])
  let priorTapAndFraOk :=
    sinceIdxHelperOk &&
    (gStandaloneExtra.object! dorkObj.id).status.tapped &&
    (gStandalonePick.object! dorkObj.id).status.tapped &&
    (gFraPaid.object! dorkObj.id).status.tapped &&
    gFraPaid.pending == .none
  let item4aOk := multiCounterDirectOk && multiCounterProposalOk && priorTapAndFraOk

  -- 4b. `!hasFollowingSeq` guard on replacement-paused pain-mana abilities in `ManaAbilities.finishActivateManaAbilityPostSac`:
  let painLandDef : CardDef := {
    name := "P41i4 PainForge"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility
      (.oneOf (.explicit #[.colored .red, .colored .green]) (.const 1)) (damageYou := 1)]
  }
  let leyADef : CardDef := { name := "P41i4 LeyA", types := #[.enchantment] }
  let leyBDef : CardDef := { name := "P41i4 LeyB", types := #[.enchantment] }
  let gPm0 :=
    addPermanent
      (addPermanent
        (addPermanent (addPermanent g3 painLandDef p0 p0) bear p2 p2)
        leyADef p0 p0)
      leyBDef p0 p0
  let pmObj := (gPm0.permanentsOf p0).find? (·.name == painLandDef.name) |>.get!
  let markerBear := (gPm0.permanentsOf p2)[0]!
  let (gPm1, _) := gPm0.move markerBear.id .exile none (cause := some testCause)
  let pmLeyA := (gPm1.permanentsOf p0).find? (·.name == leyADef.name) |>.get!.id
  let pmLeyB := (gPm1.permanentsOf p0).find? (·.name == leyBDef.name) |>.get!.id
  let dRidA : ReplacementId := { kind := .addNoncombatDamage, object := some pmLeyA }
  let dRidB : ReplacementId := { kind := .multiplyDamage, object := some pmLeyB }
  let gPmReady :=
    (((gPm1.createEffect
      (.replacement {
        id := dRidA, source := some pmLeyA, controller := some p0, affectedPlayer := p0,
        kind := .addNoncombatDamage none 1 }) (cause := some testCause)).createEffect
      (.replacement {
        id := dRidB, source := some pmLeyB, controller := some p0, affectedPlayer := p0,
        kind := .multiplyDamage none 2 }) (cause := some testCause)).change (.priority p2))
  -- Inside `.seq first rest` (`hasFollowingSeq == true`), `finishActivateManaAbilityPostSac` with `damageYou := 1` and `prevPending := .none`
  -- pauses on `Pending.chooseReplacement` WITHOUT chaining `.receivePriority p0` ahead of `rest`:
  -- Set `p1` at 0 life so premature `.receivePriority p0` would run SBAs and eliminate `p1` before `rest` runs!
  let gPmSeq0 := gPmReady.setLifeTotal p1 0
  let gPmSeqPaused :=
    gPmSeq0.resumePendingReplacement
      (.seq
        (.finishActivateManaAbilityPostSac p0 pmObj.id pmObj.printed.name
          (gPmSeq0.snapshot pmObj) #[.colored .red] true (some 0) .none 1 false .none)
        (.finishPostStep (.logExiledIfInExile markerBear.id "after-pain-mana-seq")))
  let gPmSeqResumed := mustApply gPmSeqPaused p0 (.chooseReplacement dRidA)
  -- Standalone (`hasFollowingSeq == false`) pain-mana activation DOES chain `.receivePriority p0`:
  let pmIdx := (gPmReady.manaAbilityDefs (gPmReady.object! pmObj.id)).findIdx? (fun d => d.damageYou > 0) |>.get!
  let gPmStandalonePaused : Game :=
    match (gPmReady.change (.priority p0)).activateManaAbility p0 pmObj.id pmIdx #[.colored .red] with
    | .ok g => g
    | .error e => panic! e
  let gPmStandaloneResumed := mustApply gPmStandalonePaused p0 (.chooseReplacement dRidA)
  let item4bOk :=
    (match gPmSeqPaused.pending with | .chooseReplacement chooser _ => chooser == p0 | _ => false) &&
    gPmSeqResumed.priority == p2 &&
    !(gPmSeqResumed.player p1).lost &&
    (gPmSeqResumed.log.filter (·.endsWith "after-pain-mana-seq")).size == 1 &&
    gPmStandaloneResumed.priority == p0

  mustHold41i4 "4a.sinceIdxAndCounterKind" item4aOk &&
  mustHold41i4 "4b.painManaFollowingSeq" item4bOk &&
  mustHold41i4 "4.replay"
    (replayOk41i4 #[gMcPaidDirect, gMcAct, gStandaloneExtra, gStandalonePick, gFraPaid,
      gPmSeqPaused, gPmSeqResumed, gPmStandalonePaused, gPmStandaloneResumed])

end Phase41Item4EventAlignment

end Mtg.Engine.EventTests
