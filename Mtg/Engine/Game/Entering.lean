import Mtg.Engine.Game.Triggers

/-!
# Cast and enters triggers (CR 601.2i / 603.6a)

Cast triggers, another-creature-enters triggers, counters added as a
permanent enters (CR 614.13), and everything that happens after a
permanent or land enters the battlefield.
-/

namespace Mtg.Engine
namespace Game

/-- “Whenever this or another [subtype] you control enters” and its nontoken
and “another [subtype] or Equipment” variants (Balin, Fíli, Kíli, Thorin). -/
def putSubtypeEnterTriggers (g : Game) (entered : GameObject) : Game :=
  match entered.controller with
  | none => g
  | some p =>
    let g := g.foldControlledPermanents p none fun g src =>
      (src.printed.triggeredAbilities ++ src.status.grantedTriggeredAbilities).foldl (fun g ab =>
        let o := ab.opts
        let self := src.id == entered.id
        let fire (e : TriggerEvent) (cond : Bool) : Game → Game := fun g =>
          if ab.firesOn e && cond then g.queueTrigger p src ab e (cause := some entered) else g
        let g := match o.thisOrNontokenSubtype with
          | some s => fire .thisOrNontokenSubtypeYouControlEnters
              (self || (!entered.printed.isToken && g.hasSubtype entered s)) g
          | none => g
        let g := match o.thisOrAnotherSubtype with
          | some s => fire .thisOrAnotherSubtypeYouControlEnters (self || g.hasSubtype entered s) g
          | none => g
        match o.anotherSubtypeOrEquipment with
        | some s => fire .anotherSubtypeOrEquipmentYouControlEnters
            (!self && (g.hasSubtype entered s || entered.printed.isEquipment)) g
        | none => g) g
    g.promptTriggerTargetsIfNeeded

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  let fromZone :=
    if spell.castFromGraveyard then Zone.graveyard spell.owner
    else if spell.castFromHand then Zone.hand spell.owner
    else Zone.exile
  let happened :=
    GameEvent.cast g.turnNumber caster spell.asEvent fromZone
      (g.objectManaValue spell) spell.status.manaSpentToCast
      spell.castFromGraveyard spell.teamworkPaid spell.giftPromisedTo.isSome
  let g := g.record happened
  let spells := g.loggedSpellsCast caster
  let nonc := g.loggedNoncreatureSpells caster
  let g :=
    Id.run do
      let mut g := g
      for _ in [0:spell.printed.cascade] do
        g := g.putTriggeredAbilityOnStack caster spell .onCastCascade "cascade trigger"
      return g
  -- Photon Blast Barrage: “When you cast this spell, copy it X times.”
  let copiesSelf :=
    match spell.printed.spellEffect.map (·.resolution) with
    | some (.copyThisSpellXTimesThenDamage _) => !spell.isCopy
    | _ => false
  let g :=
    if copiesSelf then
      g.putTriggeredAbilityOnStack caster spell
        (.triggered .enter { resolution := .copySourceSpellXTimes
                             phrase := "When you cast this spell, copy it X times. You may choose new targets for the copies" } {})
        "cast trigger"
    else g
  let g :=
    if happened.matchesTrigger caster spell.id .youCastInstantOrSorcery then
      g.putControlledTriggers caster .youCastInstantOrSorcery
    else g
  -- Reality Fracture cast triggers.
  let g :=
    if happened.matchesTrigger caster spell.id (.fra .castThis) then
      g.putMatchingSourceTriggers caster spell (.fra .castThis)
    else g
  let mvCast := g.objectManaValue spell
  let g := (g.livingOpponents caster).foldl (fun g pl =>
    g.putFraEventTriggersWhere pl.id (fun
      | .opponentCastsSpellMvAtMost n => mvCast ≤ n
      | _ => false) (cause := some spell)) g
  let g := if spell.isPreparedSpell then
      g.putFraEventTriggers caster .youCastPreparedSpell (cause := some spell)
    else g
  let g := if spell.printed.isCreature || spell.printed.isArtifact then
      g.putFraEventTriggers caster .youCastArtifactOrCreature (cause := some spell)
    else g
  let targetsOwnCreature : Bool :=
    match g.stack.find? (fun e => e.objectId == spell.id) with
    | some e =>
      e.targets.any (fun t =>
        match t with
        | Target.permanent id =>
          (g.findObject? id).any (fun o => o.isCreature && o.controlledBy caster)
        | _ => false)
    | none => false
  let g := if spell.printed.isEquipment || targetsOwnCreature then
      g.putFraEventTriggers caster .youCastEquipmentOrTargetingCreatureYouControl
        (cause := some spell)
    else g
  let g :=
    if spell.printed.isCreature then
      g.foldControlledPermanents caster none fun g o =>
        g.putMatchingSourceTriggers caster o .youCastCreature
          (some (Int.ofNat (g.objectManaValue spell)))
    else
      g.foldControlledPermanents caster none fun g o =>
        g.putMatchingSourceTriggers caster o .youCastNoncreature (cause := some spell)
  let g :=
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.putControlledTriggers pl.id .opponentCastsSpell) g
  let g :=
    if spells == 2 then
      g.putControlledTriggers caster .youCastSecondSpell (cause := some spell)
    else g
  let colors := spell.printed.colors
  let g :=
    Color.all.foldl (fun acc c =>
      if colors.contains c then
        let acc := acc.putControlledTriggers caster (.youCastColor c)
        if spell.castFromHand then acc.putControlledTriggers caster (.youCastColorFromHand c)
        else acc
      else acc) g
  let g := if colors.contains .green then g.putControlledTriggers caster .youCastGreen else g
  let g := if spell.treasureManaSpent then g.putControlledTriggers caster .youCastWithTreasure else g
  let mv := g.objectManaValue spell
  let g :=
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.foldControlledPermanents pl.id none fun acc o =>
        match o.status.chosenOdd with
        | none => acc
        | some odd =>
          let parityOk := if odd then mv % 2 == 1 else mv % 2 == 0
          if parityOk then
            acc.putMatchingSourceTriggers pl.id o .opponentCastsMatchingParity
          else acc) g
  let g :=
    if spells == 2 then
      g.livingPlayers.foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .anyPlayerCastsSecondSpell) g
    else g
  let g :=
    g.putControlledTriggers caster .youCastSpell
  -- Extort (CR 702.101a): each instance triggers separately.
  let g :=
    (g.permanentsOf caster).foldl (fun g o =>
      if o.staticAbilities.any (fun | .extort => true | _ => false) then
        g.queueTrigger caster o
          (.triggered .enter { resolution := .extort
                               phrase := "You may pay {W/B}. If you do, each opponent loses 1 life and you gain that much life" } {})
          .youCastSpell
      else g) g
  let g :=
    match g.pendingFreeRGCreature with
    | some p =>
      if p == caster && spell.printed.isCreature &&
          (spell.printed.colors.contains .red ||
            spell.printed.colors.contains .green) then
        g.expireEffect (.pendingFreeRGCreatureThisTurn p)
          |>.logMsg s!"World War Hulk's free-cast permission is used on {spell.name}"
      else g
    | none => g
  let g :=
    if spell.printed.hasSubtype .villain then
      g.putControlledTriggers caster .youCastVillain
    else g
  let targetsCreatureYouControl : Bool :=
    match g.stack.find? (fun e => e.objectId == spell.id) with
    | some e =>
      e.targets.any (fun t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some o => o.isCreature && o.controlledBy caster
          | none => false
        | _ => false)
    | none => false
  let g :=
    if targetsCreatureYouControl then
      g.putControlledTriggers caster .youCastTargetingCreatureYouControl
    else g
  let targetedPermanents : Array GameObject :=
    match g.stack.find? (fun e => e.objectId == spell.id) with
    | some e => e.targets.filterMap (fun t =>
        match t with
        | Target.permanent id => (g.findObject? id).filter (·.isOnBattlefield)
        | _ => none)
    | none => #[]
  let g :=
    if targetedPermanents.any (·.isCreature) then
      g.foldControlledPermanents caster none fun g o =>
        g.putMatchingSourceTriggers caster o .youCastTargetingCreature (cause := some spell)
    else g
  let g :=
    if spell.printed.isInstantOrSorcery &&
        targetedPermanents.any (fun o => o.types.contains .artifact || o.types.contains .land) then
      g.foldControlledPermanents caster none fun g o =>
        g.putMatchingSourceTriggers caster o .youCastInstantSorceryTargetingArtifactOrLand
          (cause := some spell)
    else g
  -- Danitha: once per spell, however many targets it has (ruling 849).
  let targetsOpponentOrTheirCreature : Bool :=
    match g.stack.find? (fun e => e.objectId == spell.id) with
    | some e =>
      e.targets.any (fun t =>
        match t with
        | Target.player q => q != caster
        | Target.permanent id =>
          match g.findObject? id with
          | some o => o.isCreature && o.controller.isSome && !o.controlledBy caster
          | none => false
        | _ => false)
    | none => false
  let g :=
    if targetsOpponentOrTheirCreature then
      g.putControlledTriggers caster .youCastTargetingOpponentOrTheirCreature
    else g
  let g :=
    if !spell.printed.isCreature && nonc == 1 then
      g.putControlledTriggers caster .youCastFirstNoncreature
    else g
  let g :=
    if !spell.printed.isCreature && nonc == 1 then
      (g.livingOpponents caster).foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .opponentCastsFirstNoncreature) g
    else g
  -- Way of the Cryomancer: copy the next instant or sorcery this turn. The
  -- copy has the original's targets, mode, X, and paid-cost effects, but
  -- no costs are paid for it (rulings 843–846).
  let g :=
    if spell.printed.isInstantOrSorcery && (g.player caster).copyNextInstantSorceryThisTurn > 0 then
      let g := g.expireEffect (.copyNextInstantSorceryThisTurn caster 1)
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copyTs := g.timestamp + 1
      let copyObj : GameObject := {
        id := copyId
        printed := spell.printed
        owner := caster
        controller := some caster
        zone := .stack
        timestamp := copyTs
        kicked := spell.kicked
        giftPromisedTo := spell.giftPromisedTo
        teamworkPaid := spell.teamworkPaid
        chosenX := spell.chosenX
        isCopy := true
        adventurerCard := spell.adventurerCard
      }
      let g := g.record (GameEvent.created g.turnNumber caster (g.snapshot copyObj))
      let g := g.putStackEntry caster copyId
      let g :=
        match g.stack.find? (fun e => e.objectId == spell.id),
            g.stack.findIdx? (fun e => e.objectId == copyId) with
        | some orig, some i =>
          g.changes #[
            .stackEntry i (.targets orig.targets),
            .stackEntry i (.dividedDamage orig.dividedDamage),
            .stackEntry i (.chosenMode orig.chosenMode),
            .stackEntry i (.targetsAnnounced true)]
        | _, _ => g
      g.logMsg s!"A copy of {spell.name} is created (Way of the Cryomancer)"
    else g
  -- Loki (MSH 109): copy the next instant or sorcery whose mana value is
  -- ≤ Loki's power at cast time (last known if he already left). Each
  -- activation is its own delayed trigger, so every matching pending effect
  -- of the caster copies this spell and then ends under its own `EffectId`.
  if !spell.printed.isInstantOrSorcery then g
  else
    let matching := g.activeEffects.filterMap (fun (eid, eff) =>
      match eff with
      | .pendingLokiCopy p src fallback =>
        if p != caster then none
        else
          let pw :=
            match src with
            | some id =>
              match g.findObject? id with
              | some o => if o.isOnBattlefield then g.power o else fallback
              | none => fallback
            | none => fallback
          if Int.ofNat mv <= pw then some eid else none
      | _ => none)
    matching.foldl (fun g eid =>
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copyTs := g.timestamp + 1
      let copyObj : GameObject := {
        id := copyId
        printed := spell.printed
        owner := caster
        controller := some caster
        zone := .stack
        timestamp := copyTs
        chosenX := spell.chosenX
        isCopy := true
      }
      let g := g.record (GameEvent.created g.turnNumber caster (g.snapshot copyObj))
      let g := g.putStackEntry caster copyId
      let g := g.expireEffectById eid
      g.logMsg s!"A copy of {spell.name} is created (Loki)") g

/-- Put “whenever another Elf you control enters” triggers onto the stack
(CR 603.6a). The entering permanent itself does not trigger. -/
def putAnotherElfYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  if !g.hasSubtype entering .elf then g
  else
    match entering.controller with
    | none => g
    | some p =>
      g.putControlledTriggersWithPrompt p .anotherElfYouControlEnters
        (excludeId := some entering.id)

/-- Put “whenever another creature you control enters” triggers (CR 603.6a). -/
def putAnotherCreatureYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  if !entering.isCreature then g
  else
    match entering.controller with
    | none => g
    | some p =>
      g.foldControlledPermanents p (excludeId := some entering.id) (fun g o =>
        g.putMatchingSourceTriggers p o .anotherCreatureYouControlEnters
          (cause := some entering))
      |>.promptTriggerTargetsIfNeeded

/-- Put `n` +1/+1 counters on `o` (CR 122.1). When `entersWith` is true, the
counters have already been placed in `o`'s arrival `ZoneEvent.moved` via
`extraEntersWith` (CR 614.1c), so only the log and put-counter triggers run. -/
def addPlusOnePlusOneTo (g : Game) (o : GameObject) (n : Nat := 1)
    (entersWith := false) (byPlayer : Option PlayerId := none)
    (cause : Option EventCause := none) : Game :=
  let n := g.countersYouPut o n (putter := byPlayer) (entersWith := entersWith)
  let putter0 := byPlayer.orElse (fun _ => g.counterPutter o.controller)
  let proposed :=
    GameEvent.counters g.turnNumber putter0 o.asEvent .plusOnePlusOne n (cause := cause)
  let n :=
    if proposed.watches .wouldPutCounter then g.extraPlusOneOnCreature o n else n
  let happened := GameEvent.counters g.turnNumber putter0 (g.object! o.id).asEvent .plusOnePlusOne n
    (cause := cause)
  let g := if n > 0 && !entersWith then g.record happened else g
  let phrase :=
    if entersWith then s!"{o.name} enters with {plusOnePlusOneCountersPhrase n}"
    else s!"{o.name} gets {plusOnePlusOneCountersPhrase n}"
  let g := g.logMsg phrase
  -- “Whenever you put … counters”: “you” is whoever puts them.
  let putter :=
    byPlayer.orElse (fun _ => g.counterPutter o.controller)
  match putter with
  | some q =>
    if n > 0 && happened.matchesTrigger q o.id .youPutPlusOne then
      g.foldControlledPermanents q none fun g src =>
        g.putMatchingSourceTriggers q src .youPutPlusOne (cause := some (g.object! o.id))
          (keep := fun ab => ab.shared != .resource .plusOneOnHeroesCreateWall)
    else g
  | none => g

/-- Karn, Argent Defender: an artifact or creature entering doesn't cause
abilities to trigger. Checked with the permanent as it exists on the
battlefield (rulings 891–893). Replacement effects still apply (ruling 890). -/
def enteringCausesNoTriggers (g : Game) (o : GameObject) : Bool :=
  (o.isCreature || o.types.contains .artifact) &&
    g.battlefield.any (fun src =>
      src.staticAbilities.any (fun
        | .enteringArtifactsCreaturesDontTrigger => true
        | _ => false))

/-- CR 306.5b: a planeswalker enters with loyalty counters equal to its
printed loyalty (placed in `entersWith` during the zone change). -/
def enterWithLoyalty (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown then g
  else
    match o.printed.isPlaneswalker, o.printed.loyalty with
    | true, some n =>
      if n > 0 && o.status.loyaltyCounters > 0 then
        let k := o.status.loyaltyCounters
        g.logMsg s!"{o.name} enters with {k} loyalty counter(s)"
      else g
    | _, _ => g

/-- “This creature enters with N +1/+1 counters on it” (placed in `entersWith`
during the zone change). -/
def enterWithPlusOnes (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown then g
  else
    let base := o.printed.entersWithPlusOneCounters
    if base == 0 || o.status.plusOnePlusOne == 0 then g
    else
      let n := g.extraPlusOneOnCreature o (g.extraCountersOnEntering o base)
      if n == 0 then g
      else g.logMsg s!"{o.name} enters with {n} +1/+1 counter(s)"

def enterWithIndestructibleCounter (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && o.printed.entersWithIndestructibleCounter &&
      o.status.indestructibleCounters > 0 then
    g.logMsg s!"{o.name} enters with an indestructible counter"
  else g

def enterWithShield (g : Game) (o : GameObject) : Game :=
  if o.status.faceDown then g
  else
    let base := o.printed.entersWithShield
    if base == 0 || o.status.shield == 0 then g
    else
      let n := o.status.shield
      g.logMsg s!"{o.name} enters with {n} shield counter(s)"

def enterWithXPlusOnes (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && o.staticAbilities.any (fun
      | .entersWithXPlusOne => true
      | _ => false) && o.status.plusOnePlusOne > 0 then
    let n := g.extraPlusOneOnCreature o (g.extraCountersOnEntering o (o.chosenX.getD 0))
    if n == 0 then g
    else g.logMsg s!"{o.name} enters with {n} +1/+1 counter(s)"
  else g

def enterWithHope (g : Game) (o : GameObject) : Game :=
  if !o.status.faceDown && o.printed.entersWithHopePerCreature && o.status.hope > 0 then
    g.logMsg s!"{o.name} enters with {o.status.hope} hope counter(s)"
  else g

/-- Counters and statuses a permanent enters with (CR 614.1c / 614.12):
loyalty, +1/+1, indestructible, shield, X +1/+1, prepared, and hope. The
counters and `prepared` status are placed in `moved.after` / `created.object`
and `entersWith` during the atomic zone change; this step logs the entry
effects, queues loyalty-put triggers, and creates the exiled prepare copy. -/
def applyEntersWith (g : Game) (o : GameObject) : Game :=
  let id := o.id
  let g := g.enterWithLoyalty (g.object! id)
  let g := g.enterWithPlusOnes (g.object! id)
  let g := g.enterWithIndestructibleCounter (g.object! id)
  let g := g.enterWithShield (g.object! id)
  let g := g.enterWithXPlusOnes (g.object! id)
  let g := g.ensurePreparedCopy (g.object! id)
  g.enterWithHope (g.object! id)

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
  if (g.findObject? o.id).any (·.enterProcessed) then g else
  let g := match g.findObject? o.id with
    | some x => g.changeObject x.id (.enterProcessed true)
    | none => g
  -- Storied is granted as the permanent enters, before SBA (legend rule /
  -- 0 toughness) and before enters triggers use the stack.
  let g := g.refreshEnduringStory
  let g := g.refreshCitysBlessing
  let g := g.applyEntersWith (g.object! o.id)
  let o := g.object! o.id
  -- Room of Refuge: “As it enters, choose a color.”
  let g :=
    if o.staticAbilities.any (· == .fra .entersTappedChooseColor) && o.status.chosenColor.isNone then
      match o.controller with
      | some p =>
        (g.change (.pending (.fraChoice p (.chooseColor o.id)))).logMsg
          s!"{(g.player p).name} chooses a color for {o.name}"
      | none => g
    else g
  -- An Unexpected Party: “As this enchantment enters, choose a creature type.”
  let g :=
    if o.printed.asEntersChooseCreatureType && o.status.chosenCreatureType.isNone &&
        g.pending == .none then
      match o.controller with
      | some p =>
        (g.change (.pending (.fraChoice p (.entersCreatureType o.id)))).logMsg
          s!"{(g.player p).name} chooses a creature type for {o.name}"
      | none => g
    else g
  -- Gollum, Riddle Master: “As Gollum enters, choose odd or even.”
  let g :=
    if o.printed.asEntersChooseOddEven && o.status.chosenOdd.isNone && g.pending == .none then
      match o.controller with
      | some p =>
        (g.change (.pending (.fraChoice p (.entersOddEven o.id)))).logMsg
          s!"{(g.player p).name} chooses odd or even for {o.name}"
      | none => g
    else g
  -- Meddling Mage: “As it enters, choose a nonland card name.”
  let g :=
    if o.staticAbilities.any (· == .fra .entersChooseNonlandCardName) && o.status.chosenName.isNone &&
        g.pending == .none then
      match o.controller with
      | some p =>
        (g.change (.pending (.fraChoice p (.chooseCardName o.id)))).logMsg
          s!"{(g.player p).name} chooses a nonland card name for {o.name}"
      | none => g
    else g
  let g := g.addLoreAsSagaEnters o
  let o := g.object! o.id
  if g.enteringCausesNoTriggers o then
    g.logMsg s!"{o.name} entering doesn't cause abilities to trigger"
  else
  let g := g.putEnterTriggersOnStack o
  let g := g.putAnotherElfYouControlEntersTriggers (g.object! o.id)
  let g := g.putAnotherCreatureYouControlEntersTriggers (g.object! o.id)
  let g := g.putSubtypeEnterTriggers (g.object! o.id)
  match (g.object! o.id).controller with
  | some p =>
    let entered := g.object! o.id
    let g :=
      if entered.printed.isToken then
        -- “Whenever one or more tokens you control enter” triggers once per
        -- batch via `evaluateBatchTriggers` (Mister Fantastic); Belladonna Took
        -- triggers per token.
        g.foldControlledPermanents p none fun g src =>
          g.putMatchingSourceTriggers p src .tokenYouControlEnters
            (keep := fun ab => ab.shared != .watch .tokensEnterMayDraw)
      else g
    let g :=
      if entered.printed.isArtifact then
        g.putControlledTriggersWithPrompt p .artifactYouControlEnters
      else g
    let g :=
      if entered.isCreature then
        g.putControlledTriggers p .creatureYouControlEnters
      else g
    let g :=
      entered.subtypes.foldl (fun acc sub =>
        acc.putControlledTriggers p (.subtypeYouControlEnters sub)) g
    let g :=
      if entered.printed.isEquipment then
        g.putControlledTriggers p .equipmentYouControlEnters
      else g
    let g :=
      if g.hasSubtype entered .villain || entered.printed.isArtifact then
        g.putControlledTriggers p .anotherVillainOrArtifactEnters
          (excludeId := some entered.id)
      else g
    let g :=
      if g.hasSubtype entered .villain then
        g.foldControlledPermanents p (excludeId := some entered.id) (fun g o =>
          g.putMatchingSourceTriggers p o .anotherVillainEnters
            (cause := some entered))
      else g
    let g :=
      if entered.types.contains .artifact then
        g.foldControlledPermanents p (excludeId := some entered.id) (fun g o =>
          g.putMatchingSourceTriggers p o .anotherArtifactEnters (cause := some entered))
      else g
    let g :=
      if !entered.printed.isToken && g.hasSubtype entered .hero then
        g.foldControlledPermanents p (excludeId := some entered.id) (fun g o =>
          g.putMatchingSourceTriggers p o .anotherNontokenHeroEnters (cause := some entered))
      else g
    let g :=
      if !entered.printed.isToken && entered.types.contains .artifact then
        g.foldControlledPermanents p (excludeId := some entered.id) (fun g o =>
          g.putMatchingSourceTriggers p o .anotherNontokenArtifactEnters (cause := some entered))
      else g
    -- Reality Fracture “enters” triggers.
    let isCreature := entered.isCreature
    let g :=
      if isCreature || entered.printed.isPlaneswalker then
        g.putFraEventTriggers p .anotherCreatureOrPlaneswalkerYouControlEnters
          (cause := some entered) (excludeId := some entered.id)
      else g
    let g :=
      if isCreature then
        g.putFraEventTriggers p .thisOrAnotherCreatureYouControlEnters (cause := some entered)
      else g
    let g :=
      if isCreature && !entered.printed.isToken then
        g.putFraEventTriggers p .anotherNontokenCreatureYouControlEnters
          (cause := some entered) (excludeId := some entered.id)
      else g
    let g :=
      if isCreature then
        (g.livingOpponents p).foldl (fun g opp =>
          g.putFraEventTriggers opp.id .creatureOpponentControlsEnters (cause := some entered)) g
      else g
    let power := g.power entered
    let g :=
      if isCreature then
        g.putFraEventTriggersWhere p (fun
          | .creatureYouControlPowerAtLeastEnters n => power ≥ n
          | _ => false) (cause := some entered)
      else g
    g.promptTriggerTargetsIfNeeded
  | none => g

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  let g := g.afterPermanentEnters land
  let land := g.object! land.id
  if g.enteringCausesNoTriggers land then g
  else g.putLandYouControlEntersTriggers land

/-- Process entering for tokens created since the last check, queueing
their enters triggers (CR 603.6a). -/
def flushTokenEnters (g : Game) : Game :=
  let ids := g.pendingTokenEnters
  let g := g.change (.pendingTokenEnters #[])
  ids.foldl (fun g id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && !o.enterProcessed then
        if o.printed.isLand then g.afterLandEnters o else g.afterPermanentEnters o
      else g
    | none => g) g

/-- Nick Fury power-up: put a Hero, Equipment, or Vehicle onto the battlefield.
A daybound front face enters back-face-up at night and cannot transform
(MSH 191). Otherwise it enters front-face-up; you may then transform a DFC
(MSH 192). Front-face enters abilities trigger in either case before the
optional transform. -/
def enterFromNickFury (g : Game) (controller : PlayerId) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g.logMsg "No card to put onto the battlefield"
  | some o =>
    let nightBack := g.isNight && o.printed.daybound && o.printed.otherFace.isSome
    let (g, newId) := g.putOntoBattlefield id controller (nightBack := nightBack) (cause := cause)
    let o := g.object! newId
    let g :=
      if nightBack then
        g.logMsg s!"{o.name} enters back face up (night / daybound)"
      else g
    g.afterPermanentEnters (g.object! newId)

end Game
end Mtg.Engine
