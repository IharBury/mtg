import Mtg.Engine.Game.Triggers

/-!
# Cast and enters triggers (CR 601.2i / 603.6a)

Cast triggers, another-creature-enters triggers, counters added as a
permanent enters (CR 614.13), and everything that happens after a
permanent or land enters the battlefield.
-/

namespace Mtg.Engine
namespace Game

/-- Put “whenever you cast an instant or sorcery” triggers onto the stack
(CR 601.2i / 603.3). -/
def putCastTriggersOnStack (g : Game) (caster : PlayerId) (spell : GameObject) : Game :=
  let fromZone :=
    if spell.castFromGraveyard then Zone.graveyard spell.owner
    else if spell.castFromHand then Zone.hand spell.owner
    else Zone.exile
  let extraAnnounced : Array AdditionalCostChoice :=
    let hasKicker := g.events.any fun e =>
      match e.change with
      | .rules (.cast (.announced oid _ _ cs)) => oid == spell.id && cs.any (fun | .kicker => true | _ => false)
      | _ => false
    let hasGift := g.events.any fun e =>
      match e.change with
      | .rules (.cast (.announced oid _ _ cs)) => oid == spell.id && cs.any (fun | .gift _ => true | _ => false)
      | _ => false
    let hasTeamwork := g.events.any fun e =>
      match e.change with
      | .rules (.cast (.announced oid _ _ cs)) => oid == spell.id && cs.any (fun | .teamwork _ => true | _ => false)
      | _ => false
    let cs : Array AdditionalCostChoice := #[]
    let cs := if spell.kicked && !hasKicker then cs.push .kicker else cs
    let cs :=
      match spell.giftPromisedTo with
      | some p => if !hasGift then cs.push (.gift p) else cs
      | none => cs
    let cs := if spell.teamworkPaid && !hasTeamwork then cs.push (.teamwork #[]) else cs
    cs
  let g :=
    if !extraAnnounced.isEmpty then
      g.record (GameEvent.announced g.turnNumber spell.id (costs := extraAnnounced))
    else g
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
  let happened :=
    GameEvent.spellCast g.turnNumber caster
      { (g.snapshot spell) with manaValue := g.objectManaValue spell }
      fromZone
  let g := g.record happened
  let mv := g.objectManaValue spell
  let g :=
    match g.pendingFreeRGCreature with
    | some p =>
      if p == caster && spell.printed.isCreature &&
          (spell.printed.colors.contains .red ||
            spell.printed.colors.contains .green) then
        g.expireEffect (.pendingFreeRGCreatureThisTurn p) (cause := some (.gameRule .spellCast))
          |>.logMsg s!"World War Hulk's free-cast permission is used on {spell.name}"
      else g
    | none => g
  -- Way of the Cryomancer: copy the next instant or sorcery this turn. The
  -- copy has the original's targets, mode, X, and paid-cost effects, but
  -- no costs are paid for it (rulings 843–846).
  let g :=
    if spell.printed.isInstantOrSorcery && (g.player caster).copyNextInstantSorceryThisTurn > 0 then
      let cryoEid? := g.activeEffects.findSome? (fun (eid, eff) =>
        match eff with
        | .copyNextInstantSorceryThisTurn p _ => if p == caster then some eid else none
        | _ => none)
      let copyCause : Option EventCause :=
        cryoEid?.map (fun eid => g.effectCreatedCause eid none caster)
      let g := g.expireEffect (.copyNextInstantSorceryThisTurn caster 1)
        (cause := some (.gameRule .spellCast))
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copySnap : EventObject := {
        (g.snapshot spell) with
        id := some copyId
        owner := caster
        controller := some caster
        zone := .stack
        isCopy := true
        wasCast := false
      }
      let g := g.record (GameEvent.stackObjectCopied g.turnNumber spell.id copySnap caster
        (cause := copyCause))
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
          if Int.ofNat mv <= pw then some (eid, src) else none
      | _ => none)
    matching.foldl (fun g (eid, src) =>
      let copyCause := g.effectCreatedCause eid src caster
      let copyId : ObjectId := ⟨g.nextObjectId⟩
      let copySnap : EventObject := {
        (g.snapshot spell) with
        id := some copyId
        owner := caster
        controller := some caster
        zone := .stack
        isCopy := true
        wasCast := false
      }
      let g := g.record (GameEvent.stackObjectCopied g.turnNumber spell.id copySnap caster
        (cause := some copyCause))
      let g := g.expireEffectById eid (cause := some (.gameRule .spellCast))
      g.logMsg s!"A copy of {spell.name} is created (Loki)") g

/-- Karn, Argent Defender: an artifact or creature entering doesn't cause
abilities to trigger. Checked with the permanent as it exists on the
battlefield (rulings 891–893). Replacement effects still apply (ruling 890). -/
def enteringCausesNoTriggers (g : Game) (o : GameObject) : Bool :=
  (o.isCreature || o.types.contains .artifact) &&
    g.battlefield.any (fun src =>
      src.staticAbilities.any (fun
        | .enteringArtifactsCreaturesDontTrigger => true
        | _ => false))

/-- Put `n` +1/+1 counters on `o` (CR 122.1). When `entersWith` is true, the
counters have already been placed in `o`'s arrival `ZoneEvent.moved` via
`extraEntersWith` or `ZoneEvent.created` (CR 614.1c); `.youPutPlusOne`
triggers are evaluated from the recorded event batch in `matchTriggers`. -/
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
  g.logMsg phrase

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
  let g :=
    if g.loggedEntered o.id then g
    else
      let o := g.object! o.id
      let bag :=
        if o.status.toCounterBag.isEmpty then
          g.computeEntersWithCounters o (asOf := o.timestamp)
        else o.status.toCounterBag
      let snap := g.snapshot o
      if o.printed.isToken then
        g.record (GameEvent.created g.turnNumber (o.controller.getD o.owner)
          { snap with counters := bag })
      else
        g.record (GameEvent.moved g.turnNumber
          { snap with zone := .command }
          .command .battlefield
          (after := some { snap with zone := .battlefield, counters := bag })
          (entersWith := bag))
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
    g.promptTriggerTargetsIfNeeded

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  g.afterPermanentEnters land

/-- Put “whenever a land you control enters” triggers (CR 603.6a). -/
def putLandYouControlEntersTriggers (g : Game) (land : GameObject) : Game :=
  g.afterPermanentEnters land

/-- Put “whenever another Elf you control enters” triggers onto the stack
(CR 603.6a). The entering permanent itself does not trigger. -/
def putAnotherElfYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  g.afterPermanentEnters entering

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
