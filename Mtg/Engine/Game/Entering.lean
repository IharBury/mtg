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
  let pl := g.player caster
  let spells := pl.spellsCastThisTurn + 1
  let nonc :=
    if spell.printed.isCreature then pl.noncreatureSpellsCastThisTurn
    else pl.noncreatureSpellsCastThisTurn + 1
  let creat :=
    if spell.printed.isCreature then pl.creatureSpellsCastThisTurn + 1
    else pl.creatureSpellsCastThisTurn
  let g := g.modifyPlayer caster (fun p =>
    { p with
      spellsCastThisTurn := spells
      noncreatureSpellsCastThisTurn := nonc
      creatureSpellsCastThisTurn := creat
      castManaValuesThisTurn :=
        p.castManaValuesThisTurn.push (g.objectManaValue spell) })
  let g :=
    Id.run do
      let mut g := g
      for _ in [0:spell.printed.cascade] do
        g := g.putTriggeredAbilityOnStack caster spell .onCastCascade "cascade trigger"
      return g
  let g :=
    if spell.printed.isInstantOrSorcery then
      g.putControlledTriggers caster .youCastInstantOrSorcery
    else g
  -- Reality Fracture cast triggers.
  let g := g.putMatchingSourceTriggers caster spell (.fra .castThis)
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
    else g.putControlledTriggers caster .youCastNoncreature
  let g :=
    (g.livingOpponents caster).foldl (fun acc pl =>
      acc.putControlledTriggers pl.id .opponentCastsSpell) g
  let g :=
    if spells == 2 then
      g.putControlledTriggers caster .youCastSecondSpell
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
  let extortN :=
    (g.permanentsOf caster).filter (fun o =>
      o.staticAbilities.any (fun
        | .extort => true
        | _ => false)) |>.size
  let g :=
    if extortN == 0 then g
    else
      { g with
          pendingExtort := g.pendingExtort + extortN
          pendingExtortController := some caster }
        |>.logMsg "Extort triggers"
  let g :=
    match g.pendingFreeRGCreature with
    | some p =>
      if p == caster && spell.printed.isCreature &&
          (spell.printed.colors.contains .red ||
            spell.printed.colors.contains .green) then
        { g with pendingFreeRGCreature := none }
          |>.logMsg s!"World War Hulk's free-cast permission is used on {spell.name}"
      else g
    | none => g
  let g :=
    if spell.printed.hasSubtype "Villain" then
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
      let g := g.modifyPlayer caster (fun pl =>
        { pl with copyNextInstantSorceryThisTurn := pl.copyNextInstantSorceryThisTurn - 1 })
      let (g, copy) := g.allocObject spell.printed caster .stack (some caster)
      let g := g.setObject { copy with
        kicked := spell.kicked
        giftPromisedTo := spell.giftPromisedTo
        teamworkPaid := spell.teamworkPaid
        chosenX := spell.chosenX
        isCopy := true
        adventurerCard := spell.adventurerCard }
      let g := g.putStackEntry caster copy.id
      let g :=
        match g.stack.find? (fun e => e.objectId == spell.id),
            g.stack.findIdx? (fun e => e.objectId == copy.id) with
        | some orig, some i =>
          { g with stack := g.stack.set! i { g.stack[i]! with
              targets := orig.targets, dividedDamage := orig.dividedDamage
              chosenMode := orig.chosenMode, targetsAnnounced := true } }
        | _, _ => g
      g.logMsg s!"A copy of {spell.name} is created (Way of the Cryomancer)"
    else g
  -- Loki (MSH 109): copy the next instant or sorcery whose mana value is
  -- ≤ Loki's power at cast time (last known if he already left).
  let pw? :=
    match g.pendingLokiCopy with
    | none => none
    | some (p, some id, fallback) =>
      if p != caster then none
      else
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield then some (g.power o) else some fallback
        | none => some fallback
    | some (p, none, fallback) =>
      if p == caster then some fallback else none
  match pw? with
  | some pw =>
    if spell.printed.isInstantOrSorcery && Int.ofNat mv <= pw then
      let (g, copy) := g.allocObject spell.printed caster .stack (some caster)
      let g := g.setObject { copy with
        chosenX := spell.chosenX
        isCopy := true }
      let g := g.putStackEntry caster copy.id
      { g with pendingLokiCopy := none }
        |>.logMsg s!"A copy of {spell.name} is created (Loki)"
    else g
  | none => g

/-- Put “whenever another Elf you control enters” triggers onto the stack
(CR 603.6a). The entering permanent itself does not trigger. -/
def putAnotherElfYouControlEntersTriggers (g : Game) (entering : GameObject) : Game :=
  if !g.hasSubtype entering "Elf" then g
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

/-- Extra counters Doc Samson puts on a permanent you control (MSH 165 / 238). -/
def extraCountersOn (g : Game) (controller : Option PlayerId) (n : Nat) : Nat :=
  if n == 0 then 0
  else
    match controller with
    | none => n
    | some p =>
      n + ((g.permanentsOf p).filter (fun o =>
        o.printed.staticAbilities.any (fun
          | .extraCounterOnPermanents => true
          | _ => false))).size

/-- Yoshimaru, Beloved Companion: one more +1/+1 counter for each such
permanent the creature's controller controls. -/
def extraPlusOneOnCreature (g : Game) (o : GameObject) (n : Nat) : Nat :=
  if n == 0 || !o.isCreature then n
  else
    match o.controller with
    | none => n
    | some p =>
      n + ((g.permanentsOf p).filter (·.staticAbilities.any (· == .fra .extraPlusOneCounter))).size

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
printed loyalty. -/
def enterWithLoyalty (g : Game) (o : GameObject) : Game :=
  match o.printed.isPlaneswalker, o.printed.loyalty with
  | true, some n =>
    if n > 0 then
      let g := g.setObject { o with status :=
        { o.status with loyaltyCounters := o.status.loyaltyCounters + n.toNat } }
      let g := match o.controller with
        | some p => g.queueLoyaltyPutTriggers p
        | none => g
      g.logMsg s!"{o.name} enters with {n} loyalty counter(s)"
    else g
  | _, _ => g

/-- “This creature enters with N +1/+1 counters on it.” -/
def enterWithPlusOnes (g : Game) (o : GameObject) : Game :=
  let base := o.printed.entersWithPlusOneCounters
  if base == 0 then g
  else
    let n := g.extraPlusOneOnCreature o (g.extraCountersOn o.controller base)
    let g := g.setObject { o with status := o.status.addPlusOnePlusOne n }
    g.logMsg s!"{o.name} enters with {n} +1/+1 counter(s)"

def enterWithIndestructibleCounter (g : Game) (o : GameObject) : Game :=
  if o.printed.entersWithIndestructibleCounter then
    let g := g.setObject { o with status :=
      { o.status with indestructibleCounters := o.status.indestructibleCounters + 1 } }
    g.logMsg s!"{o.name} enters with an indestructible counter"
  else g

def enterWithShield (g : Game) (o : GameObject) : Game :=
  let base := o.printed.entersWithShield
  if base == 0 then g
  else
    let n := g.extraCountersOn o.controller base
    let g := g.setObject { o with status := { o.status with shield := o.status.shield + n } }
    g.logMsg s!"{o.name} enters with {n} shield counter(s)"

def enterWithXPlusOnes (g : Game) (o : GameObject) : Game :=
  if o.staticAbilities.any (fun
      | .entersWithXPlusOne => true
      | _ => false) then
    let n := g.extraPlusOneOnCreature o (g.extraCountersOn o.controller (o.chosenX.getD 0))
    if n == 0 then g
    else
      let g := g.setObject { o with status :=
        { o.status with plusOnePlusOne := o.status.plusOnePlusOne + n } }
      g.logMsg s!"{o.name} enters with {n} +1/+1 counter(s)"
  else g

def enterWithHope (g : Game) (o : GameObject) : Game :=
  if o.printed.entersWithHopePerCreature then
    match o.controller with
    | some p =>
      let n := g.countCreaturesControlledBy p
      let g := g.setObject { o with status := { o.status with hope := n } }
      g.logMsg s!"{o.name} enters with {n} hope counter(s)"
    | none => g
  else g

/-- Counters and statuses a permanent enters with (CR 614.1c / 614.12):
loyalty, +1/+1, indestructible, shield, X +1/+1, prepared, and hope. These
replacement effects apply even when entering causes no triggers (ruling
890). -/
def applyEntersWith (g : Game) (o : GameObject) : Game :=
  let id := o.id
  let g := g.enterWithLoyalty (g.object! id)
  let g := g.enterWithPlusOnes (g.object! id)
  let g := g.enterWithIndestructibleCounter (g.object! id)
  let g := g.enterWithShield (g.object! id)
  let g := g.enterWithXPlusOnes (g.object! id)
  let o := g.object! id
  let g := g.setObject { o with status := { o.status with enteredThisTurn := true } }
  let o := g.object! id
  let g := if o.printed.entersPrepared then g.becomePrepared o else g
  g.enterWithHope (g.object! id)

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
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
        { g with pending := .fraChoice p (.chooseColor o.id) }.logMsg
          s!"{(g.player p).name} chooses a color for {o.name}"
      | none => g
    else g
  -- Meddling Mage: “As it enters, choose a nonland card name.”
  let g :=
    if o.staticAbilities.any (· == .fra .entersChooseNonlandCardName) && o.status.chosenName.isNone &&
        g.pending == .none then
      match o.controller with
      | some p =>
        { g with pending := .fraChoice p (.chooseCardName o.id) }.logMsg
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
        g.putControlledTriggers p .tokenYouControlEnters
      else g
    let g :=
      if entered.printed.isArtifact then
        let g := g.modifyPlayer p (fun pl =>
          { pl with artifactEnteredThisTurn := true })
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
      if entered.isCreature && g.hasSubtype entered "Hero" then
        g.modifyPlayer p (fun pl => { pl with heroEnteredThisTurn := true })
      else g
    let g :=
      if entered.printed.isEquipment then
        g.putControlledTriggers p .equipmentYouControlEnters
      else g
    let g :=
      if g.hasSubtype entered "Villain" || entered.printed.isArtifact then
        g.putControlledTriggers p .anotherVillainOrArtifactEnters
          (excludeId := some entered.id)
      else g
    let g :=
      if g.hasSubtype entered "Villain" then
        g.foldControlledPermanents p (excludeId := some entered.id) (fun g o =>
          g.putMatchingSourceTriggers p o .anotherVillainEnters
            (cause := some entered))
      else g
    let g :=
      if entered.printed.isArtifact then
        g.putControlledTriggers p .anotherArtifactEnters
      else g
    let g :=
      if !entered.printed.isToken && g.hasSubtype entered "Hero" then
        g.putControlledTriggers p .anotherNontokenHeroEnters
      else g
    let g :=
      if !entered.printed.isToken && entered.printed.isArtifact then
        g.putControlledTriggers p .anotherNontokenArtifactEnters
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

/-- Nick Fury power-up: put a Hero, Equipment, or Vehicle onto the battlefield.
A daybound front face enters back-face-up at night and cannot transform
(MSH 191). Otherwise it enters front-face-up; you may then transform a DFC
(MSH 192). Front-face enters abilities trigger in either case before the
optional transform. -/
def enterFromNickFury (g : Game) (controller : PlayerId) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g.logMsg "No card to put onto the battlefield"
  | some o =>
    let nightBack := g.isNight && o.printed.daybound && o.printed.otherFace.isSome
    let (g, newId) := g.putOntoBattlefield id controller
    let o := g.object! newId
    let g :=
      if nightBack then
        match o.printed.otherFace with
        | some back =>
          let shown := { back with otherFace := some { o.printed with otherFace := none } }
          let g := g.setObject { o with
            printed := shown
            status := { o.status with transformed := true, cantTransform := true } }
          g.logMsg s!"{shown.name} enters back face up (night / daybound)"
        | none => g
      else g
    g.afterPermanentEnters (g.object! newId)

end Game
end Mtg.Engine
