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
        acc.putControlledTriggers caster (.youCastColor c)
      else acc) g
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
  let g :=
    if !spell.printed.isCreature && nonc == 1 then
      (g.livingOpponents caster).foldl (fun acc pl =>
        acc.putControlledTriggers pl.id .opponentCastsFirstNoncreature) g
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

/-- After a permanent enters, put its enters triggers and “another … enters”
triggers (CR 603.6a). -/
def afterPermanentEnters (g : Game) (o : GameObject) : Game :=
  -- Storied is granted as the permanent enters, before SBA (legend rule /
  -- 0 toughness) and before enters triggers use the stack.
  let g := g.refreshEnduringStory
  let g := g.refreshCitysBlessing
  let g :=
    if o.printed.entersWithIndestructibleCounter then
      let g := g.setObject { o with status :=
        { o.status with indestructibleCounters := o.status.indestructibleCounters + 1 } }
      g.logMsg s!"{o.name} enters with an indestructible counter"
    else g
  let o := g.object! o.id
  let g :=
    if o.printed.entersWithShield > 0 then
      let n := g.extraCountersOn (o.controller) o.printed.entersWithShield
      let g := g.setObject { o with status :=
        { o.status with shield := o.status.shield + n } }
      g.logMsg s!"{o.name} enters with {n} shield counter(s)"
    else g
  let o := g.object! o.id
  let g :=
    if o.staticAbilities.any (fun
        | .entersWithXPlusOne => true
        | _ => false) then
      let n := g.extraCountersOn o.controller (o.chosenX.getD 0)
      if n == 0 then g
      else
        let g := g.setObject { o with status :=
          { o.status with plusOnePlusOne := o.status.plusOnePlusOne + n } }
        g.logMsg s!"{o.name} enters with {n} +1/+1 counter(s)"
    else g
  let o := g.object! o.id
  let g := g.setObject { o with status := { o.status with enteredThisTurn := true } }
  let o := g.object! o.id
  let g :=
    if o.printed.entersWithHopePerCreature then
      match o.controller with
      | some p =>
        let n := g.countCreaturesControlledBy p
        let g := g.setObject { o with status := { o.status with hope := n } }
        g.logMsg s!"{o.name} enters with {n} hope counter(s)"
      | none => g
    else g
  let o := g.object! o.id
  let g := g.addLoreAsSagaEnters o
  let o := g.object! o.id
  let g := g.putEnterTriggersOnStack o
  let g := g.putAnotherElfYouControlEntersTriggers (g.object! o.id)
  let g := g.putAnotherCreatureYouControlEntersTriggers (g.object! o.id)
  let g :=
    if o.printed.isToken then g
    else
      match o.controller with
      | none => g
      | some p =>
        g.putControlledTriggersWithPrompt p .thisOrNontokenSubtypeYouControlEnters
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
    g
  | none => g

/-- After a land enters, put its enters triggers, Elf-enters triggers, and landfall. -/
def afterLandEnters (g : Game) (land : GameObject) : Game :=
  let g := g.afterPermanentEnters land
  g.putLandYouControlEntersTriggers (g.object! land.id)

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
