import Mtg.Engine.Game.Costs

/-!
# The casting process (CR 601.2)

Entering the proposal window, `castSpell`, and announcing modes, a value
for `{X}` (CR 107.3a), targets, divided damage, and triggered-ability
targets.
-/

namespace Mtg.Engine
namespace Game

/-- After proposing a spell or activated ability, announce `{X}` and modes
(CR 107.3a / 601.2b), then additional costs, then targets (CR 601.2c), then
mana abilities (CR 601.2g). -/
def enterProposalWindow (g : Game) (p : PlayerId) (pl : Player) (prop : ProposedSpell)
    (needsMode needsTarget : Bool) (modeCitation : String)
    (needsAdditionalCost : Bool := false) (needsKicker : Bool := false)
    (needsGift : Bool := false) (needsTeamwork : Bool := false) : Game :=
  if prop.cost.containsX then
    let g := { g with pending := .chooseX p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a value for X (CR 107.3a / 601.2b)"
  else if needsMode then
    let g := { g with pending := .chooseMode p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a mode ({modeCitation})"
  else if needsAdditionalCost then
    let g := { g with pending := .chooseAdditionalCost p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose an additional cost (CR 601.2b)"
  else if needsKicker then
    let g := { g with pending := .chooseKicker p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may kick the spell (CR 702.32 / 601.2b)"
  else if needsGift then
    let g := { g with pending := .chooseGift p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may promise a gift (CR 702.185 / 601.2b)"
  else if needsTeamwork then
    let g := { g with pending := .chooseTeamwork p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may pay a teamwork cost (CR 702.194 / 601.2b)"
  else if needsTarget then
    let g := { g with pending := .chooseTargets p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} must choose a target (CR 601.2c)"
  else
    let g := { g with pending := .activateManaAbilities p, proposedSpell := some prop }
    g.logMsg s!"{pl.name} may activate mana abilities (CR 601.2g)"

def castSpell (g : Game) (p : PlayerId) (id : ObjectId) (asAdventure : Bool := false) :
    Except String Game := do
  if !g.hasPriority p then
    throw "You don't have priority"
  if p != g.activePlayer &&
      (g.permanentsOf g.activePlayer).any (fun o =>
        o.staticAbilities.any (fun
          | .opponentsCantCastOnYourTurn => true
          | _ => false)) then
    throw "Opponents can't cast spells during that player's turn"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if asAdventure then
    if card.printed.adventure.isNone then
      throw s!"{card.name} has no Adventure"
    if g.adventureExileForbidsRecast card then
      throw "You may not cast that card as an Adventure this way (CR 715.3d)"
  let face :=
    match asAdventure, card.printed.adventure with
    | true, some adv => adv.toCardDef
    | _, _ => card.printed
  let pl := g.player p
  if face.isLand then
    throw "Lands are played, not cast (CR 305)"
  if face.hasSorcerySpeed && !g.asSorcery? p then
    throw s!"{face.name} has sorcery speed"
  if face.isModal then
    if !face.spellModes.any (g.spellModeIsChoosable p) && !face.allowsZeroTargets then
      throw s!"{face.name} requires a target"
  else if face.requiresTarget &&
      (g.legalCastTargets p face).isEmpty && !face.allowsZeroTargets then
    throw s!"{face.name} requires a target"
  if face.additionalCostSacrificeArtifactOrCreature &&
      face.additionalCostOrPayGeneric.isNone &&
      (g.sacrificeCreatureOrArtifactChoices p id).isEmpty then
    throw s!"{face.name} requires sacrificing an artifact or creature"
  -- CR 601.2a: propose the spell by moving it onto the stack. Modes and
  -- additional costs are announced at CR 601.2b, targets at CR 601.2c; mana
  -- is not required yet (CR 601.2g). CR 715.3: an adventurer card may be
  -- cast as its Adventure.
  let cost := g.playManaCost card face
  let fromGraveyard := card.zone == .graveyard card.owner
  let needsSacrifice :=
    face.additionalCostSacrificeArtifactOrCreature &&
      face.additionalCostOrPayGeneric.isNone
  let original := card
  let handBefore := pl.hand
  let stackBefore := g.stack
  let manaBefore := pl.manaPool
  let fromTop :=
    original.zone == .library p && (g.player p).library.back? == some id
  let (g, newId) := g.move id .stack (some p)
  let g := { g with castingFromTop := fromTop || g.castingFromTop }
  let g :=
    if asAdventure then
      let o := g.object! newId
      g.setObject { o with printed := face, adventurerCard := some original.printed }
    else g
  let g :=
    if fromGraveyard then
      let o := g.object! newId
      g.setObject { o with castFromGraveyard := true }
    else g
  let g := g.putStackEntry p newId
  let needsMode := face.isModal
  let needsTarget := face.requiresTarget && !needsMode
  let needsAdditionalCostChoice := face.additionalCostOrPayGeneric.isSome
  let needsKicker := face.kicker.isSome
  let needsGift := face.giftTreasure
  let needsTeamwork := face.teamwork.isSome
  if !needsMode && !needsTarget && !cost.includesManaPayment && !cost.containsX &&
      !needsSacrifice &&
      !needsAdditionalCostChoice && !needsKicker && !needsGift && !needsTeamwork then
    return g.becomeCast p (g.object! newId)
  let lifeInstead :=
    match original.playPermission with
    | some perm =>
      if perm.payLifeEqualManaValue then g.objectManaValue original else 0
    | none => 0
  let prop : ProposedSpell := {
    caster := p
    cost := cost
    spellId := newId
    original := original
    handBefore := handBefore
    stackBefore := stackBefore
    manaBefore := manaBefore
    needsSacrificeOther := needsSacrifice
    payLife := lifeInstead
  }
  let g := g.logMsg s!"{pl.name} begins casting {face.name}"
  return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b / 700.2"
    (needsAdditionalCost := needsAdditionalCostChoice)
    (needsKicker := needsKicker) (needsGift := needsGift)
    (needsTeamwork := needsTeamwork)

/-- Announce the chosen mode for a modal spell or activated ability
(CR 601.2b / 700.2). -/
def announceMode (g : Game) (p : PlayerId) (mode : Nat) : Except String Game := do
  match g.pending with
  | .chooseMode caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a mode (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for a mode (CR 601.2b)"
    match prop.kind with
    | .activatedAbility =>
      let some chosen := prop.abilityModes[mode]?
        | throw "No such mode (CR 601.2b)"
      if !g.modeIsChoosable p chosen then
        throw "That mode requires a target (CR 700.2d)"
      let some obj := g.findObject? prop.spellId | throw "The ability left the stack"
      let g := g.setObject { obj with abilityEffect := some chosen }
      let g := g.logMsg
        s!"{(g.player p).name} chooses a mode: {chosen.toNotation} (CR 601.2b)"
      if chosen.requiresTarget then
        let g := { g with pending := .chooseTargets p }
        return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
      return g.afterTargetsChosen
    | .spell =>
      let some spell := g.findObject? prop.spellId | throw "The spell left the stack"
      if !spell.printed.isModal then
        throw "That spell is not modal (CR 700.2)"
      let some effect := spell.printed.spellModes[mode]? | throw "No such mode (CR 700.2)"
      if !g.spellModeIsChoosable p effect then
        throw "That mode has no legal target (CR 700.2d)"
      let g := g.setProposedMode mode
      let g := g.logMsg
        s!"{(g.player p).name} chooses mode {mode + 1} ({effect.toNotation}) (CR 601.2b)"
      if spell.printed.additionalCostOrPayGeneric.isSome then
        let g := { g with pending := .chooseAdditionalCost p }
        return g.logMsg s!"{(g.player p).name} must choose an additional cost (CR 601.2b)"
      if effect.requiresTarget then
        let g := { g with pending := .chooseTargets p }
        return g.logMsg s!"{(g.player p).name} must choose a target (CR 601.2c)"
      return g.afterTargetsChosen
  | _ => throw "Not time to choose a mode (CR 601.2b)"

/-- Announce the value of `{X}` for a proposed spell or ability
(CR 107.3a / 601.2b). Substitutes `{X}` into the locked-in cost and
continues the proposal window. -/
def announceX (g : Game) (p : PlayerId) (x : Nat) : Except String Game := do
  match g.pending with
  | .chooseX caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose a value for X (CR 601.2b)"
    let some prop := g.proposedSpell
      | throw "No spell or ability is waiting for X (CR 601.2b)"
    let some obj := g.findObject? prop.spellId
      | throw "The spell or ability left the stack"
    let g := g.setObject { obj with chosenX := some x }
    let cost :=
      match prop.kind, prop.activation, prop.sourceId.bind g.findObject? with
      | .activatedAbility, some ab, src =>
        g.activationManaCost p ab (source := src) (chosenX := some x)
      | .spell, _, _ =>
        let spell := g.object! prop.spellId
        g.playManaCost spell spell.printed
      | _, _, _ => prop.cost.substituteX x
    let prop := { prop with cost }
    let g := { g with proposedSpell := some prop }
    let g := g.logMsg
      s!"{(g.player p).name} chooses X = {x} (CR 107.3a / 601.2b)"
    let pl := g.player p
    match prop.kind with
    | .activatedAbility =>
      let needsMode :=
        match prop.activation with
        | some ab => ab.isModal
        | none => false
      let needsTarget :=
        match prop.activation with
        | some ab => ab.effect.requiresTarget
        | none => false
      return g.enterProposalWindow p pl prop needsMode needsTarget "CR 601.2b"
    | .spell =>
      let spell := g.object! prop.spellId
      let face := spell.printed
      return g.enterProposalWindow p pl prop face.isModal
        (face.requiresTarget && !face.isModal) "CR 601.2b / 700.2"
        (needsAdditionalCost := face.additionalCostOrPayGeneric.isSome)
        (needsKicker := face.kicker.isSome) (needsGift := face.giftTreasure)
        (needsTeamwork := face.teamwork.isSome)
  | _ => throw "Not time to choose X (CR 601.2b)"

/-- After a trigger's targets (and any damage division) are fully announced,
prompt the next trigger that needs targets or continue the CR 603.3b
process (remaining waiting triggers, then SBAs). -/
def afterTriggerTargetsChosen (g : Game) : Game :=
  match g.triggerNeedingTargets with
  | some _ =>
    promptTriggerTargetsIfNeeded { g with pending := .none }
  | none =>
    receivePriority { g with pending := .none } g.activePlayer false

/-- Loki (MSH 247): when a player or permanent becomes the target of an
ability you control, those triggers wait on the stack above that ability. -/
def queueYouTargetTriggers (g : Game) (controller : PlayerId) (obj : GameObject) : Game :=
  if obj.abilityEffect.isSome || obj.triggeredAbility.isSome then
    g.putControlledTriggers controller .youTargetSomething
  else g

/-- Announce targets for the current instance of the word “target”
(CR 601.2c / 603.3d). Multiple targets of one instance (including a
“divided as you choose” division, CR 601.2d) are chosen together. Each
further instance is a later announcement. An omitted amount on a
divided-damage ability assigns all remaining damage to that one target. -/
def announceTargetChoices (g : Game) (p : PlayerId)
    (choices : Array (Target × Option Nat)) : Except String Game := do
  match g.pending with
  | .chooseTargets caster =>
    if caster != p then
      throw s!"Only {(g.player caster).name} may choose targets (CR 601.2c)"
    let some obj := g.objectAwaitingTargets | throw "No spell is waiting for a target (CR 601.2c)"
    if choices.isEmpty then
      throw "Choose a target (CR 601.2c)"
    match obj.triggeredAbility.bind TriggeredAbility.dividedDamage? with
    | some (total, maxTargets) =>
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      if !e.targets.isEmpty || assignedDividedDamage e != 0 then
        throw "Those targets must be chosen at the same time (CR 601.2c)"
      if total == 0 then
        throw "All damage has already been divided (CR 601.2d)"
      let assignments : Array (Target × Nat) ←
        if choices.size == 1 && choices[0]!.2.isNone then
          pure #[(choices[0]!.1, total)]
        else if choices.any (fun c => c.2.isNone) then
          throw "Each target must be assigned a damage amount (CR 601.2d)"
        else
          pure (choices.map (fun c => (c.1, c.2.getD 0)))
      if assignments.size > maxTargets then
        throw s!"Cannot choose more than {maxTargets} targets (CR 601.2d)"
      let legal := g.legalProposedTargets p obj
      let mut assigned : Nat := 0
      let mut targets : Array Target := #[]
      let mut amounts : Array Nat := #[]
      for (t, n) in assignments do
        if !legal.contains t then
          throw "Illegal target (CR 601.2c)"
        if targets.contains t then
          throw "Illegal target (CR 601.2c)"
        if n == 0 then
          throw "Each target must be dealt at least 1 damage (CR 601.2d)"
        assigned := assigned + n
        targets := targets.push t
        amounts := amounts.push n
      if assigned > total then
        throw s!"Only {total} damage remains to divide (CR 601.2d)"
      if assigned < total then
        throw "Must assign all remaining damage among the chosen targets (CR 601.2d)"
      let mut g := g.setStackEntryTargets obj.id targets amounts
      for (t, n) in assignments do
        g := g.logMsg
          s!"{(g.player p).name} chooses {g.targetLogName t} to be dealt {n} damage (CR 601.2d)"
      g := g.queueYouTargetTriggers p obj
      return g.afterTriggerTargetsChosen
    | none =>
      if choices.any (fun c => c.2.isSome) then
        throw "That spell or ability does not divide damage (CR 601.2d)"
      let some e := g.stackEntry? obj.id | throw "The ability left the stack"
      let kind := (g.targetingOf obj).kind
      let (minN, maxN) := g.announcedTargetBounds obj
      if kind.spec.slots.isEmpty then
        if !e.targets.isEmpty then
          throw "Those targets must be chosen at the same time (CR 601.2c)"
        if choices.size < minN then
          throw s!"Choose at least {minN} target(s) (CR 601.2c)"
        if choices.size > maxN then
          throw s!"Cannot choose more than {maxN} targets (CR 601.2c)"
        let legal := g.legalProposedTargets p obj
        let mut targets : Array Target := #[]
        for (t, _) in choices do
          if !legal.contains t then
            throw "Illegal target (CR 601.2c)"
          if targets.contains t then
            throw "Illegal target (CR 601.2c)"
          targets := targets.push t
        let mut g := g.setStackEntryTargets obj.id targets
        for t in targets do
          g := g.logMsg
            s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
        if g.proposedSpell.isSome then
          return g.afterTargetsChosen
        g := g.queueYouTargetTriggers p obj
        return g.afterTriggerTargetsChosen
      if choices.size != 1 then
        throw "Choose each instance of the word \"target\" separately (CR 601.2c)"
      let t := choices[0]!.1
      if !(g.legalProposedTargets p obj).contains t then
        throw "Illegal target (CR 601.2c)"
      let g := g.setStackEntryTargets obj.id (e.targets.push t)
      let g := g.logMsg
        s!"{(g.player p).name} chooses {g.targetLogName t} as a target (CR 601.2c)"
      if g.currentTargetSlot obj < kind.spec.slots.size then
        return { g with pending := .chooseTargets p }
      if g.proposedSpell.isSome then
        return g.afterTargetsChosen
      let g := g.queueYouTargetTriggers p obj
      return g.afterTriggerTargetsChosen
  | _ => throw "Not time to choose targets (CR 601.2c)"

/-- Announce one target of the current instance of the word “target”
(CR 601.2c / 603.3d). On a divided-damage ability this assigns all remaining
damage to that target (CR 601.2d). On “one or two target creatures” this
chooses that one creature and finishes the instance. -/
def announceTarget (g : Game) (p : PlayerId) (t : Target) : Except String Game :=
  g.announceTargetChoices p #[(t, none)]

/-- Announce every target of one instance of the word “target” together
(CR 601.2c), including “one or two target creatures”. -/
def announceTargets (g : Game) (p : PlayerId) (ts : Array Target) : Except String Game :=
  g.announceTargetChoices p (ts.map (fun t => (t, none)))

/-- Announce every target of one instance of the word “target” on a
“divided as you choose” effect (CR 601.2c / 601.2d). -/
def announceDividedDamage (g : Game) (p : PlayerId)
    (assignments : Array (Target × Nat)) : Except String Game :=
  g.announceTargetChoices p (assignments.map (fun (t, n) => (t, some n)))

end Game
end Mtg.Engine
