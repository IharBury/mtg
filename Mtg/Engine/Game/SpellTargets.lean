import Mtg.Engine.Game.LandsAndMana

/-!
# Announcing targets and modes (CR 601.2b–d)

Legal targets and modes while announcing a spell or ability, optional
target slots, divided-damage announcement, and the default choices the
demo agent uses (CR 700.2 / 115.1c).
-/

namespace Mtg.Engine
namespace Game

def legalTargets (g : Game) (caster : PlayerId) (effect : Effect) : Array Target :=
  g.legalTargetsForKind caster effect.targetKind

/-- Legal targets for a unified `Effect` (stored spell modes and faces). -/
def legalEffectTargets (g : Game) (caster : PlayerId) (effect : Effect) : Array Target :=
  g.legalTargetsForKind caster effect.targetKind

/-- Legal targets for an Aura spell with “Enchant creature” (CR 303.4). -/
def legalAuraTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalTargetsForKind caster .creature

/-- Chosen mode of `o` if it is a modal spell on the stack (CR 700.2). -/
def chosenModeOf (g : Game) (o : GameObject) : Option Nat :=
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => e.chosenMode
  | none => none

/-- Spell effect after a modal choice, if one has been announced (CR 700.2). -/
def spellEffectOf (o : GameObject) (chosenMode : Option Nat) : Option Effect :=
  if o.printed.isModal then
    match chosenMode with
    | some i => o.printed.spellModes[i]?
    | none => none
  else
    o.printed.spellEffect

/-- Spell effect of `o` using the mode announced on the stack, if any (CR 700.2). -/
def currentSpellEffect (g : Game) (o : GameObject) : Option Effect :=
  spellEffectOf o (g.chosenModeOf o)

/-- Legal targets for card face `c`, using `chosenMode` when a modal mode has
been announced (CR 115.1, 303.4, 601.2c). `none` on a modal card unions every
mode's targets (used when beginning to cast). -/
def legalTargetsForFace (g : Game) (p : PlayerId) (c : CardDef)
    (chosenMode : Option Nat := none) : Array Target :=
  if c.isModal && chosenMode.isNone then
    c.spellModes.foldl (fun acc e => acc ++ g.legalEffectTargets p e) #[]
  else
    let effect :=
      if c.isModal then chosenMode.bind (fun i => c.spellModes[i]?)
      else c.spellEffect
    match effect with
    | some e => g.legalEffectTargets p e
    | none => if c.isAura then g.legalAuraTargets p else #[]

/-- Legal targets for beginning to cast `o`, or for the chosen mode (CR 115.1, 303.4, 601.2c). -/
def legalSpellTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  g.legalTargetsForFace p o.printed (g.chosenModeOf o)

/-- True when this mode can be announced: it needs no target, or a legal one
exists (CR 700.2d). -/
def spellModeIsChoosable (g : Game) (p : PlayerId) (e : Effect) : Bool :=
  !e.requiresTarget || !(g.legalEffectTargets p e).isEmpty

/-- Legal mode indices for a modal spell (CR 700.2d). Untargeted modes stay
choosable even when another mode has no legal target. -/
def legalModes (g : Game) (p : PlayerId) (o : GameObject) : Array Nat :=
  if !o.printed.isModal then #[]
  else
    Id.run do
      let mut acc : Array Nat := #[]
      for i in [0:o.printed.spellModes.size] do
        if g.spellModeIsChoosable p o.printed.spellModes[i]! then
          acc := acc.push i
      return acc

/-- True when `e` targets a stack spell an opponent of `p` controls. -/
def effectHasOppSpellTarget (g : Game) (p : PlayerId) (e : Effect) : Bool :=
  e.targetKind.targetsStackSpell &&
    (g.legalTargetsForKind p e.targetKind).any (g.isOppStackSpellTarget p)

/-- Default mode: a preferred mode if that mode is legal, else the first legal
mode. Spell-counter modes are skipped unless an opponent's spell is a legal
target, so the demonstration agent does not counter its own spells. -/
def defaultMode (g : Game) (p : PlayerId) (spell : GameObject) : Option Nat :=
  let legal := g.legalModes p spell
  let avoidOwnCounter (i : Nat) : Bool :=
    match spell.printed.spellModes[i]? with
    | some e => e.targetKind.targetsStackSpell && !g.effectHasOppSpellTarget p e
    | none => false
  let usable := legal.filter (fun i => !avoidOwnCounter i)
  let pool := if usable.isEmpty then legal else usable
  let preferredIdx := pool.find? (fun i =>
    match spell.printed.spellModes[i]? with
    | some e => e.preferAsDefaultMode
    | none => false)
  match preferredIdx with
  | some i => some i
  | none => pool[0]?

/-- Legal targets for an activated-ability effect (CR 115.1 / 601.2c / 702.11b). -/
def legalAbilityTargets (g : Game) (p : PlayerId) (e : Effect) : Array Target :=
  g.legalTargetsForKind p e.targetKind

/-- The spell, activated ability, or triggered ability currently waiting for
targets (CR 601.2c / 603.3d). -/
def objectAwaitingTargets (g : Game) : Option GameObject :=
  match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
  | some o => some o
  | none => g.triggerNeedingTargets.bind (fun e => g.findObject? e.objectId)

/-- True while announcing a “divided as you choose” damage trigger (CR 601.2d). -/
def announcingDividedDamage (g : Game) : Bool :=
  match g.objectAwaitingTargets with
  | some o => (o.triggeredAbility.bind TriggeredAbility.dividedDamage?).isSome
  | none => false

/-- The stack entry for `objectId`, if that object is on the stack. -/
def stackEntry? (g : Game) (objectId : ObjectId) : Option StackEntry :=
  g.stack.find? (fun e => e.objectId == objectId)

/-- Targeting shape of the object currently being announced. -/
def targetingOf (g : Game) (obj : GameObject) : EffectTargeting :=
  let fromObj : EffectTargeting :=
    match obj.abilityEffect with
    | some e => e.targeting
    | none =>
      match obj.triggeredAbility with
      | some ab => ab.targeting
      | none =>
        match g.currentSpellEffect obj with
        | some e => e.targeting
        | none =>
          if obj.printed.isAura then EffectTargeting.of .creature .own
          else EffectTargeting.of .none
  match g.proposedSpell with
  | some prop =>
    if prop.spellId == obj.id then
      match prop.targetKindOverride with
      | some k => EffectTargeting.of k
      | none => fromObj
    else fromObj
  | none => fromObj

/-- True when two permanents share a card type (CR 205.2). -/
def sharesCardType (a b : GameObject) : Bool :=
  a.types.any (fun t => b.types.contains t)

/-- Current instance of the word “target” being announced (0-based).
Skipped optional slots count toward this index so the next instance is
the next “target” word in the card text (CR 601.2c). -/
def currentTargetSlot (g : Game) (obj : GameObject) : Nat :=
  match g.stackEntry? obj.id with
  | some e => e.targets.size + e.skippedOptionalSlots
  | none => 0

/-- Skip the current optional “up to one” instance without announcing a
target (CR 115.1c / 601.2c). -/
def skipOptionalTargetSlot (g : Game) (objectId : ObjectId) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == objectId) with
  | none => g
  | some i =>
    { g with stack := g.stack.set! i { g.stack[i]! with
        skippedOptionalSlots := g.stack[i]!.skippedOptionalSlots + 1 } }

/-- True when the current instance of “target” is optional (“up to one”). -/
def canSkipCurrentOptionalSlot (g : Game) (obj : GameObject) : Bool :=
  let kind := (g.targetingOf obj).kind
  let i := g.currentTargetSlot obj
  !kind.spec.slots.isEmpty && i < kind.spec.slots.size && kind.isOptionalSlot i

/-- Legal targets for the object currently being announced (spell or ability).
Already-chosen targets are excluded (CR 115.3). Multiple instances of the
word “target” offer the next unset slot from `EffectTargetKind.slotKind`.
Multiple targets of one instance are announced together. -/
def legalProposedTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  let already :=
    match g.stackEntry? o.id with
    | some e => e.targets
    | none => #[]
  let kind := (g.targetingOf o).kind
  let slot := kind.slotKind (g.currentTargetSlot o)
  let legal := (g.legalTargetsForKind p slot o.sourceId).filter (fun t => !already.contains t)
  let legal :=
    match g.proposedSpell with
    | some prop =>
      if prop.spellId == o.id &&
          prop.kind == .activatedAbility &&
          (prop.activation.any (·.equipWorthy) ||
            prop.original.printed.hasEquipWorthy) then
        legal.filter (fun t =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some c => c.printed.isWorthy
            | none => false
          | _ => false)
      else legal
    | none => legal
  match kind with
  | .twoNonlandsSharingType =>
    match already[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some first =>
        legal.filter (fun t =>
          match t with
          | Target.permanent oid =>
            match g.findObject? oid with
            | some other => sharesCardType first other
            | none => false
          | _ => false)
      | none => legal
    | _ => legal
  | .upToTwoCreaturesTotalMvAtMost n =>
    match already[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some first =>
        legal.filter (fun t =>
          match t with
          | Target.permanent oid =>
            match g.findObject? oid with
            | some other =>
              first.printed.manaValue + other.printed.manaValue ≤ n
            | none => false
          | _ => false)
      | none => legal
    | _ => legal
  | _ => legal

/-- Required and maximum announced targets for `obj` (CR 601.2c). Spells
such as Gaze in Wonder require one target and allow a second; every target
of that one instance of the word “target” is announced together. -/
def announcedTargetBounds (g : Game) (obj : GameObject) : Nat × Nat :=
  match g.currentSpellEffect obj with
  | some e =>
    let maxN := e.maxTargetCount
    if e.allowsZeroTargets then (0, maxN) else (e.targetCount, maxN)
  | none =>
    match obj.abilityEffect with
    | some e =>
      if e.allowsZeroTargets then (0, e.targetCount) else (e.targetCount, e.targetCount)
    | none =>
      match obj.triggeredAbility with
      | some ab =>
        let n := ab.targeting.targetCount
        -- “Up to one” is min 0, max the printed count (usually 1).
        if ab.allowsZeroTargets then (0, n) else (n, n)
      | none => (1, 1)

/-- True when at least the required targets are announced and another
optional target may still be chosen. Unused for one-word variable counts
such as “one or two target creatures”, which are announced together. -/
def canFinishOptionalTargets (g : Game) (obj : GameObject) : Bool :=
  match g.stackEntry? obj.id with
  | none => false
  | some e =>
    if (g.targetingOf obj).kind.spec.slots.isEmpty then false
    else
      let (minN, maxN) := g.announcedTargetBounds obj
      e.targets.size >= minN && e.targets.size < maxN

/-- True while announcing several targets of one instance of the word “target”
that is not a damage division (e.g. “one or two target creatures”). -/
def announcingSameWordMultiTargets (g : Game) : Bool :=
  match g.objectAwaitingTargets with
  | some o =>
    (g.targetingOf o).kind.spec.slots.isEmpty &&
      (g.announcedTargetBounds o).2 > 1 &&
      !g.announcingDividedDamage
  | none => false

/-- Whether `e` currently has a legal target, or does not require one. -/
def modeIsChoosable (g : Game) (p : PlayerId) (e : Effect) : Bool :=
  !e.requiresTarget || e.allowsZeroTargets || !(g.legalAbilityTargets p e).isEmpty

/-- Whether this activated ability currently has a legal target, or does not
require one. Equip restricted to a creature subtype uses that targeting
shape rather than “any creature you control” (CR 702.6 / 601.2c). -/
def abilityCanChooseTarget (g : Game) (p : PlayerId) (ab : ActivatedAbility) : Bool :=
  if ab.equipWorthy then
    let worthy :=
      (g.legalTargetsForKind p .creatureYouControl).filter (fun t =>
        match t with
        | Target.permanent id =>
          match g.findObject? id with
          | some c => c.printed.isWorthy
          | none => false
        | _ => false)
    !worthy.isEmpty
  else
    match ab.equipSubtype with
    | some t => !(g.legalTargetsForKind p (.creatureYouControlSubtype t)).isEmpty
    | none => ab.allModes.any (g.modeIsChoosable p)

/-- Last target in `legal` matching `pred`. -/
def lastLegalTarget (legal : Array Target) (pred : Target → Bool) : Option Target :=
  legal.filter pred |>.back?

/-- Whether this target is a permanent `p` controls. -/
def isOwnPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid => (g.findObject? oid).any (fun o => o.controlledBy p)
  | _ => false

/-- Whether this target is a permanent an opponent of `p` controls. -/
def isOppPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid => (g.findObject? oid).any (fun o => o.controlledBy (g.opponent p))
  | _ => false

/-- Default choice among `legal` for this targeting shape (CR 601.2c). -/
def preferredTarget (g : Game) (p : PlayerId) (targeting : EffectTargeting)
    (legal : Array Target) : Option Target :=
  let own := lastLegalTarget legal (fun t =>
    g.isOwnPermanentTarget p t || g.isOwnStackSpellTarget p t)
  let opp := lastLegalTarget legal (fun t =>
    g.isOppPermanentTarget p t || g.isOppStackSpellTarget p t)
  match targeting.prefer with
  | .own => own
  | .opponent => opp
  | .opponentPlayer =>
    let player := Target.player (g.opponent p)
    if legal.contains player then some player else legal[0]?
  | .last => legal.back?
  | .ownThenOpponent => own <|> opp
  | .selfPlayer =>
    let player := Target.player p
    if legal.contains player then some player else legal[0]?

/-- Default object or player to announce as a target (CR 601.2c). Damage spells
and divided-damage enters or attack triggers prefer the opponent; creature-damage abilities
and dies triggers prefer an opposing creature; destroy-flying prefers an opponent's flyer;
destroy-creature prefers an opposing creature;
destroy-colorless prefers an opposing colorless nonland; destroy-artifact-or-land prefers
an opposing artifact or land; counterspells prefer an opposing spell; Mirkwood Elk prefers an Elf
card in the controller's graveyard; Crude Bent Blade prefers an opposing player; Smite the Deathless prefers an opposing creature; Quarrel prefers a creature you control, then
an opposing creature; Rogue's Passage, pumps, the +1/+1-counter
mode, Equip, landfall, Galion's and Oliphaunt's attack triggers, and Auras prefer a creature the
caster controls. -/
def defaultTarget (g : Game) (p : PlayerId) (obj : GameObject) : Option Target :=
  let legal := g.legalProposedTargets p obj
  match g.preferredTarget p (g.targetingOf obj) legal with
  | some t => if legal.contains t then some t else legal[0]?
  | none => legal[0]?

/-- Default mode index for a modal activated ability (CR 601.2b). Prefers
dealing damage to an opposing creature, then destroying a colorless nonland. -/
def defaultAbilityMode (g : Game) (p : PlayerId) (modes : Array Effect) : Option Nat :=
  let choosable : Array (Nat × Effect) :=
    Id.run do
      let mut acc : Array (Nat × Effect) := #[]
      for i in [0:modes.size] do
        let e := modes[i]!
        if g.modeIsChoosable p e then
          acc := acc.push (i, e)
      return acc
  let findKind (pred : Effect → Bool) : Option Nat :=
    (choosable.find? (fun (_, e) => pred e)).map (·.1)
  let damageIdx :=
    findKind (fun e => e.abilityKind == .creatureDamage)
  let destroyIdx :=
    findKind (fun e => e.abilityKind == .destroyColorless)
  let oppHasCreature :=
    (g.permanentsOf (g.opponent p)).any (·.isCreature)
  let hasColorless := g.battlefield.any (·.isColorlessNonland)
  if oppHasCreature then
    damageIdx <|> destroyIdx <|> choosable[0]?.map (·.1)
  else if hasColorless then
    destroyIdx <|> damageIdx <|> choosable[0]?.map (·.1)
  else
    choosable[0]?.map (·.1)

def targetLogName (g : Game) : Target → String
  | .player pid => (g.player pid).name
  | .permanent oid | .card oid =>
    match g.findObject? oid with
    | some o => o.name
    | none => toString oid

end Game
end Mtg.Engine
