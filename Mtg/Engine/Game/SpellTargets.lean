import Mtg.Engine.Game.LandsAndMana

/-!
# Announcing targets and modes (CR 601.2b–d)

Legal targets and modes while announcing a spell or ability, optional
target slots, divided-damage announcement, and the default choices the
demo agent uses (CR 700.2 / 115.1c).
-/

namespace Mtg.Engine
namespace Game

def legalTargets (g : Game) (caster : PlayerId) (effect : Effect)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForKind caster effect.targetKind sourceId

/-- Legal targets for a unified `Effect` (stored spell modes and faces). -/
def legalEffectTargets (g : Game) (caster : PlayerId) (effect : Effect)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForKind caster effect.targetKind sourceId

/-- What an Aura spell targets (CR 303.4a): a creature, a creature you control
(Secret Invasion), or an artifact or non-Aura enchantment (Puppet Crafting). -/
def auraTargetKind (aura : CardDef) : EffectTargetKind :=
  if aura.staticAbilities.any (· == .fra .enchantArtifactOrNonAuraEnchantment) then
    .filtered { noun := "target artifact or non-Aura enchantment"
                types := #[.artifact, .enchantment], nonAura := true }
  else if aura.staticAbilities.any (· == .fra .enchantCreatureYouControl) then
    .creatureYouControl
  else .creature

/-- Legal targets for an Aura spell with “Enchant creature” (CR 303.4). -/
def legalAuraTargets (g : Game) (caster : PlayerId) (aura : CardDef)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForKind caster (auraTargetKind aura) sourceId

/-- Chosen mode of `o` if it is a modal spell on the stack (CR 700.2). -/
def chosenModeOf (g : Game) (o : GameObject) : Option Nat :=
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => e.chosenMode
  | none => none

/-- Modes chosen for `o` on the stack, in printed order (CR 700.2). -/
def chosenModesOf (g : Game) (o : GameObject) : Array Nat :=
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => ((e.chosenMode.toArray ++ e.extraModes).qsort (· < ·))
  | none => #[]

/-- One effect standing for several chosen modes while targets are
announced: the instances of “target” of each mode, in printed order. -/
def combinedModesEffect (modes : Array Effect) : Option Effect :=
  match modes.toList with
  | [] => none
  | [e] => some e
  | e :: rest =>
    let kind := rest.foldl (fun k m => EffectTargetKind.pair k m.targetKind) e.targetKind
    some { e with
      targeting := .of kind
      allowsZeroTargets := modes.any (·.requiresTarget) &&
        modes.all (fun m => !m.requiresTarget || m.allowsZeroTargets)
      maxTargets := modes.foldl (fun acc m => acc + m.maxTargetCount) 0 }

/-- The targets a kicked spell announces instead (CR 702.33g / 601.2c): The
Eagles Are Coming! chooses any number of creatures you own, and Galadriel's
Dismissal targets a player. -/
def kickedSpellEffect (e : Effect) : Effect :=
  match e.resolution with
  | .eaglesAreComing =>
    { e with
      targeting := .of (.filtered
        { noun := "any number of target creatures you own", types := #[.creature], ownedByYou := true })
      allowsZeroTargets := true, maxTargets := 100 }
  | .phaseOutKicker => { e with targeting := .of .player }
  | _ => e

/-- True when `c` is a “Choose up to two” graveyard-return modal spell
(*Call Damage Control*, whose printed representation uses
`Effect.returnUpToTwoGyModal` so `OracleCandidates` round-trips cleanly). -/
def isReturnUpToTwoGyModal (c : CardDef) : Bool :=
  c.spellEffect.any (·.resolution == .returnUpToTwoGyModal)

/-- The four CR 700.2 modes of *Call Damage Control* in printed order:
0 = target artifact card, 1 = target creature card,
2 = target enchantment card, 3 = target land card (in your graveyard). -/
def returnUpToTwoGyModes : Array Effect :=
  #[(.artifact, "artifact"), (.creature, "creature"),
    (.enchantment, "enchantment"), (.land, "land")].map fun (ty, label) =>
    Effect.mkSpell
      (.of (.filtered {
        noun := s!"target {label} card in your graveyard"
        zone := .yourGraveyard
        types := #[ty]
        controller := .you }))
      .returnUpToTwoGyModal
      (castKind := .draw)
      (phraseOverride := s!"Target {label} card")

/-- Modes a modal spell face offers during CR 601.2b announcement. -/
def effectiveSpellModes (c : CardDef) : Array Effect :=
  if isReturnUpToTwoGyModal c then returnUpToTwoGyModes
  else c.spellModes

/-- True when `c` announces modes at CR 601.2b (`c.isModal` or `isReturnUpToTwoGyModal c`). -/
def isModalSpellFace (c : CardDef) : Bool :=
  c.isModal || isReturnUpToTwoGyModal c

/-- Spell effect of `c` after a modal choice, if one has been announced (CR 700.2).
With `extra` modes, the combined effect of all of them. -/
def spellEffectOfCard (c : CardDef) (chosenMode : Option Nat) (extra : Array Nat := #[])
    (kicked : Bool := false) : Option Effect :=
  let base :=
    if isModalSpellFace c then
      let modes := effectiveSpellModes c
      match chosenMode with
      | some i =>
        if extra.isEmpty then modes[i]?
        else combinedModesEffect (((#[i] ++ extra).qsort (· < ·)).filterMap (modes[·]?))
      | none => none
    else
      c.spellEffect
  if kicked then base.map kickedSpellEffect else base

/-- Spell effect of `o` after a modal choice, if one has been announced (CR 700.2),
after Layer 1 copy and Layer 3 text-changing effects (CR 612 / 613.1c).
With `extra` modes, the combined effect of all of them. -/
def spellEffectOf (g : Game) (o : GameObject) (chosenMode : Option Nat)
    (extra : Array Nat := #[]) (kicked : Bool := false) : Option Effect :=
  let bc := g.baseCard o
  let tcs := g.evalLayer3 o
  let raw := spellEffectOfCard bc chosenMode extra (kicked := kicked)
  if tcs.isEmpty then raw else raw.map (TextChange.applyEffect tcs)

/-- Spell effect of `o` using the mode announced on the stack, if any (CR 700.2),
after Layer 1 copy and Layer 3 text-changing effects (CR 612 / 613.1c). -/
def currentSpellEffect (g : Game) (o : GameObject) : Option Effect :=
  let kicked := g.wasKicked o.id
  match g.stack.find? (fun e => e.objectId == o.id) with
  | some e => g.spellEffectOf o e.chosenMode e.extraModes (kicked := kicked)
  | none => g.spellEffectOf o none (kicked := kicked)

/-- Legal targets for card face `c`, using `chosenMode` when a modal mode has
been announced (CR 115.1, 303.4, 601.2c). `none` on a modal card unions every
mode's targets (used when beginning to cast). -/
def legalTargetsForFace (g : Game) (p : PlayerId) (c : CardDef)
    (chosenMode : Option Nat := none) (tcs : Array TextChange := #[])
    (sourceId : Option ObjectId := none) : Array Target :=
  let modes := effectiveSpellModes c
  if isModalSpellFace c && chosenMode.isNone then
    modes.foldl (fun acc e =>
      acc ++ g.legalEffectTargets p (if tcs.isEmpty then e else TextChange.applyEffect tcs e) sourceId) #[]
  else
    let effect :=
      if isModalSpellFace c then chosenMode.bind (fun i => modes[i]?)
      else c.spellEffect
    match effect with
    | some e => g.legalEffectTargets p (if tcs.isEmpty then e else TextChange.applyEffect tcs e) sourceId
    | none => if c.isAura then g.legalAuraTargets p c sourceId else #[]

/-- Legal targets for beginning to cast `o`, or for the chosen mode (CR 115.1, 303.4, 601.2c). -/
def legalSpellTargets (g : Game) (p : PlayerId) (o : GameObject) : Array Target :=
  g.legalTargetsForFace p (g.baseCard o) (g.chosenModeOf o) (g.evalLayer3 o) (some o.id)

/-- Legal targets of card face `c`'s kicked spell effect (`kickedSpellEffect`). A
target-replacing kicker (*Galadriel's Dismissal* `.phaseOutKicker`, *The Eagles Are
Coming!*) announces those targets instead of the unkicked ones (CR 601.2b–c /
702.33d,g). Empty when `c` has no kicker or announces modes. -/
def legalKickedTargetsForFace (g : Game) (p : PlayerId) (c : CardDef)
    (tcs : Array TextChange := #[]) (sourceId : Option ObjectId := none) : Array Target :=
  match c.kicker, c.spellEffect with
  | some _, some e =>
    if isModalSpellFace c then #[]
    else
      let k := kickedSpellEffect e
      g.legalEffectTargets p (if tcs.isEmpty then k else TextChange.applyEffect tcs k) sourceId
  | _, _ => #[]

/-- Whether `c` may be proposed kicked with legal targets even when none of its unkicked
targets are legal: kicker may be chosen at CR 601.2b, and the kicked effect then announces
its own targets at CR 601.2c (CR 702.33d,g). Choosing not to kick afterwards with no legal
unkicked target reverses the proposal (CR 733.1). -/
def kickedFaceHasLegalTarget (g : Game) (p : PlayerId) (c : CardDef)
    (tcs : Array TextChange := #[]) (sourceId : Option ObjectId := none) : Bool :=
  match c.kicker, c.spellEffect with
  | some _, some e =>
    if isModalSpellFace c then false
    else
      let k := kickedSpellEffect e
      let k' := if tcs.isEmpty then k else TextChange.applyEffect tcs k
      !k'.requiresTarget || k'.allowsZeroTargets ||
        g.effectHasEnoughTargets p k' sourceId
  | _, _ => false

/-- True when this mode can be announced: it needs no target, or enough legal
ones exist (CR 700.2a / 601.2c / 115.3). -/
def spellModeIsChoosable (g : Game) (p : PlayerId) (e : Effect)
    (sourceId : Option ObjectId := none) : Bool :=
  !e.requiresTarget || g.effectHasEnoughTargets p e sourceId

/-- Legal mode indices for a modal spell (CR 700.2a). Untargeted modes stay
choosable even when another mode has no legal target. -/
def legalModes (g : Game) (p : PlayerId) (o : GameObject) : Array Nat :=
  let bc := g.baseCard o
  if !isModalSpellFace bc then #[]
  else
    let modes := effectiveSpellModes bc
    let tcs := g.evalLayer3 o
    Id.run do
      let mut acc : Array Nat := #[]
      for i in [0:modes.size] do
        let m := if tcs.isEmpty then modes[i]! else TextChange.applyEffect tcs modes[i]!
        if g.spellModeIsChoosable p m (some o.id) then
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
  let bc := g.baseCard spell
  let modes := effectiveSpellModes bc
  let tcs := g.evalLayer3 spell
  let modeAt? (i : Nat) : Option Effect :=
    modes[i]?.map (fun e => if tcs.isEmpty then e else TextChange.applyEffect tcs e)
  let avoidOwnCounter (i : Nat) : Bool :=
    match modeAt? i with
    | some e => e.targetKind.targetsStackSpell && !g.effectHasOppSpellTarget p e
    | none => false
  let usable := legal.filter (fun i => !avoidOwnCounter i)
  let pool := if usable.isEmpty then legal else usable
  let preferredIdx := pool.find? (fun i =>
    match modeAt? i with
    | some e => e.preferAsDefaultMode
    | none => false)
  match preferredIdx with
  | some i => some i
  | none => pool[0]?

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

/-- Targeting shape of the object currently being announced. -/
def targetingOf (g : Game) (obj : GameObject) : EffectTargeting :=
  let tcs := g.evalLayer3 obj
  let fromObj : EffectTargeting :=
    match obj.abilityEffect with
    | some e => (if tcs.isEmpty then e else TextChange.applyEffect tcs e).targeting
    | none =>
      match obj.triggeredAbility with
      | some ab => (if tcs.isEmpty then ab else TextChange.applyTriggeredAbility tcs ab).targeting
      | none =>
        match g.currentSpellEffect obj with
        | some e => e.targeting
        | none =>
          if g.isAura obj then
            match auraTargetKind (g.baseCard obj) with
            | .creature => EffectTargeting.of .creature .own
            | .creatureYouControl => EffectTargeting.of .creatureYouControl .own
            | k => EffectTargeting.of k

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
def sharesCardType (g : Game) (a b : GameObject) : Bool :=
  (g.types a).any (fun t => (g.types b).contains t)

/-- Current instance of the word “target” being announced (0-based).
Skipped optional slots count toward this index so the next instance is
the next “target” word in the card text (CR 601.2c). -/
def currentTargetSlot (g : Game) (obj : GameObject) : Nat :=
  match g.stackEntry? obj.id with
  | some e => e.targets.size + e.skippedOptionalSlots.size
  | none => 0

/-- Skip the current optional “up to one” instance without announcing a
target, recording its 0-based slot index (CR 115.1c / 601.2c). -/
def skipOptionalTargetSlot (g : Game) (objectId : ObjectId) : Game :=
  match g.findObject? objectId, g.stackEntry? objectId with
  | some obj, some _ =>
    let slot := g.currentTargetSlot obj
    g.change (.stackEntry objectId (.skipOptionalSlot slot))
  | _, _ => g

/-- Record whether every instance of “target” on this stack object has been
announced. A triggered ability with several instances stays unfinished until
the last one is chosen or skipped (CR 603.3d). -/
def markTargetsAnnounced (g : Game) (objectId : ObjectId) (done : Bool) : Game :=
  if g.stack.any (fun e => e.objectId == objectId) then
    g.change (.stackEntry objectId (.targetsAnnounced done))
  else g

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
  let (already, skipped) :=
    match g.stackEntry? o.id with
    | some e => (e.targets, e.skippedOptionalSlots)
    | none => (#[], #[])
  let kind := (g.targetingOf o).kind
  let curSlot := g.currentTargetSlot o
  let slot := kind.slotKind curSlot
  let selfSource := o.sourceId.orElse (fun _ => if o.zone == .stack then some o.id else none)
  let priorSlots : Array Nat :=
    if skipped.isEmpty then (List.range already.size).toArray
    else ((List.range curSlot).filter (fun s => !skipped.contains s)).toArray
  let forbidden : Array Target :=
    if kind.spec.slots.isEmpty then already
    else
      Id.run do
        let mut out : Array Target := #[]
        for grp in kind.distinctSlots do
          if grp.contains curSlot then
            for idx in [0:already.size] do
              if grp.contains (priorSlots[idx]?.getD idx) then
                out := out.push already[idx]!
        return out
  let legal := (g.legalTargetsForKind p slot selfSource).filter (fun t => !forbidden.contains t)
  let priorChosen : Array (Nat × Target) :=
    (List.range already.size).toArray.map (fun idx => (priorSlots[idx]?.getD idx, already[idx]!))
  let legal :=
    match kind with
    | .twoNonlandsSharingType =>
      legal.filter (fun t =>
        match t with
        | Target.permanent oid =>
          match g.findObject? oid with
          | some cand =>
            priorChosen.all (fun (_, u) =>
              match u with
              | Target.permanent pid =>
                (g.findObject? pid).any (g.sharesCardType · cand)
              | _ => false)
          | none => false
        | _ => priorChosen.isEmpty)
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
                g.objectManaValue first + g.objectManaValue other ≤ n
              | none => false
            | _ => false)
        | none => legal
      | _ => legal
    | _ => legal
  if kind.spec.slots.isEmpty || curSlot >= kind.spec.slots.size then legal
  else
    let remainingSlots : List (Nat × Array Target) :=
      ((List.range kind.spec.slots.size).drop (curSlot + 1)).map (fun s =>
        (s, g.legalTargetsForAtomicKind p (kind.slotKind s) selfSource))
    if remainingSlots.isEmpty then legal
    else
      legal.filter (fun t =>
        g.slotAssignmentExists kind remainingSlots (priorChosen.push (curSlot, t)))

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
      let maxN := e.maxTargetCount
      if e.allowsZeroTargets then (0, maxN) else (e.targetCount, maxN)
    | none =>
      match obj.triggeredAbility with
      | some ab =>
        let n := ab.targeting.targetCount
        let lifeTargets :=
          match ab.shared with
          | .resource .gainLifePlusOnes => true
          | _ => false
        let maxN :=
          if lifeTargets then ((g.lastKnownPowerOf? obj.id).getD 0).toNat
          else Nat.max n ab.effect.maxTargetCount
        -- “Up to one” is min 0, max the printed count (usually 1).
        -- Heroic Feast’s maximum is the life gained in that event.
        if lifeTargets || ab.allowsZeroTargets then (0, maxN) else (n, maxN)
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

/-- Whether `e` currently has enough legal targets, or does not require one
(CR 601.2c / 602.2b / 115.3). -/
def modeIsChoosable (g : Game) (p : PlayerId) (e : Effect)
    (sourceId : Option ObjectId := none) : Bool :=
  !e.requiresTarget || e.allowsZeroTargets || g.effectHasEnoughTargets p e sourceId

/-- Whether this activated ability currently has a legal target, or does not
require one (CR 702.6 / 601.2c / 702.16b). Subtype- and worthy-restricted Equip
targets are encoded directly in `ab.effect.targeting.kind`. -/
def abilityCanChooseTarget (g : Game) (p : PlayerId) (ab : ActivatedAbility)
    (sourceId : Option ObjectId := none) : Bool :=
  if ab.equipWorthy && ab.effect.targetKind == .creatureYouControl then
    !(g.legalTargetsForKind p .worthyCreatureYouControl sourceId).isEmpty
  else
    match ab.equipSubtype with
    | some t =>
      if ab.effect.targetKind == .creatureYouControl then
        !(g.legalTargetsForKind p (.creatureYouControlSubtype t) sourceId).isEmpty
      else
        ab.allModes.any (fun m => g.modeIsChoosable p m sourceId)
    | none => ab.allModes.any (fun m => g.modeIsChoosable p m sourceId)

/-- Last target in `legal` matching `pred`. -/
def lastLegalTarget (legal : Array Target) (pred : Target → Bool) : Option Target :=
  legal.filter pred |>.back?

/-- Whether this target is a permanent `p` controls. -/
def isOwnPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid => (g.findObject? oid).any (fun o => g.controlledBy o p)
  | _ => false

/-- Whether this target is a permanent an opponent of `p` controls. -/
def isOppPermanentTarget (g : Game) (p : PlayerId) : Target → Bool
  | .permanent oid =>
    (g.findObject? oid).any (fun o =>
      (g.livingOpponents p).any (fun pl => g.controlledBy o pl.id))
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
  let already := (g.stackEntry? obj.id).map (·.targets) |>.getD #[]
  let fresh := legal.filter (fun t => !already.contains t)
  let pool := if fresh.isEmpty then legal else fresh
  match g.preferredTarget p (g.targetingOf obj) pool with
  | some t => if legal.contains t then some t else pool[0]?
  | none => pool[0]?

/-- Default mode index for a modal activated ability (CR 601.2b). Prefers
dealing damage to an opposing creature, then destroying a colorless nonland. -/
def defaultAbilityMode (g : Game) (p : PlayerId) (modes : Array Effect)
    (sourceId : Option ObjectId := none) : Option Nat :=
  let choosable : Array (Nat × Effect) :=
    Id.run do
      let mut acc : Array (Nat × Effect) := #[]
      for i in [0:modes.size] do
        let e := modes[i]!
        if g.modeIsChoosable p e sourceId then
          acc := acc.push (i, e)
      return acc
  let findKind (pred : Effect → Bool) : Option Nat :=
    (choosable.find? (fun (_, e) => pred e)).map (·.1)
  let damageIdx :=
    findKind (fun e => e.abilityKind == .creatureDamage)
  let destroyIdx :=
    findKind (fun e => e.abilityKind == .destroyColorless)
  let oppHasCreature :=
    (g.livingOpponents p).any (fun pl => (g.permanentsOf pl.id).any (g.isCreature ·))
  let hasColorless := g.battlefield.any (g.isColorlessNonland ·)
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
    | some o => g.name o
    | none => toString oid

/-- Whether `candidate` is a legal complete target array for stack entry `e` /
`obj` with targeting shape `kind` (CR 115.3 / 115.7a,d / 707.10c): preserves
target count, satisfies each non-skipped slot's `slotKind`, enforces CR 115.3
distinctness within shared `"target"` groups (`distinctSlots` or single-slot
multi-target arrays), and checks multi-target relational constraints. -/
def validTargetArrayForEntry (g : Game) (e : StackEntry) (obj : GameObject)
    (kind : EffectTargetKind) (candidate : Array Target)
    (allowUnchangedIllegal : Bool := false) : Bool :=
  if candidate.size != e.targets.size then false
  else
    let selfSource := obj.sourceId.orElse (fun _ => if obj.zone == .stack then some obj.id else none)
    let totalSlots := candidate.size + e.skippedOptionalSlots.size
    let slotIndices : Array Nat :=
      if e.skippedOptionalSlots.isEmpty then (List.range candidate.size).toArray
      else ((List.range totalSlots).filter (fun s => !e.skippedOptionalSlots.contains s)).toArray
    let slotsOk :=
      slotIndices.size == candidate.size &&
        (List.range candidate.size).all fun idx =>
          let slotIdx := slotIndices[idx]!
          (allowUnchangedIllegal && candidate[idx]! == e.targets[idx]!) ||
            (g.legalTargetsForKind e.controller (kind.slotKind slotIdx) selfSource).contains candidate[idx]!
    let distinctOk :=
      if kind.spec.slots.isEmpty then
        candidate.toList.eraseDups.length == candidate.size
      else
        kind.distinctSlots.all fun grp =>
          let picked := (List.range candidate.size).filterMap fun idx =>
            if grp.contains slotIndices[idx]! then some candidate[idx]! else none
          picked.eraseDups.length == picked.length
    let relationOk :=
      (allowUnchangedIllegal && candidate == e.targets) ||
        match kind with
      | .twoNonlandsSharingType =>
        match candidate[0]?, candidate[1]? with
        | some (Target.permanent a), some (Target.permanent b) =>
          match g.findObject? a, g.findObject? b with
          | some oa, some ob => g.sharesCardType oa ob
          | _, _ => false
        | _, _ => candidate.size < 2
      | .upToTwoCreaturesTotalMvAtMost n =>
        let totalMv := candidate.foldl (fun acc t =>
          match t with
          | Target.permanent oid =>
            acc + ((g.findObject? oid).map g.objectManaValue |>.getD 0)
          | _ => acc) 0
        totalMv ≤ n
      | _ => true
    slotsOk && distinctOk && relationOk

end Game
end Mtg.Engine
