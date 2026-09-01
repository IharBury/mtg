import Mtg.Engine.Game.SpellTargets

/-!
# Casting legality and payment (CR 601)

Cast timing (flash, sorcery speed), castability from each zone,
restrictions on proposed spells, choosing mana sources for a proposal,
paying costs, reversing an illegal proposal (CR 733.1), ward
(CR 702.21), locking in targets, and becoming cast or activated.
-/

namespace Mtg.Engine
namespace Game

/-- Captain Mar-Vell: as though spells had flash while an opponent has
cast a spell this turn (MSH 105). The permanent need not have been on
the battlefield when that spell was cast. -/
def cosmicAwarenessFlash (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .flashIfOpponentCastThisTurn => true
      | _ => false)) &&
    (g.livingOpponents p).any (fun pl => pl.spellsCastThisTurn > 0)

/-- Timing check shared by beginning to cast a spell or an Adventure (CR 601.3). -/
def timingAllowsCast (g : Game) (p : PlayerId) (face : CardDef) : Bool :=
  let hasConditionalFlash :=
    match face.flashIfYouControlSubtype with
    | some t => g.controlsAnySubtype p #[t]
    | none => false
  let radagastFlash :=
    face.isCreature && (g.player p).creatureSpellsCastThisTurn == 0 &&
      (g.permanentsOf p).any (fun o => o.printed.firstCreatureHasFlash)
  g.hasPriority p &&
  (if face.hasSorcerySpeed && !hasConditionalFlash && !radagastFlash &&
      !g.cosmicAwarenessFlash p then
    g.asSorcery? p else true)

/-- Whether `p` may begin to cast `o` (CR 601.3). Having enough mana in the
pool is not required; mana abilities are activated at CR 601.2g. Additional
non-mana costs such as sacrificing a permanent must still be payable. -/
def canCast (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  !o.printed.isLand &&
  !(g.player p).cantCastSpellsThisTurn &&
  g.mayPlay p o &&
  (match o.playPermission with
   | some perm => perm.ignoreTiming || g.timingAllowsCast p o.printed
   | none => g.timingAllowsCast p o.printed) &&
  (if o.printed.additionalCostSacrificeArtifactOrCreature &&
      o.printed.additionalCostOrPayGeneric.isNone then
    (g.permanentsOf p).any (fun perm =>
      perm.id != o.id && (perm.isCreature || perm.printed.isArtifact))
   else true) &&
  -- Untargeted permanents, and untargeted instants/sorceries with a modeled
  -- effect (e.g. Night's Whisper), may be proposed (CR 601.3).
  if o.printed.requiresTarget then
    o.printed.allowsZeroTargets || !(g.legalSpellTargets p o |>.isEmpty)
  else o.printed.isPermanentCard || o.printed.spellEffect.isSome || o.printed.isModal

/-- Whether `p` can pay a mandatory additional cost of `o` from `available`
(another card to discard, a permanent to sacrifice, or the generic
alternative). Mana abilities are not activated here. -/
def canPayAnnouncedAdditional (g : Game) (p : PlayerId) (o : GameObject)
    (available : ManaPool) : Bool :=
  let allowElf := o.hasSubtype "Elf"
  let free := o.playPermission.any (·.withoutManaCost)
  let payExtra (n : Nat) : Bool :=
    if free then
      available.canPay (ManaCost.ofGeneric n) (allowElfRestricted := allowElf)
    else
      available.canPay (o.printed.manaCost.addGeneric n)
        (allowElfRestricted := allowElf)
  match o.printed.additionalCostOrPayGeneric, o.printed.additionalCostDiscardOrPayGeneric with
  | some n, _ =>
    (g.permanentsOf p).any (fun perm =>
      perm.id != o.id && (perm.isCreature || perm.printed.isArtifact)) || payExtra n
  | none, some n =>
    (g.player p).hand.any (fun id => id != o.id) || payExtra n
  | none, none => true

/-- True when the CR 715.3d exile permission forbids recasting as an Adventure. -/
def adventureExileForbidsRecast (_g : Game) (o : GameObject) : Bool :=
  match o.playPermission with
  | some perm => perm.fromAdventure
  | none => false

/-- Legal targets for beginning to cast card `c` (from hand or as an Adventure). -/
def legalCastTargets (g : Game) (p : PlayerId) (c : CardDef) : Array Target :=
  g.legalTargetsForFace p c none

/-- Whether `p` may begin to cast `o` as an Adventure (CR 715.3). -/
def canCastAdventure (g : Game) (p : PlayerId) (o : GameObject) : Bool :=
  match o.printed.adventure with
  | none => false
  | some adv =>
    let face := adv.toCardDef
    !g.adventureExileForbidsRecast o &&
    g.mayPlay p o &&
    (match o.playPermission with
     | some perm => perm.ignoreTiming || g.timingAllowsCast p face
     | none => g.timingAllowsCast p face) &&
    if face.requiresTarget then !(g.legalCastTargets p face).isEmpty
    else true

/-- Whether paying this proposed spell or ability may spend Elf-restricted mana
(CR 106.10): Elf spells, and activated abilities of Elf sources. -/
def proposedAllowsElfRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => g.hasSubtype o "Elf"
    | none => false
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => g.hasSubtype src "Elf"
    | none => g.hasSubtype prop.original "Elf"

/-- Whether paying this proposed spell may spend instant/sorcery-restricted mana. -/
def proposedAllowsInstRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => o.printed.isInstantOrSorcery
    | none => false
  | .activatedAbility => false

/-- Whether paying this proposed spell may spend legendary-restricted mana. -/
def proposedAllowsLegendaryRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => o.isLegendary
    | none => false
  | .activatedAbility => false

/-- Object whose types decide Hero / Villain / creature-source restrictions. -/
def proposedRestrictionSource (g : Game) (prop : ProposedSpell) : Option GameObject :=
  match prop.kind with
  | .spell => g.findObject? prop.spellId
  | .activatedAbility =>
    match prop.sourceId.bind g.findObject? with
    | some src => some src
    | none => some prop.original

/-- Whether paying this proposed spell or ability may spend Hero-restricted
mana (MSH 72): Hero spells, and activated abilities of Hero sources
(including changeling and cards in any zone). -/
def proposedAllowsHeroRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match g.proposedRestrictionSource prop with
  | some o => g.hasSubtype o "Hero"
  | none => false

/-- Whether paying this proposed spell or ability may spend Villain-restricted
mana (MSH 73): Villain spells, and activated abilities of Villain sources. -/
def proposedAllowsVillainRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match g.proposedRestrictionSource prop with
  | some o => g.hasSubtype o "Villain"
  | none => false

/-- Whether paying this proposed activation may spend creature-restricted mana
(MSH 75). Casting a creature spell does not qualify. -/
def proposedAllowsCreatureRestricted (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .spell => false
  | .activatedAbility =>
    match g.proposedRestrictionSource prop with
    | some o => o.printed.isCreature || o.isCreature
    | none => false

/-- Whether paying this proposal may spend “can't be spent to cast a
nonartifact spell” mana (MSH 345 / 347): artifact spells, and any
activated ability. -/
def proposedAllowsCantNonartifact (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.kind with
  | .activatedAbility => true
  | .spell =>
    match g.findObject? prop.spellId with
    | some o => o.printed.isArtifact
    | none => false

/-- Mana types `src` can produce that may be spent on `prop` (CR 106.10). -/
def usableManaTypesForProposed (g : Game) (src : GameObject) (types : Array ManaType)
    (prop : ProposedSpell) : Array ManaType :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let allowLeg := g.proposedAllowsLegendaryRestricted prop
  if src.printed.tapAddAnyColorEqualToPower && !allowElf then #[]
  else if src.printed.tapAddAnyColorForInstantOrSorcery && !allowInst then #[]
  else if src.printed.tapAddAnyColorForLegendary && !allowLeg then
    types.filter (fun t =>
      src.printed.simpleTapAddMana.contains t || src.printed.tapAddOneOf.contains t)
  else types

/-- Untapped mana sources `p` may activate while paying `prop` (CR 601.2g).
Sources reserved for `{T}`, or whose mana cannot be spent on this spell or
ability, are omitted. -/
def manaSourcesForProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Array (GameObject × Array ManaType) :=
  (g.manaSources p).filterMap (fun (src, types) =>
    if prop.tapSource && prop.sourceId == some src.id then none
    else
      let usable := g.usableManaTypesForProposed src types prop
      if usable.isEmpty then none
      else some (src, usable))

/-- Pool after tapping `src` for `t`, including spending restrictions. -/
def poolAfterTap (g : Game) (pool : ManaPool) (src : GameObject) (t : ManaType) :
    ManaPool :=
  pool.add t (g.manaFromTap src t)
    (elfRestricted := src.printed.tapAddAnyColorEqualToPower)
    (instRestricted := src.printed.tapAddAnyColorForInstantOrSorcery)

/-- Whether some assignment of types from `sources` pays `cost`. -/
def canPayFromSources (g : Game) (pool : ManaPool) (cost : ManaCost)
    (allowElf allowInst : Bool) : List (GameObject × Array ManaType) → Bool
  | [] => pool.canPay cost allowElf allowInst
  | (src, types) :: rest =>
    types.any (fun t =>
      g.canPayFromSources (g.poolAfterTap pool src t) cost allowElf allowInst rest)

/-- Whether tapping `src` for `t` covers more of `cost` than the current pool. -/
def typeHelpsPay (g : Game) (p : PlayerId) (src : GameObject) (t : ManaType)
    (cost : ManaCost) (allowElfRestricted : Bool) (allowInstRestricted : Bool) : Bool :=
  let amount := g.manaFromTap src t
  if amount == 0 then false
  else
    let pool := (g.player p).manaPool
    let before := pool.coveredMana cost allowElfRestricted allowInstRestricted
    let after := g.poolAfterTap pool src t
    after.coveredMana cost allowElfRestricted allowInstRestricted > before

/-- A mana type among `types` that helps pay remaining symbols of `cost`.
When `src` plus `others` can pay, types that would make the cost unpayable
are omitted so Hidden Lair taps for `{U}` or `{B}` instead of a color another
source already covers. Prefers an unmet colored requirement, then colorless
if it can be spent. -/
def preferredManaType (g : Game) (p : PlayerId) (src : GameObject)
    (types : Array ManaType) (cost : ManaCost) (allowElfRestricted : Bool)
    (allowInstRestricted : Bool := false)
    (others : List (GameObject × Array ManaType) := []) : Option ManaType :=
  let pool := (g.player p).manaPool
  let helpful := types.filter (fun t =>
    g.typeHelpsPay p src t cost allowElfRestricted allowInstRestricted)
  let payable :=
    g.canPayFromSources pool cost allowElfRestricted allowInstRestricted
      ((src, types) :: others)
  let viable :=
    if payable then
      helpful.filter (fun t =>
        g.canPayFromSources (g.poolAfterTap pool src t) cost
          allowElfRestricted allowInstRestricted others)
    else helpful
  match viable[0]? with
  | none => none
  | some first =>
    match Color.all.find? (fun c =>
      let req := cost.coloredCount c
      let held := pool.usable (.colored c) allowElfRestricted allowInstRestricted
      held < req && viable.contains (.colored c)) with
    | some c => some (.colored c)
    | none =>
      if viable.contains .colorless then some .colorless
      else some first

/-- Whether `(src, t)` is a better next tap than `(bestSrc, bestT)`: avoid
creatures when another source helps, then prefer colorless. Equal ranks keep
the earlier source. -/
def betterManaTap (src : GameObject) (t : ManaType)
    (bestSrc : GameObject) (bestT : ManaType) : Bool :=
  (!src.isCreature && bestSrc.isCreature) ||
    (src.isCreature == bestSrc.isCreature && t == .colorless && bestT != .colorless)

/-- Next source to tap for `prop`. Noncreatures are chosen before creatures
when both help, and colorless is preferred when that type can be spent.
A flexible source such as Hidden Lair is tapped for `{U}` or `{B}` when
that choice still lets the remaining sources pay. -/
def preferredManaTap (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Option (GameObject × ManaType) :=
  let allowElf := g.proposedAllowsElfRestricted prop
  let allowInst := g.proposedAllowsInstRestricted prop
  let sources := g.manaSourcesForProposed p prop
  sources.foldl (fun acc (src, types) =>
    let others := sources.filter (fun (o, _) => o.id != src.id) |>.toList
    match g.preferredManaType p src types prop.cost allowElf allowInst others with
    | none => acc
    | some t =>
      match acc with
      | none => some (src, t)
      | some (bestSrc, bestT) =>
        if betterManaTap src t bestSrc bestT then some (src, t) else acc) none

def payCost (g : Game) (p : PlayerId) (cost : ManaCost)
    (allowElfRestricted : Bool := false) (allowInstRestricted : Bool := false)
    (allowHeroRestricted : Bool := false) (allowVillainRestricted : Bool := false)
    (allowCantNonartifact : Bool := false)
    (allowCreatureRestricted : Bool := false) :
    Except String Game := do
  let pl := g.player p
  match pl.manaPool.pay? cost allowElfRestricted allowInstRestricted
      allowHeroRestricted allowVillainRestricted allowCantNonartifact
      allowCreatureRestricted with
  | none => throw s!"{pl.name} cannot pay {cost}"
  | some pool =>
    return g.setPlayer { pl with manaPool := pool }

/-- Undo a proposed spell or ability that could not be paid (CR 601.2 / 602.2 / 733.1). -/
def reverseProposedSpell (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    Id.run do
      let mut g := g
      let name := (g.player prop.caster).name
      let objects := g.objects.filter (fun o => o.id != prop.spellId)
      let objects :=
        match prop.kind with
        | .spell => objects.push prop.original
        | .activatedAbility => objects
      g := { g with
        objects := objects
        stack := prop.stackBefore
        pending := .none
        proposedSpell := none
        castingFromTop := false }
      g := g.modifyPlayer prop.caster (fun pl =>
        { pl with hand := prop.handBefore, manaPool := prop.manaBefore })
      for id in prop.tapped do
        if let some o := g.findObject? id then
          g := g.setObject { o with status := { o.status with tapped := false } }
      let reversed :=
        match prop.kind with
        | .spell => "the casting is reversed (CR 601.2 / 733.1)"
        | .activatedAbility => "the activation is reversed (CR 602.2 / 733.1)"
      g := g.logMsg s!"{name} cannot pay {prop.cost}; {reversed}"
      -- The player who had priority retains it (CR 733.2).
      return { g with priority := prop.caster, consecutivePasses := 0 }

/-- Fold `f` over each targeted permanent that still exists. Non-permanent
targets are skipped. `unique` visits a permanent only once even when it is
targeted more than once. -/
def foldPermanentTargets (g : Game) (targets : Array Target)
    (f : Game → GameObject → Game) (unique := false) : Game :=
  Id.run do
    let mut g := g
    let mut seen : Array ObjectId := #[]
    for t in targets do
      match t with
      | Target.permanent oid =>
        if !(unique && seen.contains oid) then
          seen := seen.push oid
          match g.findObject? oid with
          | some o => g := f g o
          | none => pure ()
      | _ => pure ()
    return g

/-- Queue “becomes the target” triggers once per unique targeted permanent
(CR 603.2 / 601.2c). A spell or ability that targets the same permanent
more than once still triggers only once. -/
def queueBecomesTargetTriggers (g : Game) (caster : PlayerId)
    (targets : Array Target) : Game :=
  g.foldPermanentTargets targets (unique := true) (f := fun g o =>
    match o.controller with
    | some c => if c != caster then g.putMatchingSourceTriggers c o .becomesTarget else g
    | none => g)

/-- Printed and granted ward costs currently on `o`. -/
def wardCostsOn (g : Game) (o : GameObject) : Array WardCost :=
  Id.run do
    let mut acc : Array WardCost := #[]
    match o.printed.ward with
    | some n => acc := acc.push (.genericMana n)
    | none => pure ()
    for ab in o.staticAbilities do
      match ab with
      | .wardDiscardEnchantmentInstantOrSorcery =>
        acc := acc.push .discardEnchantmentInstantOrSorcery
      | .wardSacrificeLegendary =>
        acc := acc.push .sacrificeLegendary
      | .wardDiscardOrPay n =>
        acc := acc.push (.discardOrPay n)
      | .wardPoisonCounters _ =>
        acc := acc.push .fivePoison
      | _ =>
        match ab.grantedWard? with
        | some n =>
          if ab.lordLegendaryOnly && o.isLegendary && o.isCreature then
            acc := acc.push (.genericMana n)
        | none =>
          match ab.teamWardIfEnduringStory? with
          | some n =>
            match o.controller with
            | some p =>
              if g.hasEnduringStory p && (o.printed.isArtifact || o.isCreature) then
                acc := acc.push (.genericMana n)
            | none => pure ()
          | none => pure ()
    for src in g.battlefield do
      if src.id != o.id then
        for ab in src.staticAbilities do
          match ab.grantedWard? with
          | some n =>
            if src.attachedTo == some o.id then
              acc := acc.push (.genericMana n)
            else if ab.lordLegendaryOnly && src.controller == o.controller &&
                o.isLegendary && o.isCreature then
              acc := acc.push (.genericMana n)
          | none =>
            match ab.teamWardIfEnduringStory? with
            | some n =>
              if src.controller == o.controller then
                match o.controller with
                | some p =>
                  if g.hasEnduringStory p &&
                      (o.printed.isArtifact || o.isCreature) then
                    acc := acc.push (.genericMana n)
                | none => pure ()
            | none => pure ()
    return acc

/-- Prompt the next queued ward, if any and no other choice is pending. -/
def promptNextWard (g : Game) : Game :=
  match g.pending with
  | .none =>
    match g.wardQueue[0]? with
    | none => g
    | some w =>
      let rest := g.wardQueue.extract 1 g.wardQueue.size
      let who := (g.player w.player).name
      let msg :=
        match w.cost with
        | .genericMana n =>
          s!"{who} may pay \{{n}} or the spell is countered (ward)"
        | .discardEnchantmentInstantOrSorcery =>
          s!"{who} may discard an enchantment, instant, or sorcery card or the spell is countered (ward)"
        | .sacrificeLegendary =>
          s!"{who} may sacrifice a legendary artifact or creature or the spell is countered (ward)"
        | .discardOrPay n =>
          s!"{who} may discard a card or pay \{{n}} or the spell is countered (ward)"
        | .fivePoison =>
          s!"{who} may get five poison counters or the spell is countered (ward)"
      { g with pending := .payWard w.player w.spellId w.cost, wardQueue := rest
        }.logMsg msg
  | _ => g

/-- Drop ward obligations whose spell has left the stack, then prompt. -/
def afterWardResolved (g : Game) : Game :=
  let g := { g with pending := .none }
  let g := { g with
    wardQueue := g.wardQueue.filter (fun w =>
      match g.findObject? w.spellId with
      | some o => o.zone == Zone.stack
      | none => false) }
  let g := g.promptNextWard
  if g.pending != .none then g
  else g.receivePriority g.activePlayer

/-- Queue ward payments for opponent permanents targeted by this spell
or ability (CR 702.21). -/
def beginWardsForTargets (g : Game) (caster : PlayerId) (spellId : ObjectId)
    (targets : Array Target) : Game :=
  let g := g.foldPermanentTargets targets (unique := true) (f := fun g o =>
    if o.controller != some caster && o.isOnBattlefield then
      (g.wardCostsOn o).foldl (fun g cost =>
        { g with wardQueue := g.wardQueue.push { player := caster, spellId, cost } }) g
    else g)
  g.promptNextWard

def becomeCast (g : Game) (p : PlayerId) (spell : GameObject) : Game :=
  let g := { g with castingFromTop := false }
  let g := g.logMsg s!"{(g.player p).name} casts {spell.name}"
  let g :=
    match g.stackEntry? spell.id with
    | some e =>
      let g := g.queueBecomesTargetTriggers p e.targets
      g.foldPermanentTargets e.targets (fun g o =>
        match o.controller with
        | some c => g.putMatchingSourceTriggers c o .spellTargetsSource
        | none => g)
    | none => g
  let g := g.putCastTriggersOnStack p spell
  let g :=
    match g.stackEntry? spell.id with
    | some e => g.beginWardsForTargets p spell.id e.targets
    | none => g
  g.receivePriority p

/-- After targets are announced, reduce the locked-in cost if the spell cares
about a damaged, tapped, or attacking nontoken target (CR 601.2f). -/
def lockInTargetCostReduction (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.findObject? prop.spellId with
    | none => g
    | some spell =>
      let face :=
        match spell.adventurerCard with
        | some _ => spell.printed
        | none => spell.printed
      match (g.stackEntry? spell.id).bind (fun e => e.targets[0]?) with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let nDamaged :=
            if face.costReductionIfTargetDamaged > 0 && o.status.damage > 0 then
              face.costReductionIfTargetDamaged
            else 0
          let nTapped :=
            if face.costReductionIfTargetTapped > 0 && o.status.tapped then
              face.costReductionIfTargetTapped
            else 0
          let nAttacking :=
            if face.costReductionIfTargetAttackingNontoken > 0 && o.status.attacking then
              face.costReductionIfTargetAttackingNontoken
            else if face.costReductionIfTargetAttacking > 0 && o.status.attacking then
              face.costReductionIfTargetAttacking
            else 0
          let n := nDamaged + nTapped + nAttacking
          if n == 0 then g
          else
            { g with proposedSpell := some { prop with
              cost := ManaCost.afterReduction prop.cost (prop.cost.reduceGeneric n) } }
        | none => g
      | _ => g

/-- Continue after CR 601.2c: determine the total cost (601.2f), then mana
abilities (601.2g). Additional-cost *choices* are announced earlier, at 601.2b. -/
def afterTargetsChosen (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some _ =>
    let g := g.lockInTargetCostReduction
    match g.proposedSpell with
    | none => g
    | some prop =>
      if prop.cost.includesManaPayment || prop.needsSacrificeOther ||
          prop.needsDiscardCard then
        { g with pending := .activateManaAbilities prop.caster }
          |>.logMsg s!"{(g.player prop.caster).name} may activate mana abilities (CR 601.2g)"
      else
        let spell := g.object! prop.spellId
        let g := { g with pending := .none, proposedSpell := none, consecutivePasses := 0 }
        g.becomeCast prop.caster spell

/-- Whether the proposed spell or ability still needs targets announced (CR 601.2c). -/
def proposedNeedsTarget (g : Game) (prop : ProposedSpell) : Bool :=
  match g.findObject? prop.spellId with
  | none => false
  | some o =>
    match prop.kind with
    | .spell =>
      match g.currentSpellEffect o with
      | some e => e.requiresTarget
      | none => o.printed.requiresTarget || o.printed.isAura
    | .activatedAbility =>
      match o.abilityEffect with
      | some e => e.requiresTarget
      | none => false

/-- After CR 601.2b additional-cost announcement, continue to targets (601.2c)
or cost determination (601.2f). -/
def afterAdditionalCostAnnounced (g : Game) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    if g.proposedNeedsTarget prop then
      { g with pending := .chooseTargets prop.caster }
        |>.logMsg s!"{(g.player prop.caster).name} must choose a target (CR 601.2c)"
    else
      g.afterTargetsChosen

/-- Choose new targets for a spell on the stack (Speedball; MSH 370).
Each slot that has no new legal target is left unchanged, even if the
current target is illegal. -/
def retargetStackSpell (g : Game) (spellId : ObjectId) (newTargets : Array Target) :
    Game :=
  match g.stack.findIdx? (fun e => e.objectId == spellId) with
  | none => g.logMsg "The spell is no longer on the stack"
  | some i =>
    let e := g.stack[i]!
    match g.findObject? spellId with
    | none => g.logMsg "The spell is no longer on the stack"
    | some spell =>
      let kind := (g.targetingOf spell).kind
      let legal := g.legalTargetsForKind e.controller kind (some spellId)
      let merged :=
        Id.run do
          let mut out := e.targets
          for j in [0:Nat.min out.size newTargets.size] do
            let neu := newTargets[j]!
            if legal.any (fun t => t == neu) then
              out := out.set! j neu
          return out
      { g with stack := g.stack.set! i { e with targets := merged } }
        |>.logMsg "New targets are chosen for the spell"

/-- Write `targets` (and optional damage division) onto the stack entry. -/
def setStackEntryTargets (g : Game) (objectId : ObjectId) (targets : Array Target)
    (dividedDamage : Array Nat := #[]) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == objectId) with
  | none => g
  | some i =>
    { g with stack := g.stack.set! i { g.stack[i]! with
        targets := targets, dividedDamage := dividedDamage, targetsAnnounced := true } }

/-- Write `targets` onto the stack entry for the proposed spell. -/
def setProposedTargets (g : Game) (targets : Array Target) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop => g.setStackEntryTargets prop.spellId targets

/-- Record the chosen mode on the proposed spell's stack entry (CR 700.2). -/
def setProposedMode (g : Game) (mode : Nat) : Game :=
  match g.proposedSpell with
  | none => g
  | some prop =>
    match g.stack.findIdx? (fun e => e.objectId == prop.spellId) with
    | none => g
    | some i =>
      { g with stack := g.stack.set! i { g.stack[i]! with chosenMode := some mode } }

def becomeActivated (g : Game) (p : PlayerId) (sourceName : String)
    (sourceId : Option ObjectId := none) : Game :=
  let g :=
    match sourceId with
    | none => g
    | some sid =>
      match g.findObject? sid with
      | some src =>
        let powerUp :=
          match g.proposedSpell.bind (·.activation) with
          | some ab => ab.powerUp
          | none =>
            src.printed.activatedAbilities.any (·.powerUp)
        let g := g.setObject { src with status := { src.status with
          activationsThisTurn := src.status.activationsThisTurn + 1
          powerUpUsed := src.status.powerUpUsed || powerUp
          powerUpActivations :=
            src.status.powerUpActivations + (if powerUp then 1 else 0) } }
        let src := g.object! sid
        if src.isCreature then
          g.putControlledTriggers p .youActivateCreatureAbility
        else g
      | none => g
  let g :=
    match g.stack.back? with
    | some e =>
      let g := g.queueBecomesTargetTriggers p e.targets
      g.beginWardsForTargets p e.objectId e.targets
    | none => g
  g.logMsg s!"{(g.player p).name} activates {sourceName}" |>.receivePriority p

end Game
end Mtg.Engine
