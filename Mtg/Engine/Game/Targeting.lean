import Mtg.Engine.Game.Timing

/-!
# Legal targets (CR 115)

Hexproof- and protection-aware target legality: legal permanent,
graveyard-card, and stack-spell targets, targets per `EffectTargetKind`,
and which triggered abilities still need targets.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `caster` may target `o` (CR 115.1, 702.11b). -/
def canBeTargetedBy (g : Game) (caster : PlayerId) (o : GameObject) : Bool :=
  let srcBlocked :=
    match (g.resolvingSpell.orElse (fun _ => g.proposedSpell.map (·.spellId))).bind g.findObject? with
    | some src => g.frcProtectedFrom o src
    | none => false
  (!g.hasHexproof o || o.controlledBy caster) && !srcBlocked

/-- Player targets `caster` may choose. A player with hexproof is not a
legal target for an opponent (CR 702.11c). -/
def legalPlayerTargets (g : Game) (caster : PlayerId) (ps : Array Player) : Array Target :=
  playerTargets (ps.filter (fun pl => g.playerCanBeTargetedBy caster pl.id))

/-- Battlefield permanents matching `pred` that `caster` may target. -/
def legalPermanentTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  g.battlefield.filter (fun o => pred o && g.canBeTargetedBy caster o)
    |>.map (fun o => Target.permanent o.id)

/-- Battlefield creatures matching `pred` that `caster` may target. -/
def legalCreatureTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  g.legalPermanentTargets caster (fun o => o.isCreature && pred o)

/-- Creatures `caster` controls that they may target (CR 115.1). -/
def legalCreatureYouControlTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalCreatureTargets caster (fun o => o.controlledBy caster)

/-- Creatures an opponent of `caster` controls that `caster` may target. -/
def legalOppCreatureTargets (g : Game) (caster : PlayerId) : Array Target :=
  g.legalCreatureTargets caster (fun o => o.controlledBy (g.opponent caster))

/-- Cards in `p`'s graveyard matching `pred` (CR 404 / 115.1). Hexproof does
not apply off the battlefield (CR 702.11b). -/
def legalGraveyardCardTargets (g : Game) (p : PlayerId) (pred : GameObject → Bool) :
    Array Target :=
  (g.player p).graveyard.filterMap (fun id =>
    match g.findObject? id with
    | some o => if pred o then some (Target.card o.id) else none
    | none => none)

/-- Spells on the stack matching `pred` (not activated or triggered abilities). -/
def stackSpells (g : Game) (pred : GameObject → Bool := fun _ => true) : Array GameObject :=
  g.stack.filterMap (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.abilityEffect.isNone && o.triggeredAbility.isNone && pred o then some o
      else none
    | none => none)

/-- Legal spell-on-the-stack targets matching `pred` (CR 115.1). -/
def legalStackSpellTargets (g : Game) (pred : GameObject → Bool) : Array Target :=
  g.stackSpells pred |>.map (fun o => Target.card o.id)

/-- Stack abilities `caster` controls whose source matches `sourcePred`.
Used for Echo and Scientist Supreme (MSH 74 / 87). -/
def legalStackAbilityTargets (g : Game) (caster : PlayerId)
    (sourcePred : GameObject → Bool) : Array Target :=
  g.stack.filterMap (fun e =>
    match g.findObject? e.objectId with
    | none => none
    | some o =>
      if o.zone == .stack && o.controlledBy caster &&
          (o.abilityEffect.isSome || o.triggeredAbility.isSome) then
        match o.sourceId.bind g.findObject? with
        | some src =>
          if sourcePred src then some (Target.card o.id) else none
        | none => none
      else none)

/-- Whether this target is a spell on the stack that `p` controls. -/
def isOwnStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o => o.zone == .stack && o.controlledBy p)
  | _ => false

/-- Whether this target is a spell on the stack an opponent of `p` controls. -/
def isOppStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o =>
      o.zone == .stack && (g.livingOpponents p).any (fun pl => o.controlledBy pl.id))
  | _ => false

/-- Opponent-controlled spells currently on the stack. -/
def oppStackSpells (g : Game) (p : PlayerId) : Array GameObject :=
  g.stackSpells (fun o => (g.livingOpponents p).any (fun pl => o.controlledBy pl.id))

/-- Whether `o` has card type `t`, counting type-changing effects on
permanents. -/
def objectHasCardType (o : GameObject) (t : CardType) : Bool :=
  if t == .creature then o.isCreature else o.types.contains t || o.printed.types.contains t

/-- Whether object `o` has every characteristic `f` asks for (CR 115.1).
Zone and hexproof are checked by the caller. -/
def matchesTargetFilter (g : Game) (caster : PlayerId) (f : TargetFilter)
    (sourceId : Option ObjectId) (o : GameObject) : Bool :=
  let typeOk :=
    f.types.isEmpty || f.types.any (objectHasCardType o) || (f.orLegendary && o.isLegendary)
  let colorOk := f.colors.isEmpty || f.colors.any (o.printed.colors.contains ·)
  let who := o.controller.getD o.owner
  let controllerOk :=
    match f.controller with
    | .any => true
    | .you => who == caster
    | .opponent | .eachOpponent => who != caster
    | .specific idx => who.idx == idx
  let mv := g.objectManaValue o
  let subtypeOk := f.subtypes.isEmpty || f.subtypes.any (g.hasSubtype o)
  typeOk && colorOk && controllerOk && subtypeOk &&
    (!f.nonland || !objectHasCardType o .land) &&
    (!f.noncreature || !objectHasCardType o .creature) &&
    (!f.nonAura || !o.printed.isAura) &&
    (!f.nontoken || !o.printed.isToken) &&
    (!f.permanentCard || o.printed.isPermanentCard) &&
    (!f.legendary || o.isLegendary) &&
    (!f.nonlegendary || !o.isLegendary) &&
    (f.mvAtLeast.all (mv ≥ ·)) && (f.mvAtMost.all (mv ≤ ·)) &&
    (f.toughnessAtLeast.all (g.toughness o ≥ ·)) &&
    (!f.another || some o.id != sourceId) &&
    (!f.withFlying || g.hasFlying o) &&
    (!f.withPlusOneCounter || o.status.plusOnePlusOne > 0) &&
    (!f.attacking || o.status.attacking) &&
    (!f.attackingOrBlocking || o.status.attacking || !o.status.blocking.isEmpty) &&
    (!f.attackedThisTurn || o.status.declaredAsAttackerThisTurn) &&
    (!f.enteredThisTurn || o.status.enteredThisTurn) &&
    (!f.untapped || !o.status.tapped) &&
    (!f.nonattacking || !o.status.attacking) &&
    (!f.withHaste || g.hasHaste o) &&
    (!f.ownedByYou || o.owner == caster)

/-- Legal targets described by a `TargetFilter` (CR 115.1). -/
def legalFilteredTargets (g : Game) (caster : PlayerId) (f : TargetFilter)
    (sourceId : Option ObjectId) : Array Target :=
  let ok := g.matchesTargetFilter caster f sourceId
  match f.zone with
  | .battlefield => g.legalPermanentTargets caster (fun o => o.isOnBattlefield && ok o)
  | .yourGraveyard => g.legalGraveyardCardTargets caster ok
  | .anyGraveyard =>
    g.livingPlayers.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id ok) #[]
  | .stack => g.legalStackSpellTargets ok
  | .spellOrCreature =>
    g.legalStackSpellTargets ok ++
      g.legalPermanentTargets caster (fun o => o.isOnBattlefield && o.isCreature && ok o)
  | .anyTarget =>
    playerTargets g.livingPlayers ++
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield && (o.isCreature || o.printed.isPlaneswalker || o.printed.isBattle) && ok o)
  | .player =>
    playerTargets (g.livingPlayers.filter (fun pl =>
      match f.controller with
      | .any => true
      | .you => pl.id == caster
      | .opponent | .eachOpponent => pl.id != caster
      | .specific idx => pl.id.idx == idx))

/-- Whether the spell being cast or resolved paid its teamwork cost.
`resolvingSpell` is set after the spell leaves the stack (CR 608). During
target announcement the proposal or the top stack object still has the flag. -/
def spellPaidTeamwork (g : Game) : Bool :=
  match g.resolvingSpell.bind g.findObject? with
  | some o => o.teamworkPaid
  | none =>
    if g.proposedSpell.any (·.teamworkPaid) then true
    else
      match g.stack.back? with
      | some e => (g.findObject? e.objectId).any (·.teamworkPaid)
      | none => false

/-- Legal targets for a battlefield permanent targeting shape (CR 115.1 / 110.1). -/
def legalBattlefieldTargets (g : Game) (caster : PlayerId) (t : BattlefieldTarget)
    (sourceId : Option ObjectId) : Array Target :=
  match t with
  | .creatureYouControl another legendary =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && (!another || some o.id != sourceId) && (!legendary || o.isLegendary))
  | .creature another withFlying =>
    if withFlying then
      g.legalCreatureTargets caster (fun o => g.hasFlying o)
    else
      g.legalCreatureTargets caster (fun o => !another || some o.id != sourceId)
  | .oppCreature tapped dealtDamageThisTurn =>
    g.legalCreatureTargets caster (fun o =>
      (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id) &&
        (!tapped || o.status.tapped) &&
        (!dealtDamageThisTurn || o.status.dealtDamageThisTurn))
  | .twoTypes includeCreature includeArtifact youControl =>
    if !includeCreature then
      g.legalPermanentTargets caster (·.isArtifactOrLand)
    else
      g.legalPermanentTargets caster (fun o =>
        (!youControl || o.controlledBy caster) &&
          (o.isCreature || (if includeArtifact then o.printed.isArtifact else o.printed.isLand)))
  | .artifactOrEnchantment noncreature =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (!noncreature || !o.isCreature) &&
        (o.printed.isArtifact || o.printed.isEnchantment))
  | .nonland opp nontoken colorless =>
    if colorless then
      g.legalPermanentTargets caster (·.isColorlessNonland)
    else
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield && !o.printed.isLand &&
          (!opp || (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id)) &&
          (!nontoken || !o.printed.isToken))
  | .attackingCreature withoutFlying orBlocking aloneYouControl =>
    if aloneYouControl then
      let attackers :=
        g.legalCreatureTargets caster (fun o =>
          o.controlledBy caster && o.status.attacking)
      if attackers.size == 1 then attackers else #[]
    else
      g.legalCreatureTargets caster (fun o =>
        (o.status.attacking || (orBlocking && !o.status.blocking.isEmpty)) &&
          (!withoutFlying || !g.hasFlying o))
  | .creatureYouControlSubtype subtype =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster && g.hasSubtype o subtype)
  | .defendingPlayerCreature =>
    let defender :=
      match sourceId.bind g.findObject? with
      | some src =>
        let fromHost :=
          match src.attachedTo.bind g.findObject? with
          | some host => host.status.attackingWhom
          | none => none
        let fromSelf := if src.status.attacking then src.status.attackingWhom else none
        (fromHost.orElse (fun _ => fromSelf)).getD g.defendingPlayer
      | none => g.defendingPlayer
    g.legalCreatureTargets caster (fun o => o.controlledBy defender)
  | .creatureStatAtLeast n toughness =>
    g.legalCreatureTargets caster (fun o => (if toughness then g.toughness o else g.power o) >= n)
  | .creaturePowerAtMost n controller another =>
    match controller with
    | .you =>
      g.legalCreatureTargets caster (fun o =>
        o.controlledBy caster && (!another || some o.id != sourceId) &&
          (if another then g.snapshotPower o else g.power o) <= n)
    | .opponent =>
      g.legalCreatureTargets caster (fun o =>
        g.power o <= n &&
          (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
    | _ =>
      g.legalCreatureTargets caster (fun o => g.power o <= n)
  | .creatureYouControlAnySubtype subtypes =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && subtypes.any (g.hasSubtype o))
  | .permanent controller =>
    match controller with
    | .you => g.legalPermanentTargets caster (fun o => o.isOnBattlefield && o.controlledBy caster)
    | .opponent =>
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield && o.controller.isSome && !o.controlledBy caster)
    | _ => g.legalPermanentTargets caster (·.isOnBattlefield)
  | .artifact controller tokenOnly noncreature =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact &&
        (!tokenOnly || o.printed.isToken) &&
        (!noncreature || !o.isCreature) &&
        (match controller with
         | .you => o.controlledBy caster
         | .opponent => (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id)
         | _ => true))
  | .equipmentYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && o.printed.isEquipment)
  | .creatureMvAtMost n =>
    let anyCreature := g.spellPaidTeamwork
    g.legalCreatureTargets caster (fun o => anyCreature || o.printed.manaValue ≤ n)
  | .enchantmentMvAtLeast n =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isEnchantment && o.printed.manaValue ≥ n)
  | .creatureOrPlaneswalker controller planeswalkerOnly =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && ((!planeswalkerOnly && o.isCreature) || o.printed.isPlaneswalker) &&
        (match controller with
         | .you => o.controlledBy caster
         | .opponent => o.controller.isSome && !o.controlledBy caster
         | _ => true))

/-- Legal targets for a graveyard card targeting shape (CR 115.1 / 404.1). -/
def legalGraveyardTargets (g : Game) (caster : PlayerId) (t : GraveyardTarget) : Array Target :=
  match t with
  | .elfInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o => g.hasSubtype o "Elf")
  | .oppGraveyardCard =>
    g.livingOpponents caster
      |>.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id (fun _ => true)) #[]
  | .cardInYourGraveyard permanentAny =>
    g.legalGraveyardCardTargets caster (fun o =>
      if permanentAny then o.printed.isPermanentCard else o.printed.isCreature)
  | .creatureCardInYourGraveyardMvAtMost n =>
    let anyCreature := g.spellPaidTeamwork
    g.legalGraveyardCardTargets caster (fun o =>
      o.printed.isCreature && (anyCreature || o.printed.manaValue ≤ n))
  | .multiTypeInYourGraveyard equipInstSorc =>
    g.legalGraveyardCardTargets caster (fun o =>
      if equipInstSorc then
        o.printed.isEquipment || o.printed.isInstant || o.printed.isSorcery
      else
        o.printed.isArtifact || o.printed.isEnchantment)

/-- Legal targets for a stack spell or ability targeting shape (CR 115.1 / 405.1). -/
def legalStackTargets (g : Game) (caster : PlayerId) (t : StackTarget) : Array Target :=
  match t with
  | .spell creatureOnly =>
    g.legalStackSpellTargets (fun o => !creatureOnly || o.printed.isCreature)
  | .creatureSpellPTAtMost n =>
    g.legalStackSpellTargets (fun o =>
      o.printed.isCreature &&
        ((o.printed.power.getD 0) <= (n : Int) ||
          (o.printed.toughness.getD 0) <= (n : Int)))
  | .stackAbilityFromSource fromCreature =>
    g.legalStackAbilityTargets caster (fun src =>
      if fromCreature then src.printed.isCreature else src.printed.isArtifact)

/-- Legal targets for a player or cross-category targeting shape (CR 115.1 / 115.4). -/
def legalPlayerTargetKind (g : Game) (caster : PlayerId) (t : PlayerTarget) : Array Target :=
  match t with
  | .player opponentOnly =>
    g.legalPlayerTargets caster (if opponentOnly then g.livingOpponents caster else g.livingPlayers)
  | .playerOrPermanent anyPermanent =>
    -- CR 115.4: “any target” is a creature, player, planeswalker, or battle.
    g.legalPlayerTargets caster g.livingPlayers ++
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield &&
          (anyPermanent || o.isCreature || o.printed.isPlaneswalker || o.printed.isBattle))
  | .creatureOrGyCreatureCard =>
    g.legalCreatureTargets caster (fun _ => true) ++
      g.livingPlayers.foldl (fun acc pl =>
        acc ++ g.legalGraveyardCardTargets pl.id (fun o => o.printed.isCreature)) #[]
  | _ => #[]

/-- Legal targets for a multi-target shape when evaluated as a single slot (CR 115.1 / 601.2c). -/
def legalMultiTargetKind (g : Game) (caster : PlayerId) : MultiTarget → Array Target
  | .upToTwoCreaturesTotalMvAtMost n =>
    g.legalCreatureTargets caster (fun o => o.printed.manaValue ≤ n)
  | _ => #[]

/-- Legal targets for an atomic targeting shape (no sequential slots). -/
def legalTargetsForAtomicKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId) : Array Target :=
  match kind with
  | .none => #[]
  | .battlefield t => g.legalBattlefieldTargets caster t sourceId
  | .graveyard t => g.legalGraveyardTargets caster t
  | .stack t => g.legalStackTargets caster t
  | .playerTarget t => g.legalPlayerTargetKind caster t
  | .sequence t => g.legalMultiTargetKind caster t
  | .filtered f => g.legalFilteredTargets caster f sourceId
  | .multi .. | .pair .. => #[]

/-- Legal targets for a targeting shape (CR 115.1 / 601.2c / 603.3d).
`sourceId` excludes the source of an “another” creature. Shapes with
multiple instances of the word “target” read `spec.slots` instead of
restating each slot. -/
def legalTargetsForKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId := none) : Array Target :=
  if kind.spec.slots.isEmpty then
    g.legalTargetsForAtomicKind caster kind sourceId
  else
    Id.run do
      let mut acc : Array Target := #[]
      let mut requiredMissing := false
      for i in [0:kind.spec.slots.size] do
        let part := g.legalTargetsForAtomicKind caster kind.spec.slots[i]! sourceId
        if part.isEmpty && !kind.isOptionalSlot i then
          requiredMissing := true
        acc := acc ++ part
      if requiredMissing then #[] else acc

/-- Legal targets for a triggered ability (CR 603.3d / 601.2c). `sourceId` is
the object that generated the ability, used to exclude “another” creature. -/
def legalTriggerTargets (g : Game) (p : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalTargetsForKind p ab.targetKind sourceId

/-- Damage already assigned on a “divided as you choose” stack entry (CR 601.2d). -/
def assignedDividedDamage (e : StackEntry) : Nat :=
  e.dividedDamage.foldl (· + ·) 0

/-- Whether this stacked triggered ability still needs targets or a damage
division announced (CR 603.3d / 601.2d). -/
def triggerStillNeedsTargets (e : StackEntry) (ab : TriggeredAbility) : Bool :=
  match ab.dividedDamage? with
  | some (amount, _) => assignedDividedDamage e < amount
  | none =>
    if ab.allowsZeroTargets || ab.targeting.kind.spec.slots.size > 1 then !e.targetsAnnounced
    else ab.requiresTarget && e.targets.isEmpty

/-- Stack entry for a triggered ability that still needs targets announced
(CR 603.3d). Oldest first so targets are chosen in the order abilities were
put on the stack. -/
def triggerNeedingTargets (g : Game) : Option StackEntry :=
  g.stack.find? (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      match o.triggeredAbility, o.abilityEffect with
      | some _, some eff =>
        -- A modal trigger whose modes were chosen (CR 603.3c).
        if eff.allowsZeroTargets || eff.targetKind.spec.slots.size > 1 then !e.targetsAnnounced
        else eff.requiresTarget && e.targets.isEmpty
      | some ab, none =>
        match ab.effect.resolution with
        | .chooseModes _ (.fraTrigger _) => false
        | _ => triggerStillNeedsTargets e ab
      | none, _ => false
    | none => false)

end Game
end Mtg.Engine
