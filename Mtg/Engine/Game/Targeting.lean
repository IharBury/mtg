import Mtg.Engine.Game.Timing

/-!
# Legal targets (CR 115)

Hexproof- and protection-aware target legality: legal permanent,
graveyard-card, and stack-spell targets, targets per `EffectTargetKind`,
and which triggered abilities still need targets.
-/

namespace Mtg.Engine
namespace Game

/-- Whether `caster` may target `o` (CR 115.1, 702.11b, 702.16b). -/
def canBeTargetedBy (g : Game) (caster : PlayerId) (o : GameObject)
    (sourceId : Option ObjectId := none) : Bool :=
  let srcBlocked :=
    match g.targetingSourceObject? sourceId with
    | some src => g.frcProtectedFrom o src
    | none => false
  (!g.hasHexproof o || g.controlledBy o caster) && !srcBlocked

/-- Player targets `caster` may choose. A player with hexproof or protection is
not a legal target when prohibited (CR 702.11c / 702.16b). -/
def legalPlayerTargets (g : Game) (caster : PlayerId) (ps : Array Player)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.playerTargets (ps.filter (fun pl => g.playerCanBeTargetedBy caster pl.id sourceId))

/-- Battlefield permanents matching `pred` that `caster` may target. -/
def legalPermanentTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.battlefield.filter (fun o => pred o && g.canBeTargetedBy caster o sourceId)
    |>.map (fun o => Target.permanent o.id)

/-- Battlefield creatures matching `pred` that `caster` may target. -/
def legalCreatureTargets (g : Game) (caster : PlayerId) (pred : GameObject → Bool)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalPermanentTargets caster (fun o => g.isCreature o && pred o) sourceId

/-- Creatures `caster` controls that they may target (CR 115.1). -/
def legalCreatureYouControlTargets (g : Game) (caster : PlayerId)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalCreatureTargets caster (fun o => g.controlledBy o caster) sourceId

/-- Creatures an opponent of `caster` controls that `caster` may target. -/
def legalOppCreatureTargets (g : Game) (caster : PlayerId)
    (sourceId : Option ObjectId := none) : Array Target :=
  g.legalCreatureTargets caster (fun o => g.controlledBy o (g.opponent caster)) sourceId

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

/-- Legal spell-on-the-stack targets matching `pred` (CR 115.1 / 115.5). -/
def legalStackSpellTargets (g : Game) (pred : GameObject → Bool)
    (excludeId : Option ObjectId := none) : Array Target :=
  let selfId := excludeId.orElse (fun _ => g.proposedSpell.map (·.spellId))
  g.stackSpells (fun o => some o.id != selfId && pred o) |>.map (fun o => Target.card o.id)

/-- Stack abilities `caster` controls whose source matches `sourcePred` (CR 115.5).
Used for Echo and Scientist Supreme (MSH 74 / 87). -/
def legalStackAbilityTargets (g : Game) (caster : PlayerId)
    (sourcePred : GameObject → Bool)
    (excludeId : Option ObjectId := none) : Array Target :=
  let selfId := excludeId.orElse (fun _ => g.proposedSpell.map (·.spellId))
  g.stack.filterMap (fun e =>
    match g.findObject? e.objectId with
    | none => none
    | some o =>
      if o.zone == .stack && some o.id != selfId && g.controlledBy o caster &&
          (o.abilityEffect.isSome || o.triggeredAbility.isSome) then
        match o.sourceId.bind g.findObject? with
        | some src =>
          if sourcePred src then some (Target.card o.id) else none
        | none => none
      else none)

/-- Whether this target is a spell on the stack that `p` controls. -/
def isOwnStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o => o.zone == .stack && g.controlledBy o p)
  | _ => false

/-- Whether this target is a spell on the stack an opponent of `p` controls. -/
def isOppStackSpellTarget (g : Game) (p : PlayerId) : Target → Bool
  | .card oid =>
    (g.findObject? oid).any (fun o =>
      o.zone == .stack && (g.livingOpponents p).any (fun pl => g.controlledBy o pl.id))
  | _ => false

/-- Opponent-controlled spells currently on the stack. -/
def oppStackSpells (g : Game) (p : PlayerId) : Array GameObject :=
  g.stackSpells (fun o => (g.livingOpponents p).any (fun pl => g.controlledBy o pl.id))

/-- Whether `o` has card type `t`, counting type-changing effects on
permanents. -/
def objectHasCardType (g : Game) (o : GameObject) (t : CardType) : Bool :=
  g.hasType o t

/-- Whether object `o` has every characteristic `f` asks for (CR 115.1).
Zone and hexproof are checked by the caller. -/
def matchesTargetFilter (g : Game) (caster : PlayerId) (f : TargetFilter)
    (sourceId : Option ObjectId) (o : GameObject) : Bool :=
  let typeOk :=
    (f.types.isEmpty && f.orSupertypes.isEmpty) ||
      f.types.any (g.objectHasCardType o) || f.orSupertypes.any (g.hasSupertype o)
  let supertypeOk := f.supertypes.isEmpty || f.supertypes.any (g.hasSupertype o)
  let colorOk := f.colors.isEmpty || f.colors.any ((g.colors o).contains ·)
  let who := (g.controllerOf o).getD o.owner
  let controllerOk :=
    match f.controller with
    | .any => true
    | .you => who == caster
    | .opponent | .eachOpponent => who != caster
    | .specific idx => who.idx == idx
  let mv := g.objectManaValue o
  let subtypeOk := f.subtypes.isEmpty || f.subtypes.any (fun s => g.hasSubtype o s)
  typeOk && supertypeOk && colorOk && controllerOk && subtypeOk &&
    f.nonSupertypes.all (fun s => !g.hasSupertype o s) &&
    f.nonTypes.all (fun t => !g.objectHasCardType o t) &&
    (!f.nonAura || !g.isAura o) &&
    (!f.nontoken || !o.printed.isToken) &&
    (!f.permanentCard || g.isPermanentCard o) &&
    (f.mvAtLeast.all (mv ≥ ·)) && (f.mvAtMost.all (mv ≤ ·)) &&
    (f.toughnessAtLeast.all (g.toughness o ≥ ·)) &&
    (!f.another || some o.id != sourceId) &&
    (!f.withFlying || g.hasFlying o) &&
    (!f.withPlusOneCounter || o.status.plusOnePlusOne > 0) &&
    (!f.attacking || o.status.attacking) &&
    (!f.attackingOrBlocking || o.status.attacking || !o.status.blocking.isEmpty) &&
    (!f.attackedThisTurn || g.declaredAsAttackerThisTurn o.id) &&
    (!f.enteredThisTurn || g.loggedEntered o.id) &&
    (!f.untapped || !o.status.tapped) &&
    (!f.nonattacking || !o.status.attacking) &&
    (!f.withHaste || g.hasHaste o) &&
    (!f.ownedByYou || o.owner == caster)

/-- Legal targets described by a `TargetFilter` (CR 115.1). -/
def legalFilteredTargets (g : Game) (caster : PlayerId) (f : TargetFilter)
    (sourceId : Option ObjectId) : Array Target :=
  let ok := g.matchesTargetFilter caster f sourceId
  match f.zone with
  | .battlefield => g.legalPermanentTargets caster (fun o => o.isOnBattlefield && ok o) sourceId
  | .yourGraveyard => g.legalGraveyardCardTargets caster ok
  | .anyGraveyard =>
    g.livingPlayers.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id ok) #[]
  | .stack => g.legalStackSpellTargets ok sourceId
  | .spellOrCreature =>
    g.legalStackSpellTargets ok sourceId ++
      g.legalPermanentTargets caster (fun o => o.isOnBattlefield && g.isCreature o && ok o) sourceId
  | .anyTarget =>
    g.legalPlayerTargets caster g.livingPlayers sourceId ++
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o || g.isBattle o) && ok o) sourceId
  | .player =>
    g.legalPlayerTargets caster (g.livingPlayers.filter (fun pl =>
      match f.controller with
      | .any => true
      | .you => pl.id == caster
      | .opponent | .eachOpponent => pl.id != caster
      | .specific idx => pl.id.idx == idx)) sourceId

/-- Whether the spell being cast or resolved paid its teamwork cost (CR 601.2 / 608.2).
Checks an active `proposedSpell` first (including mid-resolution casts), then
`resolvingSpell`, then the top stack entry. -/
def spellPaidTeamwork (g : Game) : Bool :=
  match g.proposedSpell with
  | some prop => prop.teamworkPaid || g.teamworkPaid prop.spellId
  | none =>
    match g.resolvingSpell with
    | some id => g.teamworkPaid id
    | none =>
      match g.stack.back? with
      | some e => g.teamworkPaid e.objectId
      | none => false

/-- Legal targets for an atomic targeting shape (no sequential slots). -/
def legalTargetsForAtomicKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId) : Array Target :=
  match kind with
  | .none => #[]
  | .creatureYouControl =>
    g.legalCreatureYouControlTargets caster sourceId
  | .anotherCreatureYouControl =>
    g.legalCreatureTargets caster (fun o => g.controlledBy o caster && some o.id != sourceId) sourceId
  | .anotherCreature =>
    g.legalCreatureTargets caster (fun o => some o.id != sourceId) sourceId
  | .playerOrCreature =>
    -- CR 115.4: “any target” is a creature, player, planeswalker, or battle.
    g.legalPlayerTargets caster g.livingPlayers sourceId ++
      g.legalPermanentTargets caster (fun o =>
        o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o || g.isBattle o)) sourceId
  | .elfInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o => g.hasSubtype o .elf)
  | .oppCreature =>
    g.legalOppCreatureTargets caster sourceId
  | .oppTappedCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.status.tapped &&
        (g.livingOpponents caster).any (fun pl => g.controlledBy o pl.id)) sourceId
  | .creature =>
    g.legalCreatureTargets caster (fun _ => true) sourceId
  | .creatureOrGyCreatureCard =>
    g.legalCreatureTargets caster (fun _ => true) sourceId ++
      g.livingPlayers.foldl (fun acc pl =>
        acc ++ g.legalGraveyardCardTargets pl.id (g.isCreature ·)) #[]
  | .creatureWithFlying =>
    g.legalCreatureTargets caster (fun o => g.hasFlying o) sourceId
  | .artifactOrLand =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && (g.isArtifact o || g.isLand o)) sourceId
  | .colorlessNonland =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && !g.isLand o && (g.colors o).isColorless) sourceId
  | .creatureYouControlThenOppCreature => #[]
  | .playerThenCreature => #[]
  | .oppCreatureThenUpToOneCreatureYouControl => #[]
  | .player =>
    g.legalPlayerTargets caster g.livingPlayers sourceId
  | .opponent =>
    g.legalPlayerTargets caster (g.livingOpponents caster) sourceId
  | .oppGraveyardCard =>
    g.livingOpponents caster
      |>.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id (fun _ => true)) #[]
  | .artifactOrEnchantment =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (g.isArtifact o || g.isEnchantment o)) sourceId
  | .artifactOrCreatureYouControl =>
    g.legalPermanentTargets caster (fun o =>
      g.controlledBy o caster && (g.isCreature o || g.isArtifact o)) sourceId
  | .nonland =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && !g.isLand o) sourceId
  | .oppNonland =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !g.isLand o &&
        (g.livingOpponents caster).any (fun pl => g.controlledBy o pl.id)) sourceId
  | .attackingCreatureWithoutFlying =>
    g.legalCreatureTargets caster (fun o => o.status.attacking && !g.hasFlying o) sourceId
  | .creatureYouControlSubtype subtype =>
    g.legalCreatureTargets caster (fun o => g.controlledBy o caster && g.hasSubtype o subtype) sourceId
  | .spell =>
    g.legalStackSpellTargets (fun _ => true) sourceId
  | .creatureSpell =>
    g.legalStackSpellTargets (g.isCreature ·) sourceId
  | .creatureSpellPTAtMost n =>
    g.legalStackSpellTargets (fun o =>
      g.isCreature o &&
        (g.snapshotPower o <= (n : Int) ||
          g.snapshotToughness o <= (n : Int))) sourceId
  | .defendingPlayerCreature =>
    let defender :=
      match sourceId.bind g.findObject? with
      | some src =>
        let fromHost :=
          match src.attachedTo.bind g.findObject? with
          | some host => if host.status.attacking then some (g.defendingPlayerOf host) else none
          | none => none
        let fromSelf := if src.status.attacking then some (g.defendingPlayerOf src) else none
        (fromHost.orElse (fun _ => fromSelf)).getD g.defendingPlayer
      | none => g.defendingPlayer
    g.legalCreatureTargets caster (fun o => g.controlledBy o defender) sourceId
  | .twoNonlandsSharingType => #[]
  | .creaturePowerAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.power o >= n) sourceId
  | .creaturePowerAtMost n =>
    g.legalCreatureTargets caster (fun o => g.power o <= n) sourceId
  | .creatureYouControlAnySubtype subtypes =>
    g.legalCreatureTargets caster (fun o =>
      g.controlledBy o caster && subtypes.any (fun s => g.hasSubtype o s)) sourceId
  | .permanent =>
    g.legalPermanentTargets caster (·.isOnBattlefield) sourceId
  | .creatureCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (g.isCreature ·)
  | .legendaryCreatureYouControl =>
    g.legalCreatureTargets caster (fun o =>
      g.controlledBy o caster && g.isLegendary o) sourceId
  | .creatureYouControlPowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      g.controlledBy o caster && g.power o <= n) sourceId
  | .artifact =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && g.isArtifact o) sourceId
  | .oppArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && g.isArtifact o &&
        (g.livingOpponents caster).any (fun pl => g.controlledBy o pl.id)) sourceId
  | .creatureCardInYourGraveyardMvAtMost n =>
    let anyCreature := g.spellPaidTeamwork
    g.legalGraveyardCardTargets caster (fun o =>
      g.isCreature o && (anyCreature || g.objectManaValue o ≤ n))
  | .artifactToken =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && g.isArtifact o && o.printed.isToken) sourceId
  | .attackingCreature =>
    g.legalCreatureTargets caster (fun o => o.status.attacking) sourceId
  | .equipmentYouControl =>
    g.legalPermanentTargets caster (fun o =>
      g.controlledBy o caster && g.isEquipment o) sourceId
  | .creatureOrLandYouControl =>
    g.legalPermanentTargets caster (fun o =>
      g.controlledBy o caster && (g.isCreature o || g.isLand o)) sourceId
  | .twoCreaturesOrLandsYouControl => #[]
  | .equipmentYouControlThenCreatureYouControl => #[]
  | .upToOneEquipmentThenCreatureYouControl => #[]
  | .twoPlayers => #[]
  | .upToOneCreatureThenPlayer => #[]
  | .attackingOrBlockingCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.status.attacking || !o.status.blocking.isEmpty) sourceId
  | .creatureMvAtMost n =>
    let anyCreature := g.spellPaidTeamwork
    g.legalCreatureTargets caster (fun o => anyCreature || g.objectManaValue o ≤ n) sourceId
  | .creatureToughnessAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.toughness o >= n) sourceId
  | .enchantmentMvAtLeast n =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && g.isEnchantment o && g.objectManaValue o ≥ n) sourceId
  | .noncreatureArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && g.isArtifact o && !g.isCreature o) sourceId
  | .stackAbilityFromSource ty =>
    g.legalStackAbilityTargets caster (fun src => g.hasType src ty) sourceId
  | .oppCreaturePowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      g.power o <= n &&
        (g.livingOpponents caster).any (fun pl => g.controlledBy o pl.id)) sourceId
  | .oppCreatureDealtDamageThisTurn =>
    g.legalCreatureTargets caster (fun o =>
      g.dealtDamageThisTurn o.id &&
        (g.livingOpponents caster).any (fun pl => g.controlledBy o pl.id)) sourceId
  | .nonlandNontoken =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !g.isLand o && !o.printed.isToken) sourceId
  | .permanentCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (g.isPermanentCard ·)
  | .equipmentInstantOrSorceryInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o =>
      g.isEquipment o || g.isInstantOrSorcery o)
  | .artEnchCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o =>
      g.isArtifact o || g.isEnchantment o)
  | .artifactYouControl =>
    g.legalPermanentTargets caster (fun o =>
      g.controlledBy o caster && o.isOnBattlefield && g.isArtifact o) sourceId
  | .twoArtifactsYouControl => #[]
  | .creatureOrPlaneswalker =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o)) sourceId
  | .permanentYouControl =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && g.controlledBy o caster) sourceId
  | .oppPermanent =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (g.controllerOf o).isSome && !g.controlledBy o caster) sourceId
  | .planeswalkerYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && g.isPlaneswalker o && g.controlledBy o caster) sourceId
  | .oppCreatureOrPlaneswalker =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (g.isCreature o || g.isPlaneswalker o) &&
        (g.controllerOf o).isSome && !g.controlledBy o caster) sourceId
  | .creatureYouControlThenOppCreatureOrPlaneswalker => #[]
  | .planeswalkerYouControlThenOppCreatureOrPlaneswalker => #[]
  | .anotherCreatureYouControlPowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      g.controlledBy o caster && some o.id != sourceId && g.snapshotPower o <= n) sourceId
  | .attackingAloneCreatureYouControl =>
    let attackers :=
      g.legalCreatureTargets caster (fun o =>
        g.controlledBy o caster && o.status.attacking) sourceId
    if attackers.size == 1 then attackers else #[]
  | .noncreatureArtifactOrEnchantment =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !g.isCreature o &&
        (g.isArtifact o || g.isEnchantment o)) sourceId
  | .permanentOrPlayer =>
    g.legalPlayerTargets caster g.livingPlayers sourceId ++
      g.legalPermanentTargets caster (·.isOnBattlefield) sourceId
  | .upToTwoCreaturesTotalMvAtMost n =>
    g.legalCreatureTargets caster (fun o => g.objectManaValue o ≤ n) sourceId
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
        match eff.dividedDamage with
        | some (amount, _) => assignedDividedDamage e < amount
        | none =>
          if eff.allowsZeroTargets || eff.targetKind.spec.slots.size > 1 then !e.targetsAnnounced
          else eff.requiresTarget && e.targets.isEmpty
      | some ab, none =>
        match ab.effect.resolution with
        | .chooseTriggerModes _ => false
        | _ => triggerStillNeedsTargets e ab
      | none, _ => false
    | none => false)

end Game
end Mtg.Engine
