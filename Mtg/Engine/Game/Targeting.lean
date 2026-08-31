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
  !g.hasHexproof o || o.controlledBy caster

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

/-- Legal targets for an atomic targeting shape (no sequential slots). -/
def legalTargetsForAtomicKind (g : Game) (caster : PlayerId) (kind : EffectTargetKind)
    (sourceId : Option ObjectId) : Array Target :=
  match kind with
  | .none => #[]
  | .creatureYouControl =>
    g.legalCreatureYouControlTargets caster
  | .anotherCreatureYouControl =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster && some o.id != sourceId)
  | .anotherCreature =>
    g.legalCreatureTargets caster (fun o => some o.id != sourceId)
  | .playerOrCreature =>
    playerTargets g.livingPlayers ++
      g.legalCreatureTargets caster (fun _ => true)
  | .elfInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o => g.hasSubtype o "Elf")
  | .oppCreature =>
    g.legalOppCreatureTargets caster
  | .oppTappedCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.status.tapped &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .creature =>
    g.legalCreatureTargets caster (fun _ => true)
  | .creatureWithFlying =>
    g.legalCreatureTargets caster (fun o => g.hasFlying o)
  | .artifactOrLand =>
    g.legalPermanentTargets caster (·.isArtifactOrLand)
  | .colorlessNonland =>
    g.legalPermanentTargets caster (·.isColorlessNonland)
  | .creatureYouControlThenOppCreature => #[]
  | .player =>
    playerTargets g.livingPlayers
  | .opponent =>
    playerTargets (g.livingOpponents caster)
  | .oppGraveyardCard =>
    g.livingOpponents caster
      |>.foldl (fun acc pl => acc ++ g.legalGraveyardCardTargets pl.id (fun _ => true)) #[]
  | .artifactOrEnchantment =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && (o.printed.isArtifact || o.printed.isEnchantment))
  | .artifactOrCreatureYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && (o.isCreature || o.printed.isArtifact))
  | .nonland =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && !o.printed.isLand)
  | .oppNonland =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !o.printed.isLand &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .attackingCreatureWithoutFlying =>
    g.legalCreatureTargets caster (fun o => o.status.attacking && !g.hasFlying o)
  | .creatureYouControlSubtype subtype =>
    g.legalCreatureTargets caster (fun o => o.controlledBy caster && g.hasSubtype o subtype)
  | .spell =>
    g.legalStackSpellTargets (fun _ => true)
  | .creatureSpell =>
    g.legalStackSpellTargets (·.printed.isCreature)
  | .creatureSpellPTAtMost n =>
    g.legalStackSpellTargets (fun o =>
      o.printed.isCreature &&
        ((o.printed.power.getD 0) <= (n : Int) ||
          (o.printed.toughness.getD 0) <= (n : Int)))
  | .defendingPlayerCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy g.defendingPlayer)
  | .twoNonlandsSharingType => #[]
  | .creaturePowerAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.power o >= n)
  | .creaturePowerAtMost n =>
    g.legalCreatureTargets caster (fun o => g.power o <= n)
  | .creatureYouControlAnySubtype subtypes =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && subtypes.any (g.hasSubtype o))
  | .permanent =>
    g.legalPermanentTargets caster (·.isOnBattlefield)
  | .creatureCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (·.printed.isCreature)
  | .legendaryCreatureYouControl =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && o.isLegendary)
  | .creatureYouControlPowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      o.controlledBy caster && g.power o <= n)
  | .artifact =>
    g.legalPermanentTargets caster (fun o => o.isOnBattlefield && o.printed.isArtifact)
  | .oppArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .creatureCardInYourGraveyardMvAtMost n =>
    g.legalGraveyardCardTargets caster (fun o =>
      o.printed.isCreature && o.printed.manaValue ≤ n)
  | .artifactToken =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact && o.printed.isToken)
  | .attackingCreature =>
    g.legalCreatureTargets caster (fun o => o.status.attacking)
  | .equipmentYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && o.printed.isEquipment)
  | .creatureOrLandYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && (o.isCreature || o.printed.isLand))
  | .twoCreaturesOrLandsYouControl => #[]
  | .equipmentYouControlThenCreatureYouControl => #[]
  | .twoPlayers => #[]
  | .upToOneCreatureThenPlayer => #[]
  | .attackingOrBlockingCreature =>
    g.legalCreatureTargets caster (fun o =>
      o.status.attacking || !o.status.blocking.isEmpty)
  | .creatureMvAtMost n =>
    g.legalCreatureTargets caster (fun o => o.printed.manaValue ≤ n)
  | .creatureToughnessAtLeast n =>
    g.legalCreatureTargets caster (fun o => g.toughness o >= n)
  | .enchantmentMvAtLeast n =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isEnchantment && o.printed.manaValue ≥ n)
  | .noncreatureArtifact =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && o.printed.isArtifact && !o.isCreature)
  | .stackAbilityFromCreatureSource =>
    g.legalStackAbilityTargets caster (fun src => src.printed.isCreature)
  | .stackAbilityFromArtifactSource =>
    g.legalStackAbilityTargets caster (fun src => src.printed.isArtifact)
  | .oppCreaturePowerAtMost n =>
    g.legalCreatureTargets caster (fun o =>
      g.power o <= n &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .oppCreatureDealtDamageThisTurn =>
    g.legalCreatureTargets caster (fun o =>
      o.status.dealtDamageThisTurn &&
        (g.livingOpponents caster).any (fun pl => o.controlledBy pl.id))
  | .nonlandNontoken =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !o.printed.isLand && !o.printed.isToken)
  | .permanentCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o => o.printed.isPermanentCard)
  | .equipmentInstantOrSorceryInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o =>
      o.printed.isEquipment || o.printed.isInstant || o.printed.isSorcery)
  | .artEnchCardInYourGraveyard =>
    g.legalGraveyardCardTargets caster (fun o =>
      o.printed.isArtifact || o.printed.isEnchantment)
  | .artifactYouControl =>
    g.legalPermanentTargets caster (fun o =>
      o.controlledBy caster && o.isOnBattlefield && o.printed.isArtifact)
  | .twoArtifactsYouControl => #[]
  | .attackingAloneCreatureYouControl =>
    let attackers :=
      g.legalCreatureTargets caster (fun o =>
        o.controlledBy caster && o.status.attacking)
    if attackers.size == 1 then attackers else #[]
  | .noncreatureArtifactOrEnchantment =>
    g.legalPermanentTargets caster (fun o =>
      o.isOnBattlefield && !o.isCreature &&
        (o.printed.isArtifact || o.printed.isEnchantment))
  | .permanentOrPlayer =>
    playerTargets g.livingPlayers ++
      g.legalPermanentTargets caster (·.isOnBattlefield)
  | .upToTwoCreaturesTotalMvAtMost n =>
    g.legalCreatureTargets caster (fun o => o.printed.manaValue ≤ n)

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
    if ab.allowsZeroTargets then !e.targetsAnnounced
    else ab.requiresTarget && e.targets.isEmpty

/-- Stack entry for a triggered ability that still needs targets announced
(CR 603.3d). Oldest first so targets are chosen in the order abilities were
put on the stack. -/
def triggerNeedingTargets (g : Game) : Option StackEntry :=
  g.stack.find? (fun e =>
    match g.findObject? e.objectId with
    | some o =>
      match o.triggeredAbility with
      | some ab => triggerStillNeedsTargets e ab
      | none => false
    | none => false)

end Game
end Mtg.Engine
