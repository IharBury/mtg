import Mtg.Engine.Game

/-!
# Demonstration agent

A deterministic heuristic used by `Mtg.Demo` and compile-time smoke tests
to exercise the engine without a human at the console.
-/

namespace Mtg.Engine.Agent

open Mtg.Engine
open Mtg.Engine.Game

/-- During CR 601.2g, tap sources until the locked-in cost is payable, then pay.
Only mana that can be spent on the pending payment is considered (CR 106.10).
Noncreatures are tapped before creatures when both help. Colorless is
preferred when it can be spent; otherwise colors meet unmet requirements.
Flexible sources such as Hidden Lair tap for `{U}` or `{B}` when that
color is needed and the rest of the board can still finish the cost. -/
def chooseManaPayment (g : Game) (p : PlayerId) : Option Action :=
  match g.proposedSpell with
  | none => some .pay
  | some prop =>
    let allowElf := g.proposedAllowsElfRestricted prop
    let allowInst := g.proposedAllowsInstRestricted prop
    if (g.player p).manaPool.canPay prop.cost allowElf allowInst then
      some .pay
    else
      match g.preferredManaTap p prop with
      | some (src, t) => some (.tapForMana src.id t)
      | none => some .pay

/-- Pay `{n}` from the pool if possible; otherwise tap the first mana source. -/
def payGenericOrTapFirstSource (g : Game) (p : PlayerId) (n : Nat) : Option Action :=
  if (g.player p).manaPool.canPay (ManaCost.ofGeneric n) then
    some .payGeneric
  else
    match (g.manaSources p).find? (fun (_, types) => !types.isEmpty) with
    | some (src, types) =>
      match types[0]? with
      | some t => some (.tapForMana src.id t)
      | none => some .decline
    | none => some .decline

/-- Choose a single legal action for `p`, or `none` if that player is not to act. -/
def choose (g : Game) (p : PlayerId) : Option Action :=
  if g.over then none
  else if g.actor != some p then none
  else
    match g.pending with
    | .declareAttackers =>
      let ids := g.battlefield.filter (g.canAttack) |>.map (·.id)
      some (.declareAttackers ids)
    | .declareBlockers =>
      -- Naive: don't block. The demo still exercises the declare-blockers step.
      some (.declareBlockers #[])
    | .activateManaAbilities _ =>
      chooseManaPayment g p
    | .chooseMode _ =>
      match g.proposedSpell with
      | some prop =>
        if prop.kind == .activatedAbility then
          chooseAbilityMode g p
        else
          chooseSpellMode g p
      | none => some .pass
    | .chooseX _ =>
      match g.proposedSpell with
      | some prop => some (.chooseX (maxAffordableX g p prop.cost))
      | none => some (.chooseX 0)
    | .chooseTargets _ =>
      chooseSpellTarget g p
    | .sacrificePermanent _ sourceId =>
      match (g.sacrificeCreatureOrArtifactChoices p sourceId)[0]? with
      | some sac => some (.sacrifice sac.id)
      | none => some .pass
    | .sacrificeCreature _ =>
      match (g.sacrificeCreatureChoices p)[0]? with
      | some sac => some (.sacrifice sac.id)
      | none => some .pass
    | .declareMulligan _ =>
      some .keep
    | .putOnBottom _ n =>
      some (.putOnBottom ((g.player p).hand.extract 0 n))
    | .scry _ n =>
      some (.scry (g.scryLookedIds p n) #[])
    | .mayDiscardDraw _ _ =>
      match (g.player p).hand.back? with
      | some id => some (.discard id)
      | none => some .decline
    | .chooseAdditionalCost _ =>
      match g.proposedSpell with
      | some prop =>
        if (g.sacrificeCreatureOrArtifactChoices p prop.spellId).isEmpty then
          some (.chooseAdditionalCost true)
        else
          some (.chooseAdditionalCost false)
      | none => some .pass
    | .chooseSacrificeCreature _ _ _ =>
      match (g.creaturesControlledBy p)[0]? with
      | some o => some (.sacrifice o.id)
      | none => some .pass
    | .chooseDiscardCard _ _ =>
      match (g.player p).hand.back? with
      | some id => some (.discard id)
      | none => some .decline
    | .assignCombatDamage _ _ =>
      some (.assignCombatDamage #[])
    | .chooseLegend _ _ ids =>
      some (.keepLegend (defaultLegendToKeep g ids))
    | .chooseTriggerToStack q =>
      some (.stackTriggers (defaultTriggerSourceIds g q))
    | .mayPayGeneric _ n =>
      payGenericOrTapFirstSource g p n
    | .chooseLibraryPlacement _ _ =>
      some .chooseBottom
    | .mayAttachEquipment _ hostId =>
      match (g.permanentsOf p).find? (fun o =>
        o.printed.isEquipment && o.attachedTo != some hostId) with
      | some eq => some (.choosePermanents #[eq.id])
      | none => some .decline
    | .tapHumans _ =>
      let humans :=
        (g.permanentsOf p).filter (fun o =>
          g.hasSubtype o "Human" && !o.status.tapped)
      if humans.isEmpty then some .decline
      else some (.choosePermanents (humans.map (·.id)))
    | .payOrLetCounter _ n _ =>
      payGenericOrTapFirstSource g p n
    | .payWard _ _ cost =>
      match cost with
      | .genericMana n | .discardOrPay n =>
        match cost with
        | .discardOrPay _ =>
          match (g.player p).hand.back? with
          | some id => some (.discard id)
          | none => payGenericOrTapFirstSource g p n
        | _ => payGenericOrTapFirstSource g p n
      | .discardEnchantmentInstantOrSorcery =>
        match (g.player p).hand.find? (fun id =>
          match g.findObject? id with
          | some o =>
            o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
          | none => false) with
        | some id => some (.discard id)
        | none => some .decline
      | .sacrificeLegendary =>
        match (g.legendaryWardSacrificeChoices p)[0]? with
        | some o => some (.sacrifice o.id)
        | none => some .decline
      | .fivePoison => some .pay
    | .recruitDiscard _ =>
      match (g.player p).hand.back? with
      | some id => some (.discard id)
      | none => some .decline
    | .chooseKicker _ =>
      some (.announceKicker false)
    | .chooseGift _ =>
      some (.announceGift none)
    | .chooseTeamwork _ =>
      some (.announceTeamwork false)
    | .chooseTeamworkCreatures _ need =>
      some (.choosePermanents (g.pickTeamworkCreatures p need))
    | .chooseRingBearer _ =>
      match (g.ringBearerChoices p)[0]? with
      | some o => some (.chooseRingBearer (some o.id))
      | none => some (.chooseRingBearer none)
    | .maySacrificeAnotherBolg _ bolgId =>
      match (g.permanentsOf p).find? (fun o => o.isCreature && o.id != bolgId) with
      | some o => some (.sacrifice o.id)
      | none => some .decline
    | .mayCastFromLooked _ ids maxMv =>
      match ids.reverse.find? (fun id =>
        (g.mayCastFromLookedError p ids maxMv id).isNone) with
      | some id => some (.cast id)
      | none => some .decline
    | .resolveRandom _ =>
      -- Random results are supplied by the host (`--norandom`), never the heuristic.
      none
    | .none =>
      -- Play a land if possible (from hand or from exile under a permission).
      let lands :=
        (g.handObjects p).filter (·.printed.isLand) ++
        (g.exiledPlayable p).filter (·.printed.isLand)
      if g.canPlayLand p then
        match lands[0]? with
        | some land => some (.playLand land.id)
        | none =>
          chooseActivate g p
      else
        chooseActivate g p
where
  /-- During CR 601.2b, announce a legal mode for the proposed modal spell. -/
  chooseSpellMode (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | none => some .pass
    | some spell =>
      match g.defaultMode p spell with
      | some i => some (.chooseMode i)
      | none => some .pass
  /-- During CR 601.2c / 603.3d, announce a legal target for the current
  instance of the word “target” on the proposed spell, activated ability,
  or triggered ability. Optional “up to one” triggers may choose no target. -/
  chooseSpellTarget (g : Game) (p : PlayerId) : Option Action :=
    match g.objectAwaitingTargets with
    | none => some .pass
    | some spell =>
      match g.defaultTarget p spell with
      | some t => some (.target t)
      | none =>
        if g.canSkipCurrentOptionalSlot spell then some .decline
        else if g.canFinishOptionalTargets spell then some .decline
        else
          match spell.triggeredAbility with
          | some ab =>
            if ab.allowsZeroTargets then some .decline else some .pass
          | none => some .pass
  /-- During CR 601.2b, announce a mode of a modal activated ability. -/
  chooseAbilityMode (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell with
    | none => some .pass
    | some prop =>
      match g.defaultAbilityMode p prop.abilityModes with
      | some idx => some (.chooseMode idx)
      | none => some .pass
  /-- Largest `{X}` `p` can currently pay for `cost` (CR 107.3a). -/
  maxAffordableX (g : Game) (p : PlayerId) (cost : ManaCost) : Nat :=
    let available := g.availableMana p
    Id.run do
      let mut best : Nat := 0
      for x in [0:available.total + 1] do
        if available.canPay (cost.substituteX x) then
          best := x
      return best
  /-- Activate a non-mana ability if the available mana covers its cost. -/
  chooseActivate (g : Game) (p : PlayerId) : Option Action :=
    let shouldActivate (o : GameObject) (ab : ActivatedAbility) : Bool :=
      let available :=
        g.availableManaExcept p (if ab.cost.tap then some o.id else none)
      let manaCost := g.activationManaCost p ab (some o)
      g.canActivate p o ab &&
      available.canPay ab.cost.mana (allowElfRestricted := o.hasSubtype "Elf") &&
      -- Don't pay life that would reduce the player to 0 or less.
      (ab.cost.payLife == 0 || (g.player p).life > (ab.cost.payLife : Int)) &&
      -- Don't spend a once-only X power-up at X = 0.
      !(ab.effect == .plusOneX && maxAffordableX g p manaCost == 0) &&
      -- Don't spend mana re-equipping a creature that is already equipped.
      !(ab.effect == .attachToTargetCreatureYouControl && o.attachedTo.isSome) &&
      -- Spend {4}{T} on Rogue's Passage only after attackers are declared.
      !(ab.effect == .targetCantBeBlockedThisTurn &&
        !(g.permanentsOf p).any (fun c => c.isCreature && c.status.attacking)) &&
      -- Don't typecycle a card you can currently afford to cast.
      !(ab.activateFromHand && g.canCast p o &&
        (g.availableMana p).canPay o.printed.manaCost
          (allowElfRestricted := o.hasSubtype "Elf"))
    let firstAbility (o : GameObject) : Option Nat :=
      (g.activatedAbilitiesOf o).findIdx? (shouldActivate o)
    let gy := (g.player p).graveyard.filterMap (fun id => g.findObject? id)
    let candidate :=
      (g.permanentsOf p).find? (fun o => (firstAbility o).isSome) <|>
        gy.find? (fun o => (firstAbility o).isSome) <|>
        (g.handObjects p).find? (fun o => (firstAbility o).isSome)
    match candidate with
    | some o =>
      match firstAbility o with
      | some idx => some (.activate o.id idx)
      | none => chooseCast g p
    | none => chooseCast g p
  chooseCast (g : Game) (p : PlayerId) : Option Action :=
    let available := g.availableMana p
    let playable := (g.handObjects p ++ g.exiledPlayable p).filter (fun o =>
      g.canCast p o &&
        (o.playPermission.any (·.withoutManaCost) ||
          available.canPay o.printed.manaCost
            (allowElfRestricted := o.hasSubtype "Elf")
            (allowInstRestricted := o.printed.isInstantOrSorcery)))
    let adventurePlayable := (g.handObjects p ++ g.exiledPlayable p).filter (fun o =>
      g.canCastAdventure p o &&
        match o.printed.adventure with
        | some adv =>
          available.canPay adv.manaCost
            (allowInstRestricted := adv.types.any CardType.isInstantOrSorcery)
        | none => false)
    let oppHasCreature := !(g.creaturesControlledBy (g.opponent p)).isEmpty
    let ownCreature := (g.creaturesControlledBy p).back?
    let spellKind (o : GameObject) (k : SpellCastKind) : Bool :=
      o.printed.hasCastKind k
    let adventureKind (o : GameObject) (k : SpellCastKind) : Bool :=
      o.printed.adventure.any (fun a => a.hasCastKind k)
    let modeKind (o : GameObject) (k : SpellCastKind) : Bool :=
      o.printed.hasModeCastKind k
    let hasLegalKind (k : EffectTargetKind) : Bool :=
      !(g.legalTargetsForKind p k).isEmpty
    let adventureRemoval :=
      if oppHasCreature then
        adventurePlayable.find? (fun o =>
          adventureKind o .creatureDamage || adventureKind o .burn)
      else none
    let burn := playable.find? (fun o => spellKind o .burn)
    let creatureDamage :=
      if oppHasCreature then
        playable.find? (fun o => spellKind o .creatureDamage)
      else none
    let fight := playable.find? (fun o => spellKind o .fight)
    let draw := playable.find? (fun o =>
      (spellKind o .draw || modeKind o .draw) &&
        match o.printed.spellEffect with
        | some e =>
          match e.resolution with
          | .drawAndLoseLife cards life =>
            (g.player p).life > (life : Int) &&
              (g.player p).library.size >= cards
          | _ => true
        | none => true)
    let removal := playable.find? (fun o =>
      (oppHasCreature && (spellKind o .destroyCreature || modeKind o .destroyCreature)) ||
      (hasLegalKind .creatureWithFlying &&
        (spellKind o .destroyFlying || modeKind o .destroyFlying)) ||
      (hasLegalKind .creature &&
        (spellKind o .destroyCreature || modeKind o .destroyCreature)) ||
      (hasLegalKind .artifactOrLand && spellKind o .destroyArtifactOrLand))
    let massPump := playable.find? (fun o =>
      spellKind o .massPump || modeKind o .massPump)
    let creature := playable.find? (fun o => o.printed.isCreature)
    let artifact := playable.find? (fun o =>
      o.printed.isArtifact &&
        (!o.printed.activatedAbilities.isEmpty || o.printed.isEquipment))
    let pump :=
      if ownCreature.isSome then
        playable.find? (fun o =>
          spellKind o .pump ||
            o.printed.spellModes.any (fun e =>
              e.castKind == .pump && !(g.legalTargetsForKind p e.targetKind).isEmpty))
      else none
    let aura :=
      if ownCreature.isSome then
        playable.find? (fun o => o.printed.isAura)
      else none
    let extraLandAdventure :=
      adventurePlayable.find? (fun o => adventureKind o .extraLand)
    let isSpellCounter (o : GameObject) : Bool :=
      o.printed.spellEffect.any (fun e => e.targetKind.targetsStackSpell) ||
        o.printed.spellModes.any (fun e => e.targetKind.targetsStackSpell)
    let hasOppSpellTarget (o : GameObject) : Bool :=
      match o.printed.spellEffect with
      | some e => g.effectHasOppSpellTarget p e
      | none => o.printed.spellModes.any (g.effectHasOppSpellTarget p)
    -- Cast a counter only when an opponent's spell is a legal target.
    let counter :=
      playable.find? (fun o =>
        (spellKind o .counter || modeKind o .counter) &&
          if isSpellCounter o then hasOppSpellTarget o
          else !(g.stackSpells (fun _ => true)).isEmpty)
    if let some o := counter then
      some (.cast o.id)
    else if let some o := burn then
      some (.cast o.id)
    else if let some o := adventureRemoval then
      some (.castAdventure o.id)
    else if let some o := creatureDamage then
      some (.cast o.id)
    else if let some o := removal then
      some (.cast o.id)
    else if let some o := fight then
      some (.cast o.id)
    else if let some o := draw then
      some (.cast o.id)
    else if let some o := creature then
      some (.cast o.id)
    else if let some o := artifact then
      some (.cast o.id)
    else if let some o := pump then
      some (.cast o.id)
    else if let some o := aura then
      some (.cast o.id)
    else if let some o := extraLandAdventure then
      some (.castAdventure o.id)
    else if let some o := massPump then
      some (.cast o.id)
    else
      some .pass

/-- Apply the heuristic once. Returns `none` if no actor or the action failed. -/
def step (g : Game) : Except String Game := do
  match g.actor with
  | none => throw "No player has an action"
  | some p =>
    match choose g p with
    | none => g.apply p .pass
    | some a => g.apply p a

/-- Run the heuristic until the game ends or `fuel` actions have been taken. -/
def play (g : Game) (fuel : Nat := 400) : Game :=
  match fuel with
  | 0 => g.logMsg "Stopped: action limit reached"
  | n + 1 =>
    if g.over then g
    else if !g.playersReceivePriority && g.pending == .none then
      -- Untap, or a cleanup with no CR 514.3a exception: recover by advancing.
      play (g.advanceStep) n
    else
      match step g with
      | .ok g' => play g' n
      | .error e => g.logMsg s!"Agent error: {e}"

end Mtg.Engine.Agent
