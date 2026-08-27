import Mtg.Engine.Game

/-!
# Demonstration agent

A deterministic heuristic used by `Mtg.Demo` and compile-time smoke tests
to exercise the engine without a human at the console.
-/

namespace Mtg.Engine.Agent

open Mtg.Engine
open Mtg.Engine.Game

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
    | .assignCombatDamage _ _ =>
      some (.assignCombatDamage #[])
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
  /-- During CR 601.2c / 603.3d, announce a legal target for the proposed
  spell, activated ability, or triggered ability. Optional “up to one”
  triggers may choose no target. -/
  chooseSpellTarget (g : Game) (p : PlayerId) : Option Action :=
    match g.objectAwaitingTargets with
    | none => some .pass
    | some spell =>
      match g.defaultTarget p spell with
      | some t => some (.target t)
      | none =>
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
  /-- During CR 601.2g, tap sources until the locked-in cost is payable, then pay. -/
  chooseManaPayment (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell with
    | none => some .pay
    | some prop =>
      let allowElf := g.proposedAllowsElfRestricted prop
      if (g.player p).manaPool.canPay prop.cost allowElf then
        some .pay
      else
        match (g.manaSources p).find? (fun (src, types) =>
          !(prop.tapSource && prop.sourceId == some src.id) &&
          !(src.printed.tapAddAnyColorEqualToPower && !allowElf) && !types.isEmpty) with
        | some (src, types) =>
          match g.preferredManaType p types prop.cost allowElf with
          | some t => some (.tapForMana src.id t)
          | none => some .pay
        | none => some .pay
  /-- Activate a non-mana ability if the available mana covers its cost. -/
  chooseActivate (g : Game) (p : PlayerId) : Option Action :=
    let candidate := (g.permanentsOf p).find? (fun o =>
      match o.printed.activatedAbilities[0]? with
      | some ab =>
        let available :=
          g.availableManaExcept p (if ab.cost.tap then some o.id else none)
        g.canActivate p o ab &&
        available.canPay ab.cost.mana (allowElfRestricted := o.hasSubtype "Elf") &&
        -- Don't spend mana re-equipping a creature that is already equipped.
        !(ab.effect == .attachToTargetCreatureYouControl && o.attachedTo.isSome) &&
        -- Spend {4}{T} on Rogue's Passage only after attackers are declared.
        !(ab.effect == .targetCantBeBlockedThisTurn &&
          !(g.permanentsOf p).any (fun c => c.isCreature && c.status.attacking))
      | none => false)
    match candidate with
    | some o => some (.activate o.id 0)
    | none => chooseCast g p
  chooseCast (g : Game) (p : PlayerId) : Option Action :=
    let available := g.availableMana p
    let playable := (g.handObjects p ++ g.exiledPlayable p).filter (fun o =>
      g.canCast p o &&
        available.canPay o.printed.manaCost (allowElfRestricted := o.hasSubtype "Elf"))
    let adventurePlayable := (g.handObjects p ++ g.exiledPlayable p).filter (fun o =>
      g.canCastAdventure p o &&
        match o.printed.adventure with
        | some adv => available.canPay adv.manaCost
        | none => false)
    let oppHasCreature := (g.permanentsOf (g.opponent p)).any (·.isCreature)
    let ownCreature := (g.permanentsOf p).filter (·.isCreature) |>.back?
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
    let removal := playable.find? (fun o =>
      (hasLegalKind .creatureWithFlying &&
        (spellKind o .destroyFlying || modeKind o .destroyFlying)) ||
      (hasLegalKind .artifactOrLand && spellKind o .destroyArtifactOrLand))
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
    if let some o := burn then
      some (.cast o.id)
    else if let some o := adventureRemoval then
      some (.castAdventure o.id)
    else if let some o := creatureDamage then
      some (.cast o.id)
    else if let some o := removal then
      some (.cast o.id)
    else if let some o := fight then
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
