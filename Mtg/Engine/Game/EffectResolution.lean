import Mtg.Engine.Game.ModeledTriggers

/-!
# Unified effect resolution (CR 608)

`applyUnified` and `applyUnifiedAbility`: the interpreters for the
unified `Effect` vocabulary shared by spells, activated abilities, and
triggered abilities.
-/

namespace Mtg.Engine
namespace Game

/-- Move the source into its owner's library and shuffle (CR 701.19).
A following draw is rewritten to that owner so a stolen source still
draws for the printed owner. -/
def shuffleSourceIntoLibrary (g : Game) (sourceId : Option ObjectId)
    (after : AfterRandom := .none) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The source is no longer in play"
  | some src =>
    let owner := src.owner
    let after :=
      match after with
      | .draw _ n => .draw owner n
      | other => other
    let (g, _) := g.move src.id (.library owner) none
    g.requestShuffle owner after |>.continueIfShuffled

/-- Resolve a unified `Effect` as a spell (CR 608). -/
partial def applyUnified (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0) : Game :=
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.shuffleSource, .draw n] =>
      g.shuffleSourceIntoLibrary none (.draw controller n)
    | steps =>
      steps.foldl (fun g r =>
        g.applyUnified controller { effect with resolution := r } targets
          (castFromGraveyard := castFromGraveyard) (kicked := kicked)
          (giftPromised := giftPromised) (chosenX := chosenX)) g
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary none
  | .gainLife n => g.gainLife controller n
  | .recruit => g.beginRecruit controller
  | .addMana types =>
    g.addManaLogged controller types
  | .discard n =>
    g.beginDiscardCards #[controller] n
  | .onSource a =>
    g.applyOnPermanent controller effect.targetKind targets a
  | _ =>
  match effect.spellResolution with
  | .fight =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      let srcOk := (g.legalCreatureYouControlTargets controller).contains
        (Target.permanent srcId)
      let destOk := (g.legalOppCreatureTargets controller).contains
        (Target.permanent destId)
      if srcOk && destOk then
        g.dealFightDamage (g.object! srcId) (g.object! destId)
      else
        let logIllegal (g : Game) (ok : Bool) (id : ObjectId) : Game :=
          if ok then g else g.illegalAbilityTarget (Target.permanent id)
        logIllegal (logIllegal g srcOk srcId) destOk destId
    | _, _ => g.logMsg "The target is no longer legal"
  | .extraLand =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with additionalLandsThisTurn := pl.additionalLandsThisTurn + 1 })
    g.logMsg s!"{(g.player controller).name} may play an additional land this turn"
  | .drawAndLoseLife cards life =>
    g.drawThenLoseLife controller cards life
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action
  | .allCreaturesPump p t =>
    g.foldBattlefield (fun o => o.isCreature) (fun g o => g.pumpPermanent o p t)
  | .playerDrawLoseLife cards life =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.drawThenLoseLife pid cards life)
  | .creaturesOfPlayerPump pw tw =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.pumpControlledCreatures pid pw tw)
  | .destroyAndControllerLosesLife n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let ctrl := o.controller
      let g := g.destroyPermanent o
      match ctrl with
      | some pid => g.loseLife pid n
      | none => g)
  | .exileGraveyardCreaturesGrantCast =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.exileCreaturesFromGraveyard controller pid)
  | .draw n =>
    g.draw controller n
  | .drawThenDiscard n =>
    g.drawThenBeginDiscard controller n
  | .scry n =>
    g.beginScry controller n
  | .tapScryDraw scryN drawN =>
    let legal := g.legalTargetsForKind controller effect.targetKind
    match targets[0]? with
    | some t =>
      if legal.contains t then
        let g := g.applyOnPermanent controller effect.targetKind targets .tap
        let g := { g with pendingDrawAfterScry := some (controller, drawN) }
        let g := g.beginScry controller scryN
        if g.pendingDrawAfterScry.isSome &&
            (match g.pending with | .scry _ _ => false | _ => true) then
          let g := { g with pendingDrawAfterScry := none }
          g.draw controller drawN
        else g
      else
        g.logMsg "The spell doesn't resolve"
    | none => g.logMsg "The spell doesn't resolve"
  | .tapTargets =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.isCreature then g.applyPermanentAction o .tap else g)
  | .counter =>
    match targets[0]? with
    | some (Target.card id) => g.counterStackSpell id
    | _ => g.logMsg "The target is no longer legal"
  | .counterUnlessPays n =>
    g.beginPayOrLetCounter targets n
  | .counterExilePermanentMayCast =>
    match targets[0]? with
    | some (Target.card id) =>
      g.counterStackSpell id (exilePermanent := true) (grantFreeCast := true)
        controller
    | _ => g.logMsg "The target is no longer legal"
  | .putOnTopOrBottom =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          { g with pending := .chooseLibraryPlacement o.owner id }.logMsg
            s!"{(g.player o.owner).name} chooses top or bottom of their library for {o.name}"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .untapPumpMaybeAttach p t =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.applyPermanentAction o .untap
      let o := g.object! o.id
      let g := g.pumpPermanent o p t
      let o := g.object! o.id
      if g.hasSubtype o "Dwarf" then
        { g with pending := .mayAttachEquipment controller o.id }.logMsg
          s!"{(g.player controller).name} may attach an Equipment to {o.name}"
      else g)
  | .exchangeControl =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some oa, some ob =>
        if oa.isOnBattlefield && ob.isOnBattlefield then
          let ca := oa.controller
          let cb := ob.controller
          let g :=
            match cb with
            | some p => g.changeControl oa p
            | none => g.setObject { oa with controller := none }
          let g :=
            match ca with
            | some p => g.changeControl (g.object! b) p
            | none => g.setObject { (g.object! b) with controller := none }
          g.logMsg s!"{oa.name} and {ob.name} exchange control"
        else g.logMsg "The target is no longer legal"
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneAndPlayerGainsLife n =>
    Id.run do
      let creatureLegal := g.legalTargetsForAtomicKind controller .creature none
      let playerLegal := g.legalTargetsForAtomicKind controller .player none
      let mut g := g
      for t in targets do
        match t with
        | Target.permanent oid =>
          if creatureLegal.contains t then
            match g.findObject? oid with
            | some o => g := g.addPlusOnePlusOneTo o 1
            | none => g := g.logMsg "The target is no longer in play"
          else
            g := g.illegalAbilityTarget t
        | Target.player pid =>
          if playerLegal.contains t then
            if n != 0 then
              let pl := g.player pid
              g := g.setLife pid (pl.life + (n : Int))
                s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
          else
            g := g.illegalAbilityTarget t
        | Target.card _ =>
          g := g.illegalAbilityTarget t
      return g
  | .returnSpellDraw =>
    let g :=
      match targets[0]? with
      | some (Target.card id) => g.returnStackSpell id
      | _ => g.logMsg "The target is no longer legal"
    g.draw controller 1
  | .creaturesYouControlPump pw tw =>
    g.pumpControlledCreatures controller pw tw
  | .amassGoblins n =>
    g.amassGoblins controller n
  | .drawLoseLifeThenAmass n =>
    let g := g.draw controller 1
    let g := g.loseLife controller 1
    g.amassGoblins controller n
  | .returnCreatureFromGyThenAmass n =>
    let g :=
      match targets[0]? with
      | some (Target.card oid) =>
        match g.findObject? oid with
        | none => g.logMsg "The target is no longer in the graveyard"
        | some o =>
          g.returnToHand o.id controller
      | _ => g
    g.amassGoblins controller n
  | .counterThenRecruitIfMvAtMost n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let mv := o.printed.manaValue
        let g := g.counterStackSpell id
        if mv <= n then g.beginRecruit controller else g
    | _ => g.logMsg "The target is no longer legal"
  | .plusOneThenFight n =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      match g.findObject? srcId, g.findObject? destId with
      | some src, some dest =>
        let g := g.addPlusOnePlusOneTo src n
        g.fightCreatures (g.object! src.id) (g.object! dest.id)
      | _, _ => g.logMsg "The target is no longer legal"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneThenEachOtherIfFromGy =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.findObject? oid with
      | none => g.logMsg "The target is no longer legal"
      | some o =>
        let g := g.addPlusOnePlusOneTo o 1
        if !castFromGraveyard then g
        else
          g.forEachControlledCreature controller
            (fun g c => g.addPlusOnePlusOneTo c 1) (some oid)
    | _ => g.logMsg "The target is no longer legal"
  | .drawIfFromGy n fromGy =>
    g.draw controller (if castFromGraveyard then fromGy else n)
  | .amassGoblinsOrFromGy n fromGy =>
    g.amassGoblins controller (if castFromGraveyard then fromGy else n)
  | .searchLegendaryCreatureToHand =>
    g.resolveLibrarySearchToHand controller (fun c =>
      c.isCreature && c.hasSupertype .legendary) "legendary creature card"
  | .dealDamageToEachOppCreature n =>
    g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
  | .targetPlayerDraw n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n)
  | .dealDamageToCreatureExileIfDies n =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with untilEotExileIfDies := true })
      g.applyPermanentAction (g.object! o.id) (.dealDamage n))
  | .addRedPerOppArtifacts =>
    let n := g.countOpponentArtifacts controller
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) n })
    g.logMsg s!"{(g.player controller).name} adds {n} red mana"
  | .dealDamageToEachNonDragon n =>
    g.dealDamageToEachNonDragon n
  | .chooseTypeReturnOthers =>
    let chosen :=
      (g.battlefield.find? (fun o => o.isCreature && o.controlledBy controller)
        |>.bind (fun o => o.printed.subtypes[0]?)).getD "Elf"
    g.foldBattlefield (fun o => o.isCreature && !g.hasSubtype o chosen)
      (fun g o => g.returnToHand o.id o.owner)
  | .drawEqualToughnessThenPutCreatures =>
    let greatest :=
      (g.permanentsOf controller).foldl (fun acc o =>
        if o.isCreature then max acc (g.toughness o).toNat else acc) 0
    let g := g.draw controller greatest
    Id.run do
      let mut g := g
      for id in (g.player controller).hand do
        let o := g.object! id
        if o.printed.isCreature then
          let sick := !o.printed.keywords.haste
          let (g', newId) := g.putOntoBattlefield id controller (summoningSick := sick)
          g := g'.logMsg s!"{o.name} enters the battlefield"
          g := g.afterPermanentEnters (g.object! newId)
      return g
  | .millThenPutInstantOrSorcery n =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery) (some 1)
  | .millThenPutLands n max =>
    g.millThenPutFromGy controller n (fun o => o.printed.isLand) (some max)
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    let g := g.dealDamageToEachNonDragon n
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) 4 })
      |>.logMsg
        s!"{(g.player controller).name} adds four mana that can be spent only on Dragon spells"
  | .millThenPutAllInstantsOrSorceries n =>
    g.millThenPutFromGy controller n
      (fun o => o.printed.isInstant || o.printed.isSorcery)
  | .exileAttackersSearchBasics =>
    g.withLegalKindTarget controller effect.targetKind targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        Id.run do
          let mut g := g
          let mut n : Nat := 0
          for o in g.battlefield do
            if o.isCreature && o.status.attacking && o.controlledBy pid then
              let name := o.name
              let (g', _) := g.move o.id (.exile) none
              g := g'.logMsg s!"{name} is exiled"
              n := n + 1
          return g.logMsg s!"{(g.player pid).name} may search for {n} basic lands"
      | _ => g.logMsg "The target is no longer legal")
  | .createTokensX kind =>
    g.createKindTokens controller kind 1
  | .exileTopPlayIfYouControlSubtype n subtype =>
    g.exileTopPlayIfYouControlSubtype controller n subtype
  | .exileThenReturnYouControl =>
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller then
        g.exileThenReturn o "is exiled, then returned to the battlefield"
      else g)
  | .destroyArtifactOrEnchantmentGainLife n =>
    let g := g.applyOnPermanent controller effect.targetKind targets .destroy
    if n == 0 then g
    else
      let pl := g.player controller
      g.setLife controller (pl.life + (n : Int))
        s!"{pl.name} gains {n} life ({pl.life + (n : Int)} life)"
  | .returnSpellCantCastIfGift =>
    let g :=
      match targets[0]? with
      | some (Target.card sid) => g.returnStackSpell sid
      | _ => g.logMsg "The target is no longer legal"
    if giftPromised then
      g.players.foldl (fun acc pl =>
        acc.setPlayer { pl with cantCastSpellsThisTurn := true }) g
        |>.logMsg "Players can't cast spells this turn"
    else g
  | .exileTopXOppPlayForLife =>
    match targets[0]? with
    | some (Target.player pid) =>
      Id.run do
        let mut g := g
        for _ in List.range chosenX do
          let pl := g.player pid
          if pl.library.isEmpty then
            g := g.logMsg s!"{pl.name} has no cards in their library to exile"
          else
            let top := pl.library.back!
            let name := (g.object! top).name
            let (g', newId) := g.move top .exile none
            g := g'
            let o := g.object! newId
            g := g.setObject { o with
              playPermission := some {
                player := controller
                turnEndsRemaining := 1
                whileExiled := true
                payLifeEqualManaValue := true } }
            g := g.logMsg s!"{(g.player controller).name} exiles {name}"
        return g
    | _ => g.logMsg "The target is no longer legal"
  | .riddlesInTheDark =>
    g.riddlesInTheDark controller 2 false
  | .supperForSpiders =>
    let ids :=
      g.battlefieldCreaturesToGyThisTurn.filter (fun id =>
        match g.findObject? id with
        | some o =>
          o.zone == .graveyard o.owner && o.owner != controller
        | none => false)
    g.supperForSpidersReturn controller ids
  | .eaglesAreComing =>
    let ids :=
      targets.filterMap (fun
        | Target.permanent id => some id
        | _ => none)
    Id.run do
      let mut g := g
      let mut n : Nat := 0
      for id in ids do
        match g.findObject? id with
        | none => pure ()
        | some o =>
          if o.isOnBattlefield && o.isCreature && o.owner == controller then
            let name := o.name
            let owner := o.owner
            let (g', _) := g.move o.id (.hand owner) none
            g := g'.logMsg s!"{name} is returned to {(g'.player owner).name}'s hand"
            n := n + 1
      if n > 0 then
        g := g.modifyPlayer controller (fun pl =>
          { pl with eaglesBirdsNextUpkeep := pl.eaglesBirdsNextUpkeep + n })
        g := g.logMsg
          s!"At the beginning of the next upkeep, {n} Bird Soldier token(s) will be created"
      return g
  | .lookAtTopLandsGainLife n life =>
    Id.run do
      let mut g := g
      let ids := g.scryLookedIds controller n
      for id in ids do
        match g.findObject? id with
        | some o =>
          if o.printed.isLand then
            let name := o.name
            let (g', newId) := g.putOntoBattlefield id controller (tapped := true)
            g := g'
            g := g.setObject { (g.object! newId) with
              status := { (g.object! newId).status with tapped := true } }
            g := g.logMsg s!"{name} enters tapped"
            g := g.afterLandEnters (g.object! newId)
          else pure ()
        | none => pure ()
      g := g.requestShuffle controller (.gainLife controller life)
      return g.continueIfShuffled
  | .gainControlOppArtifacts =>
    g.foldPermanentTargets targets (fun g o =>
      if o.isOnBattlefield && o.printed.isArtifact && !o.controlledBy controller then
        g.changeControl o controller
      else g)
  | .damageOppCreaturesEqualOtherSpellsMv =>
    let xs := (g.player controller).castManaValuesThisTurn
    let n : Nat := (xs.extract 0 xs.size.pred).foldl (fun a b => a + b) 0
    g.dealDamageToEachCreatureMatching n (fun o => !o.controlledBy controller)
      |>.logMsg s!"deals {n} damage to each opposing creature"
  | .phaseOutKicker =>
    if kicked then
      match targets[0]? with
      | some (Target.player pid) =>
        (g.permanentsOf pid).foldl (fun acc o =>
          if o.isCreature then acc.phaseOut o else acc) g
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o =>
          let pid := o.controller.getD controller
          (g.permanentsOf pid).foldl (fun acc x =>
            if x.isCreature then acc.phaseOut x else acc) g
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
    else
      match targets[0]? with
      | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o => g.phaseOut o
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal"
  | .dealDamageTeamwork n teamworkN =>
    let amt := g.teamworkAmount n teamworkN
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.dealDamageToPermanent o amt)
  | .dealDamageThenControllerIfTeamwork n extra =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.dealDamageToPermanent o n
      if g.resolvingTeamworkPaid then
        match o.controller with
        | some pid => g.dealDamageToPlayer pid extra
        | none => g
      else g)
  | .grantDoubleStrikeTeamworkTrample =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.doubleStrike)
      if g.resolvingTeamworkPaid then
        g.mapObjectStatus (g.object! o.id) (·.grantUntilEot Keyword.trample)
      else g)
  | .counterUnlessPaysTeamwork n teamworkN =>
    let amt := g.teamworkAmount n teamworkN
    g.beginPayOrLetCounter targets amt
  | .exileCreatureMvAtMostOrAnyIfTeamwork _n life =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let (g, _) := g.move o.id .exile none
      if g.resolvingTeamworkPaid then
        g.modifyPlayer controller (fun pl => { pl with life := pl.life + (life : Int) })
      else g)
  | .returnGyCreatureMvAtMostOrAny _n =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some _ =>
        let (g, _) := g.putOntoBattlefield id controller
        g
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .revealTopPutCreatures n =>
    Id.run do
      let mut g := g
      let top := g.scryLookedIds controller n
      let teamwork := g.resolvingTeamworkPaid
      let mut putOne := false
      for id in top do
        let o := g.object! id
        if o.printed.isCreature && (teamwork || !putOne) then
          let (g', _) := g.putOntoBattlefield id controller
          g := g'
          putOne := true
        else
          let (g', _) := g.move id (.graveyard o.owner) none
          g := g'
      return g
  | .createTokens kind n =>
    g.createKindTokens controller kind n
  | .exileTarget =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      (g.move o.id .exile none).1)
  | .returnOneOrTwoNonlands =>
    targets.foldl (fun g t =>
      match t with
      | Target.permanent oid =>
        match g.findObject? oid with
        | some o => (g.move o.id (.hand o.owner) none).1
        | none => g
      | _ => g) g
  | .targetPlayerCreatesTokens kind n =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => p
      | _ => controller
    g.createKindTokens pid kind n
  | .destroyCreatureSurveil =>
    let stillLegal :=
      match targets[0]? with
      | some t => (g.legalTargetsForKind controller effect.targetKind).contains t
      | none => false
    if stillLegal then
      let g := g.withLegalKindPermanent controller effect.targetKind targets
        (fun g o => g.destroyPermanent o)
      g.beginScry controller 1
    else
      g.logMsg "The target is no longer legal. You won't surveil."
  | .investigatePumpFlyingUntap =>
    let g := (g.createToken controller clueToken).1
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.flying)
      let o := g.object! o.id
      let g := g.applyPermanentAction o .untap
      g.applyPermanentAction (g.object! o.id) (.pump 1 0))
  | .plusOneLifelinkIndestructible =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + 1 })
      g.grantUntilEotKeywords (g.object! o.id) [Keyword.lifelink, Keyword.indestructible])
  | .dealDamageToEachCreature n =>
    g.dealDamageToEachCreatureMatching n
  | .destroyLandSearchBasic =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let owner := o.owner
      let g := g.destroyPermanent o
      g.logMsg s!"{(g.player owner).name} may search for a basic land")
  | .doublePowerAndToughness =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let p := g.power o
      let t := g.toughness o
      g.applyPermanentAction o (.pump p t))
  | .returnGySubtypeToHand _subtype =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some o => (g.move o.id (.hand o.owner) none).1
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal"
  | .grantVigilanceUnblockable =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.grantUntilEotKeywords o [Keyword.vigilance, Keyword.cantBeBlocked]
      g.draw controller 1)
      none (some "The target is no longer legal. You won't draw a card.")
  | .becomeArtifactCreature44Flying =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.setUntilEotForm o (4, 4) Keyword.flying
        s!"{o.name} becomes a 4/4 artifact creature with flying until end of turn"
        (additionalCreature := true) (additionalArtifact := true))
  | .drawThreeDiscardUnlessArtifact =>
    let g := g.draw controller 3
    let g := { g with thirstDiscardsLeft := 2 }
    g.beginDiscardCards #[controller]
  | .eachOpponentLosesLife n =>
    g.forEachOpponent controller (fun g pid => g.loseLife pid n)
  | .fightUpToOne =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent srcId), some (Target.permanent destId) =>
      g.dealFightDamage (g.object! srcId) (g.object! destId)
    | some (Target.permanent srcId), none =>
      g.logMsg s!"{(g.object! srcId).name} has nothing to fight"
    | _, _ => g.logMsg "The target is no longer legal"
  | .plusOneOnEachYouControl =>
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  | .plusOneOnCreatureN n =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o => g.addPlusOnePlusOneTo o n)
  | .pumpThenDraw p t =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o p t
      g.draw controller 1)
      none (some "The target is no longer legal. You won't draw a card.")
  | .pumpThenExileTopPlay p t =>
    g.withLegalKindPermanent controller .creature targets (fun g o =>
      let g := g.pumpPermanent o p t
      g.exileTopPlayThisTurn controller 1)
      none (some "The target is no longer legal. No card will be exiled.")
  | .creatureYouControlDealsTwicePower =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      g.dealFightDamage (g.object! a) (g.object! b)
    | _, _ => g.logMsg "The target is no longer legal"
  | .createTokensThenTeamPump kind n p t =>
    let g := g.createKindTokens controller kind n
    g.pumpControlledCreatures controller p t
  | .createTokensPerSubtype kind subtype =>
    g.createKindTokens controller kind (g.countSubtype controller subtype)
  | .creaturesYouControlGetAndGrant p t k =>
    let g := g.pumpControlledCreatures controller p t
    let label :=
      match k.toList with
      | [a] => a
      | [a, b] => s!"{a} and {b}"
      | ks => String.intercalate ", " ks
    g.grantUntilEotToControlledCreatures controller k label
  | .destroyUpToOneNonland =>
    g.withLegalKindPermanent controller .nonland targets
      (fun g o => g.destroyPermanent o) none none
  | .createGalactus =>
    g.createNamedToken controller galactusToken
  | .worldsWithinWorlds =>
    g.applyWorldsWithinWorlds controller none
  | .exileHandDrawPlayUntilNext =>
    g.applyLeftoverTextEffect controller
      "Exile all the cards from your hand, then draw that many cards. Until the end of your next turn, you may play cards exiled this way."
      targets none
  | .copyNontokenCreaturesYouControl =>
    g.applyLeftoverTextEffect controller
      "For each nontoken creature you control, create a token that's a copy of that creature, except it isn't legendary."
      targets none
  | .gainControlUntilEotOrNextIfVillain =>
    g.applyLeftoverTextEffect controller
      "Gain control of target creature until end of turn."
      targets none
  | .millThenPutPermanentGainLife n life =>
    g.applyLeftoverTextEffect controller
      s!"Mill {n} cards. You may put a permanent card from among the milled cards into your hand. You gain {life} life."
      targets none
  | .searchLibraryOrGyArtifactCreatureX =>
    g.applyLeftoverTextEffect controller
      "Search your library and/or graveyard for an artifact creature card"
      targets none
  | .gainLifeSearchBasicPlusOne life =>
    g.applyLeftoverTextEffect controller
      s!"Target player gains {life} life. Put a +1/+1 counter"
      targets none
  | .nextFreeRGCreature =>
    { g with pendingFreeRGCreature := some controller }
      |>.logMsg "The next red or green creature spell you cast this turn can be cast without paying its mana cost"
  | .ownerPutsLibraryThenConnive =>
    g.applyOwnerPutsLibraryThenConnive controller targets
  | .copyThisSpellXTimesThenDamage n =>
    g.applyDamageToKindTarget controller .creature targets n
  | .mayDrawPerArtifactOppsDraw =>
    g.applyLeftoverTextEffect controller
      "You may draw a card for each artifact you control. If you do, each opponent draws a card"
      targets none
  | .mayPutHeroMvOrDraw _n =>
    g.applyLeftoverTextEffect controller
      "You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card"
      targets none
  | .maySacArtifactOrDiscardDraw cards =>
    g.applyLeftoverTextEffect controller
      s!"You may sacrifice an artifact or discard a card. If you do, draw {cards} cards."
      targets none
  | .chooseTargetDoubleAndTrample =>
    g.withLegalKindPermanent controller .creatureYouControl targets
      (fun g o =>
        let p := g.power o
        let t := g.toughness o
        let g := g.applyPermanentAction o (.pump p t)
        g.grantUntilEotLogged (g.object! o.id) Keyword.trample) none none
  | .returnUpToTwoGyModal =>
    g.applyLeftoverTextEffect controller
      "Choose up to two. Return those cards from your graveyard to your hand."
      targets none
  | .artifactSpellsCostLessThisTurn _n =>
    g

/-- Resolve a printed spell effect (CR 608). -/
def applyEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (castFromGraveyard := false)
    (kicked := false) (giftPromised := false) (chosenX : Nat := 0) : Game :=
  g.applyUnified controller effect targets
    (castFromGraveyard := castFromGraveyard) (kicked := kicked)
    (giftPromised := giftPromised) (chosenX := chosenX)

/-- Apply `action` if `sourceId` is still on the battlefield. -/
def applyOnSource (g : Game) (sourceId : Option ObjectId) (action : PermanentAction)
    (missing := "The ability's source is no longer in play") : Game :=
  g.withSourceOnBattlefield sourceId (fun g o => g.applyPermanentAction o action) missing

/-- Return a graveyard source to the battlefield tapped or to its owner's hand. -/
def returnSourceFromGraveyard (g : Game) (sourceId : Option ObjectId)
    (controller : PlayerId) (tapped := false) (toHand := false) : Game :=
  match sourceId.bind g.findObject? with
  | none => g.logMsg "The ability's source is no longer in the graveyard"
  | some o =>
    if o.zone != .graveyard o.owner then
      g.logMsg s!"{o.name} is no longer in the graveyard"
    else if toHand then
      g.returnToHand o.id o.owner
    else
      let name := o.name
      let sick := !o.printed.keywords.haste
      let (g, newId) := g.putOntoBattlefield o.id controller (tapped := tapped)
        (summoningSick := sick)
      let g := g.logMsg
        (if tapped then s!"{name} returns to the battlefield tapped"
         else s!"{name} returns to the battlefield")
      g.afterPermanentEnters (g.object! newId)

/-- Resolve a unified activated-ability `Effect` (CR 608). -/
partial def applyUnifiedAbility (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  match effect.resolution with
  | .sequence rs =>
    match rs.flatMap Resolution.flatten with
    | [.shuffleSource, .draw n] =>
      g.shuffleSourceIntoLibrary sourceId (.draw controller n)
    | steps =>
      steps.foldl (fun g r =>
        g.applyUnifiedAbility controller { effect with resolution := r } targets
          sourceId lastKnownPower chosenX) g
  | .shuffleSource =>
    g.shuffleSourceIntoLibrary sourceId
  | .amassGoblins n => g.amassGoblins controller n
  | .discard n =>
    g.beginDiscardCards #[controller] n
  | .spell r =>
    g.applyUnified controller { effect with resolution := .spell r } targets
      (chosenX := chosenX)
  | _ =>
  match effect.abilityResolution with
  | .searchBasicLand => g.resolveSearchBasicLandTapped controller
  | .searchLandTypeToHand t => g.resolveSearchLandTypeToHand controller t
  | .exileTop => g.resolveExileTopPlayUntilEndOfNextTurn controller
  | .attach =>
    g.withLegalKindPermanent controller effect.targetKind targets fun g host =>
      g.withSourceOnBattlefield sourceId (fun g src =>
        if src.attachedTo == some host.id then
          g.logMsg s!"{src.name} is already attached to {host.name}"
        else
          g.attachSourceTo src host)
        "The Equipment is no longer in play"
  | .onPermanent action =>
    g.applyOnPermanent controller effect.targetKind targets action sourceId
  | .onSource action =>
    g.applyOnSource sourceId action
  | .becomeBear =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let subtypes :=
        if g.hasSubtype o "Bear" then o.status.additionalSubtypes
        else o.status.additionalSubtypes.push "Bear"
      let granted :=
        if g.hasLandsYouControlPT o then o.status.grantedStaticAbilities
        else o.status.grantedStaticAbilities.push .powerToughnessEqualLandsYouControl
      let g := g.mapObjectStatus o (fun s =>
        { s with
          additionalCreature := true
          additionalSubtypes := subtypes
          grantedStaticAbilities := granted })
      g.logMsg
        s!"{o.name} becomes a Bear creature. Its power and toughness are each equal to the number of lands you control"
  | .returnFromGraveyardTapped =>
    g.returnSourceFromGraveyard sourceId controller (tapped := true)
  | .returnFromGraveyardToHand =>
    g.returnSourceFromGraveyard sourceId controller (toHand := true)
  | .creaturesYouControlPump pw tw =>
    g.pumpControlledCreatures controller pw tw
  | .mill n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.mill pid n)
  | .addAnyColor =>
    let g := g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
    g.logMsg s!"{(g.player controller).name} adds one mana of any color"
  | .recruit =>
    g.beginRecruit controller
  | .scry n =>
    g.beginScry controller n
  | .gainLife n =>
    g.gainLife controller n
  | .createTokens kind n =>
    g.createKindTokens controller kind n
  | .returnFromGyAttach =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "The source is no longer in the graveyard"
    | some src =>
      g.withLegalKindPermanent controller effect.targetKind targets (fun g host =>
        let (g, newId) := g.putOntoBattlefield src.id controller
          (attachedTo := some host.id)
        let o := g.object! newId
        let g := g.logMsg s!"{o.name} enters the battlefield attached to {host.name}"
        g.afterPermanentEnters (g.object! newId))
        sourceId (some "The target is no longer legal. Eagle's Rescue remains in the graveyard.")
  | .addMana types =>
    g.addManaLogged controller types
  | .searchBasicLandToHand =>
    g.resolveSearchBasicLandToHand controller
  | .createTokensX kind =>
    g.createKindTokens controller kind 1
  | .draw n =>
    g.draw controller n
  | .searchTwoBasicsSplit =>
    g.resolveLibrarySearch controller isBasicLandCard "basic land card"
      fun g cardId =>
        let cardName := (g.object! cardId).name
        let (g, _) := g.move cardId .battlefield (some controller)
        let g :=
          match g.findObject? cardId with
          | some o => g.setObject { o with status := { o.status with tapped := true } }
          | none => g
        g.logMsg s!"{(g.player controller).name} puts {cardName} onto the battlefield tapped"
  | .subtypesGainMenace subtypes =>
    g.grantUntilEotToControlledCreatures controller Keyword.menace "menace"
      (fun g o => subtypes.any (g.hasSubtype o))
  | .exileThenReturnNextEnd =>
    -- Return immediately for this engine (next end step is modeled as a
    -- delayed return at the next end step via eagles-style bookkeeping:
    -- bounce now, then put back tapped next end).
    g.foldPermanentTargets targets (fun g o =>
      if o.controlledBy controller && !o.printed.isLand && some o.id != sourceId then
        g.exileThenReturn o "is exiled, then returned" (clearExileFields := true)
      else g)
  | .searchBasicBeholdElfUntap =>
    let g := g.resolveSearchBasicLandTapped controller
    let g := g.beholdQuality controller "Elf"
    if g.qualityWasBeheld controller "Elf" then
      match (g.permanentsOf controller).find? (fun o => o.printed.isLand && o.status.tapped) with
      | none => g
      | some land => g.applyPermanentAction land .untap
    else g
  | .twoPlayersDraw =>
    match targets[0]?, targets[1]? with
    | some (Target.player a), some (Target.player b) =>
      if a == b then g.logMsg "Two target players must be different"
      else g.draw a 1 |>.draw b 1
    | _, _ => g.logMsg "The targets are no longer legal"
  | .discardLegendarySameNameDraw =>
    g.draw controller 2
  | .dealDamageToAny n =>
    g.applyEffect controller (Effect.dealDamage n) targets
  | .drawEqualSacrificedPowerThenDiscard =>
    let n :=
      match sourceId.bind g.findObject? with
      | some src => (g.power src).toNat
      | none => 1
    g.drawThenBeginDiscard controller (max n 1)
  | .arwenShare =>
    match sourceId, targets[0]? with
    | some sid, some (Target.permanent tid) => g.resolveArwenShare sid (some tid)
    | some sid, _ => g.resolveArwenShare sid none
    | _, _ => g.logMsg "The ability's source is no longer in play"
  | .grantCombatDamageCreateTreasure =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with combatDamageCreatesTreasure := true })
      g.logMsg
        s!"{o.name} gains \"Whenever this creature deals combat damage to a player, create a Treasure token\"")
      sourceId (some "The target is no longer legal")
  | .putShadowCounter =>
    g.withLegalKindPermanent controller effect.targetKind targets (fun g o =>
      g.putShadowCounter o) sourceId (some "The target is no longer legal")
  | .damageEachOpponent n =>
    g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid n)
  | .chooseTwoDestroyRest =>
    let keep :=
      targets.filterMap (fun | Target.permanent id => some id | _ => none)
    Id.run do
      let mut g := g
      for o in g.battlefield do
        if o.isCreature && !keep.contains o.id then
          g := g.destroyPermanent o
      return g.logMsg "Chosen creatures are kept; the rest are destroyed"
  | .blackGateUnblockable =>
    match targets[0]? with
    | some (Target.permanent oid) =>
      match g.playersWithMostLife[0]? with
      | some pid => g.applyBlackGateUnblockable oid pid
      | none => g
    | _ => g.logMsg "The target is no longer legal"
  | .burdenThenDraw =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with burden := o.status.burden + 1 } }
      let n := (g.object! o.id).status.burden
      let g := g.logMsg s!"{o.name} gets a burden counter ({n})"
      g.draw controller n
  | .teamGainDoubleStrike =>
    g.grantUntilEotToControlledCreatures controller Keyword.doubleStrike
      "double strike"
  | .sourceGainsIndestructibleTap =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.mapObjectStatus o (·.grantUntilEot Keyword.indestructible)
      let o := g.object! o.id
      let g := g.setObject { o with status := { o.status with tapped := true } }
      g.logMsg s!"{o.name} gains indestructible until end of turn and becomes tapped"
  | .plusOneOnEachOtherSubtype subtype n =>
    g.foldBattlefield (fun o =>
        o.controlledBy controller && o.id != sourceId.getD ⟨0⟩ && g.hasSubtype o subtype)
      (fun g o => g.mapObjectStatus o (fun s =>
        { s with plusOnePlusOne := s.plusOnePlusOne + n }))
  | .plusOneAndIndestructibleCounter =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1
        indestructibleCounters := o.status.indestructibleCounters + 1 } }
  | .plusOneAndExtraTurn =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
      g.logMsg s!"{(g.player controller).name} takes an extra turn after this one"
  | .plusOneX =>
    g.withSourceOnBattlefield sourceId fun g o =>
      g.addPlusOnePlusOneTo o chosenX
  | .eachOppDiscardThenPlusOne =>
    let g :=
      (g.livingOpponents controller).foldl (fun acc pl =>
        acc.beginDiscardCards #[pl.id]) g
    g.withSourceOnBattlefield sourceId fun g o =>
      g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 1 } }
  | .lookAtTopPutHeroEquipVehicle n =>
    g.withSourceOnBattlefield sourceId fun g o =>
      let g := g.setObject { o with status := { o.status with
        plusOnePlusOne := o.status.plusOnePlusOne + 2 } }
      g.logLookAtTop controller n
  | .transform =>
    g.withSourceOnBattlefield sourceId fun g o =>
      if o.status.cantTransform then
        g.logMsg s!"{o.name} can't transform (entered back face up at night)"
      else
        match o.printed.otherFace with
        | none => g.logMsg s!"{o.name} has no other face"
        | some face =>
          let back := { face with otherFace := some { o.printed with otherFace := none } }
          let g := g.setObject { o with
            printed := back
            status := { o.status with transformed := !o.status.transformed } }
          g.logMsg s!"{o.name} transforms into {back.name}"
  | .drawX =>
    g.draw controller chosenX
  | .lookAtTopRevealArtifact n =>
    g.logLookAtTop controller n
  | .connive =>
    g.applyConnive controller sourceId
  | .addAnyColorSpendOnlyHero =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .white) 1 (heroRestricted := true) })
  | .addAnyColorSpendOnlyVillain =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .black) 1 (villainRestricted := true) })
  | .addAnyColorSpendOnlyArtifactSpell =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 1 })
  | .addTwoAnyColorCreatureSources =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .green) 2 (creatureRestricted := true) })
  | .addBlueCantNonartifact =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .blue) 1 (cantNonartifact := true) })
  | .addAnyColorEqualToSourcePower =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o => (g.power o).toNat
      | none => 0
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .green) x })
  | .addFourAnyCombination =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) 4 })
  | .addTwoAnyColorEquipment =>
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool :=
        pl.manaPool.add (.colored .white) 2 })
  | .drawPerDiscardedThisTurn =>
    g.draw controller (g.player controller).cardsDiscardedThisTurn
  | .dealDamageToEachCreature n =>
    g.dealDamageToEachCreatureMatching n
  | .createTokensEqualRemovedPlusOnes kind =>
    g.createKindTokens controller kind 1
  | .exileTopXPlayThisTurn =>
    let x := g.sourcePowerNatAtResolution sourceId lastKnownPower
    g.exileTopPlayThisTurn controller x
  | .targetPlayerDraw n =>
    g.withLegalKindPlayer controller effect.targetKind targets
      (fun g pid => g.draw pid n)
  | .copyControlledAbility _ =>
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == .stack then g.copyStackAbility o controller
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g
  | .createTokensEqualSubtype kind subtype =>
    let n := g.countSubtype controller subtype
    g.createKindTokens controller kind n
  | .createTappedTokens kind n =>
    g.createKindTokens controller kind n (tapped := true)
  | .proliferateEachKind =>
    g.applyLeftoverTextEffect controller
      (Effect.proliferateEachKind.phrase) targets sourceId
  | .equipmentBecomesConstructHero =>
    match sourceId.bind g.findObject? with
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The Equipment is no longer in play"
      else if o.isCreature then
        g.logMsg s!"{o.name} is already a creature"
      else
        let wasAttached := o.attachedTo.isSome
        let g :=
          if wasAttached then
            g.setObject { o with attachedTo := none }
              |>.logMsg s!"{o.name} becomes unattached"
          else g
        let o := g.object! o.id
        g.setUntilEotForm o (0, 0) Keyword.flying
          s!"{o.name} becomes a 0/0 Construct Hero artifact creature"
          (types := some #["Construct", "Hero"])
          (additionalCreature := true) (additionalArtifact := true)
          (pumpPerArtifact := true)
    | none => g.logMsg "The Equipment is no longer in play"
  | .lookAtTopRevealSubtype n _subtype =>
    g.logLookAtTop controller n
  | .millThenPutHeroOrEnchantment n =>
    g.applyLeftoverTextEffect controller
      ((Effect.millThenPutHeroOrEnchantment n).phrase) targets sourceId
  | .plusOneAndDoubleStrikeCounter =>
    g.applyLeftoverTextEffect controller
      (Effect.plusOneAndDoubleStrikeCounter.phrase) targets sourceId
  | .plusOneThenFightUpToOne =>
    g.applyLeftoverTextEffect controller
      (Effect.plusOneThenFightUpToOne.phrase) targets sourceId
  | .plusOneAndCreateTigerGod =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
        "The source is no longer in play"
    g.createNamedToken controller tigerGodToken
  | .plusTwoThenOddEvenDestroy =>
    g.applyLeftoverTextEffect controller
      (Effect.plusTwoThenOddEvenDestroy.phrase) targets sourceId
  | .returnFromGyFinalityAttach =>
    g.applyLeftoverTextEffect controller
      (Effect.returnFromGyFinalityAttach.phrase) targets sourceId
  | .returnGyCreatureThenPlusOne n =>
    g.applyLeftoverTextEffect controller
      ((Effect.returnGyCreatureThenPlusOne n).phrase) targets sourceId
  | .revealTopDrawIfArtifact =>
    g.applyLeftoverTextEffect controller
      (Effect.revealTopDrawIfArtifact.phrase) targets sourceId
  | .copyArtifactYouControlNotLegendary =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      match g.findObject? a, g.findObject? b with
      | some dest, some src =>
        if dest.isOnBattlefield && src.isOnBattlefield &&
            dest.controlledBy controller && src.controlledBy controller &&
            dest.printed.isArtifact && src.printed.isArtifact then
          g.becomeCopyOf dest src (untilEot := true) (notLegendary := true)
        else
          g.logMsg "The target is no longer legal. The ability has no effect."
      | _, _ =>
        g.logMsg "The target is no longer legal. The ability has no effect."
    | _, _ =>
      g.logMsg "The target is no longer legal. The ability has no effect."
  | .pumpAttackingAloneGainLife =>
    g.withLegalKindPermanent controller .creatureYouControl targets (fun g o =>
      let g := g.pumpPermanent o 1 0
      g.gainLife controller 1)
      sourceId (some "The target is no longer legal. You won't gain life.")
  | .becomeDinosaurHero p t k =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.setUntilEotForm o (p, t) k
        s!"{o.name} becomes a {p}/{t} Dinosaur Hero"
        (types := some #["Dinosaur", "Hero"]))
      "The source is no longer in play"
  | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
    let pw :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.power o else o.power
      | none => (0 : Int)
    { g with pendingLokiCopy := some (controller, sourceId, pw) }
      |>.logMsg s!"The next instant or sorcery with mana value {pw} or less will be copied"
  | .harnessInfinityStone =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.mapObjectStatus o (fun s => { s with harnessed := true })
      g.logMsg s!"{o.name} is harnessed") "The source is no longer in play"
  | .destroyTargetNoncreatureArtOrEnch =>
    g.withLegalKindPermanent controller .noncreatureArtifactOrEnchantment targets
      (fun g o => g.applyPermanentAction o .destroy) sourceId none
  | .targetSubtypeConnives _ =>
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller none

/-- Resolve a printed activated ability (CR 608). -/
def applyAbilityEffect (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (sourceId : Option ObjectId := none)
    (lastKnownPower : Option Int := none) (chosenX : Nat := 0) : Game :=
  g.applyUnifiedAbility controller effect targets
    sourceId lastKnownPower chosenX

end Game
end Mtg.Engine
