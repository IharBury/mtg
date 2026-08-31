import Mtg.Engine.Game.ResolutionEffects

/-!
# Modeled trigger resolution

`applyModeledTrigger` — resolving the shared-trigger payloads — leftover
rules-text effects, and boast, teamwork, and pay-or-counter helpers.
-/

namespace Mtg.Engine
namespace Game

/-- The lone attacking creature `p` controls, if exactly one is attacking. -/
def attackingAlone? (g : Game) (p : PlayerId) : Option GameObject :=
  let xs := (g.permanentsOf p).filter (fun o => o.isCreature && o.status.attacking)
  if xs.size == 1 then some xs[0]! else none

/-- Permanent this Aura or Equipment is attached to. -/
def attachedHost? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind g.findObject? |>.bind (fun src => src.attachedTo.bind g.findObject?)

/-- Newest non-ability object on the stack (the spell that caused a cast trigger). -/
def lastStackSpell? (g : Game) : Option GameObject :=
  g.stack.foldl (fun acc e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.triggeredAbility.isNone && o.abilityEffect.isNone then some o else acc
    | none => acc) none

/-- 1/1 blue Merfolk creature token (Namora / similar leftover cast triggers). -/
def merfolk11blueToken : CardDef :=
  creatureToken "Merfolk" #["Merfolk"] 1 1 (some .blue)

/-- Copy a keyword counter onto Super-Adaptoid when the other creature has it. -/
def copyKeywordCounter (g : Game) (adaptoid other : GameObject)
    (has : GameObject → Bool) (kw : Keywords) (name : String) : Game :=
  if has other && !has adaptoid then
    let src := g.object! adaptoid.id
    g.setObject { src with
        printed := { src.printed with
          keywords := Keywords.merge src.printed.keywords kw } }
      |>.logMsg s!"{src.name} gets a {name} counter"
  else g

/-- Exile from `pid`'s library until a nonland is exiled. -/
def exileLibraryUntilNonland (g : Game) (pid : PlayerId) : Game × Option ObjectId :=
  Id.run do
    let mut g := g
    let mut found : Option ObjectId := none
    while found.isNone && !(g.player pid).library.isEmpty do
      match (g.player pid).library.back? with
      | none => pure ()
      | some id =>
        let (g', newId) := g.move id .exile none
        g := g'
        let o := g.object! newId
        g := g.logMsg s!"{(g.player pid).name} exiles {o.name}"
        if !o.printed.isLand then found := some newId
    return (g, found)

/-- Resolve a modeled leftover trigger from its `SharedTrigger` constructor.
Effects are applied from that structured payload — not from Oracle text. -/
def applyModeledTrigger (g : Game) (controller : PlayerId) (t : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (sourceName : String := "This creature")
    (lastKnownPower : Option Int := none) : Game :=
  match t.shared with
  | (.step .copyAbsorbingMan) =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          g.becomeCopyOf src tgt (untilNextTurn := true)
            (exceptName := some "Absorbing Man")
            (forceLegendary := true) (addCreature := true)
            (addSubtypes := #["Human", "Villain"])
            (setPT := some (4, 4)) (addVigilance := true)
        | none => g
      | _ => g) "The source is no longer in play"
  | (.step .copyTaskmaster) =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) | some (Target.card id) =>
        match g.findObject? id with
        | some tgt =>
          g.becomeCopyOf src tgt (untilNextTurn := true)
            (exceptName := some "Taskmaster, Mercenary Mimic")
            (forceLegendary := true) (addCreature := true)
            (addSubtypes := #["Human", "Mercenary", "Villain"])
        | none => g
      | _ => g) "The source is no longer in play"
  | (.watch .sheHulkRedirectOnce) =>
    if g.sheHulkDamageUsedThisTurn then
      g.logMsg "The Sensational She-Hulk already dealt damage this turn. The ability has no effect."
    else
      let amt := lastKnownPower.getD 0
      let g :=
        g.withLegalKindTarget controller .playerOrCreature targets
          (fun g tgt => g.dealDamageToTarget tgt amt) sourceId none
      { g with sheHulkDamageUsedThisTurn := true }
        |>.logMsg "The Sensational She-Hulk deals damage (only once each turn)"
  | (.watch .hawkeyeModes) =>
    let paid := (lastKnownPower.getD (0 : Int)).toNat
    g.queueModeledReflexiveIfPaid controller sourceId 2 paid
      "Hawkeye didn't pay. The reflexive ability doesn't trigger."
  | (.thisAttack .equippedDrain) =>
    let x :=
      match sourceId.bind g.findObject? with
      | some o =>
        if o.isOnBattlefield then g.attachedEquipmentCount o
        else (lastKnownPower.getD (0 : Int)).toNat
      | none => (lastKnownPower.getD (0 : Int)).toNat
    if x == 0 then
      g.logMsg "Whiplash isn't equipped"
    else
      let g := g.forEachOpponent controller (fun g pid => g.loseLife pid x)
      g.gainLife controller x
  | (.thisAttack .drawIfPower4) =>
    let pw := g.sourcePowerAtResolution sourceId lastKnownPower
    if pw >= 4 then g.draw controller 1
    else g.logMsg "Viv Vision's power is not 4 or greater"
  | (.watch .hulklingCompare) =>
    g.withSourceOnBattlefield sourceId (fun g hulkling =>
      let entered :=
        match targets[0]? with
        | some (Target.permanent id) => g.findObject? id
        | _ =>
          let cands := (g.permanentsOf controller).filter (fun (x : GameObject) =>
            x.isCreature && x.id != hulkling.id && x.status.enteredThisTurn)
          if cands.isEmpty then none
          else some (cands.foldl (fun (acc : GameObject) (x : GameObject) =>
            if x.timestamp > acc.timestamp then x else acc) cands[0]!)
      match entered with
      | none => g
      | some other =>
        let op := if other.isOnBattlefield then g.power other
          else other.lastKnownPower.getD (g.power other)
        let ot := if other.isOnBattlefield then g.toughness other
          else other.lastKnownToughness.getD (g.toughness other)
        if op > g.power hulkling || ot > g.toughness hulkling then
          g.addPlusOnePlusOneTo hulkling 1
        else g) "The source is no longer in play"
  | (.watch .firstTapUntap) =>
    match g.lastBecameTapped.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield && o.status.tapped then
        g.applyPermanentAction o .untap
      else g
    | none => g
  | (.watch .hulk) =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o =>
        let g := g.addPlusOnePlusOneTo o 1
        if o.status.attacking then
          g.applyPermanentAction o .untap
        else g) "The source is no longer in play"
    if g.enrageGrantsAdditionalCombat > 0 then
      { g with
          enrageGrantsAdditionalCombat := g.enrageGrantsAdditionalCombat - 1
          additionalCombatPhases := g.additionalCombatPhases + 1 }
        |>.logMsg "There is an additional combat phase after this phase"
    else g
  | (.watch .redHulk) =>
    match sourceId.bind g.findObject? with
    | some o =>
      if o.isOnBattlefield then
        let g := g.addPlusOnePlusOneTo o 1
        let o := g.object! o.id
        g.queueModeledReflexive controller sourceId 8 o.status.plusOnePlusOne
      else
        g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
    | none =>
      g.logMsg "Red Hulk is no longer on the battlefield. The reflexive ability doesn't trigger."
  | (.thisAttack .payReturnAttacking) =>
    g.queueModeledReflexiveIfPaid controller sourceId 6
      (lastKnownPower.getD (0 : Int)).toNat
      "Grim Reaper's cost wasn't paid. The reflexive ability doesn't trigger."
  | (.casting .mayPayHasteUnblockable) =>
    g.queueModeledReflexiveIfPaid controller sourceId 9
      (lastKnownPower.getD (0 : Int)).toNat
      "Speed's cost wasn't paid. The reflexive ability doesn't trigger."
  | (.watch .speedballTargeted) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.pumpPermanent o 2 2)
      "Speedball is no longer on the battlefield"
  | (.youAttacking .exileTopHeroPump) =>
    -- Daredevil: exile the top card. Hero-ness only affects the pump;
    -- the card may be played this turn either way (MSH 333).
    let top? := (g.player controller).library.back?
    let isHero :=
      match top? with
      | some top => (g.object! top).hasSubtype "Hero"
      | none => false
    let g := g.exileTopPlayThisTurn controller 1
    if isHero then
      g.withSourceOnBattlefield sourceId (fun g src => g.pumpPermanent src 2 1)
        "Daredevil is no longer on the battlefield"
    else g
  | (.youAttacking .pay2LifeToughness) =>
    g.ifPaid (lastKnownPower.getD (0 : Int)).toNat "The Kingpin's cost wasn't paid"
      fun g =>
        { g with assignCombatDamageEqualToughness := some controller }
          |>.logMsg "Creatures you control assign combat damage equal to their toughness"
  | (.watch .villainPlusOneDamageOnce) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.addPlusOnePlusOneTo o 1
      g.forEachOpponent controller (fun g pid =>
        g.dealDamageToPlayer pid 2 (source := some (g.object! o.id))))
      "Crossbones is no longer on the battlefield"
  | (.watch .villainConniveOnce) =>
    match sourceId.bind g.findObject? with
    | none =>
      g.logMsg "Baron Strucker is no longer on the battlefield. The ability has no effect."
    | some src =>
      if src.status.optionalOnceUsed then
        g.logMsg
          "The optional connive was already chosen this turn. This instance has no effect."
      else
        match g.villainConniveTarget? controller src.id targets lastKnownPower with
        | none =>
          g.logMsg "The Villain does not connive"
        | some vid =>
          g.beginMayHaveVillainConnive controller src.id vid
  | (.death .attackingReturnHand) =>
    match g.lastDiedAttacker.bind g.findObject? with
    | none => g.logMsg "The attacking creature is no longer in the graveyard"
    | some o =>
      if o.printed.isToken then
        g.logMsg s!"{o.name} ceases to exist"
      else
        g.returnToHand o.id o.owner
  | (.watch .ultronCopy) =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some src =>
        if src.isOnBattlefield && src.printed.isArtifact && !src.printed.isToken then
          let (g, tok) := g.copyBattlefieldPermanent src controller
          let tok := g.object! tok.id
          let g := g.afterPermanentEnters tok
          let tok := g.object! tok.id
          if tok.isCreature then g
          else
            let printed :=
              { tok.printed with
                types :=
                  if tok.printed.types.any (· == .creature) then tok.printed.types
                  else tok.printed.types.push .creature
                subtypes := mergeSubtypes tok.printed.subtypes #["Robot", "Villain"]
                power := some 2
                toughness := some 2 }
            g.setObject { tok with printed }
              |>.logMsg s!"{printed.name} becomes a 2/2 Robot Villain creature after it enters"
        else g
      | none => g
    | _ => g
  | (.death .villainReturnAsHero) =>
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard o.owner && g.hasSubtype o "Villain" then
          let owner := o.owner
          let (g, newId) := g.putOntoBattlefield id owner
          let o := g.object! newId
          let subtypes :=
            if o.printed.subtypes.any (· == "Hero") then o.printed.subtypes
            else o.printed.subtypes.push "Hero"
          let g := g.setObject { o with
            printed := { o.printed with subtypes }
            status := { o.status with finality := o.status.finality + 1 } }
          g.afterPermanentEnters (g.object! newId)
        else g
      | none => g
    | _ => g
  | (.casting .villainToken) =>
    g.createKindTokens controller .villain21menace 1
  | (.enterOrAttack .createSquirrel) =>
    g.createKindTokens controller .squirrel11green 1
  | (.resource .plusOneCreateInsectOnce) =>
    g.createKindTokens controller .insect11green 1
  | (.resource .plusOneOnHeroesCreateWall) =>
    g.createKindTokens controller .wall04defender 1
  | (.resource .secondDrawBecome66) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with
          setBasePT := some (6, 6)
          untilEotKeywords := Keywords.merge s.untilEotKeywords Keyword.trample })
        |>.logMsg s!"{o.name}'s base power and toughness become 6/6")
      "The source is no longer in play"
  | (.casting .visionModes) =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.status.chosenModes.size >= 3 then
        g.logMsg "The Vision's ability is removed from the stack with no effect"
      else
        let mode := (lastKnownPower.getD 0).toNat
        let g := g.mapObjectStatus src (fun s =>
          { s with chosenModes := s.chosenModes.push mode })
        if mode == 0 then
          g.mapObjectStatus (g.object! src.id)
            (·.grantUntilEot Keyword.doubleStrike)
        else if mode == 1 then
          g.mapObjectStatus (g.object! src.id)
            (·.grantUntilEot Keyword.indestructible)
        else
          g.draw controller 1
    | none => g.logMsg "The Vision is no longer in play"
  | (.casting .ironFistTap) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with ironFistTapGrants := s.ironFistTapGrants + 1 })
        |>.logMsg s!"{o.name} gains a tap ability until end of turn")
      "The source is no longer in play"
  | (.casting .drawPowerEqualHand) =>
    let g := g.draw controller 1
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.mapObjectStatus o (fun s =>
        { s with grantedStaticAbilities :=
            s.grantedStaticAbilities.push .powerEqualCardsInHand })
        |>.logMsg s!"{o.name}'s base power is the number of cards in your hand")
      "The source is no longer in play"
  | (.step .hydeChoose) =>
    let mode := (lastKnownPower.getD 0).toNat
    if mode == 0 then
      g.withSourceOnBattlefield sourceId (fun g o =>
        g.addPlusOnePlusOneTo o 1) "The source is no longer in play"
    else
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.controlledBy controller &&
              o.status.plusOnePlusOne > 0 then
            let g := g.mapObjectStatus o (fun s =>
              { s with plusOnePlusOne := s.plusOnePlusOne - 1 })
            g.draw controller 1
          else
            g.logMsg "You must remove a counter from a creature you control if you can"
        | none =>
          g.logMsg "You must remove a counter from a creature you control if you can"
      | _ =>
        if (g.permanentsOf controller).any (fun o =>
            o.isCreature && o.status.plusOnePlusOne > 0) then
          g.logMsg "You must remove a counter from a creature you control if you can"
        else g
  | (.resource .drawIfAnotherHeroDamage) =>
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o "Hero" && some o.id != sourceId) then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 1
        | _ => g) sourceId none
    else
      g.logMsg "Human Torch's ability has no effect"
  | (.step .drawToTen) =>
    let n := 10 - (g.player controller).hand.size
    if n > 0 then g.draw controller n
    else g.logMsg "You already have ten or more cards in hand"
  | (.step .harnessedFlicker) =>
    match sourceId.bind g.findObject? with
    | some src =>
      if !src.status.harnessed then
        g.logMsg "The Mind Stone is not harnessed"
      else
        match targets[0]? with
        | some (Target.permanent id) =>
          match g.findObject? id with
          | some o =>
            if o.isOnBattlefield && o.id != src.id then
              let (g, newId) :=
                let g := g.exileUntilSourceLeaves sourceId o
                match g.objects.find? (fun x =>
                  x.name == o.name && x.zone == .exile) with
                | some ex => (g, ex.id)
                | none => (g, id)
              g.returnExiledId newId
            else g
          | none => g.logMsg "The target is no longer legal"
        | _ => g
    | none => g
  | (.watch .enchantedAttachEquipment) =>
    match sourceId.bind g.findObject? with
    | some src =>
      match src.attachedTo.bind g.findObject? with
      | none =>
        g.logMsg "The enchanted creature has left. Equipment stays where it is."
      | some host =>
        targets.foldl (fun (g : Game) (t : Target) =>
          match t with
          | Target.permanent id =>
            match g.findObject? id with
            | some eq =>
              if eq.isOnBattlefield && eq.printed.isEquipment then
                g.attachSourceTo eq host
              else g
            | none => g
          | _ => g) g
    | none =>
      g.logMsg "The enchanted creature has left. Equipment stays where it is."
  | (.watch .villainAttachEquipment) =>
    match targets[0]?, targets[1]? with
    | some (Target.permanent eqId), some (Target.permanent crId) =>
      match g.findObject? eqId, g.findObject? crId with
      | some eq, some cr =>
        if eq.isOnBattlefield && cr.isOnBattlefield && eq.printed.isEquipment then
          g.attachSourceTo eq cr
        else
          g.logMsg "The Equipment won't move"
      | _, _ => g.logMsg "The Equipment won't move"
    | _, _ => g.logMsg "The Equipment won't move"
  | (.thisAttack .ifArtifactEnteredDraw) =>
    if (g.player controller).artifactEnteredThisTurn then
      g.draw controller 1
    else
      g.logMsg "No artifact entered under your control this turn. Iron Man's ability doesn't trigger."
  | (.youAttacking .lookSixCast) =>
    g.beginMayCastFromLooked controller 6 (g.greatestPowerAmongAttacking controller)
  | (.step .enchantedControllerDraws) =>
    match g.attachedHost? sourceId with
    | some host =>
      match host.controller with
      | some pid => g.draw pid 1
      | none => g.draw host.owner 1
    | none =>
      g.logMsg "The enchanted creature has left. No card is drawn."
  | (.death .hellcatReturn) =>
    match sourceId.bind g.findObject? with
    | none => g.logMsg "Hellcat is no longer in the graveyard"
    | some o =>
      if o.zone != .graveyard o.owner then
        g.logMsg "Hellcat is no longer in the graveyard"
      else
        let owner := o.owner
        let (g, newId) := g.putOntoBattlefield o.id owner
        let o := g.object! newId
        let g := g.setObject { o with
          printed := { o.printed with
            keywords := Keyword.haste
            triggeredAbilities := #[]
            activatedAbilities := #[]
            staticAbilities := #[] }
          status := { o.status with
            losesAbilitiesGrantedBy := o.status.losesAbilitiesGrantedBy.push newId } }
        let o := g.object! newId
        let g := g.addPlusOnePlusOneTo o 1
        g.afterPermanentEnters (g.object! newId)
          |>.logMsg s!"{o.name} returns, loses all abilities, and gains haste"
  | (.death .deathtouchOppSac) =>
    (g.livingOpponents controller).foldl (fun (g : Game) pl =>
      match (g.permanentsOf pl.id).find? (fun o => o.isCreature && !o.printed.isToken) with
      | some o => g.sacrificeToGraveyard o
          s!"{(g.player pl.id).name} sacrifices {o.name}"
      | none =>
        g.logMsg s!"{(g.player pl.id).name} has no nontoken creature to sacrifice") g
  | (.thisAttack .mayPayPlusOne) =>
    g.ifPaid (lastKnownPower.getD (0 : Int)).toNat "Ant-Man's cost wasn't paid"
      fun g =>
        g.withLegalKindPermanent controller .creature targets
          (fun g o => g.addPlusOnePlusOneTo o 1) sourceId
          (some "The target is no longer legal")
  | (.thisAttack .blinkNontoken) =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && !o.printed.isToken &&
            (o.printed.isArtifact || o.isCreature) then
          let owner := o.owner
          let name := o.name
          let (g, newId) := g.move o.id .exile none
          let (g, retId) := g.move newId .battlefield (some owner)
          let ret := g.object! retId
          let g := g.setObject { ret with
            status := { ret.status with
              tapped := true
              summoningSick := !ret.printed.keywords.haste } }
          g.afterPermanentEnters (g.object! retId)
            |>.logMsg s!"{name} is exiled, then returned tapped"
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g
  | (.thisAttack .attacksAlonePlus2Indestructible) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.pumpPermanent o 2 0
      g.grantUntilEotLogged (g.object! o.id) Keyword.indestructible)
      "The source is no longer in play"
  | (.enterOrAttack .copyKeywords) =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some other =>
          if !other.isOnBattlefield || other.id == src.id then g
          else
            let g := g.copyKeywordCounter src other g.hasHaste Keyword.haste "haste"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasFlying Keyword.flying "flying"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasFirstStrike Keyword.firstStrike
              "first strike"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasDoubleStrike Keyword.doubleStrike
              "double strike"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasDeathtouch Keyword.deathtouch
              "deathtouch"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasIndestructible Keyword.indestructible
              "indestructible"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasLifelink Keyword.lifelink "lifelink"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasMenace Keyword.menace "menace"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other
              (fun o => g.hasKeyword o (·.reach)) Keyword.reach "reach"
            let src := g.object! src.id
            let g := g.copyKeywordCounter src other g.hasTrample Keyword.trample "trample"
            let src := g.object! src.id
            g.copyKeywordCounter src other g.hasVigilance Keyword.vigilance "vigilance"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "The target is no longer legal")
      "The source is no longer in play"
  | (.watch .combatDamageExileUntilNonland) =>
    let pid :=
      match targets[0]? with
      | some (Target.player p) => some p
      | _ =>
        match (g.livingOpponents controller)[0]? with
        | some pl => some pl.id
        | none => none
    match pid with
    | none => g
    | some pid =>
      let (g, nonland?) := g.exileLibraryUntilNonland pid
      if (lastKnownPower.getD 1) != 0 then
        g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
          "Black Widow is no longer on the battlefield"
      else
        match nonland? with
        | none => g
        | some id =>
          let o := g.object! id
          g.setObject { o with
              playPermission := some {
                player := controller
                turnEndsRemaining := 1
                anyMana := true } }
            |>.logMsg
              s!"{(g.player controller).name} may cast {o.name} until end of turn"
  | (.watch .attacksAloneDrain) =>
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid =>
        let g := g.loseLife pid 1
        g.gainLife controller 1
      | _ => g) sourceId none
  | (.watch .attacksAloneFirstStrikeMenace) =>
    match g.attackingAlone? controller with
    | none => g.logMsg "No creature is attacking alone"
    | some o =>
      let g := g.grantUntilEotLogged o Keyword.firstStrike
      g.grantUntilEotLogged (g.object! o.id) Keyword.menace
  | (.watch .anyPlayerSecondDraw) =>
    g.draw controller 1
  | (.watch .youTargetDrawOnce) =>
    g.draw controller 1
  | (.watch .villainOrArtifactDamage) =>
    g.withLegalKindTarget controller .opponent targets (fun g tgt =>
      match tgt with
      | Target.player pid => g.dealDamageToPlayer pid 1
      | _ => g) sourceId none
  | (.watch .villainPlusOneLifelink) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      let g := g.pumpPermanent o 1 0
      g.grantUntilEotLogged (g.object! o.id) Keyword.lifelink)
      "The source is no longer in play"
  | (.watch .justiceBounce) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | (.watch .nontokenHeroModal) =>
    let mode := (lastKnownPower.getD 0).toNat
    if mode == 0 then
      g.createKindTokens controller .soldier11white 1
    else
      g.pumpControlledCreatures controller 1 1
  | (.watch .equippedAttacksAloneUntapScry) =>
    match g.attachedHost? sourceId with
    | some host =>
      if host.isOnBattlefield then
        let g := g.applyPermanentAction host .untap
        g.beginScry controller 1
      else g.logMsg "The equipped creature has left"
    | none => g.logMsg "The equipped creature has left"
  | (.watch .equippedAttacksTap) =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.applyPermanentAction o .tap) sourceId
      (some "The target is no longer legal")
  | (.watch .equippedTappedDamage) =>
    match g.attachedHost? sourceId with
    | some host =>
      g.forEachOpponent controller (fun g pid =>
        g.dealDamageToPlayer pid 1 (source := some host))
    | none =>
      g.forEachOpponent controller (fun g pid => g.dealDamageToPlayer pid 1)
  | (.watch .heroesDamagePlusTwo) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 2)
      "The source is no longer in play"
  | (.watch .merfolkAttackDraw) =>
    g.draw controller 1
  | (.watch .tokensEnterMayDraw) =>
    g.ifPaid (lastKnownPower.getD 1).toNat "The optional draw was declined"
      fun g => g.draw controller 1
  | (.casting .merfolkFromBlue) =>
    let n :=
      match lastKnownPower with
      | some p => p.toNat
      | none =>
        match g.lastStackSpell? with
        | some o => o.printed.manaCost.symbolsIncludingColor .blue
        | none => 0
    if n == 0 then
      g.logMsg "No blue mana symbols. No Merfolk are created."
    else
      Id.run do
        let mut g := g
        for _ in [0:n] do
          let (g', _) := g.createToken controller merfolk11blueToken
          g := g'
        return g
  | (.casting .plusOneEachOther) =>
    g.forEachControlledCreature controller (fun g o =>
      if some o.id != sourceId then g.addPlusOnePlusOneTo o 1 else g)
  | (.casting .exileFlicker) =>
    g.withLegalKindPermanent controller .nonland targets (fun g o =>
      if o.printed.isToken then
        g.logMsg "The target is a token and can't be flickered"
      else
        let name := o.name
        let (g, newId) := g.move o.id .exile none
        { g with delayedEndStepReturns := g.delayedEndStepReturns.push newId }
          |>.logMsg s!"{name} is exiled until the beginning of the next end step")
      sourceId (some "The target is no longer legal")
  | (.casting .damageEqualMv) =>
    let n :=
      match lastKnownPower with
      | some p => p.toNat
      | none =>
        match g.lastStackSpell? with
        | some o => o.printed.manaValue
        | none =>
          match (g.player controller).castManaValuesThisTurn.back? with
          | some mv => mv
          | none => 0
    g.applyDamageToKindTarget controller .playerOrCreature targets n sourceId none
  | (.casting .plusOneThis) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | (.casting .plusOneScry) =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
        "The source is no longer in play"
    g.beginScry controller 1
  | (.casting .targetsGainFlying) =>
    let ids :=
      if !targets.isEmpty then
        targets.filterMap (fun t =>
          match t with
          | Target.permanent id => some id
          | _ => none)
      else
        match g.lastStackSpell? with
        | none => #[]
        | some spell =>
          match g.stack.find? (fun e => e.objectId == spell.id) with
          | none => #[]
          | some e =>
            e.targets.filterMap (fun t =>
              match t with
              | Target.permanent id => some id
              | _ => none)
    ids.foldl (fun (g : Game) id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature then
          g.grantUntilEotLogged o Keyword.flying
        else g
      | none => g) g
  | (.casting .copyIfArtifactOrLand) =>
    let g :=
      match g.lastStackSpell? with
      | some spell =>
        if spell.printed.isInstantOrSorcery then
          let (g, copy) := g.allocObject spell.printed controller .stack (some controller)
          let g := g.setObject { copy with
            kicked := spell.kicked
            giftPromisedTo := spell.giftPromisedTo
            chosenX := spell.chosenX
            isCopy := true }
          g.putStackEntry controller copy.id
            |>.logMsg s!"A copy of {spell.name} is created"
        else g
      | none => g
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 2)
      "The source is no longer in play"
  | (.casting .tapCreatureOrLand) =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.applyPermanentAction o .tap) sourceId
      (some "The target is no longer legal")
  | (.resource .discardExilePlay) =>
    let id? :=
      match lastKnownPower with
      | some n =>
        if n ≥ 0 then some (⟨n.toNat⟩ : ObjectId) else none
      | none => (g.player controller).graveyard.back?
    match id? with
    | none => g.logMsg "No discarded card is in the graveyard"
    | some id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard controller then
          let name := o.name
          let (g, newId) := g.move o.id .exile none
          let o := g.object! newId
          g.setObject { o with
              playPermission := some {
                player := controller
                turnEndsRemaining := 2 } }
            |>.logMsg
              s!"{name} is exiled. {(g.player controller).name} may play it until the end of their next turn"
        else
          g.logMsg "The discarded card is no longer in the graveyard"
      | none => g.logMsg "The discarded card is no longer in the graveyard"
  | (.resource .secondDrawPlusOneTarget) =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.addPlusOnePlusOneTo o 1) sourceId
      (some "The target is no longer legal")
  | (.resource .secondDrawDrain) =>
    let g := g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    g.gainLife controller 1
  | (.resource .gainLifePlusOnes) =>
    targets.foldl (fun (g : Game) t =>
      match t with
      | Target.permanent id =>
        match g.findObject? id with
        | some o =>
          if o.isOnBattlefield && o.isCreature && o.controlledBy controller then
            g.addPlusOnePlusOneTo o 1
          else g
        | none => g
      | _ => g) g
  | (.resource .plusOneOnThisOnce) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | _ =>
    g.withSourceOnBattlefield sourceId (fun g _ => g)
      s!"{sourceName} resolves"

/-- Resolve leftover MSH wording that is not yet a named constructor arm. -/
def applyLeftoverTextEffect (g : Game) (controller : PlayerId) (text : String)
    (targets : Array Target) (sourceId : Option ObjectId) : Game :=
  if text.contains "finality" then
    match sourceId.bind g.findObject? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, newId) := g.putOntoBattlefield o.id controller
        let g := g.logMsg s!"{o.name} returns to the battlefield"
        g.addFinalityTo (g.object! newId) 1
      else g
    | none => g
  else if text.contains "connive" then
    match targets[0]? with
    | some (Target.permanent id) => g.applyConnive controller (some id)
    | _ => g.applyConnive controller none
  else if text.contains "Galactus" then
    g.createNamedToken controller galactusToken
  else if text.contains "Tiger God" then
    let g :=
      match targets[0]? with
      | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
      | _ => g
    g.createNamedToken controller tigerGodToken
  else if text.contains "Squirrel" then
    let n := g.countSubtype controller "Squirrel"
    g.createKindTokens controller .squirrel11green (if n == 0 then 1 else n)
  else if text.contains "Treasure token for each Villain" then
    let n := g.countSubtype controller "Villain"
    g.createKindTokens controller .treasure n
  else if text.contains "two 2/1 black Villain" then
    g.createKindTokens controller .villain21menace 2
  else if text.contains "2/1 black Villain" && text.contains "+1/+0" then
    let g := g.createKindTokens controller .villain21menace 1
    g.pumpControlledCreatures controller 1 0
  else if text.contains "Treasure token" then
    g.createKindTokens controller .treasure 1
  else if text.contains "0/4 colorless Wall" then
    g.createKindTokens controller .wall04defender 1
  else if text.contains "each opponent loses" then
    g.forEachOpponent controller (fun g pid => g.loseLife pid 2)
  else if text.contains "fights" then
    match targets[0]?, targets[1]? with
    | some (Target.permanent a), some (Target.permanent b) =>
      g.dealFightDamage (g.object! a) (g.object! b)
    | _, _ => g
  else if text.contains "draw" && text.contains "lose" then
    g.drawThenLoseLife controller 2 2
  else if text.contains "Draw" || text.contains "draw" then
    g.draw controller 1
  else if text.contains "deals" && text.contains "damage" then
    g.applyDamageToKindTarget controller .playerOrCreature targets 4
  else if text.contains "+1/+1 counter on each" then
    g.forEachControlledCreature controller (fun g o => g.addPlusOnePlusOneTo o 1)
  else if text.contains "+1/+1" then
    match targets[0]? with
    | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
    | _ => g
  else if text.startsWith "Add " || text.startsWith "Add" then
    g.modifyPlayer controller (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .white) })
  else
    g

/-- Put the targeted creature into its owner's library, second from the top
or on the bottom (Trickster's Stratagem). -/
def applyOwnerPutsLibraryThenConnive (g : Game) (_controller : PlayerId)
    (targets : Array Target) (putOnBottom := false) : Game :=
  match targets[0]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield then
        let owner := o.owner
        if putOnBottom then
          let (g, _) := g.move id (.library owner) none
          g.logMsg s!"{o.name} is put on the bottom of {(g.player owner).name}'s library"
        else
          let (g, newId) := g.move id (.library owner) none
          let pl := g.player owner
          let lib := pl.library
          let without := lib.filter (· != newId)
          let lib :=
            match without.back? with
            | none => #[newId]
            | some top => without.pop.push newId |>.push top
          g.setPlayer { pl with library := lib }
            |>.logMsg s!"{o.name} is put second from the top of {(g.player owner).name}'s library"
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | _ => g.logMsg "The target is no longer legal"

/-- Avengers Disassembled: if the land mode was chosen and that target is
illegal, the spell does not resolve — even the untargeted damage mode
(MSH 207). If the land is legal but indestructible, its controller still
searches. -/
def applyAvengersDisassembled (g : Game) (_controller : PlayerId)
    (choseDamage choseLand : Bool) (landId : Option ObjectId) : Game :=
  let landOk :=
    match landId.bind g.findObject? with
    | some o => o.isOnBattlefield && o.printed.isLand
    | none => false
  if choseLand && !landOk then
    g.logMsg "The target is no longer legal. Avengers Disassembled doesn't resolve."
  else
    let g :=
      if choseDamage then
        g.dealDamageToEachCreatureMatching 3
      else g
    if choseLand then
      match landId.bind g.findObject? with
      | some o =>
        let owner := o.owner
        let g := g.destroyPermanent o
        g.logMsg s!"{(g.player owner).name} may search for a basic land"
      | none => g
    else g

/-- Black mana symbols among `ids` for Zemo's boast, counting hybrid symbols
that include black (MSH 128). -/
def zemoBoastBlackSymbols (g : Game) (ids : Array ObjectId) : Nat :=
  ids.foldl (fun n id =>
    match g.findObject? id with
    | some o => n + o.printed.manaCost.symbolsIncludingColor .black
    | none => n) 0

/-- True when `ids` are black cards in `p`'s graveyard whose mana costs have
fifteen or more black mana symbols, including `{B/x}` hybrids (MSH 128). -/
def canPayZemoBoast (g : Game) (p : PlayerId) (ids : Array ObjectId) : Bool :=
  !ids.isEmpty &&
    ids.all (fun id =>
      match g.findObject? id with
      | some o =>
        o.zone == .graveyard p && o.printed.colors.contains .black
      | none => false) &&
    g.zemoBoastBlackSymbols ids >= 15

/-- Baron Helmut Zemo boast: copy only the cards exiled to this activation
(MSH 227). Copies are cast while the ability is resolving (MSH 353). -/
def applyZemoBoast (g : Game) (controller : PlayerId) (exileIds : Array ObjectId)
    (castN : Nat := 0) : Game :=
  Id.run do
    let mut g := g
    let mut copied : Array ObjectId := #[]
    for id in exileIds do
      match g.findObject? id with
      | some o =>
        if o.zone == .graveyard controller then
          let (g', newId) := g.move id .exile none
          g := g'
          copied := copied.push newId
      | none => pure ()
    g := { g with zemoBoastExiles := copied }
    g := g.logMsg s!"Zemo copies {copied.size} card(s) exiled to this activation"
    for id in copied.take castN do
      g := g.castAsPartOfResolution controller id
    return g

/-- Cast up to `n` cards that currently have a free-cast exile permission,
as the ability resolves (Doom Reigns; MSH 357). -/
def castExiledAsResolves (g : Game) (p : PlayerId) (n : Nat) : Game :=
  let ids :=
    (g.objects.filter (fun o =>
      o.zone == .exile &&
        match o.playPermission with
        | some perm => perm.player == p && perm.withoutManaCost
        | none => false)).map (·.id)
  ids.take n |>.foldl (fun acc id =>
    acc.castAsPartOfResolution p id) g

/-- Whether the resolving stack object paid its teamwork cost. -/
def resolvingTeamworkPaid (g : Game) : Bool :=
  g.stack.back?.any (fun e => (g.findObject? e.objectId).any (·.teamworkPaid))

/-- `alt` if the resolving spell paid teamwork; otherwise `base`. -/
def teamworkAmount (g : Game) (base alt : Nat) : Nat :=
  if g.resolvingTeamworkPaid then alt else base

/-- Add `types` to `p`'s mana pool and log it (shared `.addMana` resolution). -/
def addManaLogged (g : Game) (p : PlayerId) (types : Array ManaType) : Game :=
  let g := g.modifyPlayer p (fun pl =>
    { pl with manaPool :=
      types.foldl (fun pool t => pool.add t) pl.manaPool })
  g.logMsg s!"{(g.player p).name} adds mana"

/-- Ask the target spell's controller to pay `{n}` or let it be countered. -/
def beginPayOrLetCounter (g : Game) (targets : Array Target) (n : Nat) : Game :=
  match targets[0]? with
  | some (Target.card id) =>
    match g.findObject? id with
    | some o =>
      let ctrl := o.controller.getD o.owner
      { g with pending := .payOrLetCounter ctrl n id }.logMsg
        s!"{(g.player ctrl).name} may pay \{{n}} or {o.name} is countered"
    | none => g.logMsg "The target is no longer legal"
  | _ => g.logMsg "The target is no longer legal"

/-- Exile `o`, then immediately return it to the battlefield under its
owner's control. `clearExileFields` drops a play permission or linked exile
carried while exiled. With `land := false` the permanent returns summoning
sick unless it has haste and `afterPermanentEnters` runs; with `land := true`
it returns tapped when `tapped` is set and `afterLandEnters` runs. -/
def exileThenReturn (g : Game) (o : GameObject) (logText : String)
    (clearExileFields := false) (tapped := false) (land := false) : Game :=
  let owner := o.owner
  let name := o.name
  let (g, newId) := g.move o.id .exile none
  let g :=
    if clearExileFields then
      let ex := g.object! newId
      g.setObject { ex with playPermission := none, linkedExile := #[] }
    else g
  let (g, retId) := g.move newId .battlefield (some owner)
  let ret := g.object! retId
  let g :=
    if land then
      if tapped then
        g.setObject { ret with status := { ret.status with tapped := true } }
      else g
    else
      g.setObject { ret with
        status := { ret.status with summoningSick := !ret.printed.keywords.haste } }
  let g := g.logMsg s!"{name} {logText}"
  if land then g.afterLandEnters (g.object! retId)
  else g.afterPermanentEnters (g.object! retId)

end Game
end Mtg.Engine
