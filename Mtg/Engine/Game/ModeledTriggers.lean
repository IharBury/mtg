import Mtg.Engine.Game.ResolutionEffects

/-!
# Modeled trigger resolution

`applyModeledTrigger` — resolving the shared-trigger payloads — leftover
rules-text effects, and boast, teamwork, and pay-or-counter helpers.
-/

namespace Mtg.Engine
namespace Game

/-- Resolve a modeled MSH trigger. Performs the printed effect: tokens, draw,
damage, destroy, attach, exile, or pump. -/
def applyModeledTrigger (g : Game) (controller : PlayerId) (t : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (sourceName : String := "This creature")
    (lastKnownPower : Option Int := none) : Game :=
  let text := t.toNotation
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
        match targets[0]? with
        | some (Target.permanent id) =>
          let g := g.setObject { src with status :=
            { src.status with optionalOnceUsed := true } }
          g.applyConnive controller (some id)
        | _ =>
          g.logMsg "The Villain does not connive"
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
  | _ =>
    if text.contains "create two 1/1 white Soldier" ||
        text.contains "create a 1/1 white Soldier" then
      g.createKindTokens controller .soldier11white
        (if text.contains "two" then 2 else 1)
    else if text.contains "Doombot" then
      g.createKindTokens controller .doombot 2
    else if text.contains "draw a card" && text.contains "lose 1 life" then
      g.drawThenLoseLife controller 1 1
    else if text.contains "draw a card" || text.contains "you draw" ||
        text.contains "draw cards" then
      g.draw controller 1
    else if text.contains "connive" then
      g.applyConnive controller sourceId
    else if text.contains "surveil" || text.contains "Scry" || text.contains "scry" then
      g.beginScry controller 1
    else if text.contains "destroy target" then
      g.withLegalKindPermanent controller .oppCreature targets
        (fun g o => g.destroyPermanent o) sourceId none
    else if text.contains "exile" && text.contains "leaves" then
      g.withSourceStillOnBattlefield sourceId fun g _ =>
        g.withLegalKindPermanent controller .oppNonland targets
          (fun g o => g.exileUntilSourceLeaves sourceId o) sourceId none
    else if text.contains "+1/+1 counter" then
      match targets[0]? with
      | some (Target.permanent id) => g.addPlusOnePlusOneTo (g.object! id) 1
      | _ =>
        g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
          "The source is no longer in play"
    else if text.contains "each opponent loses" then
      g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    else if text.contains "deals" && text.contains "damage" then
      g.applyDamageToKindTarget controller .playerOrCreature targets 1 sourceId none
    else if text.contains "fights" then
      match sourceId, targets[0]? with
      | some sid, some (Target.permanent id) =>
        g.dealFightDamage (g.object! sid) (g.object! id)
      | _, _ => g
    else if text.contains "attach" then
      g.withLegalKindPermanent controller .creatureYouControl targets
        (fun g host =>
          g.withSourceOnBattlefield sourceId (fun g src => g.attachSourceTo src host)
            "The Equipment is no longer in play") sourceId none
    else
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
