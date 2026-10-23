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

/-- The spell that caused the resolving cast trigger. -/
def castTriggerSpell? (g : Game) : Option GameObject :=
  ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).bind
    (fun id => g.findObject? (g.followMoved id))

/-- Newest non-ability object on the stack (the spell that caused a cast trigger). -/
def lastStackSpell? (g : Game) : Option GameObject :=
  g.stack.foldl (fun acc e =>
    match g.findObject? e.objectId with
    | some o =>
      if o.triggeredAbility.isNone && o.abilityEffect.isNone then some o else acc
    | none => acc) none

/-- 1/1 blue Merfolk creature token (Namora / similar leftover cast triggers). -/
def merfolk11blueToken : CardDef :=
  creatureToken "Merfolk" #[.merfolk] 1 1 (some .blue)

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

/-- Ask the next player in `players` with a nontoken creature to choose one
to sacrifice; once all have chosen, sacrifice them together. -/
def continueNontokenSacrifices (g : Game) (players : Array PlayerId) (chosen : Array ObjectId) :
    Game :=
  let hasOne (p : PlayerId) := (g.permanentsOf p).any (fun o => o.isCreature && !o.printed.isToken)
  match (players.filter hasOne).toList with
  | p :: rest =>
    (g.change (.pending (.fraChoice p (.sacrificeNontokenEach rest.toArray chosen)))).logMsg
      s!"{(g.player p).name} sacrifices a nontoken creature"
  | [] =>
    chosen.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield then
          g.sacrificeToGraveyard o s!"{(g.player (o.controller.getD o.owner)).name} sacrifices {o.name}"
        else g
      | none => g) g

/-- Let `controller` cast the exiled nonland with any type of mana until end of turn. -/
def grantWidowCast (g : Game) (controller : PlayerId) (exiled : Option ObjectId) : Game :=
  match exiled.bind g.findObject? with
  | none => g.logMsg "No nonland card was exiled"
  | some o =>
    g.changeObject o.id (.playPermission (some {
      player := controller
      turnEndsRemaining := 1
      anyMana := true }))
      |>.logMsg s!"{(g.player controller).name} may cast {o.name} until end of turn"

/-- Copy the nontoken artifact that entered, then make a noncreature token a
2/2 Robot Villain after it enters (Ultron; MSH 574 / 656). -/
def copyEnteredArtifact (g : Game) (controller : PlayerId) (artifactId : ObjectId) : Game :=
  match g.findObject? (g.followMoved artifactId) with
  | none => g.logMsg "Ultron has nothing to copy"
  | some src =>
    if src.printed.isToken || !src.printed.isArtifact then
      g.logMsg "That permanent isn't a nontoken artifact"
    else
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
            subtypes := mergeSubtypes tok.printed.subtypes #[.robot, .villain]
            power := some 2
            toughness := some 2 }
        g.changeObject tok.id (.printed printed)
          |>.logMsg s!"{printed.name} becomes a 2/2 Robot Villain creature after it enters"

/-- Exile the top card of your library. A Hero card pumps Daredevil. The
exiled card may be played this turn either way (MSH 685). -/
def applyDaredevilExile (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  let top? := (g.player controller).library.back?
  let isHero :=
    match top? with
    | some top => (g.object! top).hasSubtype .hero
    | none => false
  let g := g.exileTopPlayThisTurn controller 1
  if isHero then
    g.withSourceOnBattlefield sourceId (fun g src => g.pumpPermanent src 2 1)
      "Daredevil is no longer on the battlefield"
  else g

/-- The Vision's chosen mode that hasn't been chosen yet this turn.
0 double strike, 1 indestructible, 2 draw. -/
def applyVisionMode (g : Game) (controller : PlayerId) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? (g.followMoved sourceId) with
  | none =>
    if mode == 2 then g.draw controller 1
    else g.logMsg "The Vision is no longer in play"
  | some src =>
    if src.status.modesChosenThisTurn.contains mode || src.status.modesChosenThisTurn.size >= 3 then
      g.logMsg "The Vision's ability is removed from the stack with no effect"
    else if !src.isOnBattlefield then
      if mode == 2 then g.draw controller 1
      else g.logMsg "The Vision is no longer in play"
    else
      let g := g.changeStatus src.id (.pushModeChosenThisTurn mode)
      if mode == 0 then
        g.changeStatus src.id (.grantUntilEot Keyword.doubleStrike)
      else if mode == 1 then
        g.changeStatus src.id (.grantUntilEot Keyword.indestructible)
      else
        g.draw controller 1

/-- Ask to change the spell's target at `index`, then the later slots. -/
def offerSpellRetarget (g : Game) (controller : PlayerId) (spellId : ObjectId) (index : Nat) : Game :=
  match g.stackEntry? spellId with
  | none => g
  | some e =>
    if index < e.targets.size then
      g.change (.pending (.fraChoice controller (.mayChangeSpellTarget spellId index)))
        |>.logMsg "You may choose a new target for the spell"
    else g

/-- Replace one target of a spell when the replacement is legal. An illegal
choice leaves that target unchanged (MSH 722). -/
def setSpellTargetAt (g : Game) (spellId : ObjectId) (index : Nat) (neu : Target) : Game :=
  match g.stack.findIdx? (fun e => e.objectId == spellId) with
  | none => g.logMsg "The spell is no longer on the stack"
  | some i =>
    let e := g.stack[i]!
    match g.findObject? spellId with
    | none => g.logMsg "The spell is no longer on the stack"
    | some spell =>
      let legal := g.legalTargetsForKind e.controller (g.targetingOf spell).kind (some spellId)
      if index < e.targets.size && legal.contains neu then
        g.changeStackEntry i (.setTargetAt index neu)
          |>.logMsg "A new target is chosen for the spell"
      else
        g.logMsg "That target stays unchanged"

/-- Mister Hyde's chosen mode. Mode 0 puts a +1/+1 counter on the source.
Mode 1 removes a counter from the chosen creature, then draws. -/
def applyHydeMode (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (mode : Nat) (targets : Array Target) : Game :=
  if mode == 0 then
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.addPlusOnePlusOneTo o 1) "The source is no longer in play"
  else
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.controlledBy controller && o.status.hasCounters then
          let g :=
            if o.status.plusOnePlusOne > 0 then
              g.changeStatus o.id (.removeCounters .plusOnePlusOne 1)
                |>.logMsg s!"A counter is removed from {o.name}"
            else if o.status.indestructibleCounters > 0 then
              g.changeStatus o.id (.removeCounters .indestructible 1)
                |>.logMsg s!"A counter is removed from {o.name}"
            else g.logMsg "A counter is removed from the creature"
          g.draw controller 1
        else
          g.logMsg "You must remove a counter from a creature you control if you can"
      | none =>
        g.logMsg "You must remove a counter from a creature you control if you can"
    | _ =>
      if (g.permanentsOf controller).any (fun o =>
          o.isCreature && o.status.hasCounters) then
        g.logMsg "You must remove a counter from a creature you control if you can"
      else g

/-- Draw one card for the controller of the creature the source enchants.
Nothing enchanted draws nothing. -/
def drawForEnchantedController (g : Game) (sourceId : Option ObjectId) : Game :=
  match g.attachedHost? sourceId with
  | some host =>
    match host.controller with
    | some pid => g.draw pid 1
    | none => g.draw host.owner 1
  | none =>
    g.logMsg "The enchanted creature has left. No card is drawn."

/-- Draw until `controller` has `n` cards in hand. A hand that already has
`n` draws nothing. -/
def drawUpToHandSize (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  let cards := (g.player controller).hand.size
  if cards < n then g.draw controller (n - cards)
  else if n == 10 then
    g.logMsg "You already have ten or more cards in hand"
  else
    g.logMsg s!"You already have {n} or more cards in hand"

/-- Ask the controller to put a +1/+1 counter on the source, or to remove a
counter from a creature they control and draw. -/
def offerHydeChoice (g : Game) (controller : PlayerId) (sourceId : Option ObjectId) : Game :=
  g.change (.pending (.fraChoice controller (.hydeMode (sourceId.getD ⟨0⟩))))
    |>.logMsg s!"{(g.player controller).name} chooses one — 0 put a +1/+1 counter, 1 remove a counter and draw"

/-- Something becomes a copy, as `of` says. The source copies an announced
object until the controller's next turn and keeps the printed exception
name. Choosing none copies nothing. A missing source copies nothing.
`.noted` makes the enchanted creature a copy of the creature an earlier
step noted, until the source leaves. Nothing noted copies nothing.
`.cause` with no subtype creates a token copy of the nontoken artifact
that caused this. An announced permanent is used when one was chosen;
otherwise the recorded cause. The source need not still be on the
battlefield. Any other selector copies nothing. -/
def applyBecomeCopy (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) (of : TriggeredAbility.ObjectSelector) : Game :=
  match of with
  | .noted =>
    let copied := g.notedCopyObject
    let hostId := g.notedHostId
    let g := g.changes #[.notedCopyObject none, .notedHostId none]
    match copied, hostId with
    | some tgt, some hid =>
      match g.findObject? hid with
      | some host => g.becomeCopyOf host tgt (untilSourceLeaves := sourceId)
      | none => g
    | _, _ => g
  | .cause none =>
    let fromTarget :=
      match targets[0]? with
      | some (Target.permanent id) => some id
      | _ => none
    let causeId :=
      ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved
    match fromTarget.orElse (fun _ => causeId) with
    | none => g.logMsg "Ultron has nothing to copy"
    | some id => g.copyEnteredArtifact controller id
  | .artifactEnchantmentOrLand =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some tgt =>
          let ok := tgt.isOnBattlefield && !tgt.printed.isAura &&
            (tgt.printed.isArtifact || tgt.printed.isEnchantment || tgt.printed.isLand)
          if ok then
            g.becomeCopyOf src tgt (untilNextTurn := true)
              (exceptName := some "Absorbing Man")
              (addSupertypes := #[.legendary]) (addTypes := #[.creature])
              (addSubtypes := #[.human, .villain])
              (setPT := some (4, 4)) (addVigilance := true)
          else g.logMsg "That permanent isn't an artifact, non-Aura enchantment, or land"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "Absorbing Man doesn't become a copy")
      "The source is no longer in play"
  | .creatureOrGraveyardCard =>
    g.withSourceOnBattlefield sourceId (fun g src =>
      match targets[0]? with
      | some (Target.permanent id) | some (Target.card id) =>
        match g.findObject? id with
        | some tgt =>
          let onBf := tgt.isOnBattlefield && tgt.isCreature
          let inGy := tgt.zone == .graveyard tgt.owner && tgt.printed.isCreature
          if onBf || inGy then
            g.becomeCopyOf src tgt (untilNextTurn := true)
              (exceptName := some "Taskmaster, Mercenary Mimic")
              (addSupertypes := #[.legendary]) (addTypes := #[.creature])
              (addSubtypes := #[.human, .mercenary, .villain])
              (replaceCreatureLine := true)
          else g.logMsg "That isn't a creature or a creature card in a graveyard"
        | none => g.logMsg "The target is no longer legal"
      | _ => g.logMsg "Taskmaster doesn't become a copy")
      "The source is no longer in play"
  | _ => g

/-- Exile the announced nonland the controller still controls, other than the
source, then return it under its owner's control. Choosing none does nothing.
An illegal target is reported. -/
def flickerChosenNonland (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  match targets[0]? with
  | some (Target.permanent id) =>
    match g.findObject? id with
    | some o =>
      let other :=
        match sourceId with
        | some sid => o.id != sid
        | none => true
      if o.isOnBattlefield && o.controlledBy controller && !o.printed.isLand && other then
        let owner := o.owner
        let name := o.name
        let (g, exId) := g.move o.id .exile none
        let (g, retId) := g.move exId .battlefield (some owner)
        let ret := g.object! retId
        let g := g.changeStatus retId (.summoningSick (!ret.printed.keywords.haste))
        g.afterPermanentEnters (g.object! retId)
          |>.logMsg s!"{name} is exiled, then returned"
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | _ => g

/-- Exile the announced nontoken artifact or creature, then return it
tapped under its owner's control. Choosing none does nothing.
A token, a permanent that is neither an artifact nor a creature, or a
missing target is not exiled. -/
def returnNontokenTapped (g : Game) (targets : Array Target) : Game :=
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
        let g := g.changeStatuses retId
          #[.tapped true, .summoningSick (!ret.printed.keywords.haste)]
        g.afterPermanentEnters (g.object! retId)
          |>.logMsg s!"{name} is exiled, then returned tapped"
      else g.logMsg "The target is no longer legal"
    | none => g.logMsg "The target is no longer legal"
  | _ => g

/-- True when `mods` strips abilities and grants haste, as Hellcat returns. -/
def losesAbilitiesAndHaste (mods : List TriggeredAbility.TriggerEnterWith) : Bool :=
  mods.any (· == .loseAllAbilities) &&
    mods.any (fun m =>
      match m with
      | .keywords k => k.haste
      | _ => false)

/-- Apply one enters-with change to the permanent `id`. -/
def applyEnterMod (g : Game) (controller : PlayerId) (id : ObjectId)
    (mod : TriggeredAbility.TriggerEnterWith) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    match mod with
    | .loseAllAbilities =>
      g.changeObject id (.printed { o.printed with
        keywords := Keywords.none
        triggeredAbilities := #[]
        activatedAbilities := #[]
        staticAbilities := #[] })
    | .keywords k =>
      let o := g.object! id
      g.changeObject id (.printed { o.printed with
        keywords := Keywords.merge o.printed.keywords k })
    | .additionalSubtype subtype =>
      let o := g.object! id
      if o.printed.hasSubtype subtype then g
      else
        g.changeObject id (.printed { o.printed with
          subtypes := o.printed.subtypes.push subtype.englishName })
    | .counter kind n asEnters =>
      let o := g.object! id
      match kind, asEnters with
      | .plusOnePlusOne, true =>
        g.addPlusOnePlusOneTo o n (entersWith := true)
      | .plusOnePlusOne, false =>
        g.addPlusOnePlusOneTo o n (byPlayer := some controller)
      | .finality, _ =>
        g.addFinalityTo o n (byPlayer := some controller)
      | kind, asEnters =>
        g.addCounters o kind n (entersWith := asEnters) (byPlayer := some controller)
    | .attacking =>
      let whom :=
        match (g.livingOpponents controller)[0]? with
        | some pl => some pl.id
        | none => none
      g.changeStatuses id #[.attacking true, .attackingWhom whom]

/-- Put `o` onto the battlefield under its owner's control, then apply
`mods` before its enters abilities. -/
def enterFromOwnerGraveyard (g : Game) (controller : PlayerId) (o : GameObject)
    (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  let (g, newId) := g.putOntoBattlefield o.id o.owner
  let g := mods.foldl (fun g m => g.applyEnterMod controller newId m) g
  let g := g.afterPermanentEnters (g.object! newId)
  if losesAbilitiesAndHaste mods then
    g.logMsg s!"{(g.object! newId).name} returns, loses all abilities, and gains haste"
  else g

/-- Return the source from its owner's graveyard under its owner's control.
Hellcat's return reports her by name when she has already left. -/
def returnSourceUnderOwner (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  let hellcat := losesAbilitiesAndHaste mods
  let missing :=
    if hellcat then "Hellcat is no longer in the graveyard"
    else "The ability's source is no longer in the graveyard"
  match (sourceId.map g.followMoved).bind g.findObject? with
  | none => g.logMsg missing
  | some o =>
    if o.zone != .graveyard o.owner then g.logMsg missing
    else g.enterFromOwnerGraveyard controller o mods

/-- The announced card or permanent, or the recorded cause. -/
def announcedOrCauseId? (g : Game) (targets : Array Target) : Option ObjectId :=
  match targets[0]? with
  | some (Target.card id) | some (Target.permanent id) => some id
  | _ =>
    ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved

/-- Return the cause from its owner's graveyard under its owner's control.
`subtype`, when set, requires that subtype. A missing cause puts nothing. -/
def returnCauseUnderOwner (g : Game) (controller : PlayerId) (targets : Array Target)
    (subtype : Option CardSubtype) (mods : List TriggeredAbility.TriggerEnterWith) : Game :=
  match (g.announcedOrCauseId? targets).bind g.findObject? with
  | some o =>
    let ok :=
      match subtype with
      | none => true
      | some s => g.hasSubtype o s
    if o.zone == .graveyard o.owner && ok then
      g.enterFromOwnerGraveyard controller o mods
    else g
  | none => g

/-- The announced card, the recorded cause, or the last attacking creature
that died. -/
def diedCardId? (g : Game) (targets : Array Target) : Option ObjectId :=
  let fromTarget :=
    match targets[0]? with
    | some (Target.card id) | some (Target.permanent id) => some id
    | _ => none
  let fromCause :=
    ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved
  let fromAttacker := g.loggedLastDiedAttacker.map g.followMoved
  (fromTarget.orElse (fun _ => fromCause)).orElse (fun _ => fromAttacker)

/-- Return the card that caused this trigger to its owner's hand.
A token ceases to exist. A card that has left is reported. -/
def returnCauseToOwnerHand (g : Game) (targets : Array Target) : Game :=
  match (g.diedCardId? targets).bind g.findObject? with
  | none => g.logMsg "The attacking creature is no longer in the graveyard"
  | some o =>
    if o.printed.isToken then
      g.logMsg s!"{o.name} ceases to exist"
    else if o.zone != .graveyard o.owner then
      g.logMsg "The attacking creature is no longer in the graveyard"
    else
      g.returnToHand o.id o.owner

/-- Exile and return the announced permanent when the source is harnessed.
A missing source does nothing. An unharnessed source is reported. -/
def resolveHarnessedFlicker (g : Game) (controller : PlayerId) (sourceId : Option ObjectId)
    (targets : Array Target) : Game :=
  match sourceId.bind g.findObject? with
  | some src =>
    if !src.status.harnessed then
      g.logMsg "The Mind Stone is not harnessed"
    else
      g.flickerChosenNonland controller sourceId targets
  | none => g

/-- You may exile the top card of your library. A Hero card gives the source
+2/+1 until end of turn, and the card may be played this turn (Daredevil). -/
def offerExileTopHeroPump (g : Game) (controller : PlayerId)
    (sourceId : Option ObjectId) : Game :=
  g.change (.pending (.fraChoice controller (.daredevilMayExile sourceId)))
    |>.logMsg "You may exile the top card of your library"

/-- You may pay 2 life. If you do, creatures you control assign combat damage
equal to their toughness this turn (The Kingpin of Crime). -/
def offerPay2LifeToughness (g : Game) (controller : PlayerId) : Game :=
  if g.canPayLife controller 2 then
    g.change (.pending (.fraChoice controller .kingpinMayPay2Life))
      |>.logMsg "You may pay 2 life"
  else
    g.logMsg "The Kingpin's cost wasn't paid"

/-- Look at the top `n` cards and you may cast one with mana value at most the
greatest power among attacking creatures you control (Cosmic Cube). -/
def offerLookSixCast (g : Game) (controller : PlayerId) (n : Nat := 6) : Game :=
  g.beginMayCastFromLooked controller n (g.greatestPowerAmongAttacking controller)

/-- Mana value of the spell that caused this cast trigger, including X.
A spell that has left uses the last-known power, then the newest spell on
the stack, then a mana value recorded this turn. -/
def castSpellManaValue (g : Game) (controller : PlayerId)
    (lastKnownPower : Option Int) : Nat :=
  match g.castTriggerSpell? with
  | some spell => spell.printed.manaValue + spell.chosenX.getD 0
  | none =>
    match lastKnownPower with
    | some p => p.toNat
    | none =>
      match g.lastStackSpell? with
      | some o => o.printed.manaValue + o.chosenX.getD 0
      | none =>
        match (g.loggedCastManaValues controller).back? with
        | some mv => mv
        | none => 0

/-- Blue mana symbols in the spell that caused this cast trigger. -/
def blueSymbolsInCastSpell (g : Game) (lastKnownPower : Option Int) : Nat :=
  match g.castTriggerSpell? with
  | some spell => spell.printed.manaCost.symbolsIncludingColor .blue
  | none =>
    match lastKnownPower with
    | some p => p.toNat
    | none =>
      match g.lastStackSpell? with
      | some o => o.printed.manaCost.symbolsIncludingColor .blue
      | none => 0

/-- Create one 1/1 blue Merfolk for each blue mana symbol in the causing spell. -/
def createMerfolkForBlueSymbols (g : Game) (controller : PlayerId)
    (lastKnownPower : Option Int) : Game :=
  let n := g.blueSymbolsInCastSpell lastKnownPower
  if n == 0 then
    g.logMsg "No blue mana symbols. No Merfolk are created."
  else
    Id.run do
      let mut g := g
      for _ in [0:n] do
        let (g', _) := g.createToken controller merfolk11blueToken
        g := g'
      return g

/-- Ask for one Vision mode that has not been chosen this turn. The chosen
resolution is `TriggerResolution.visionModes`. -/
def offerVisionModes (g : Game) (controller : PlayerId) (ab : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (lastKnownPower : Option Int := none) (sourceName : String := "This creature") : Game :=
  match sourceId.bind (fun id => g.findObject? (g.followMoved id)) with
  | some src =>
    let available :=
      #[0, 1, 2].filter (fun m => !src.status.modesChosenThisTurn.contains m)
    if available.isEmpty then
      g.logMsg "The Vision's ability is removed from the stack with no effect"
    else
      g.changes #[
        .pending (.fraChoice controller (.visionMode src.id available)),
        .chooseModesRest (some {
          controller
          ability := ab
          sourceId
          targets
          lastKnownPower
          sourceName
          modes := TriggeredAbility.TriggerResolution.visionModes
          how := .vision })]
        |>.logMsg "Choose one that hasn't been chosen this turn"
  | none =>
    g.logMsg "The Vision is no longer in play"

/-- The source gains Iron Fist's tap ability until end of turn. -/
def grantIronFistTap (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.changeStatus o.id (.ironFistTapGrants (o.status.ironFistTapGrants + 1))
      |>.logMsg s!"{o.name} gains a tap ability until end of turn")
    "The source is no longer in play"

/-- Until end of turn, the source's base power is the cards in hand. -/
def grantHandSizePower (g : Game) (sourceId : Option ObjectId) : Game :=
  g.withSourceOnBattlefield sourceId (fun g o =>
    g.changeStatus o.id (.cardsInHandPowerUntilEot true)
      |>.logMsg s!"{o.name}'s base power is the number of cards in your hand until end of turn")
    "The source is no longer in play"

/-- Grant `k` until end of turn to each creature the causing spell targets. -/
def grantKeywordsToSpellCreatureTargets (g : Game) (k : Keywords) : Game :=
  let ids :=
    match g.castTriggerSpell? with
    | none => #[]
    | some spell =>
      match g.stack.find? (fun (e : StackEntry) => e.objectId == spell.id) with
      | none => (#[] : Array ObjectId)
      | some e =>
        e.targets.filterMap (fun t =>
          match t with
          | Target.permanent id => some id
          | _ => none)
  ids.foldl (fun (g : Game) id =>
    match g.findObject? id with
    | some o =>
      if o.isOnBattlefield && o.isCreature then
        g.grantUntilEotLogged o k
      else g
    | none => g) g

/-- Copy the spell that caused this trigger and ask for new targets. -/
def copyCastTriggerSpell (g : Game) (controller : PlayerId) : Game :=
  match g.castTriggerSpell? with
  | some spell =>
    if spell.zone != .stack then g.logMsg s!"{spell.name} is no longer on the stack"
    else
      let g := g.copyStackSpell spell controller
      let copyId := (g.stack.back?.map (·.objectId)).getD spell.id
      (g.change (.pending (.fraChoice controller (.newTargetsForCopies #[copyId])))).logMsg
        s!"{(g.player controller).name} may choose new targets for the copy"
  | none => g

/-- You may exile the discarded card, recorded as `lastKnownPower`, and play
it until the end of your next turn. -/
def offerMayExileDiscarded (g : Game) (controller : PlayerId)
    (lastKnownPower : Option Int) : Game :=
  let id? :=
    match lastKnownPower with
    | some n =>
      if n ≥ 0 then some (g.followMoved ⟨n.toNat⟩) else none
    | none => none
  match id?.bind g.findObject? with
  | some o =>
    if o.zone == .graveyard controller then
      g.change (.pending (.fraChoice controller (.moonstoneMayExile o.id)))
        |>.logMsg s!"You may exile {o.name} from your graveyard"
    else
      g.logMsg "The discarded card is no longer in your graveyard"
  | none => g.logMsg "No discarded card is in the graveyard"

/-- You may create a 0/4 Wall creature token with defender. -/
def offerMayCreateWall (g : Game) (controller : PlayerId) : Game :=
  g.change (.pending (.fraChoice controller (.mayCreateTokens .wall04defender 1)))
    |>.logMsg
      s!"{(g.player controller).name} may create a 0/4 Wall creature token with defender"

/-- Put a +1/+1 counter on each announced creature you control, up to the
life gained in that event (the trigger's last-known power). -/
def putPlusOnesUpToLastKnown (g : Game) (controller : PlayerId)
    (targets : Array Target) (lastKnownPower : Option Int) : Game :=
  let n := (lastKnownPower.getD 0).toNat
  (targets.extract 0 n).foldl (fun (g : Game) t =>
    match t with
    | Target.permanent id =>
      match g.findObject? id with
      | some o =>
        if o.isOnBattlefield && o.isCreature && o.controlledBy controller then
          g.addPlusOnePlusOneTo o 1
        else g.logMsg "The target is no longer legal"
      | none => g.logMsg "The target is no longer legal"
    | _ => g.logMsg "The target is no longer legal") g

/-- Resolve a modeled leftover trigger from its `SharedTrigger` constructor.
Effects are applied from that structured payload — not from Oracle text. -/
def applyModeledTrigger (g : Game) (controller : PlayerId) (t : TriggeredAbility)
    (sourceId : Option ObjectId) (targets : Array Target := #[])
    (sourceName : String := "This creature")
    (lastKnownPower : Option Int := none) : Game :=
  match t.shared with
  | (.step .copyAbsorbingMan) =>
    g.applyBecomeCopy controller sourceId targets .artifactEnchantmentOrLand
  | (.step .copyTaskmaster) =>
    g.applyBecomeCopy controller sourceId targets .creatureOrGraveyardCard
  | (.casting .mayPayHasteUnblockable) =>
    g.offerPayForReflexive controller sourceId #[.generic 1] 9
  | (.youAttacking .exileTopHeroPump) =>
    g.offerExileTopHeroPump controller sourceId
  | (.youAttacking .pay2LifeToughness) =>
    g.offerPay2LifeToughness controller
  | (.death .attackingReturnHand) =>
    g.returnCauseToOwnerHand targets
  | (.death .villainReturnAsHero) =>
    g.returnCauseUnderOwner controller targets (some .villain)
      [.additionalSubtype .hero, .counter .finality]
  | (.casting .villainToken) =>
    g.createKindTokens controller .villain21menace 1
  | (.resource .plusOneCreateInsectOnce) =>
    g.createKindTokens controller .insect11green 1
  | (.resource .plusOneOnHeroesCreateWall) =>
    g.offerMayCreateWall controller
  | (.resource .secondDrawBecome66) =>
    g.withSourceOnBattlefield sourceId (fun g o =>
      g.changeStatuses o.id
        #[.setBasePT (some (6, 6)), .grantUntilEot Keyword.trample]
        |>.logMsg s!"{o.name}'s base power and toughness become 6/6")
      "The source is no longer in play"
  | (.casting .visionModes) =>
    g.offerVisionModes controller t sourceId targets lastKnownPower sourceName
  | (.casting .ironFistTap) =>
    g.grantIronFistTap sourceId
  | (.casting .drawPowerEqualHand) =>
    (g.draw controller 1).grantHandSizePower sourceId
  | (.step .hydeChoose) =>
    match lastKnownPower with
    | none => g.offerHydeChoice controller sourceId
    | some mode => g.applyHydeMode controller sourceId mode.toNat targets
  | (.resource .drawIfAnotherHeroDamage) =>
    if (g.permanentsOf controller).any (fun o =>
        g.hasSubtype o .hero && some o.id != sourceId) then
      g.withLegalKindTarget controller .opponent targets (fun g tgt =>
        match tgt with
        | Target.player pid => g.dealDamageToPlayer pid 1
        | _ => g) sourceId none
    else
      g.logMsg "Human Torch's ability has no effect"
  | (.step .drawToTen) =>
    g.drawUpToHandSize controller 10
  | (.step .harnessedFlicker) =>
    g.resolveHarnessedFlicker controller sourceId targets
  | (.youAttacking .lookSixCast) =>
    g.offerLookSixCast controller
  | (.step .enchantedControllerDraws) =>
    g.drawForEnchantedController sourceId
  | (.death .hellcatReturn) =>
    g.returnSourceUnderOwner controller sourceId
      [.loseAllAbilities, .keywords Keyword.haste, .counter .plusOnePlusOne (asEnters := true)]
  | (.death .deathtouchOppSac) =>
    g.continueNontokenSacrifices ((g.livingOpponents controller).map (·.id)) #[]
  | (.casting .exileFlicker) =>
    let kind := EffectTargetKind.filtered {
      noun := "another target nonland, nontoken permanent"
      nonTypes := #[.land], nontoken := true, another := true }
    g.withLegalKindPermanent controller kind targets (fun g o =>
      let name := o.name
      let (g, newId) := g.move o.id .exile none
      g.change (.pushDelayedEndStepReturn newId)
        |>.logMsg s!"{name} is exiled until the beginning of the next end step")
      sourceId (some "The target is no longer legal")
  | (.casting .damageEqualMv) =>
    let n := g.castSpellManaValue controller lastKnownPower
    g.applyDamageToKindTarget controller .playerOrCreature targets n sourceId none
  | (.casting .merfolkFromBlue) =>
    g.createMerfolkForBlueSymbols controller lastKnownPower
  | (.casting .plusOneEachOther) =>
    g.forEachControlledCreature controller (fun g o =>
      if some o.id != sourceId then g.addPlusOnePlusOneTo o 1 else g)
  | (.casting .plusOneThis) =>
    g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
      "The source is no longer in play"
  | (.casting .plusOneScry) =>
    let g :=
      g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 1)
        "The source is no longer in play"
    g.beginScry controller 1
  | (.casting .targetsGainFlying) =>
    g.grantKeywordsToSpellCreatureTargets Keyword.flying
  | (.casting .copyIfArtifactOrLand) =>
    let g := g.withSourceOnBattlefield sourceId (fun g o => g.addPlusOnePlusOneTo o 2)
      "The source is no longer in play"
    g.copyCastTriggerSpell controller
  | (.casting .tapCreatureOrLand) =>
    let kind := EffectTargetKind.filtered {
      noun := "target creature or land",
      types := #[.creature, .land] }
    g.withLegalKindPermanent controller kind targets
      (fun g o => g.applyPermanentAction o .tap) sourceId
      (some "The target is no longer legal")
  | (.resource .discardExilePlay) =>
    g.offerMayExileDiscarded controller lastKnownPower
  | (.resource .secondDrawPlusOneTarget) =>
    g.withLegalKindPermanent controller .creature targets
      (fun g o => g.addPlusOnePlusOneTo o 1) sourceId
      (some "The target is no longer legal")
  | (.resource .secondDrawDrain) =>
    let g := g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    g.gainLife controller 1
  | (.resource .gainLifePlusOnes) =>
    g.putPlusOnesUpToLastKnown controller targets lastKnownPower
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
    let n := g.countSubtype controller .squirrel
    g.createKindTokens controller .squirrel11green (if n == 0 then 1 else n)
  else if text.contains "Treasure token for each Villain" then
    let n := g.countSubtype controller .villain
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
    g.changePlayer controller (.addMana (.colored .white))
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
          let (g, newId) := g.move id (.library owner) none
          let pl := g.player owner
          let without := pl.library.filter (· != newId)
          g.changePlayer owner (.library (#[newId] ++ without))
            |>.logMsg s!"{o.name} is put on the bottom of {(g.player owner).name}'s library"
        else
          let (g, newId) := g.move id (.library owner) none
          let pl := g.player owner
          let lib := pl.library
          let without := lib.filter (· != newId)
          let lib :=
            match without.back? with
            | none => #[newId]
            | some top => without.pop.push newId |>.push top
          g.changePlayer owner (.library lib)
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
        g.offerMaySearchBasics owner
      | none => g
    else g

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
  g.spellPaidTeamwork

/-- `alt` if the resolving spell paid teamwork; otherwise `base`. -/
def teamworkAmount (g : Game) (base alt : Nat) : Nat :=
  if g.resolvingTeamworkPaid then alt else base

/-- Add `types` to `p`'s mana pool and log it (shared `.addMana` resolution). -/
def addManaLogged (g : Game) (p : PlayerId) (types : Array ManaType) : Game :=
  let g := g.changePlayers p (types.map fun t => .addMana t)
  g.logMsg s!"{(g.player p).name} adds mana"

/-- Ask the target spell's controller to pay `{n}` or let it be countered. -/
def beginPayOrLetCounter (g : Game) (targets : Array Target) (n : Nat) : Game :=
  match targets[0]? with
  | some (Target.card id) =>
    match g.findObject? id with
    | some o =>
      let ctrl := o.controller.getD o.owner
      ((g.clearUnlessPays).change (.pending (.payOrLetCounter ctrl n id))).logMsg
        s!"{(g.player ctrl).name} may pay \{{n}} or {o.name} is countered"
    | none => g.logMsg "The target is no longer legal"
  | _ => g.logMsg "The target is no longer legal"

/-- Ask the target's controller to pay `{n}`. If they do not, resolve `r`.
Countering uses the existing “pay or let the spell be countered” choice. -/
def beginUnlessPays (g : Game) (controller : PlayerId) (effect : Effect)
    (targets : Array Target) (r : SpellResolution) (n : Nat) : Game :=
  match r with
  | .counter => g.beginPayOrLetCounter targets n
  | _ =>
    let payer? : Option (PlayerId × ObjectId) :=
      match targets[0]? with
      | some (Target.card id) =>
        match g.findObject? id with
        | some o => some (o.controller.getD o.owner, id)
        | none => none
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          let pid? :=
            if o.zone == .battlefield then o.controller
            else o.lastController.orElse (fun _ => o.controller)
          -- The pending choice still stores an object id. Use one that has
          -- not been allocated so the counter fallback cannot hit this permanent.
          match pid? with
          | some pid => some (pid, { raw := g.nextObjectId })
          | none => none
        | none => none
      | some (Target.player pid) => some (pid, { raw := g.nextObjectId })
      | _ => none
    match payer? with
    | none => g.logMsg "The target is no longer legal"
    | some (payer, spellId) =>
      let inner := { effect with resolution := Resolution.ofSpell r }
      (g.changes #[
        .pending (.payOrLetCounter payer n spellId),
        .unlessPaysInstead (some inner),
        .unlessPaysController controller,
        .unlessPaysTargets targets,
        .unlessPaysDue false]).logMsg
        s!"{(g.player payer).name} may pay \{{n}} or {SpellResolution.toPhrase r effect.targeting.kind.noun}"

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
      g.changeObjects newId #[.playPermission none, .linkedExile #[]]
    else g
  let (g, retId) := g.move newId .battlefield (some owner)
  let ret := g.object! retId
  let g :=
    if land then
      if tapped then
        g.changeStatus retId (.tapped true)
      else g
    else
      g.changeStatus retId (.summoningSick (!ret.printed.keywords.haste))
  let g := g.logMsg s!"{name} {logText}"
  if land then g.afterLandEnters (g.object! retId)
  else g.afterPermanentEnters (g.object! retId)

end Game
end Mtg.Engine
