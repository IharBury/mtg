import Mtg.Engine.Game.Allocation

/-!
# Tokens (CR 111)

Printed definitions of the tokens the engine creates, and token creation
including create-multipliers and Food/Treasure replacement effects.
-/

namespace Mtg.Engine
namespace Game

/-- A Treasure token (CR 111.10a). -/
def treasureToken : CardDef := {
  name := "Treasure"
  types := #[.artifact]
  subtypes := #["Treasure"]
  tapSacrificeAddAnyColor := true
  isToken := true
}

/-- A creature token. `color` is the color indicator (CR 202.2e). -/
def creatureToken (name : String) (subtypes : Array CardSubtype)
    (power toughness : Int) (color : Option Color := none)
    (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) : CardDef := {
  name
  types
  subtypes := subtypes.map CardSubtype.englishName
  power := some power
  toughness := some toughness
  colorIndicator := color.map ColorSet.singleton
  keywords
  isToken := true
}

/-- A 5/5 red Dragon creature token with flying. -/
def dragon55flyingToken : CardDef :=
  creatureToken "Dragon" #[.dragon] 5 5 (some .red) (keywords := Keyword.flying)

/-- A 1/1 white Human Soldier creature token. -/
def humanSoldierToken : CardDef :=
  creatureToken "Human Soldier" #[.human, .soldier] 1 1 (some .white)

/-- Additional +1/+1 counters from Arwen, Weaver of Hope as `entering` enters.
Only weavers already on the battlefield before timestamp `asOf` apply
(simultaneous enters do not see each other). -/
def hopeCountersOnEnter (g : Game) (entering : GameObject) (asOf : Nat) : Nat :=
  match entering.controller with
  | none => 0
  | some p =>
    if !entering.isCreature then 0
    else
      (g.permanentsOf p).foldl (fun acc weaver =>
        if weaver.id == entering.id then acc
        else if !((g.baseCard weaver).othersEnterWithPlusOneEqualToughness &&
            g.retainsPrintedAbilities weaver) then acc
        else if weaver.timestamp >= asOf then acc
        else acc + (g.toughness weaver).toNat) 0

/-- Put `n` additional +1/+1 counters on `o` as it enters from hope-weaver
replacements. -/
def applyHopeEnterCounters (g : Game) (o : GameObject) (asOf : Nat) : Game :=
  let n := g.hopeCountersOnEnter o asOf
  if n == 0 then g
  else
    let g := g.recordPutCounters o.id .plusOnePlusOne n (byPlayer := g.controllerOf o)
    g.logMsg s!"{g.nameWithToken o} enters with {n} additional +1/+1 counter(s)"

/-- Counters placed on `entering` as it enters the battlefield from replacement
effects (CR 614.1c / 614.12 / 306.5b / 714.3a). -/
def computeEntersWithCounters (g : Game) (entering : GameObject)
    (fromStackTime : Nat := 0) (applyHope : Bool := true)
    (asOf : Nat := g.timestamp) (extraCounters : CounterBag := #[]) : CounterBag :=
  (g.applyEtbReplacements entering (fromStackTime := fromStackTime)
    (applyHope := applyHope) (asOf := asOf) (extraCounters := extraCounters)).entersWith

/-- Create one token on the battlefield, running the CR 616.1a–g ETB replacement
loop for the entering token (CR 111.2 / 608.2c / 614.1c). Callers that must let
enters-the-battlefield triggers see the token (amass, recruit) invoke
`afterPermanentEnters` after this returns. -/
def createOneToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) (attacking := false)
    (attackingTarget : Option AttackTarget := none)
    (extraCounters : CounterBag := #[])
    (recordRecent : Bool := false)
    (cause : Option EventCause := none) : Game × GameObject :=
  if (g.player controller).lost then
    (g.logMsg "no token is created (CR 800.4b)",
      { id := ⟨0⟩, printed := { printed with isToken := true },
        owner := controller, zone := .command })
  else
    g.withBatchReturn cause fun g =>
      let printed := { printed with isToken := true }
      let sick := printed.isCreature && !printed.keywords.haste
      let asOf := g.timestamp
      let newId : ObjectId := ⟨g.nextObjectId⟩
      let ts := g.timestamp + 1
      let isAttacking := attacking || attackingTarget.isSome
      let resolvedAttackTarget : Option AttackTarget :=
        if isAttacking then
          some (attackingTarget.getD (.player g.defendingPlayer))
        else none
      let baseObj : GameObject := {
        id := newId
        printed := printed
        owner := controller
        controller := some controller
        defaultController := some controller
        zone := .battlefield
        status := {
          tapped := tapped
          summoningSick := sick
          attacking := isAttacking
          attackingTarget := resolvedAttackTarget
        }
        timestamp := ts
      }
      let etb :=
        g.applyEtbReplacements baseObj (asOf := asOf) (extraCounters := extraCounters)
          (cause := cause)
      match etb.choice? with
      | some (chooser, choices) =>
        (g.promptChooseReplacement chooser choices
          (.createToken controller printed tapped isAttacking resolvedAttackTarget false extraCounters recordRecent cause),
         baseObj)
      | none =>
      let g := g.consumeReplacementOrder etb.applied
      let obj := etb.candidate
      let g := g.record (GameEvent.created g.turnNumber controller (g.snapshot obj) (cause := etb.cause))
      let g : Game :=
        match resolvedAttackTarget with
        | some tgt =>
          g.record (GameEvent.becameAttacking g.turnNumber (g.snapshot (g.object! newId)) tgt
            (cause := etb.cause))
        | none => g
      let g := g.createPrintedStaticEffects (g.object! newId)
      let g := g.logMsg s!"{(g.player controller).name} creates {g.nameWithToken (g.object! newId)}"
      let g :=
        if etb.weaverBonus > 0 then
          g.logMsg s!"{g.nameWithToken (g.object! newId)} enters with {etb.weaverBonus} additional +1/+1 counter(s)"
        else g
      -- Storied is not a trigger; an artifact token can be the third permanent.
      let g := g.refreshEnduringStory
      let g := g.refreshCitysBlessing
      let g :=
        if recordRecent then
          g.change (.recentTokenIds (g.recentTokenIds.push newId))
        else g
      (g, g.object! newId)

/-- True if a proposed token creation of `printed` under `controller` watches
`.wouldCreateToken`. -/
private def tokenBatchWatchesCreation (g : Game) (controller : PlayerId) (printed : CardDef) : Bool :=
  let proposed := GameEvent.created g.turnNumber controller {
    controller := some controller, owner := controller, token := true
    types := printed.types
    subtypes :=
      let baseSubs := CardSubtype.ofSubtypes printed.subtypes
      if printed.keywords.changeling && (printed.types.contains .creature || printed.types.contains .kindred) then
        CardSubtype.allCreatureSubtypes.foldl (fun acc s => if acc.contains s then acc else acc.push s) baseSubs
      else baseSubs
    changeling := printed.keywords.changeling }
  proposed.watches .wouldCreateToken

/-- True if `printed` is a Food token as created. -/
private def tokenBatchIsFood (printed : CardDef) : Bool :=
  (CardSubtype.ofSubtypes printed.subtypes).contains .food

/-- Run the CR 616.1 replacement loop on a proposed token-creation batch
(CR 614.1a / 614.5 / 614.6 / 616.1), returning `(batches, applied, choice?)`.
Handles:
- Bilbo, Fellow Conspirator (`foodAlsoCreatesTreasure` / `.createExtraTokenWithFood`)
- Draconic Visitor (`artifactTokensBecomeDragons` / `.artifactTokensBecome`, rulings 780–782)
- Bard, King of Dale (`tokenDoubling` / `.multiplyTokenCreation`, rulings 180 / 190)
- Active `ContinuousEffect.replacement` specs for token creation. -/
def replaceTokenCreationChoice (g : Game) (initial : ProposedTokenBatch)
    (applied : Array ReplacementId := #[])
    (includeKindReplacements : Bool := true)
    (includeMultiplier : Bool := true) :
    Array ProposedTokenBatch × Array ReplacementId × Option (PlayerId × Array ReplacementId) := Id.run do
  if initial.count == 0 then
    return (#[], applied, none)
  let mut batches : Array ProposedTokenBatch := #[initial]
  let mut curApplied := applied
  let mut curOrder := g.replacementOrder
  let mut choice? : Option (PlayerId × Array ReplacementId) := none
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    let ctrl := initial.controller
    let anyWatch := batches.any (fun b => g.tokenBatchWatchesCreation b.controller b.printed)
    if !anyWatch then
      fuel := 0
    else
      let hasFood := batches.any (fun b => tokenBatchIsFood b.printed)
      let hasArtifact := batches.any (fun b => b.printed.isArtifact)
      let mut specs : Array ReplacementSpec := #[]
      if includeKindReplacements && hasFood then
        for o in g.permanentsOf ctrl do
          if (g.baseCard o).foodAlsoCreatesTreasure && g.retainsPrintedAbilities o then
            specs := specs.push {
              id := { kind := .foodAlsoCreatesTreasure, object := some o.id }
              source := some o.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .createExtraTokenWithFood ctrl treasureToken
            }
      if includeKindReplacements && hasArtifact then
        for o in g.permanentsOf ctrl do
          if (g.staticAbilities o).any (· == .artifactTokensBecomeDragons) then
            specs := specs.push {
              id := { kind := .artifactTokensBecomeDragons, object := some o.id }
              source := some o.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .artifactTokensBecome ctrl dragon55flyingToken
            }
      if includeMultiplier then
        for o in g.permanentsOf ctrl do
          if (g.baseCard o).tokenDoubling && g.retainsPrintedAbilities o then
            specs := specs.push {
              id := { kind := .tokenDoubling, object := some o.id }
              source := some o.id
              controller := some ctrl
              affectedPlayer := ctrl
              kind := .multiplyTokenCreation ctrl 2
            }
      for (_, eff) in g.activeEffects do
        match eff with
        | .replacement spec _ =>
          match spec.kind with
          | .createExtraTokenWithFood p _ =>
            if includeKindReplacements && p == ctrl && hasFood then specs := specs.push spec
          | .artifactTokensBecome p _ =>
            if includeKindReplacements && p == ctrl && hasArtifact then specs := specs.push spec
          | .multiplyTokenCreation p _ =>
            if includeMultiplier && p == ctrl then specs := specs.push spec
          | _ => pure ()
        | _ => pure ()
      let candidates := specs.map (fun s => (ReplacementOrPrevention.replacement s).toCandidate)
      match g.selectNextReplacementStep candidates curApplied curOrder with
      | .none => fuel := 0
      | .needChoice chooser choices ord' =>
        curOrder := ord'
        choice? := some (chooser, choices)
        fuel := 0
      | .chosen chosen ord' =>
        curOrder := ord'
        match specs.find? (fun s => s.id == chosen.id) with
        | none => fuel := 0
        | some spec =>
          curApplied := curApplied.push chosen.id
          match spec.kind with
          | .createExtraTokenWithFood _ extraCard =>
            let foodCount := batches.foldl (fun acc b =>
              if tokenBatchIsFood b.printed then acc + b.count else acc) 0
            batches := batches.map (fun b =>
              if tokenBatchIsFood b.printed then
                { b with cause := g.wrapReplacedCause chosen.id b.cause (some ctrl) }
              else b)
            if foodCount > 0 then
              let baseCause := batches[0]!.cause
              batches := batches.push {
                controller := ctrl
                printed := extraCard
                count := foodCount
                tapped := initial.tapped
                cause := baseCause
              }
          | .artifactTokensBecome _ newCard =>
            batches := batches.map (fun b =>
              if b.printed.isArtifact then
                { b with
                  printed := newCard
                  cause := g.wrapReplacedCause chosen.id b.cause (some ctrl) }
              else b)
          | .multiplyTokenCreation _ factor =>
            batches := batches.map (fun b =>
              { b with
                count := b.count * factor
                cause := g.wrapReplacedCause chosen.id b.cause (some ctrl) })
          | _ => pure ()
  return (batches, curApplied, choice?)

/-- Run the CR 616.1 replacement loop on a proposed token-creation batch
(CR 614.1a / 614.5 / 614.6 / 616.1), returning `(batches, applied, choice?)`. -/
def replaceTokenCreation (g : Game) (initial : ProposedTokenBatch)
    (applied : Array ReplacementId := #[])
    (includeKindReplacements : Bool := true)
    (includeMultiplier : Bool := true) :
    Array ProposedTokenBatch × Array ReplacementId × Option (PlayerId × Array ReplacementId) :=
  g.replaceTokenCreationChoice initial (applied := applied)
    (includeKindReplacements := includeKindReplacements)
    (includeMultiplier := includeMultiplier)

/-- Create each single-token batch in `batches`, stopping if an ETB replacement
choice opens so the remaining batches can resume after the choice is answered. -/
def createTokenBatches (g : Game) (batches : Array ProposedTokenBatch)
    (attacking : Bool := false) (attackingTarget : Option AttackTarget := none)
    (extraCounters : CounterBag := #[])
    (recordRecent : Bool := false)
    (cause : Option EventCause := none) : Game × GameObject :=
  g.withBatchReturn cause fun g => Id.run do
    let mut g := g
    let mut last : Option GameObject := none
    for i in [0:batches.size] do
      let b := batches[i]!
      let isPrimary :=
        b.attacking == attacking && b.attackingTarget == attackingTarget &&
          b.extraCounters == extraCounters
      let (g', obj) := g.createOneToken b.controller b.printed (tapped := b.tapped)
        (attacking := b.attacking)
        (attackingTarget := b.attackingTarget)
        (extraCounters := b.extraCounters) (recordRecent := recordRecent && isPrimary)
        (cause := b.cause)
      g := g'
      if isPrimary then
        last := some obj
      else if last.isNone then
        last := some obj
      if let .chooseReplacement .. := g.pending then
        let rem := batches.extract (i + 1) batches.size
        if !rem.isEmpty then
          g := g.chainPendingReplacement
            (.createTokenBatches rem attacking attackingTarget extraCounters recordRecent cause)
        return (g, obj)
    match last with
    | some obj => (g, g.object! obj.id)
    | none => (g, g.object! ⟨0⟩)

/-- Create a token under `controller`, running the CR 616.1 token-creation
replacement loop (Food/Treasure, Draconic Visitor, token-doubling). -/
def createToken (g : Game) (controller : PlayerId) (printed : CardDef)
    (tapped := false) (_batch := false) (attacking := false)
    (attackingTarget : Option AttackTarget := none)
    (applyFoodBonus : Bool := true)
    (extraCounters : CounterBag := #[])
    (recordRecent : Bool := false)
    (cause : Option EventCause := none) : Game × GameObject :=
  if (g.player controller).lost || !applyFoodBonus then
    g.createOneToken controller printed (tapped := tapped)
      (attacking := attacking)
      (attackingTarget := attackingTarget)
      (extraCounters := extraCounters) (recordRecent := recordRecent) (cause := cause)
  else
    let (batches, applied, choice?) := g.replaceTokenCreationChoice {
      controller := controller
      printed := printed
      count := 1
      tapped := tapped
      attacking := attacking
      attackingTarget := attackingTarget
      extraCounters := extraCounters
      cause := cause
    }
    match choice? with
    | some (chooser, choices) =>
      (g.promptChooseReplacement chooser choices
        (.createToken controller printed tapped attacking attackingTarget true extraCounters recordRecent cause),
       { id := ⟨0⟩, printed := { printed with isToken := true },
         owner := controller, zone := .command })
    | none =>
    let g := g.consumeReplacementOrder applied
    let expanded := batches.foldl (fun acc b =>
      Id.run do
        let mut acc := acc
        for _ in [0:b.count] do
          acc := acc.push { b with count := 1 }
        return acc) #[]
    g.createTokenBatches expanded (attacking := attacking)
      (attackingTarget := attackingTarget) (extraCounters := extraCounters)
      (recordRecent := recordRecent) (cause := cause)

/-- Create `n` Treasure tokens, optionally tapped. -/
def createTreasureTokens (g : Game) (controller : PlayerId) (n : Nat)
    (tapped := false) (cause : Option EventCause := none) : Game :=
  if (g.player controller).lost then
    if n == 0 then g else g.logMsg "no token is created (CR 800.4b)"
  else
    g.withBatch cause fun g => Id.run do
      let mut g := g
      for i in [0:n] do
        let (g', _) := g.createToken controller treasureToken (tapped := tapped) (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := n - (i + 1)
          if rem > 0 then
            g := g.chainPendingReplacement (.createTreasureTokens controller rem tapped cause)
          return g
      return g

/-- A 0/0 black Army creature token of the given subtype (amass). -/
def armyToken (subtype : CardSubtype) : CardDef := {
  name := s!"{subtype} Army"
  types := #[.creature]
  subtypes := #[subtype.englishName, "Army"]
  power := some 0
  toughness := some 0
  colorIndicator := some (ColorSet.singleton .black)
  isToken := true
}

/-- A 0/0 black Goblin Army creature token (amass Goblins). -/
def goblinArmyToken : CardDef := armyToken .goblin

/-- A 0/0 black Orc Army creature token (amass Orcs). -/
def orcArmyToken : CardDef := armyToken .orc

/-- A 0/0 black Zombie Army creature token (amass Zombies). -/
def zombieArmyToken : CardDef := armyToken .zombie

/-- A Food token (CR 111 / 701.34). -/
def foodToken : CardDef := {
  name := "Food"
  types := #[.artifact]
  subtypes := #["Food"]
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := Effect.gainLife 3
  }]
  isToken := true
}

def wolfToken : CardDef :=
  creatureToken "Wolf" #[.wolf] 2 2 (some .green)

def dwarfToken : CardDef :=
  creatureToken "Dwarf" #[.dwarf] 2 2 (some .red)

def bearToken : CardDef :=
  creatureToken "Bear" #[.bear] 2 2 (some .green)

def elfToken : CardDef :=
  creatureToken "Elf" #[.elf] 1 1 (some .green)

/-- A 1/1 white Spirit creature token with flying. -/
def spiritToken : CardDef :=
  creatureToken "Spirit" #[.spirit] 1 1 (some .white) Keyword.flying

/-- A 4/4 white Bird Soldier creature token with flying. -/
def birdSoldierToken : CardDef :=
  creatureToken "Bird Soldier" #[.bird, .soldier] 4 4 (some .white) Keyword.flying

/-- A 6/6 red Dragon creature token with flying. -/
def dragonToken : CardDef :=
  creatureToken "Dragon" #[.dragon] 6 6 (some .red) Keyword.flying

/-- A 3/1 colorless Wall artifact creature token with defender. -/
def wallToken : CardDef :=
  creatureToken "Stone Boulder" #[.wall] 3 1 none Keyword.defender
    (types := #[.artifact, .creature])

/-- A colorless Equipment artifact token named Axe. -/
def axeToken : CardDef := {
  name := "Axe"
  types := #[.artifact]
  subtypes := #["Equipment"]
  staticAbilities := #[.equippedCreatureGets 1 0]
  activatedAbilities := #[
    { cost := { mana := ManaCost.ofGeneric 2 }
      effect := Effect.attachToTargetCreatureYouControl
      onlyAsSorcery := true }
  ]
  isToken := true
}

/-- A Clue artifact token (CR 701.55). -/
def clueToken : CardDef := {
  name := "Clue"
  types := #[.artifact]
  subtypes := #["Clue"]
  activatedAbilities := #[{
    cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true }
    effect := Effect.abilityDraw 1
  }]
  isToken := true
}

/-- A 3/2 white Hero creature token with vigilance. -/
def hero32vigilanceToken : CardDef :=
  creatureToken "Hero" #[.hero] 3 2 (some .white) Keyword.vigilance

/-- A 2/1 black Villain creature token with menace. -/
def villain21menaceToken : CardDef :=
  creatureToken "Villain" #[.villain] 2 1 (some .black) Keyword.menace

/-- A 2/2 colorless Robot Villain artifact creature token. -/
def robotVillain22Token : CardDef :=
  creatureToken "Robot Villain" #[.robot, .villain] 2 2 none
    (types := #[.artifact, .creature])

/-- A 6/5 blue Leviathan creature token with hexproof. -/
def leviathan65hexproofToken : CardDef :=
  creatureToken "Leviathan" #[.leviathan] 6 5 (some .blue) Keyword.hexproof

/-- A 1/1 white Soldier creature token. -/
def soldier11whiteToken : CardDef :=
  creatureToken "Soldier" #[.soldier] 1 1 (some .white)

/-- A 1/1 green Squirrel creature token. -/
def squirrel11greenToken : CardDef :=
  creatureToken "Squirrel" #[.squirrel] 1 1 (some .green)

/-- A 0/4 colorless Wall creature token with defender. -/
def wall04defenderToken : CardDef :=
  creatureToken "Wall" #[.wall] 0 4 none Keyword.defender

/-- A 3/3 colorless Robot Villain artifact creature token named Doombot. -/
def doombotToken : CardDef :=
  creatureToken "Doombot" #[.robot, .villain] 3 3 none
    (types := #[.artifact, .creature])

/-- A 1/1 green Insect creature token. -/
def insect11greenToken : CardDef :=
  creatureToken "Insect" #[.insect] 1 1 (some .green)

/-- A 1/1 green Minion creature token named Moloid. -/
def moloidToken : CardDef :=
  creatureToken "Moloid" #[.minion] 1 1 (some .green)

/-- A 1/1 red Alien creature token with haste that attacks each combat if able. -/
def alien11redHasteToken : CardDef := {
  name := "Alien"
  types := #[.creature]
  subtypes := #["Alien"]
  power := some 1
  toughness := some 1
  colorIndicator := some (ColorSet.singleton .red)
  keywords := Keyword.haste
  staticAbilities := #[.attacksEachCombatIfAble]
  isToken := true
}

/-- A predefined Vibranium artifact token (MSH). Indestructible; `{T}: Add {C}`
that cannot be spent to cast a nonartifact spell. -/
def vibraniumToken : CardDef := {
  name := "Vibranium"
  types := #[.artifact]
  subtypes := #["Vibranium"]
  keywords := Keyword.indestructible
  tapAddMana := #[.colorless]
  isToken := true
}

/-- A 2/2 colorless Wizard Soldier creature token named Cadet (FRA). -/
def cadetToken : CardDef :=
  creatureToken "Cadet" #[.wizard, .soldier] 2 2 none

/-- A red and green Heartwood artifact token. `{T}: Add {R} or {G}`. -/
def heartwoodToken : CardDef := {
  name := "Heartwood"
  types := #[.artifact]
  subtypes := #["Heartwood"]
  colorIndicator := some ((ColorSet.singleton .red).insert .green)
  tapAddOneOf := #[ManaType.colored .red, ManaType.colored .green]
  isToken := true
}

/-- A colorless Lotus artifact token. `{T}`, sacrifice: add three mana of any
one color. -/
def lotusToken : CardDef := {
  name := "Lotus"
  types := #[.artifact]
  isToken := true
  staticAbilities := #[.fra .tapSacrificeAddThreeOfOneColor]
}

/-- A blue Jace planeswalker token with loyalty 0, `[-1]: Surveil 1`, and
`[-3]: Draw a card` (Reality Fracture). -/
def jacePlaneswalkerToken : CardDef := {
  name := "Jace"
  types := #[.planeswalker]
  subtypes := #["Jace"]
  colorIndicator := some (ColorSet.singleton .blue)
  loyalty := some 0
  isToken := true
  activatedAbilities := #[
    { cost := { loyalty := some (.minus 1) }
      effect := { resolution := .surveil 1, phrase := "Surveil 1" } },
    { cost := { loyalty := some (.minus 3) }
      effect := { resolution := .draw 1, phrase := "Draw a card" } }]
}

/-- A 1/1 colorless Sculpture Treasure artifact creature token. -/
def sculptureToken : CardDef :=
  { creatureToken "Sculpture" #[.sculpture, .treasure] 1 1 none
      (types := #[.artifact, .creature]) with
    tapSacrificeAddAnyColor := true }

/-- A legendary 3/3 green Dog creature token named Mowu. -/
def mowuToken : CardDef := {
  name := "Mowu"
  types := #[.creature]
  subtypes := #["Dog"]
  supertypes := #[.legendary]
  power := some 3
  toughness := some 3
  colorIndicator := some (ColorSet.singleton .green)
  isToken := true
}

/-- A 2/2 white Cat Soldier creature token named Ajani's Pridemate. -/
def pridemateToken : CardDef :=
  { creatureToken "Ajani's Pridemate" #[.cat, .soldier] 2 2 (some .white) with
    triggeredAbilities := #[TriggeredAbility.onGainLifePlusOne] }

/-- A 3/3 green Forest Tentacle land creature token. It isn't basic (ruling
802); the Forest type gives it `{T}: Add {G}`. -/
def forestTentacleToken : CardDef :=
  creatureToken "Forest Tentacle" #[.forest, .tentacle] 3 3 (some .green)
    (types := #[.land, .creature])

/-- A 4/4 green Beast creature token with trample. -/
def beast44trampleToken : CardDef :=
  creatureToken "Beast" #[.beast] 4 4 (some .green) (keywords := Keyword.trample)

/-- Jace planeswalker tokens `controller` controls. Nontoken Jace
planeswalkers don't count, but a token copy of one does (ruling 733). -/
def jacePlaneswalkerTokens (g : Game) (controller : PlayerId) : Array GameObject :=
  (g.permanentsOf controller).filter (fun o =>
    g.isPlaneswalker o && g.hasSubtype o .jace && o.printed.isToken)

/-- Empower Jace `n` (Reality Fracture, ruling 732). If you don't control a
Jace planeswalker token, create one with 0 loyalty. Then put `n` loyalty
counters on a Jace planeswalker token you control. You can't create a new
token while you control one; with several, `chosen` picks which (ruling
731), defaulting to the one that entered most recently. -/
def empowerJace (g : Game) (controller : PlayerId) (n : Nat)
    (chosen : Option ObjectId := none) : Game :=
  let g :=
    if (g.jacePlaneswalkerTokens controller).isEmpty then
      let (g, _) := g.createToken controller jacePlaneswalkerToken
      g.logMsg s!"{(g.player controller).name} creates a Jace planeswalker token"
    else g
  let tokens := g.jacePlaneswalkerTokens controller
  let pick :=
    match chosen.bind (fun id => tokens.find? (·.id == id)) with
    | some o => some o
    | none =>
      tokens.foldl (fun (best : Option GameObject) (o : GameObject) =>
        match best with
        | some b => if o.timestamp ≥ b.timestamp then some o else best
        | none => some o) none
  match pick with
  | none => g.logMsg "Empower Jace creates no token"
  | some o =>
    let k := g.countersYouPut o n (putter := some controller)
    let g :=
      if k > 0 then
        g.record (GameEvent.counters g.turnNumber (some controller) o.asEvent .loyalty k)
      else g
    g.logMsg s!"Empower Jace {n}: {k} loyalty counter(s) are put on {g.name o}"

/-- Printed characteristics for a `TokenKind`. -/
def tokenPrinted (k : TokenKind) : CardDef :=
  match k with
  | .treasure => treasureToken
  | .food => foodToken
  | .humanSoldier => humanSoldierToken
  | .wolf => wolfToken
  | .dwarf => dwarfToken
  | .bear => bearToken
  | .elf => elfToken
  | .spirit => spiritToken
  | .birdSoldier => birdSoldierToken
  | .wall => wallToken
  | .dragon => dragonToken
  | .clue => clueToken
  | .hero32vigilance => hero32vigilanceToken
  | .villain21menace => villain21menaceToken
  | .robotVillain22 => robotVillain22Token
  | .leviathan65hexproof => leviathan65hexproofToken
  | .soldier11white => soldier11whiteToken
  | .squirrel11green => squirrel11greenToken
  | .wall04defender => wall04defenderToken
  | .doombot => doombotToken
  | .insect11green => insect11greenToken
  | .vibranium => vibraniumToken
  | .moloid => moloidToken
  | .cadet => cadetToken
  | .heartwood => heartwoodToken
  | .lotus => lotusToken
  | .jace => jacePlaneswalkerToken
  | .sculpture => sculptureToken
  | .mowu => mowuToken
  | .pridemate => pridemateToken
  | .beast44trample => beast44trampleToken
  | .dragon55flying => dragon55flyingToken
  | .forestTentacle => forestTentacleToken
  | .thopter =>
    creatureToken "Thopter" #[.thopter] 1 1 (keywords := Keyword.flying)
      (types := #[.artifact, .creature])
  | .angel33blue => creatureToken "Angel" #[.angel] 3 3 (some .blue) (keywords := Keyword.flying)
  | .illusion11blue => creatureToken "Illusion" #[.illusion] 1 1 (some .blue)
  | .leviathan88hexproof =>
    creatureToken "Leviathan" #[.leviathan] 8 8 (some .blue) (keywords := Keyword.hexproof)

/-- Create `n` tokens of `kind`. -/
def createKindTokens (g : Game) (controller : PlayerId) (kind : TokenKind)
    (n : Nat) (tapped := false) (attacking := false)
    (attackingTarget : Option AttackTarget := none)
    (resetRecent : Bool := true)
    (cause : Option EventCause := none) : Game :=
  if (g.player controller).lost then
    let g := if resetRecent then g.change (.recentTokenIds #[]) else g
    if n == 0 then g
    else g.logMsg "no token is created (CR 800.4b)"
  else
    let g := if resetRecent then g.change (.recentTokenIds #[]) else g
    g.withBatch cause fun g => Id.run do
      let mut g := g
      let isAttacking := attacking || attackingTarget.isSome
      let resolvedTarget :=
        if isAttacking then
          some (attackingTarget.getD (.player g.defendingPlayer))
        else none
      let printed := tokenPrinted kind
      for i in [0:n] do
        let (g', _) := g.createToken controller printed (tapped := tapped)
          (attacking := isAttacking)
          (attackingTarget := resolvedTarget) (recordRecent := true) (cause := cause)
        g := g'
        if let .chooseReplacement .. := g.pending then
          let rem := n - (i + 1)
          if rem > 0 then
            g := g.chainPendingReplacement
              (.createKindTokens controller kind rem tapped attacking attackingTarget false cause)
          return g
      return g

end Game
end Mtg.Engine
