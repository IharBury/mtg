import Mtg.Engine.Game.Casting

/-!
# Resolution choices

Choices made while resolving: sacrifice choices, lifetime modal choices
(Alliance, Gollum), and card-specific helpers such as beholding a
quality, Riddles in the Dark, The Black Gate, and Gríma's exile.
-/

namespace Mtg.Engine
namespace Game

/-- Permanents `p` may sacrifice to pay “sacrifice another creature or artifact”. -/
def sacrificeCreatureOrArtifactChoices (g : Game) (p : PlayerId) (sourceId : ObjectId) :
    Array GameObject :=
  g.permanentsOf p |>.filter (fun o =>
    o.id != sourceId && (o.isCreature || o.printed.isArtifact))

/-- Creatures `p` may sacrifice to a “sacrifices a creature of their choice” effect. -/
def sacrificeCreatureChoices (g : Game) (p : PlayerId) : Array GameObject :=
  g.creaturesControlledBy p

/-- Whether `sac` is a legal “another creature or artifact” sacrifice for `sourceId`. -/
def canSacrificeAsCreatureOrArtifact (g : Game) (p : PlayerId) (sourceId : ObjectId)
    (sac : GameObject) : Bool :=
  (g.sacrificeCreatureOrArtifactChoices p sourceId).any (·.id == sac.id)

/-- Whether `sac` is a legal creature for `p` to sacrifice to an edict. -/
def canSacrificeCreature (g : Game) (p : PlayerId) (sac : GameObject) : Bool :=
  (g.sacrificeCreatureChoices p).any (·.id == sac.id)

/-- Creatures `p` controls that are tied for least power. -/
def leastPowerCreatures (g : Game) (p : PlayerId) : Array GameObject :=
  let cs := g.sacrificeCreatureChoices p
  match cs[0]? with
  | none => #[]
  | some first =>
    let minP := cs.foldl (fun acc o => min acc (g.power o)) (g.power first)
    cs.filter (fun o => g.power o == minP)

/-- Sacrifice a least-power creature `p` controls. If several are tied and
`chosen` is none, the player still chooses (logged; no sacrifice yet). -/
def sacrificeLeastPowerCreature (g : Game) (p : PlayerId)
    (chosen : Option ObjectId := none) : Game :=
  let tied := g.leastPowerCreatures p
  if tied.isEmpty then
    g.logMsg s!"{(g.player p).name} controls no creatures to sacrifice"
  else
    let pick :=
      match chosen with
      | some id => tied.find? (fun o => o.id == id)
      | none => if tied.size == 1 then some tied[0]! else none
    match pick with
    | some o =>
      g.sacrificeToGraveyard o
        s!"{(g.player p).name} sacrifices {o.name} (least power)"
    | none =>
      g.logMsg
        s!"{(g.player p).name} chooses one of the creatures tied for least power to sacrifice"

/-- Modes in `all` that have not yet been chosen. -/
def unusedModes (chosen : Array Nat) (all : Array Nat := #[0, 1, 2]) : Array Nat :=
  all.filter (fun m => !chosen.contains m)

/-- Unused Alliance modes on `src` (0 = add GGG, 1 = +1/+1 each, 2 = scry 2
then draw). -/
def unusedAllianceModes (_g : Game) (src : GameObject) : Array Nat :=
  unusedModes src.status.allianceModesChosen

/-- Apply one Alliance mode of `sourceId` if it has not been chosen this turn.
If every mode was already chosen, the ability is removed with no effect. -/
def applyAllianceMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if src.status.allianceModesChosen.size >= 3 ||
        (g.unusedAllianceModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen this turn. The ability is removed from the stack with no effect"
    else if src.status.allianceModesChosen.contains mode then
      g.logMsg "That Alliance mode has already been chosen this turn"
    else
      let g := g.setObject { src with status :=
        { src.status with allianceModesChosen := src.status.allianceModesChosen.push mode } }
      match src.controller, mode with
      | some c, 0 =>
        let g := g.modifyPlayer c (fun pl =>
          { pl with manaPool :=
            pl.manaPool.add (.colored .green) 3 })
        g.logMsg ((g.player c).name ++ " adds {G}{G}{G}")
      | some c, 1 =>
        Id.run do
          let mut g := g
          for o in g.battlefield do
            if o.isCreature && o.controlledBy c then
              g := g.setObject { o with status := o.status.addPlusOnePlusOne 1 }
          return g.logMsg
            s!"{(g.player c).name} puts a +1/+1 counter on each creature they control"
      | some c, 2 =>
        (g.draw c 1).logMsg ((g.player c).name ++ " scries 2, then draws a card")
      | _, _ => g

/-- Unused Gollum modes on `src` (0 = +1/+1, 1 = drain, 2 = draw). Modes last
for the object's lifetime (ruling 164). -/
def unusedGollumModes (_g : Game) (src : GameObject) : Array Nat :=
  unusedModes src.status.chosenModes

/-- Apply one unused Gollum mode. If every mode was already chosen, the
ability is removed with no effect and Gollum remains. -/
def applyGollumMode (g : Game) (sourceId : ObjectId) (mode : Nat) : Game :=
  match g.findObject? sourceId with
  | none =>
    g.logMsg "The ability is removed from the stack with no effect"
  | some src =>
    if (g.unusedGollumModes src).isEmpty then
      g.logMsg
        "all three modes have been chosen. The ability is removed from the stack with no effect"
    else if src.status.chosenModes.contains mode then
      g.logMsg "That mode has already been chosen"
    else
      let g := g.setObject { src with status :=
        { src.status with chosenModes := src.status.chosenModes.push mode } }
      match src.controller, mode with
      | some _, 0 =>
        let src := g.object! sourceId
        let g := g.setObject { src with status := src.status.addPlusOnePlusOne 1 }
        g.logMsg s!"{src.name} gets a +1/+1 counter"
      | some c, 1 =>
        let g := g.forEachOpponent c (fun g pid =>
          let pl := g.player pid
          g.setLife pid (pl.life - 2)
            s!"{pl.name} loses 2 life ({pl.life - 2} life)")
        let pl := g.player c
        g.setLife c (pl.life + 2)
          s!"{pl.name} gains 2 life ({pl.life + 2} life)"
      | some c, 2 =>
        g.draw c 1
      | _, _ => g

/-- Apply the first unused mode of `sourceId`, or log `gone` / `exhausted`. -/
def applyNextUnusedMode (g : Game) (sourceId : Option ObjectId)
    (unused : GameObject → Array Nat)
    (apply : Game → ObjectId → Nat → Game)
    (exhausted : String)
    (gone := "The ability is removed from the stack with no effect") : Game :=
  match sourceId with
  | none => g.logMsg gone
  | some sid =>
    match g.findObject? sid with
    | none => g.logMsg gone
    | some src =>
      match (unused src)[0]? with
      | none => g.logMsg exhausted
      | some mode => apply g sid mode

/-- As Gollum enters, choose odd (`true`) or even (`false`). Zero is even. -/
def chooseGollumParity (g : Game) (sourceId : ObjectId) (odd : Bool) : Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.setObject { src with status := { src.status with chosenOdd := some odd } }
    g.logMsg
      (if odd then s!"{src.name}: odd is chosen" else s!"{src.name}: even is chosen")

/-- Remove an indestructible counter as a cost (ruling 357). -/
def payRemoveIndestructibleCounter (g : Game) (o : GameObject) : Except String Game := do
  if o.status.indestructibleCounters == 0 then
    throw s!"{o.name} has no indestructible counter"
  let g := g.setObject { o with status :=
    { o.status with indestructibleCounters := o.status.indestructibleCounters - 1 } }
  return g.logMsg s!"{o.name} loses an indestructible counter"

/-- Resolve Arwen, Mortal Queen's activated ability. An illegal target means
no counters are put on Arwen or the target (ruling 189). -/
def resolveArwenShare (g : Game) (arwenId : ObjectId) (targetId : Option ObjectId) : Game :=
  match targetId.bind g.findObject? with
  | none =>
    g.logMsg "The target is no longer legal. The ability does nothing."
  | some o =>
    if !o.isOnBattlefield || !o.isCreature || o.id == arwenId then
      g.logMsg "The target is no longer legal. The ability does nothing."
    else
      let putCounters (g : Game) (oid : ObjectId) : Game :=
        match g.findObject? oid with
        | none => g
        | some x =>
          let g := g.setObject { x with status :=
            { x.status with
              plusOnePlusOne := x.status.plusOnePlusOne + 1
              lifelinkCounters := x.status.lifelinkCounters + 1 } }
          g.logMsg s!"{x.name} gets a +1/+1 counter and a lifelink counter"
      let g := g.setObject { o with status := o.status.grantUntilEot Keyword.indestructible }
      let g := g.logMsg s!"{o.name} gains indestructible until end of turn"
      let g := putCounters g o.id
      putCounters g arwenId

/-- Behold a quality: choose a matching permanent you control or reveal a
matching card from your hand. Later zone changes do not un-behold (117). -/
def beholdQuality (g : Game) (p : PlayerId) (quality : String) : Game :=
  let hasPerm := (g.permanentsOf p).any (fun o => g.hasSubtype o quality)
  let hasHand :=
    (g.player p).hand.any (fun id =>
      match g.findObject? id with
      | some o => o.printed.hasSubtype quality
      | none => false)
  if hasPerm || hasHand then
    let g := g.modifyPlayer p (fun pl =>
      { pl with beheldQualities := pl.beheldQualities.push quality })
    g.logMsg s!"{(g.player p).name} beholds a {quality}"
  else
    g.logMsg s!"{(g.player p).name} does not behold a {quality}"

/-- True when `p` has beheld `quality`, even if the card or permanent later left. -/
def qualityWasBeheld (g : Game) (p : PlayerId) (quality : String) : Bool :=
  (g.player p).beheldQualities.contains quality

/-- Choose a creature type as this permanent enters. The static pump applies
immediately; no player may act between the choice and the bonus. -/
def chooseCreatureTypeAsEnters (g : Game) (sourceId : ObjectId) (creatureType : String) :
    Game :=
  match g.findObject? sourceId with
  | none => g
  | some src =>
    let g := g.setObject { src with status :=
      { src.status with chosenCreatureType := some creatureType } }
    g.logMsg s!"{src.name}: {creatureType} is chosen as it enters"

/-- Draw one card for each graveyard with seven or more cards. -/
def drawPerSevenCardGraveyard (g : Game) (p : PlayerId) : Game :=
  let n := g.players.filter (fun pl => pl.graveyard.size >= 7) |>.size
  if n == 0 then
    g.logMsg s!"{(g.player p).name} draws no cards (no graveyard has seven cards)"
  else
    g.draw p n

/-- Discard the hand (zero cards is legal) and draw that many. The choice is
made during resolution; nothing happens between discard and draw. -/
def mayDiscardHandDrawThatMany (g : Game) (p : PlayerId) (doDiscard : Bool) : Game :=
  if !doDiscard then
    g.logMsg s!"{(g.player p).name} does not discard their hand"
  else
    let ids := (g.player p).hand
    let n := ids.size
    let g :=
      ids.foldl (fun acc id =>
        match acc.findObject? id with
        | none => acc
        | some o =>
          let (acc, _) := acc.move id (.graveyard o.owner) none
          acc) g
    let g := g.logMsg s!"{(g.player p).name} discards {n} card(s)"
    if n == 0 then g else g.draw p n

/-- Players currently tied for most life. -/
def playersWithMostLife (g : Game) : Array PlayerId :=
  let living := g.livingPlayers
  match living[0]? with
  | none => #[]
  | some first =>
    let best := living.foldl (fun acc pl => max acc pl.life) first.life
    living.filter (fun pl => pl.life == best) |>.map (·.id)

/-- The Black Gate: check most life as the ability resolves, then those
creatures (including later ones) cannot block the target this turn. -/
def applyBlackGateUnblockable (g : Game) (attackerId : ObjectId)
    (chosen : PlayerId) : Game :=
  if !(g.playersWithMostLife).contains chosen then
    g.logMsg "The chosen player does not have the most life. The ability does nothing."
  else
    match g.findObject? attackerId with
    | none => g.logMsg "The target is no longer legal"
    | some o =>
      if !o.isOnBattlefield then
        g.logMsg "The target is no longer legal"
      else
        let g := g.setObject { o with status :=
          { o.status with cantBeBlockedByPlayer := some chosen } }
        g.logMsg
          s!"{o.name} can't be blocked by creatures {(g.player chosen).name} controls this turn"

/-- Put the returned cards onto the battlefield as Food artifacts only.
They keep name, mana cost, mana value, abilities, and legendary. -/
def supperForSpidersReturn (g : Game) (controller : PlayerId)
    (ids : Array ObjectId) : Game :=
  ids.foldl (fun acc id =>
    match acc.findObject? id with
    | none => acc
    | some o =>
      if o.zone != .graveyard o.owner then acc
      else
        let (acc, newId) := acc.move id .battlefield (some controller)
        let o := acc.object! newId
        let acc := acc.setObject { o with status :=
          { o.status with onlyFoodArtifact := true, summoningSick := true } }
        acc.logMsg s!"{o.name} returns as a Food artifact") g

/-- Exile the top `n` cards face down. They may be played while exiled if you
control `subtype`. Timing and costs are unchanged. -/
def exileTopPlayIfYouControlSubtype (g : Game) (p : PlayerId) (n : Nat)
    (subtype : String) : Game :=
  Id.run do
    let mut g := g
    for _ in List.range n do
      let pl := g.player p
      if pl.library.isEmpty then
        g := g.logMsg s!"{pl.name} has no cards in their library to exile"
      else
        let top := pl.library.back!
        let cardName := (g.object! top).name
        let (g', newId) := g.move top .exile none
        g := g'
        let o := g.object! newId
        g := g.setObject { o with
          playPermission := some {
            player := p
            turnEndsRemaining := 0
            whileExiled := true
            requireSubtype := some subtype
            faceDown := true } }
        g := g.logMsg s!"{pl.name} exiles a card face down"
        let _ := cardName
    return g

/-- Exile cards from `victim`'s library until an instant or sorcery, face up.
An empty library becomes that player's library again. The found card may be
cast as this ability resolves, ignoring timing. Uncast cards go on the bottom
in a random order. -/
partial def grimaExileUntilInstantOrSorcery (g : Game) (controller victim : PlayerId)
    (castTheCard : Bool) : Game :=
  Id.run do
    let mut g := g
    let mut exiled : Array ObjectId := #[]
    let mut found : Option ObjectId := none
    while found.isNone && !(g.player victim).library.isEmpty do
      let top := (g.player victim).library.back!
      let name := (g.object! top).name
      let (g', newId) := g.move top .exile none
      g := g'
      let o := g.object! newId
      g := g.logMsg s!"{(g.player victim).name} exiles {name} face up"
      if o.printed.isInstantOrSorcery then
        found := some newId
      else
        exiled := exiled.push newId
    match found with
    | none =>
      return g.requestOrderInto exiled (.library victim)
        s!"{(g.player victim).name} randomizes the exiled cards; they become that player's library"
    | some instId =>
      if castTheCard then
        let o := g.object! instId
        let (g', _) := g.move instId .stack (some controller)
        g := g'.logMsg
          s!"{(g.player controller).name} casts {o.name} as the ability resolves"
      else
        let (g', _) := g.move instId (.library victim) none
        g := g'
      return g.requestOrderInto exiled (.library victim)
        s!"{(g.player victim).name} puts the remaining exiled cards on the bottom of their library in a random order"

/-- An uncast copy ceases the next time state-based actions are checked. -/
def ceaseUncastCopies (g : Game) : Game :=
  g.objects.foldl (fun acc o =>
    if o.isCopy && o.zone != .stack && o.zone != .battlefield then
      let acc := acc.ceaseToExist o.id
      acc.logMsg s!"{o.name} ceases to exist"
    else acc) g

/-- True when `p` can pay Saruman's ward (discard an enchantment, instant,
or sorcery card). -/
def canPaySarumanWard (g : Game) (p : PlayerId) : Bool :=
  (g.player p).hand.any (fun id =>
    match g.findObject? id with
    | some o => o.printed.isEnchantment || o.printed.isInstant || o.printed.isSorcery
    | none => false)

/-- Legendary artifacts and creatures `p` may sacrifice to Sauron's ward. -/
def legendaryWardSacrificeChoices (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (fun o =>
    o.isLegendary && (o.isCreature || o.printed.isArtifact))

/-- Split the top four library cards into a face-up pile and a face-down pile.
A 4/0 split is legal. The face-down pile is not revealed if it is put into
hand. -/
def riddlesInTheDark (g : Game) (p : PlayerId) (faceUpCount : Nat)
    (chooseFaceDown : Bool) : Game :=
  let lib := (g.player p).library
  let n := min 4 lib.size
  let taken := lib.extract (lib.size - n) lib.size
  let faceUpN := min faceUpCount taken.size
  let faceUp := taken.extract (taken.size - faceUpN) taken.size
  let faceDown := taken.extract 0 (taken.size - faceUpN)
  let g := g.logMsg
    s!"{(g.player p).name} separates {faceUp.size} face-up and {faceDown.size} face-down"
  let toHand := if chooseFaceDown then faceDown else faceUp
  let toGy := if chooseFaceDown then faceUp else faceDown
  let g :=
    if chooseFaceDown then
      g.logMsg "The face-down pile is put into hand without being revealed"
    else
      g.logMsg "The face-up pile is put into hand"
  let g :=
    toHand.foldl (fun acc id =>
      (acc.move id (.hand p) none).1) g
  toGy.foldl (fun acc id =>
    (acc.move id (.graveyard p) none).1) g

/-- Linked activated abilities last only while the copier still has them. -/
def linkedAbilitiesStillLinked (stillHasThoseAbilities : Bool) : Bool :=
  stillHasThoseAbilities

/-- Treat a copied activated ability as referring to the copier's name. -/
def rewriteAbilityCardName (abilityText printedName copierName : String) : String :=
  abilityText.replace printedName copierName

/-- Must-attack-if-able may be declined when every legal attack would cost. -/
def mustAttackCanDeclineIfOnlyAttackCosts (onlyAttacksRequireCost : Bool) : Bool :=
  onlyAttacksRequireCost

/-- Ares and similar “attacks each combat if able” statics (MSH 130). -/
def hasAttacksIfAble (o : GameObject) : Bool :=
  o.staticAbilities.any (fun
    | .attacksEachCombatIfAble => true
    | _ => false) ||
    o.printed.oracleText.contains "attacks each combat if able"

/-- True when `o` must attack this combat. Summoning sickness, being tapped,
or an unpaid attack cost means it does not have to attack (MSH 130). -/
def mustAttackIfAble (g : Game) (o : GameObject) (attackRequiresCost := false) : Bool :=
  hasAttacksIfAble o && g.canAttack o &&
    !mustAttackCanDeclineIfOnlyAttackCosts attackRequiresCost

/-- Failed Adventure from Bilbo's graveyard ability is exiled by Bilbo, not
as an Adventure, so it cannot be cast as a permanent later. -/
def exileFailedAdventureFromBilbo (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, newId) := g.move id .exile none
    let o := g.object! newId
    let g := g.setObject { o with playPermission := none, adventurerCard := none }
    g.logMsg s!"{name} is exiled (Bilbo's replacement). It cannot be cast as a permanent"

/-- Tom Bombadil is on the battlefield as a final chapter finishes resolving,
so his last ability triggers (ruling 74). -/
def finishSagaFinalChapter (g : Game) (controller : PlayerId) : Game :=
  let g := g.logMsg "The final chapter ability is removed from the stack"
  match (g.permanentsOf controller).find? (fun o =>
    o.printed.hexproofIndestructibleIfLore.isSome) with
  | none => g
  | some tom =>
    g.putMatchingSourceTriggers controller tom .finalSagaChapterResolves
        |>.logMsg s!"{tom.name}'s last ability triggers"

/-- A token copy of a battlefield permanent. The copy is not kicked. -/
def copyBattlefieldPermanent (g : Game) (src : GameObject) (controller : PlayerId)
    : Game × GameObject :=
  let (g, tok) := g.createToken controller src.printed
  let tok := { tok with kicked := false }
  (g.setObject tok, tok)

/-- Whether the source of a proposed activated ability can still pay tap/sacrifice/discard. -/
def sourceStillPayable (g : Game) (prop : ProposedSpell) : Bool :=
  match prop.sourceId with
  | none => true
  | some sid =>
    match g.findObject? sid with
    | none => false
    | some src =>
      (src.isOnBattlefield && src.controlledBy prop.caster &&
        (!prop.tapSource || !src.status.tapped) && !prop.discardSource) ||
      (src.zone == .graveyard src.owner && src.owner == prop.caster &&
        !prop.tapSource && !prop.sacrificeSource && !prop.discardSource) ||
      (src.zone == .hand src.owner && src.owner == prop.caster &&
        prop.discardSource && !prop.tapSource && !prop.sacrificeSource)

end Game
end Mtg.Engine
