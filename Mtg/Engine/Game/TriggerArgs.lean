import Mtg.Engine.Game.Chapters

/-!
# Reading `TriggerResolution` arguments

Counts, players, and permanents named by a selector. A printed match arm
keeps its own log and side effects; these readers supply every other
combination so a constructor argument is applied instead of dropped.
-/

namespace Mtg.Engine
namespace Game

/-- Context a `NumberSelector` or `PlayerSelector` is read in. -/
structure TriggerRead where
  controller : PlayerId
  sourceId : Option ObjectId := none
  targets : Array Target := #[]
  lastKnownPower : Option Int := none
  lastKnownToughness : Option Int := none
  sequencedCardPower : Option Nat := none

/-- Object id recorded as the cause of the ability now resolving. -/
private def recordedCauseId (g : Game) : Option ObjectId :=
  ((g.resolvingAbility.bind g.findObject?).bind (·.fraCauseId)).map g.followMoved

/-- Objects of `xs` that also occur in `ys`, in the order of `xs`. -/
def intersectObjects (xs ys : Array GameObject) : Array GameObject :=
  xs.filter fun o => ys.any (·.id == o.id)

/-- `xs`, then each object of `ys` whose id is not already named. -/
def unionObjects (xs ys : Array GameObject) : Array GameObject :=
  ys.foldl (fun acc o => if acc.any (·.id == o.id) then acc else acc.push o) xs

/-- Permanents named by every set. One `none` names nothing.
An empty list names nothing. -/
private def intersectPermanentSets (parts : List (Option (Array GameObject))) :
    Option (Array GameObject) :=
  match parts with
  | [] => some #[]
  | none :: _ => none
  | some xs :: rest =>
    match intersectPermanentSets rest with
    | none => none
    | some ys =>
      match rest with
      | [] => some xs
      | _ => some (intersectObjects xs ys)

/-- Permanents named by any set. A `none` adds nothing.
Every part `none` names nothing as `none`. An empty list names nothing. -/
private def unionPermanentSets (parts : List (Option (Array GameObject))) :
    Option (Array GameObject) :=
  if parts.isEmpty then some #[]
  else
    let named := parts.filterMap id
    if named.isEmpty then none
    else some (named.foldl (fun acc xs => unionObjects acc xs) #[])

/-- Permanents `who` names. Selectors that name a card, a hand, or a
choice that has not been offered are `none`. An empty array means the
selector named permanents and none of them are on the battlefield.
`.any` and `.target .any` are the announced permanents. A restriction
read on its own names the same permanents as `.target` of that
restriction. Any other `.target` restriction names nothing.
`.intersection` names permanents every selector names. One selector that
does not name permanents names nothing. `.union` names permanents any
selector names. A selector that does not name permanents adds nothing.
An empty list names nothing. -/
def permanentsNamed (g : Game) (ctx : TriggerRead) (who : TriggeredAbility.ObjectSelector) :
    Option (Array GameObject) :=
  let controller := ctx.controller
  let sourceId := ctx.sourceId
  let onBf (id : ObjectId) : Option GameObject :=
    match g.findObject? id with
    | some o => if o.isOnBattlefield then some o else none
    | none => none
  let permanentTargets :=
    ctx.targets.filterMap fun
      | Target.permanent id => onBf id
      | _ => none
  let someEmpty : Option (Array GameObject) := some #[]
  match who with
  | .source | .sourceIfPresent | .sacrificedSource _ | .plan =>
    match sourceId.bind onBf with
    | some o => some #[o]
    | none => someEmpty
  | .any | .ifPresent | .eachPermanent | .laterCreature | .eachEquipment
    | .target .any | .target .ifPresent | .target .eachPermanent
    | .target .laterCreature | .target .eachEquipment
    | .permanent _ | .announced | .announcedCreature
    | .optionalCreature | .artifactEnchantmentOrLand
    | .eachUpToLastKnown | .announcedEquipment
    | .creatureOrGraveyardCard =>
    some permanentTargets
  | .enchanted | .enchantedWhileSource | .enchantedCreature =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then
        match src.attachedTo.bind onBf with
        | some host => some #[host]
        | none => someEmpty
      else someEmpty
    | none => someEmpty
  | .whileSource | .target .whileSource =>
    match sourceId.bind onBf with
    | some _ => some permanentTargets
    | none => someEmpty
  | .cause subtype =>
    match g.recordedCauseId.bind onBf with
    | some o =>
      match subtype with
      | some s => if g.hasSubtype o s then some #[o] else someEmpty
      | none => some #[o]
    | none => someEmpty
  | .creaturesYouControl => some (g.creaturesControlledBy controller)
  | .othersOfSubtype subtype =>
    some (g.battlefield.filter fun o =>
      o.controlledBy controller && some o.id != sourceId && g.hasSubtype o subtype)
  | .opponentsCreatures =>
    some (g.battlefield.filter fun o => o.isCreature && !o.controlledBy controller)
  | .blockers =>
    match sourceId with
    | some sid => some (g.blockersOf sid)
    | none => someEmpty
  | .eachNonSubtypeAndOpponents subtype =>
    some (g.battlefield.filter fun o => o.isCreature && !g.hasSubtype o subtype)
  | .youControl which =>
    match which with
    | .eachCreature | .citysBlessing => some (g.creaturesControlledBy controller)
    | .subtype s =>
      some ((g.permanentsOf controller).filter (g.hasSubtype · s))
  | .eachOther =>
    some (g.battlefield.filter fun o =>
      o.isCreature && o.controlledBy controller && some o.id != sourceId)
  | .createdToken =>
    match g.createdTokenThisWay.bind onBf with
    | some o => some #[o]
    | none => someEmpty
  | .humans =>
    some (g.battlefield.filter fun o =>
      o.isCreature && o.controlledBy controller && g.hasSubtype o "Human")
  | .attackingCreatures =>
    some (g.battlefield.filter (·.status.attacking))
  | .equipped =>
    match g.attachedHost? sourceId with
    | some host => if host.isOnBattlefield then some #[host] else someEmpty
    | none => someEmpty
  | .firstThisTurn =>
    let id := g.recordedCauseId.orElse (fun _ => g.lastBecameTapped)
    match id.bind onBf with
    | some o => if o.status.tapped then some #[o] else someEmpty
    | none => someEmpty
  | .oppArtifactsEnchantments =>
    some (g.battlefield.filter fun o =>
      !o.controlledBy controller &&
        (o.types.contains .artifact || o.types.contains .enchantment))
  | .permanentDealtDamage =>
    match g.permanentDealtDamageThisWay.bind onBf with
    | some o => some #[o]
    | none => someEmpty
  | .equippedAttackers =>
    some (g.battlefield.filter fun o =>
      o.isCreature && o.status.attacking &&
        g.battlefield.any (fun eq => eq.attachedTo == some o.id))
  | .attackingAlone =>
    match g.attackingAlone? controller with
    | some o => some #[o]
    | none => someEmpty
  | .spellTargets =>
    let ids :=
      match g.castTriggerSpell? with
      | none => #[]
      | some spell =>
        match g.stack.find? (fun (e : StackEntry) => e.objectId == spell.id) with
        | none => #[]
        | some e =>
          e.targets.filterMap fun
            | Target.permanent id => some id
            | _ => none
    some (ids.filterMap fun id =>
      match onBf id with
      | some o => if o.isCreature then some o else none
      | none => none)
  | .equipmentHost =>
    match g.equipmentAttachedHost.bind onBf with
    | some o => some #[o]
    | none => someEmpty
  | .noted | .notedHost =>
    match g.notedHostId.bind onBf with
    | some o => some #[o]
    | none => someEmpty
  | .enteringVillain =>
    match g.recordedCauseId.bind onBf with
    | some o => if g.hasSubtype o "Villain" then some #[o] else someEmpty
    | none => someEmpty
  | .landsYouControl =>
    some ((g.permanentsOf controller).filter (·.printed.isLand))
  | .legendaryCreaturesYouControl =>
    some ((g.permanentsOf controller).filter fun o => o.isCreature && o.isLegendary)
  | .planeswalkersYouControl =>
    some ((g.permanentsOf controller).filter (·.printed.isPlaneswalker))
  | .forestsExceptCause =>
    -- The causing Forest's id is this trigger's last-known power.
    let cause : Option ObjectId := ctx.lastKnownPower.map (fun k => ⟨k.toNat⟩)
    some ((g.permanentsOf controller).filter fun o =>
      g.hasSubtype o "Forest" && some o.id != cause)
  | .creature | .target .creature =>
    some (permanentTargets.filter (·.isCreature))
  | .planeswalker | .target .planeswalker =>
    some (permanentTargets.filter (·.printed.isPlaneswalker))
  | .anotherSubtype subtype | .target (.anotherSubtype subtype) =>
    some (permanentTargets.filter fun o =>
      g.hasSubtype o subtype && some o.id != sourceId)
  | .target _ => none
  | .putArtifact | .putEquipment =>
    match g.putArtifactThisWay with
    | some (oid, _) =>
      match onBf oid with
      | some o =>
        if who == .putEquipment && !o.printed.isEquipment then someEmpty else some #[o]
      | none => someEmpty
    | none => someEmpty
  | .harnessedSource =>
    match sourceId.bind onBf with
    | some o => if o.status.harnessed then some #[o] else someEmpty
    | none => someEmpty
  | .artifact =>
    some ((g.permanentsOf controller).filter (·.printed.isArtifact))
  | .anotherCreatureOrArtifact =>
    match sourceId with
    | some sid =>
      some ((g.permanentsOf controller).filter fun o =>
        o.id != sid && (o.isCreature || o.printed.isArtifact))
    | none => someEmpty
  | .allCreatures =>
    some (g.battlefield.filter (·.isCreature))
  | .creaturesOfTargetPlayer =>
    match ctx.targets.findSome? (fun | Target.player pid => some pid | _ => none) with
    | some pid => some (g.creaturesControlledBy pid)
    | none => someEmpty
  | .nonSubtypeCreatures subtype =>
    some (g.battlefield.filter fun o => o.isCreature && !g.hasSubtype o subtype)
  | .oppCreaturesAndPlaneswalkers =>
    some (g.battlefield.filter fun o =>
      !o.controlledBy controller && (o.isCreature || o.printed.isPlaneswalker))
  | .creaturesExceptYourTokens =>
    some (g.battlefield.filter fun o =>
      o.isCreature && !(o.printed.isToken && o.controlledBy controller))
  | .creaturesWithPlusOne =>
    some (g.battlefield.filter fun o =>
      o.isCreature && o.controlledBy controller && o.status.plusOnePlusOne > 0)
  | .wizardTokensExceptRecent =>
    some (g.battlefield.filter fun o =>
      o.controlledBy controller && o.printed.isToken && g.hasSubtype o "Wizard" &&
        !g.recentTokenIds.contains o.id)
  | .tokensYouControl =>
    some ((g.permanentsOf controller).filter (·.printed.isToken))
  | .targetAt idx =>
    match ctx.targets[idx]? with
    | some (Target.permanent id) =>
      match onBf id with
      | some o => some #[o]
      | none => someEmpty
    | _ => someEmpty
  | .creaturesControlledBy (.targetAt idx) =>
    match ctx.targets[idx]? with
    | some (Target.player pid) => some (g.creaturesControlledBy pid)
    | _ => someEmpty
  | .creaturesControlledBy _ => none
  | .creatureTargets =>
    some (permanentTargets.filter (·.isCreature))
  | .firstTargetCreatureYouControl =>
    match permanentTargets.find? (fun o => o.isCreature && o.controlledBy controller) with
    | some o => some #[o]
    | none => someEmpty
  | .creaturesWithoutFlying =>
    some (g.battlefield.filter fun o => o.isCreature && !g.hasKeyword o (·.flying))
  | .oppPermanents ty =>
    some (g.battlefield.filter fun o => !o.controlledBy controller && o.types.contains ty)
  | .player _ | .youIfCast | .cards _ _ | .hand | .chosenNonland
    | .graveyardCard | .graveyardPermanent | .milledSubtype _
    | .revealed | .basicLand | .linkedExile | .graveyardInstants _
    | .opponentChosenCreature | .eachPlayersCreature | .eachOpponentsCreature | .leastPower
    | .combatDamager | .another | .chosenNontokenCreature
    | .cardFromHand | .top | .basicUpTo _ _ | .discarded | .opponentTop _
    | .nonlandMvAtMost _ | .notedLands | .discardedLand | .landFromHand
    | .artifactFromHand | .randomCreature | .forest | .basicLandOnTop
    | .dragon | .creatureMvAtMost _ | .creatureFromHand _ _
    | .creatureCard | .anyYouControl | .questCounters | .creatureCardsInGraveyard
    | .card | .nonland | .targetSpell | .graveyardSubtype _
    | .allNonlandPermanentsInGraveyard | .chosenNonlandPermanent | .topPower
    | .land | .creatureOrPlaneswalker | .landCard
    | .landsUpTo _ | .landsEqualDamage | .planeswalkerCard | .enchantmentCard
    | .supertypeCard _ _ | .landSubtype _ | .basicBeholdUntap _
    | .basicLandsDifferentNamesX | .artifactCreatureX | .random =>
    none
  | .intersection sels =>
    intersectPermanentSets (sels.map (g.permanentsNamed ctx))
  | .union sels =>
    unionPermanentSets (sels.map (g.permanentsNamed ctx))

/-- Controllers of the objects `what` names.
`none` means `what` does not name objects, or a single object it names
cannot be found.
An empty array means it named objects and none of them remain.
Each player is named once, in the order the objects are named.
The enchanted creature is the creature the source enchants. Nothing
enchanted is `none`.
An announced permanent is read after it has left the battlefield. The
controller it had is used. -/
def controllersNamed (g : Game) (ctx : TriggerRead) (what : TriggeredAbility.ObjectSelector) :
    Option (Array PlayerId) :=
  let controlling (o : GameObject) : PlayerId :=
    (o.controller.orElse (fun _ => o.lastController)).getD o.owner
  let distinct (pids : Array PlayerId) : Array PlayerId :=
    pids.foldl (fun acc pid => if acc.contains pid then acc else acc.push pid) #[]
  match what with
  | .enchanted =>
    match g.attachedHost? ctx.sourceId with
    | some host => some #[host.controller.getD host.owner]
    | none => none
  | .any | .target .any | .permanent _ =>
    let ids := ctx.targets.filterMap fun
      | Target.permanent oid => some (g.followMoved oid)
      | _ => none
    if ids.isEmpty then none
    else
      let pids := distinct (ids.filterMap fun oid => (g.findObject? oid).map controlling)
      if pids.isEmpty then none else some pids
  | what =>
    match g.permanentsNamed ctx what with
    | none => none
    | some objs => some (distinct (objs.map controlling))

/-- Players `who` names. `.opponentHasYou` is an offer, not a recipient.
An announced player that was not chosen is `none`.
`.player`, `.opponent`, `.target .player`, and `.target .opponent` are that
announced player. `.controller` is the controllers of the objects it names.
Any other `.target` restriction names nothing. -/
def collectPlayers (g : Game) (ctx : TriggerRead) (who : TriggeredAbility.PlayerSelector) :
    Option (Array PlayerId) :=
  let controller := ctx.controller
  let one (pid : PlayerId) : Option (Array PlayerId) := some #[pid]
  let announcedPlayer : Option (Array PlayerId) :=
    match ctx.targets.findSome? fun
      | Target.player pid => some pid
      | _ => none with
    | some pid => one pid
    | none => none
  match who with
  | .you => one controller
  | .eachOpponent => some ((g.livingOpponents controller).map (·.id))
  | .eachPlayer => some (g.players.map (·.id))
  | .player | .opponent | .target .player | .target .opponent => announcedPlayer
  | .targetAt idx =>
    match ctx.targets[idx]? with
    | some (Target.player pid) => one pid
    | _ => none
  | .targetPlayers =>
    let pids := ctx.targets.filterMap fun
      | Target.player pid => some pid
      | _ => none
    if pids.isEmpty then none else some pids
  | .controller what => g.controllersNamed ctx what
  | .target _ => none
  | .thatPlayer =>
    ctx.lastKnownToughness.map fun idx => #[⟨idx.toNat⟩]
  | .damagedPlayer =>
    one (g.lastCombatDamagePlayer.getD (g.opponent controller))
  | .announced =>
    match ctx.targets.findSome? fun
      | Target.player pid => some pid
      | _ => none with
    | some pid => one pid
    | none =>
      match (g.resolvingAbility.bind g.findObject?).bind (·.lastKnownToughness) with
      | some idx => one ⟨idx.toNat⟩
      | none => none
  | .opponentHasYou => none

/-- How many objects `what` names.
`none` means `what` does not name a counted set. An empty set is `some 0`.
Quest counters are counted only while the source is on the battlefield.
A missing source, or one that has left, is `none`. -/
def countNamed (g : Game) (ctx : TriggerRead) (what : TriggeredAbility.ObjectSelector) :
    Option Nat :=
  let sourceId := ctx.sourceId
  match what with
  | .questCounters =>
    match sourceId.bind g.findObject? with
    | some src => if src.isOnBattlefield then some src.status.quest else none
    | none => none
  | .creatureCardsInGraveyard =>
    some ((g.player ctx.controller).graveyard.filter (fun id =>
      (g.object! id).printed.isCreature)).size
  | .harnessedSource =>
    match sourceId.bind g.findObject? with
    | some src => some (if src.status.harnessed then 1 else 0)
    | none => some 0
  | .putEquipment =>
    match g.putArtifactThisWay with
    | some (oid, _) =>
      match g.findObject? oid with
      | some o => some (if o.printed.isEquipment then 1 else 0)
      | none => some 0
    | none => some 0
  | _ =>
    (g.permanentsNamed ctx what).map (·.size)

/-- The integer `amount` names. `none` is not a number here: `.double`,
a choice that has not been made, a note that was never written, or a
`.count` whose selector does not name a counted set.
A missing last-known power is zero for `.lastKnownPower` and absent for
`.thatManyLost`. Quest counters that cannot be read are `none`. -/
def triggerInt (g : Game) (ctx : TriggerRead) (amount : TriggeredAbility.NumberSelector) :
    Option Int :=
  let controller := ctx.controller
  let sourceId := ctx.sourceId
  match amount with
  | .fixed n => some n
  | .double => none
  | .chosenCreatureType => none
  | .greatestPower => some (g.greatestPowerAmongCreatures controller)
  | .perLookedAt => some (Int.ofNat (ctx.lastKnownPower.getD 0).toNat)
  | .perOtherCreature =>
    some (g.battlefield.filter (fun c =>
      c.isCreature && c.controlledBy controller && some c.id != sourceId)).size
  | .perPlains => some (g.countSubtype controller "Plains")
  | .equalSourcePower => some (g.sourcePowerAtResolution sourceId ctx.lastKnownPower)
  | .equalSourceToughness =>
    some <|
      match sourceId.bind g.findObject? with
      | some src =>
        if src.isOnBattlefield then g.toughness src
        else ctx.lastKnownToughness.getD (g.toughness src)
      | none => ctx.lastKnownToughness.getD 0
  | .lastKnownPower => some (ctx.lastKnownPower.getD 0)
  | .subtypeCount subtype | .perSubtype subtype =>
    some (g.countSubtype controller subtype)
  | .discardedHand => g.handDiscardedThisWay.map Int.ofNat
  | .greatestArtifactMv =>
    some (g.greatestManaValueAmong controller (·.printed.isArtifact))
  | .spellManaValue =>
    some (g.castSpellManaValue controller ctx.lastKnownPower)
  | .forEachTappedHuman => some g.humansTappedThisWay
  | .perFatGraveyard =>
    some (g.players.filter (fun pl => pl.graveyard.size >= 7)).size
  | .equalToManaSpent =>
    some <|
      ((g.resolvingAbilityObject?.bind (·.fraCauseStatus)).map (·.manaSpentToCast)).getD 0
  | .perControlled ty =>
    some ((g.permanentsOf controller).filter (fun o => o.printed.hasType ty)).size
  | .upToHandSize n =>
    let cards := (g.player controller).hand.size
    if cards < n then some (n - cards) else some 0
  | .plusOneCounters =>
    match sourceId.bind g.findObject? with
    | some src =>
      if src.isOnBattlefield then some src.status.plusOnePlusOne else none
    | none => none
  | .equalToTargetPower =>
    match ctx.sequencedCardPower with
    | some k => some (Int.ofNat k)
    | none =>
      match ctx.targets[0]? with
      | some (Target.card oid) | some (Target.permanent oid) =>
        match g.findObject? oid with
        | some o => some (g.power o)
        | none => none
      | _ => none
  | .forEachDestroyedThisWay => some g.permanentsDestroyedThisWay
  | .attachedEquipment =>
    some (g.attachedEquipmentAtResolution sourceId ctx.lastKnownPower)
  | .perBurden =>
    match sourceId.bind g.findObject? with
    | some src => some src.status.burden
    | none => none
  | .thatManyLost => ctx.lastKnownPower
  | .notedExcess => some g.excessDamageThisWay
  | .notedPower =>
    if g.destroyedForAmassThisWay then some g.amassAmountThisWay else none
  | .perChargeCounter =>
    let n :=
      match sourceId.bind g.findObject? with
      | some o => if o.isOnBattlefield then o.status.charge else 0
      | none => 0
    let n :=
      if n == 0 then
        match sourceId.bind (fun id => g.lastKnownStatus.reverse.find? (·.1 == id)) with
        | some (_, last) => last.charge
        | none => n
      else n
    some n
  | .oppArtifacts => some (g.countOpponentArtifacts controller)
  | .damagedPlayerArtifacts =>
    let pid := g.lastCombatDamagePlayer.getD (g.opponent controller)
    some (g.countArtifactsControlledBy pid)
  | .blueManaSymbols => some (g.blueSymbolsInCastSpell ctx.lastKnownPower)
  | .count what => (g.countNamed ctx what).map (fun n => (n : Int))
  | .cardsDrawnThisTurn => some (g.player controller).cardsDrawnThisTurn
  | .libraryCards => some (g.player controller).library.size
  | .causePower =>
    some ((g.recordedCauseId.bind g.findObject?).map g.power |>.getD 0)
  | .minusGraveyardCards =>
    some (-(Int.ofNat (g.player controller).graveyard.size))
  | .lifeGainedThisTurn =>
    some (g.player controller).lifeGainedThisTurn
  | .cardsDiscardedThisTurn =>
    some (g.player controller).cardsDiscardedThisTurn
  | .milledByTargetPlayerThisTurn =>
    match ctx.targets.findSome? (fun | Target.player pid => some pid | _ => none) with
    | some pid => some (g.player pid).cardsMilledThisTurn
    | none => none
  | .power of =>
    match g.permanentsNamed ctx of with
    | some #[o] => some (g.power o)
    | _ => none
  | .loyalty of =>
    match g.permanentsNamed ctx of with
    | some #[o] => some (Int.ofNat o.status.loyaltyCounters)
    | _ => none
  | .otherSpellsManaValue | .removedPlusOnes | .colorsAmongOtherArtifacts
  | .chosenX | .planeswalkerTypes => none

/-- `triggerInt` as a `Nat`. A negative integer counts as zero. -/
def triggerCount (g : Game) (ctx : TriggerRead) (amount : TriggeredAbility.NumberSelector) :
    Option Nat :=
  g.triggerInt ctx amount |>.map (·.toNat)

/-- Create `n` tokens with `face` for each player. The last token's id is
returned when at least one was created. -/
def spawnFace (g : Game) (pids : Array PlayerId) (face : CardDef) (n : Nat)
    (tapped : Bool := false) : Game × Option ObjectId :=
  Id.run do
    let mut g := g
    let mut last : Option ObjectId := none
    for pid in pids do
      for _ in [0:n] do
        let (g', tok) := g.createToken pid face (tapped := tapped)
        g := g'
        last := some tok.id
    return (g, last)

/-- Recipients of a created token. The Void with no announced opponent is
created for the controller. -/
def tokenRecipients (g : Game) (ctx : TriggerRead) (token : TriggeredAbility.TriggerToken)
    (who : TriggeredAbility.PlayerSelector) : Array PlayerId :=
  match who, token with
  | .target .opponent, .theVoid =>
    match ctx.targets.findSome? fun
      | Target.player pid => some pid
      | _ => none with
    | some pid => #[pid]
    | none => #[ctx.controller]
  | _, _ => (g.collectPlayers ctx who).getD #[]

/-- Mill `pids` `n` cards and record `note`. -/
def millCollected (g : Game) (controller : PlayerId) (pids : Array PlayerId) (n : Nat)
    (note : TriggeredAbility.TriggerMillNote) : Game :=
  match note with
  | .none =>
    pids.foldl (fun g pid => g.mill pid n) g
  | .milledCards =>
    let before := pids.foldl (fun acc pid => acc ++ (g.player pid).graveyard) #[]
    let g := pids.foldl (fun g pid => g.mill pid n) g
    let after := pids.foldl (fun acc pid => acc ++ (g.player pid).graveyard) #[]
    { g with milledIdsThisWay := after.filter (fun id => !before.contains id) }
  | .opponentsMilled =>
    let opps := pids.filter (· != controller)
    let (g, flag) := g.millThenReflexive opps n
    let g := pids.foldl (fun g pid =>
      if pid == controller then g.mill pid n else g) g
    { g with opponentsMilledThisWay := flag }

end Game
end Mtg.Engine
