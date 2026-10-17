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

/-- Players `who` names. `.opponentHasYou` is an offer, not a recipient.
An announced player that was not chosen is `none`. -/
def collectPlayers (g : Game) (ctx : TriggerRead) (who : TriggeredAbility.PlayerSelector) :
    Option (Array PlayerId) :=
  let controller := ctx.controller
  let one (pid : PlayerId) : Option (Array PlayerId) := some #[pid]
  match who with
  | .you => one controller
  | .eachOpponent => some ((g.livingOpponents controller).map (·.id))
  | .target | .targetOpponent =>
    match ctx.targets.findSome? fun
      | Target.player pid => some pid
      | _ => none with
    | some pid => one pid
    | none => none
  | .thatPlayer =>
    ctx.lastKnownToughness.map fun idx => #[⟨idx.toNat⟩]
  | .damagedPlayer =>
    one (g.lastCombatDamagePlayer.getD (g.opponent controller))
  | .enchantedController =>
    match g.attachedHost? ctx.sourceId with
    | some host => one (host.controller.getD host.owner)
    | none => none
  | .announced =>
    match ctx.targets.findSome? fun
      | Target.player pid => some pid
      | _ => none with
    | some pid => one pid
    | none =>
      match (g.resolvingAbility.bind g.findObject?).bind (·.lastKnownToughness) with
      | some idx => one ⟨idx.toNat⟩
      | none => none
  | .notedController =>
    if g.destroyedForAmassThisWay then g.amassControllerThisWay.map (#[·]) else none
  | .targetController =>
    match ctx.targets.findSome? fun
      | Target.permanent oid => some oid
      | _ => none with
    | some oid =>
      match g.findObject? (g.followMoved oid) with
      | some o =>
        one ((o.controller.orElse (fun _ => o.lastController)).getD o.owner)
      | none => none
    | none => none
  | .opponentHasYou => none

/-- Permanents `who` names. Selectors that name a card, a hand, or a
choice that has not been offered are `none`. An empty array means the
selector named permanents and none of them are on the battlefield. -/
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
  | .target | .permanent _ | .targetIfPresent | .announced | .announcedCreature
    | .creatureTarget | .optionalCreature | .artifactEnchantmentOrLand
    | .eachTarget | .eachUpToLastKnown | .announcedEquipment | .eachTargetEquipment
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
  | .targetWhileSource =>
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
  | .othersOfSubtypes subtypes =>
    some (g.battlefield.filter fun o =>
      o.isCreature && o.controlledBy controller && some o.id != sourceId &&
        subtypes.any (g.hasSubtype o))
  | .othersOfSubtype subtype =>
    some (g.battlefield.filter fun o =>
      o.controlledBy controller && some o.id != sourceId && g.hasSubtype o subtype)
  | .opponentsCreatures =>
    some (g.battlefield.filter fun o => o.isCreature && !o.controlledBy controller)
  | .youControlSubtype subtype =>
    some (g.creaturesControlledBy controller |>.filter (g.hasSubtype · subtype))
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
  | .equippedLegendary =>
    match sourceId.bind g.findObject? with
    | some eq =>
      match eq.attachedTo.bind onBf with
      | some host =>
        if host.isLegendary && host.controller == some controller then some #[host] else someEmpty
      | none => someEmpty
    | none => someEmpty
  | .targetCreature =>
    some (permanentTargets.filter (·.isCreature))
  | .targetPlaneswalker =>
    some (permanentTargets.filter (·.printed.isPlaneswalker))
  | .targetAnotherSubtype subtype =>
    some (permanentTargets.filter fun o =>
      g.hasSubtype o subtype && some o.id != sourceId)
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
  | .attackingSource =>
    match sourceId.bind onBf with
    | some o => if o.status.attacking then some #[o] else someEmpty
    | none => someEmpty
  | .player _ | .youIfCast | .cards _ _ | .hand | .chosenNonland
    | .graveyardCard | .graveyardPermanent | .milledSubtype _
    | .revealed | .basicLand | .linkedExile | .graveyardInstants _
    | .opponentChosenCreature | .eachPlayersCreature | .leastPower
    | .combatDamager | .another | .chosenNontokenCreature
    | .cardFromHand | .top | .basicUpTo _ _ | .discarded | .opponentTop _
    | .nonlandMvAtMost _ | .notedLands | .discardedLand | .landFromHand
    | .artifactFromHand | .randomCreature | .forest | .basicLandOnTop
    | .dragon | .creatureMvAtMost _ | .creatureFromHand _ _
    | .creatureCard | .anyYouControl | .questCounters | .creatureCardsInGraveyard =>
    none

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
  | .targetOpponent, .theVoid =>
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
