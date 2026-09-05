import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Auras

/-!
# Adventurer cards and blocking restrictions.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/- Smaug, the Great Calamity // Spew Flame (CR 715). -/

/-- Smaug in hand, an opposing creature, and enough mana for either face. -/
def smaugSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  withRedMana (addToHand g smaugTheGreatCalamityCard ⟨0⟩) ⟨0⟩ 7

#guard smaugTheGreatCalamityCard.hasAdventure
#guard smaugTheGreatCalamityCard.keywords.flying
#guard smaugSetup.canCast ⟨0⟩ (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")
#guard smaugSetup.canCastAdventure ⟨0⟩ (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity")
#guard smaugSetup.asSorcery? ⟨0⟩

/-- Spew Flame requires a creature. -/
def smaugNoTarget : Game :=
  withRedMana (addToHand afterDraw smaugTheGreatCalamityCard ⟨0⟩) ⟨0⟩ 5

#guard !smaugNoTarget.canCastAdventure ⟨0⟩
  (handCardNamed smaugNoTarget ⟨0⟩ "Smaug, the Great Calamity")
#guard
  match smaugNoTarget.apply ⟨0⟩
      (.castAdventure (handCardNamed smaugNoTarget ⟨0⟩ "Smaug, the Great Calamity").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- A card without an Adventure cannot be cast as one.
#guard
  match boltSetup.apply ⟨0⟩ (.castAdventure boltInHand.id) with
  | .error msg => mentions msg "has no Adventure"
  | .ok _ => false

def proposedSpewFlame : Game :=
  mustApply smaugSetup ⟨0⟩
    (.castAdventure (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id)

#guard proposedSpewFlame.pending == .chooseTargets ⟨0⟩
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).name == "Spew Flame"
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).printed.isSorcery
#guard (proposedSpewFlame.object! proposedSpewFlame.stack.back!.objectId).isAdventureSpell
#guard proposedSpewFlame.log.any (fun s => mentions s "begins casting Spew Flame")
#guard proposedSpewFlame.log.any (fun s => mentions s "must choose a target (CR 601.2c)")

-- Spew Flame cannot target a player.
#guard
  match proposedSpewFlame.apply ⟨0⟩ (.target (Target.player ⟨1⟩)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- The heuristic targets an opposing creature.
#guard
  match Agent.choose proposedSpewFlame ⟨0⟩ with
  | some (.target (Target.permanent tid)) =>
    (proposedSpewFlame.object! tid).name == "Grizzly Bears"
  | _ => false

def targetedSpewFlame : Game :=
  mustApply proposedSpewFlame ⟨0⟩
    (.target (Target.permanent (namedPermanent proposedSpewFlame "Grizzly Bears").id))

#guard targetedSpewFlame.pending == .activateManaAbilities ⟨0⟩
#guard targetedSpewFlame.stack.back!.targets ==
  #[Target.permanent (namedPermanent targetedSpewFlame "Grizzly Bears").id]

def paidSpewFlame : Game := mustApply targetedSpewFlame ⟨0⟩ .pay

#guard paidSpewFlame.hasPriority ⟨0⟩
#guard paidSpewFlame.log.any (fun s => mentions s "casts Spew Flame")
#guard (paidSpewFlame.object! paidSpewFlame.stack.back!.objectId).name == "Spew Flame"

def resolvedSpewFlame : Game := passBoth paidSpewFlame

#guard resolvedSpewFlame.stack.isEmpty
#guard !(resolvedSpewFlame.battlefield.any (fun o => o.name == "Grizzly Bears"))
#guard resolvedSpewFlame.log.any (fun s => mentions s "Grizzly Bears is dealt 5 damage")
#guard resolvedSpewFlame.objects.any (fun o =>
  o.zone == .exile && o.name == "Smaug, the Great Calamity")
#guard !((resolvedSpewFlame.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedSpewFlame.object! id).name == "Smaug, the Great Calamity"))
#guard resolvedSpewFlame.log.any (fun s => mentions s "is exiled")
#guard resolvedSpewFlame.log.any (fun s => mentions s "may cast it for as long as it remains exiled")

def exiledSmaug (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Smaug, the Great Calamity") with
  | some o => o
  | none => panic! "expected Smaug, the Great Calamity in exile"

#guard resolvedSpewFlame.mayPlayFromExile ⟨0⟩ (exiledSmaug resolvedSpewFlame)
#guard !resolvedSpewFlame.canCastAdventure ⟨0⟩ (exiledSmaug resolvedSpewFlame)
#guard resolvedSpewFlame.adventureExileForbidsRecast (exiledSmaug resolvedSpewFlame)

-- The CR 715.3d permission does not allow recasting as an Adventure.
#guard
  match resolvedSpewFlame.castSpell ⟨0⟩ (exiledSmaug resolvedSpewFlame).id true with
  | .error msg => mentions msg "may not cast that card as an Adventure"
  | .ok _ => false

/-- Permission lasts past the end of the caster's next turn (CR 715.3d). -/
def smaugPermissionLater : Game :=
  let g := skipTo resolvedSpewFlame .end 80
  let g := passBoth g
  let g := skipTo g .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard smaugPermissionLater.activePlayer == ⟨0⟩
#guard smaugPermissionLater.mayPlayFromExile ⟨0⟩ (exiledSmaug smaugPermissionLater)
#guard !smaugPermissionLater.log.any (fun s =>
  mentions s "can no longer be played from exile")

/-- Cast Smaug from exile as the creature (CR 715.3d). -/
def smaugFromExileSetup : Game :=
  withRedMana resolvedSpewFlame ⟨0⟩ 7

#guard smaugFromExileSetup.canCast ⟨0⟩ (exiledSmaug smaugFromExileSetup)

def proposedExiledSmaug : Game :=
  mustApply smaugFromExileSetup ⟨0⟩ (.cast (exiledSmaug smaugFromExileSetup).id)

#guard proposedExiledSmaug.pending == .activateManaAbilities ⟨0⟩
#guard proposedExiledSmaug.log.any (fun s => mentions s "begins casting Smaug, the Great Calamity")
#guard (proposedExiledSmaug.object! proposedExiledSmaug.stack.back!.objectId).name ==
  "Smaug, the Great Calamity"
#guard !(proposedExiledSmaug.object! proposedExiledSmaug.stack.back!.objectId).isAdventureSpell

def resolvedExiledSmaug : Game :=
  passBoth (mustApply proposedExiledSmaug ⟨0⟩ .pay)

#guard resolvedExiledSmaug.stack.isEmpty
#guard resolvedExiledSmaug.battlefield.any (fun o => o.name == "Smaug, the Great Calamity")
#guard (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity").printed.keywords.flying
#guard resolvedExiledSmaug.power
  (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity") == 5
#guard resolvedExiledSmaug.toughness
  (namedPermanent resolvedExiledSmaug "Smaug, the Great Calamity") == 5
#guard resolvedExiledSmaug.log.any (fun s =>
  mentions s "Smaug, the Great Calamity enters the battlefield")
#guard !(resolvedExiledSmaug.objects.any (fun o =>
  o.zone == .exile && o.name == "Smaug, the Great Calamity"))

/-- Casting the creature from hand still works. -/
def proposedSmaugCreature : Game :=
  mustApply smaugSetup ⟨0⟩ (.cast (handCardNamed smaugSetup ⟨0⟩ "Smaug, the Great Calamity").id)

#guard proposedSmaugCreature.pending == .activateManaAbilities ⟨0⟩
#guard proposedSmaugCreature.log.any (fun s => mentions s "begins casting Smaug, the Great Calamity")
#guard (proposedSmaugCreature.object! proposedSmaugCreature.stack.back!.objectId).name ==
  "Smaug, the Great Calamity"

def resolvedSmaugCreature : Game :=
  passBoth (mustApply proposedSmaugCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedSmaugCreature "Smaug, the Great Calamity").printed.keywords.flying
#guard resolvedSmaugCreature.battlefield.any (fun o => o.name == "Grizzly Bears")

/-- Spew Flame is sorcery speed. -/
def smaugAtEndStep : Game := skipTo smaugSetup .end 80

#guard smaugAtEndStep.step == .end
#guard
  match smaugAtEndStep.apply ⟨0⟩
      (.castAdventure (handCardNamed smaugAtEndStep ⟨0⟩ "Smaug, the Great Calamity").id) with
  | .error msg => mentions msg "has sorcery speed"
  | .ok _ => false

/-- Reversing an unpaid Adventure returns the creature card to hand. -/
def unpaidSpewFlame : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := addToHand g smaugTheGreatCalamityCard ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Smaug, the Great Calamity").id)
  mustApply g ⟨0⟩ (.target (Target.permanent (namedPermanent g "Grizzly Bears").id))

def reversedSpewFlame : Game := mustApply unpaidSpewFlame ⟨0⟩ .pay

#guard reversedSpewFlame.stack.isEmpty
#guard (reversedSpewFlame.handObjects ⟨0⟩).any (fun o => o.name == "Smaug, the Great Calamity")
#guard reversedSpewFlame.log.any (fun s => mentions s "the casting is reversed")

/-- The heuristic casts Spew Flame when that is the playable spell. -/
def agentSmaugOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withRedMana (addToHand g smaugTheGreatCalamityCard ⟨0⟩) ⟨0⟩ 5

#guard
  match Agent.choose agentSmaugOnly ⟨0⟩ with
  | some (.castAdventure id) =>
    (agentSmaugOnly.object! id).name == "Smaug, the Great Calamity"
  | _ => false

/-- With no opposing creature, the heuristic casts Smaug as a creature. -/
def agentSmaugCreatureOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withRedMana (addToHand g smaugTheGreatCalamityCard ⟨0⟩) ⟨0⟩ 7

#guard
  match Agent.choose agentSmaugCreatureOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentSmaugCreatureOnly.object! id).name == "Smaug, the Great Calamity"
  | _ => false

/- Beorn, Reluctant Host // Till and Tend (CR 715, 305.2b). -/

/-- Beorn in hand with enough mana for Till and Tend. -/
def beornSetup : Game :=
  withGreenMana (addToHand afterDraw beornReluctantHost ⟨0⟩) ⟨0⟩ 2

#guard beornReluctantHost.hasAdventure
#guard beornReluctantHost.keywords.trample
#guard beornSetup.canCast ⟨0⟩ (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host")
#guard beornSetup.canCastAdventure ⟨0⟩ (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host")
#guard beornSetup.asSorcery? ⟨0⟩
#guard
  match beornReluctantHost.adventure with
  | some adv => !adv.toCardDef.requiresTarget
  | none => false

-- Without extra land plays, a second land is illegal (CR 305.2).
#guard
  let g := addToHand (addToHand afterDraw forest ⟨0⟩) forest ⟨0⟩
  let g := mustApply g ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id)
  match g.apply ⟨0⟩ (.playLand (handCardNamed g ⟨0⟩ "Forest").id) with
  | .error msg => mentions msg "Can't play a land now"
  | .ok _ => false

-- Extra land grants stack (CR 305.2b).
#guard
  let g := afterDraw.applyEffect ⟨0⟩ (Effect.playAdditionalLandThisTurn) #[]
  let g := g.applyEffect ⟨0⟩ (Effect.playAdditionalLandThisTurn) #[]
  (g.player ⟨0⟩).additionalLandsThisTurn == 2 && g.landPlaysAllowed ⟨0⟩ == 3

def proposedTillAndTend : Game :=
  mustApply beornSetup ⟨0⟩
    (.castAdventure (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host").id)

#guard proposedTillAndTend.pending == .activateManaAbilities ⟨0⟩
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).name == "Till and Tend"
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).printed.isSorcery
#guard (proposedTillAndTend.object! proposedTillAndTend.stack.back!.objectId).isAdventureSpell
#guard proposedTillAndTend.log.any (fun s => mentions s "begins casting Till and Tend")
#guard proposedTillAndTend.log.any (fun s => mentions s "may activate mana abilities (CR 601.2g)")

def paidTillAndTend : Game := mustApply proposedTillAndTend ⟨0⟩ .pay

#guard paidTillAndTend.hasPriority ⟨0⟩
#guard paidTillAndTend.log.any (fun s => mentions s "casts Till and Tend")
#guard (paidTillAndTend.object! paidTillAndTend.stack.back!.objectId).name == "Till and Tend"

def resolvedTillAndTend : Game := passBoth paidTillAndTend

#guard resolvedTillAndTend.stack.isEmpty
#guard resolvedTillAndTend.objects.any (fun o =>
  o.zone == .exile && o.name == "Beorn, Reluctant Host")
#guard !((resolvedTillAndTend.player ⟨0⟩).graveyard.any (fun id =>
  (resolvedTillAndTend.object! id).name == "Beorn, Reluctant Host"))
#guard resolvedTillAndTend.log.any (fun s => mentions s "is exiled")
#guard resolvedTillAndTend.log.any (fun s => mentions s "may cast it for as long as it remains exiled")
#guard resolvedTillAndTend.log.any (fun s => mentions s "may play an additional land this turn")
#guard (resolvedTillAndTend.player ⟨0⟩).additionalLandsThisTurn == 1
#guard resolvedTillAndTend.landPlaysAllowed ⟨0⟩ == 2
#guard resolvedTillAndTend.canPlayLand ⟨0⟩

def exiledBeorn (g : Game) : GameObject :=
  match g.objects.find? (fun o => o.zone == .exile && o.name == "Beorn, Reluctant Host") with
  | some o => o
  | none => panic! "expected Beorn, Reluctant Host in exile"

#guard resolvedTillAndTend.mayPlayFromExile ⟨0⟩ (exiledBeorn resolvedTillAndTend)
#guard !resolvedTillAndTend.canCastAdventure ⟨0⟩ (exiledBeorn resolvedTillAndTend)
#guard resolvedTillAndTend.adventureExileForbidsRecast (exiledBeorn resolvedTillAndTend)

-- The CR 715.3d permission does not allow recasting as an Adventure.
#guard
  match resolvedTillAndTend.castSpell ⟨0⟩ (exiledBeorn resolvedTillAndTend).id true with
  | .error msg => mentions msg "may not cast that card as an Adventure"
  | .ok _ => false

/-- Play a land, resolve Till and Tend, then play a second land. -/
def beornTwoLandsSetup : Game :=
  let g := addToHand afterDraw beornReluctantHost ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  let g := addToHand g forest ⟨0⟩
  withGreenMana g ⟨0⟩ 2

def afterFirstForestForBeorn : Game :=
  mustApply beornTwoLandsSetup ⟨0⟩
    (.playLand (handCardNamed beornTwoLandsSetup ⟨0⟩ "Forest").id)

#guard (afterFirstForestForBeorn.player ⟨0⟩).landsPlayedThisTurn == 1
#guard !afterFirstForestForBeorn.canPlayLand ⟨0⟩

def resolvedTillAfterLand : Game :=
  let g := mustApply afterFirstForestForBeorn ⟨0⟩
    (.castAdventure (handCardNamed afterFirstForestForBeorn ⟨0⟩ "Beorn, Reluctant Host").id)
  passBoth (mustApply g ⟨0⟩ .pay)

#guard resolvedTillAfterLand.canPlayLand ⟨0⟩
#guard (resolvedTillAfterLand.player ⟨0⟩).additionalLandsThisTurn == 1
#guard resolvedTillAfterLand.landPlaysAllowed ⟨0⟩ == 2

def afterSecondForestForBeorn : Game :=
  mustApply resolvedTillAfterLand ⟨0⟩
    (.playLand (handCardNamed resolvedTillAfterLand ⟨0⟩ "Forest").id)

#guard (afterSecondForestForBeorn.player ⟨0⟩).landsPlayedThisTurn == 2
#guard !afterSecondForestForBeorn.canPlayLand ⟨0⟩
#guard (afterSecondForestForBeorn.battlefield.filter (fun o => o.name == "Forest")).size == 2
#guard
  match afterSecondForestForBeorn.apply ⟨0⟩
      (.playLand (handCardNamed afterSecondForestForBeorn ⟨0⟩ "Forest").id) with
  | .error msg => mentions msg "Can't play a land now"
  | .ok _ => false

/-- Permission lasts past the end of the caster's next turn (CR 715.3d);
the extra land play does not. -/
def beornPermissionLater : Game :=
  let g := skipTo resolvedTillAndTend .end 80
  let g := passBoth g
  let g := skipTo g .end 80
  let g := passBoth g
  skipTo g .precombatMain 80

#guard beornPermissionLater.activePlayer == ⟨0⟩
#guard beornPermissionLater.mayPlayFromExile ⟨0⟩ (exiledBeorn beornPermissionLater)
#guard (beornPermissionLater.player ⟨0⟩).additionalLandsThisTurn == 0
#guard (beornPermissionLater.player ⟨0⟩).landsPlayedThisTurn == 0
#guard beornPermissionLater.landPlaysAllowed ⟨0⟩ == 1

/-- Cast Beorn from exile as the creature (CR 715.3d). -/
def beornFromExileSetup : Game :=
  withGreenMana resolvedTillAndTend ⟨0⟩ 5

#guard beornFromExileSetup.canCast ⟨0⟩ (exiledBeorn beornFromExileSetup)

def proposedExiledBeorn : Game :=
  mustApply beornFromExileSetup ⟨0⟩ (.cast (exiledBeorn beornFromExileSetup).id)

#guard proposedExiledBeorn.pending == .activateManaAbilities ⟨0⟩
#guard proposedExiledBeorn.log.any (fun s => mentions s "begins casting Beorn, Reluctant Host")
#guard (proposedExiledBeorn.object! proposedExiledBeorn.stack.back!.objectId).name ==
  "Beorn, Reluctant Host"
#guard !(proposedExiledBeorn.object! proposedExiledBeorn.stack.back!.objectId).isAdventureSpell

def resolvedExiledBeorn : Game :=
  passBoth (mustApply proposedExiledBeorn ⟨0⟩ .pay)

#guard resolvedExiledBeorn.stack.isEmpty
#guard resolvedExiledBeorn.battlefield.any (fun o => o.name == "Beorn, Reluctant Host")
#guard (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host").printed.keywords.trample
#guard resolvedExiledBeorn.power
  (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host") == 5
#guard resolvedExiledBeorn.toughness
  (namedPermanent resolvedExiledBeorn "Beorn, Reluctant Host") == 5
#guard resolvedExiledBeorn.log.any (fun s =>
  mentions s "Beorn, Reluctant Host enters the battlefield")
#guard !(resolvedExiledBeorn.objects.any (fun o =>
  o.zone == .exile && o.name == "Beorn, Reluctant Host"))

/-- Casting the creature from hand still works. -/
def proposedBeornCreature : Game :=
  mustApply (withGreenMana beornSetup ⟨0⟩ 5) ⟨0⟩
    (.cast (handCardNamed beornSetup ⟨0⟩ "Beorn, Reluctant Host").id)

#guard proposedBeornCreature.pending == .activateManaAbilities ⟨0⟩
#guard proposedBeornCreature.log.any (fun s => mentions s "begins casting Beorn, Reluctant Host")
#guard (proposedBeornCreature.object! proposedBeornCreature.stack.back!.objectId).name ==
  "Beorn, Reluctant Host"

def resolvedBeornCreature : Game :=
  passBoth (mustApply proposedBeornCreature ⟨0⟩ .pay)

#guard (namedPermanent resolvedBeornCreature "Beorn, Reluctant Host").printed.keywords.trample
#guard resolvedBeornCreature.power
  (namedPermanent resolvedBeornCreature "Beorn, Reluctant Host") == 5

/-- Till and Tend is sorcery speed. -/
def beornAtEndStep : Game := skipTo beornSetup .end 80

#guard beornAtEndStep.step == .end
#guard
  match beornAtEndStep.apply ⟨0⟩
      (.castAdventure (handCardNamed beornAtEndStep ⟨0⟩ "Beorn, Reluctant Host").id) with
  | .error msg => mentions msg "has sorcery speed"
  | .ok _ => false

/-- Reversing an unpaid Adventure returns the creature card to hand. -/
def unpaidTillAndTend : Game :=
  let g := addToHand afterDraw beornReluctantHost ⟨0⟩
  mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Beorn, Reluctant Host").id)

def reversedTillAndTend : Game := mustApply unpaidTillAndTend ⟨0⟩ .pay

#guard reversedTillAndTend.stack.isEmpty
#guard (reversedTillAndTend.handObjects ⟨0⟩).any (fun o => o.name == "Beorn, Reluctant Host")
#guard reversedTillAndTend.log.any (fun s => mentions s "the casting is reversed")

/-- The heuristic casts Till and Tend when that is the playable spell. -/
def agentBeornOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g beornReluctantHost ⟨0⟩) ⟨0⟩ 2

#guard
  match Agent.choose agentBeornOnly ⟨0⟩ with
  | some (.castAdventure id) =>
    (agentBeornOnly.object! id).name == "Beorn, Reluctant Host"
  | _ => false

/-- With enough mana, the heuristic casts Beorn as a creature. -/
def agentBeornCreatureOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g beornReluctantHost ⟨0⟩) ⟨0⟩ 5

#guard
  match Agent.choose agentBeornCreatureOnly ⟨0⟩ with
  | some (.cast id) =>
    (agentBeornCreatureOnly.object! id).name == "Beorn, Reluctant Host"
  | _ => false

/-- A sorcery Adventure is an instant-or-sorcery spell (CR 715.3b / 601.2i). -/
def paidTillWithGuttersnipe : Game :=
  let g := addPermanent beornSetup guttersnipe ⟨0⟩ ⟨0⟩
  let g := mustApply g ⟨0⟩
    (.castAdventure (handCardNamed g ⟨0⟩ "Beorn, Reluctant Host").id)
  mustApply g ⟨0⟩ .pay

#guard paidTillWithGuttersnipe.stack.size == 2
#guard (paidTillWithGuttersnipe.object! paidTillWithGuttersnipe.stack.back!.objectId).triggeredAbility ==
  some (.onCastInstantOrSorceryDealDamageToEachOpponent 2)
#guard (paidTillWithGuttersnipe.object! paidTillWithGuttersnipe.stack[0]!.objectId).name ==
  "Till and Tend"
#guard paidTillWithGuttersnipe.log.any (fun s => mentions s "casts Till and Tend")
#guard paidTillWithGuttersnipe.log.any (fun s => mentions s "cast trigger is put on the stack")

def tillWithGuttersnipeResolved : Game :=
  passBoth (passBoth paidTillWithGuttersnipe)

#guard (tillWithGuttersnipeResolved.player ⟨1⟩).life == 18
#guard (tillWithGuttersnipeResolved.player ⟨0⟩).additionalLandsThisTurn == 1

/-- Chandra's Gray Ogre attacks; Nissa has Olog-hai Crusher with no Goblin or Orc. -/
def ogreVsCrusher : Game :=
  addPermanent (addPermanent started grayOgre ⟨0⟩ ⟨0⟩) ologHaiCrusher ⟨1⟩ ⟨1⟩

def ogreVsCrusherReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusher .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard ogreVsCrusherReadyToBlock.pending == .declareBlockers
#guard
  let g := ogreVsCrusherReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")
#guard
  match ogreVsCrusherReadyToBlock.apply ⟨1⟩ (.declareBlockers #[(
    (namedPermanent ogreVsCrusherReadyToBlock "Olog-hai Crusher").id,
    (namedPermanent ogreVsCrusherReadyToBlock "Gray Ogre").id)]) with
  | .error msg => mentions msg "cannot block"
  | .ok _ => false

/-- Nissa's Goblin lets Olog-hai Crusher block. The Goblin need not block. -/
def ogreVsCrusherAndGoblin : Game :=
  addPermanent ogreVsCrusher ragingGoblin ⟨1⟩ ⟨1⟩

def ogreVsCrusherAndGoblinReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherAndGoblin .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherAndGoblinReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

def crusherBlocksOgre : Game :=
  let g := ogreVsCrusherAndGoblinReadyToBlock
  mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Olog-hai Crusher").id,
    (namedPermanent g "Gray Ogre").id)])

#guard (namedPermanent crusherBlocksOgre "Olog-hai Crusher").status.blocking ==
  #[(namedPermanent crusherBlocksOgre "Gray Ogre").id]
#guard (namedPermanent crusherBlocksOgre "Gray Ogre").status.blocked
#guard crusherBlocksOgre.log.any (fun s => mentions s "Olog-hai Crusher blocks Gray Ogre")

/-- A tapped Goblin still enables blocking (it does not have to block). -/
def ogreVsCrusherTappedGoblinReadyToBlock : Game :=
  let g := ogreVsCrusherAndGoblinReadyToBlock
  let goblin := namedPermanent g "Raging Goblin"
  g.setObject { goblin with status := { goblin.status with tapped := true } }

#guard
  let g := ogreVsCrusherTappedGoblinReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")
#guard !(ogreVsCrusherTappedGoblinReadyToBlock.canBlock
  (namedPermanent ogreVsCrusherTappedGoblinReadyToBlock "Raging Goblin")
  (namedPermanent ogreVsCrusherTappedGoblinReadyToBlock "Gray Ogre"))

/-- An Orc also enables blocking. -/
def ogreVsCrusherAndOrc : Game :=
  addPermanent ogreVsCrusher orcishSiegemaster ⟨1⟩ ⟨1⟩

def ogreVsCrusherAndOrcReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherAndOrc .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherAndOrcReadyToBlock
  g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

/-- An opponent's Goblin does not enable blocking. -/
def ogreVsCrusherOppGoblin : Game :=
  addPermanent ogreVsCrusher ragingGoblin ⟨0⟩ ⟨0⟩

def ogreVsCrusherOppGoblinReadyToBlock : Game :=
  let g := passBoth (skipTo ogreVsCrusherOppGoblin .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Gray Ogre").id])
  passBoth g

#guard
  let g := ogreVsCrusherOppGoblinReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Gray Ogre")

/-- Whether you control a Goblin or Orc is checked only when declaring blockers. -/
def crusherStillBlockingAfterGoblinLeaves : Game :=
  let g := crusherBlocksOgre
  let goblin := namedPermanent g "Raging Goblin"
  (g.move goblin.id (.graveyard ⟨1⟩) none).1

#guard !(crusherStillBlockingAfterGoblinLeaves.battlefield.any
  (fun o => o.name == "Raging Goblin"))
#guard (namedPermanent crusherStillBlockingAfterGoblinLeaves "Olog-hai Crusher").status.blocking ==
  #[(namedPermanent crusherStillBlockingAfterGoblinLeaves "Gray Ogre").id]

/-- A Goblin still does not let Crusher block a flyer. -/
def flyerVsCrusherAndGoblinReadyToBlock : Game :=
  let g := addPermanent (addPermanent (addPermanent started greatFierceBeeCard ⟨0⟩ ⟨0⟩)
    ologHaiCrusher ⟨1⟩ ⟨1⟩) ragingGoblin ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Great Fierce Bee").id])
  passBoth g

#guard
  let g := flyerVsCrusherAndGoblinReadyToBlock
  !g.canBlock (namedPermanent g "Olog-hai Crusher") (namedPermanent g "Great Fierce Bee")

/-- Crusher can attack without a Goblin or Orc; printed trample assigns leftover. -/
def crusherReadyToAttack : Game :=
  passBoth (skipTo (addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩) .beginningOfCombat 80)

#guard crusherReadyToAttack.canAttack (namedPermanent crusherReadyToAttack "Olog-hai Crusher")
#guard crusherReadyToAttack.hasTrample (namedPermanent crusherReadyToAttack "Olog-hai Crusher")

def afterCrusherTrample : Game :=
  let g := addPermanent (addPermanent started ologHaiCrusher ⟨0⟩ ⟨0⟩)
    grizzlyBears ⟨1⟩ ⟨1⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Olog-hai Crusher").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[(
    (namedPermanent g "Grizzly Bears").id,
    (namedPermanent g "Olog-hai Crusher").id)])
  passBoth g

#guard afterCrusherTrample.log.any (fun s =>
  mentions s "Olog-hai Crusher deals 2 combat damage to Grizzly Bears")
#guard afterCrusherTrample.log.any (fun s =>
  mentions s "Olog-hai Crusher tramples for 2 to Nissa")
#guard (afterCrusherTrample.player ⟨1⟩).life == 18

end Mtg.Engine.Tests
