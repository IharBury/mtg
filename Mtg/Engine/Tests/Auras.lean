import Mtg.Engine.Agent
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.Oracle
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Turns

/-!
# Mana helpers, counters, Auras, the legend rule, and enters triggers.
-/

namespace Mtg.Engine.Tests

open Mtg.Engine
open Mtg.Engine.Catalog

/-- Fill `p`'s mana pool with `n` mana of color `c`. -/
def withMana (g : Game) (p : PlayerId) (c : Color) (n : Nat := 4) : Game :=
  g.modifyPlayer p (fun pl => { pl with manaPool := pl.manaPool.add (.colored c) n })

/-- Fill `p`'s mana pool with `n` green mana. -/
def withGreenMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .green n

/-- Fill `p`'s mana pool with `n` red mana. -/
def withRedMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .red n

/-- Fill `p`'s mana pool with `n` black mana. -/
def withBlackMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .black n

/-- Fill `p`'s mana pool with `n` white mana. -/
def withWhiteMana (g : Game) (p : PlayerId) (n : Nat := 5) : Game :=
  withMana g p .white n

/-- Fill `p`'s mana pool with `n` blue mana. -/
def withBlueMana (g : Game) (p : PlayerId) (n : Nat := 4) : Game :=
  withMana g p .blue n

/-- Nissa proposes Thranduil's Decree with Lightning Bolt on the stack. -/
def proposedDecree : Game :=
  let g := mustApply paidBolt ⟨0⟩ .pass
  let g := withBlueMana (addToHand g thranduilsDecree ⟨1⟩) ⟨1⟩ 6
  mustApply g ⟨1⟩ (.cast (handCardNamed g ⟨1⟩ "Thranduil's Decree").id)

#guard proposedDecree.pending == .chooseTargets ⟨1⟩
#guard proposedDecree.stack.size == 2
#guard (proposedDecree.object! proposedDecree.stack.back!.objectId).name ==
  "Thranduil's Decree"
#guard
  (proposedDecree.legalProposedTargets ⟨1⟩
    (proposedDecree.object! proposedDecree.stack.back!.objectId)).contains
    (Target.card paidBolt.stack.back!.objectId)

#guard
  match proposedDecree.apply ⟨1⟩ (.target (Target.card paidBolt.stack.back!.objectId)) with
  | .ok g' =>
    g'.stack.back!.targets == #[Target.card paidBolt.stack.back!.objectId] &&
      g'.log.any (fun s => mentions s "chooses Lightning Bolt as a target")
  | .error _ => false

-- A stack spell is a card target, not a permanent (CR 115.1).
#guard
  match proposedDecree.apply ⟨1⟩
      (.target (Target.permanent paidBolt.stack.back!.objectId)) with
  | .error msg => mentions msg "Illegal target"
  | .ok _ => false

-- Prefer an opposing spell over your own (CR 601.2c heuristic).
#guard
  match Agent.choose proposedDecree ⟨1⟩ with
  | some (.target (Target.card id)) =>
    (proposedDecree.object! id).name == "Lightning Bolt"
  | _ => false

/-- Empty `p`'s hand and mark a land already played this turn. -/
def clearHandPlayedLand (g : Game) (p : PlayerId) : Game :=
  g.modifyPlayer p (fun pl => { pl with hand := #[], landsPlayedThisTurn := 1 })

/-- Chandra has her own Bolt on the stack and a counter in hand. -/
def agentOwnBoltWithDecree : Game :=
  let g := clearHandPlayedLand paidBolt ⟨0⟩
  withBlueMana (addToHand g thranduilsDecree ⟨0⟩) ⟨0⟩ 6

-- The heuristic does not counter its own spell.
#guard
  match Agent.choose agentOwnBoltWithDecree ⟨0⟩ with
  | some (.cast id) =>
    (agentOwnBoltWithDecree.object! id).name != "Thranduil's Decree"
  | _ => true

/-- Nissa has a counter in hand and Chandra's Bolt is on the stack. -/
def agentOppBoltWithDecree : Game :=
  let g := mustApply paidBolt ⟨0⟩ .pass
  let g := clearHandPlayedLand g ⟨1⟩
  withBlueMana (addToHand g thranduilsDecree ⟨1⟩) ⟨1⟩ 6

-- The heuristic does counter an opposing spell.
#guard
  match Agent.choose agentOppBoltWithDecree ⟨1⟩ with
  | some (.cast id) =>
    (agentOppBoltWithDecree.object! id).name == "Thranduil's Decree"
  | _ => false

/-- Nissa's instant is under Chandra's Bolt, then Nissa proposes a counter. -/
def proposedDecreeOverOwnSpell : Game :=
  let g := mustApply afterDraw ⟨0⟩ .pass
  let g := withBlueMana (addToHand g confusticateAndBebother ⟨1⟩) ⟨1⟩ 3
  let g := mustApply g ⟨1⟩
    (.cast (handCardNamed g ⟨1⟩ "Confusticate and Bebother").id)
  let g := mustApply g ⟨1⟩ (.chooseMode 1)
  let g := mustApply g ⟨1⟩ .pay
  let g := mustApply g ⟨1⟩ .pass
  let g := withRedMana (addToHand g lightningBolt ⟨0⟩) ⟨0⟩ 1
  let g := mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Lightning Bolt").id)
  let g := mustApply g ⟨0⟩ (.target (Target.player ⟨1⟩))
  let g := mustApply g ⟨0⟩ .pay
  let g := mustApply g ⟨0⟩ .pass
  let g := withBlueMana (addToHand g thranduilsDecree ⟨1⟩) ⟨1⟩ 6
  mustApply g ⟨1⟩ (.cast (handCardNamed g ⟨1⟩ "Thranduil's Decree").id)

#guard proposedDecreeOverOwnSpell.pending == .chooseTargets ⟨1⟩
#guard proposedDecreeOverOwnSpell.stack.size == 3

-- Prefer the opposing Bolt, not Nissa's Confusticate already on the stack.
#guard
  match Agent.choose proposedDecreeOverOwnSpell ⟨1⟩ with
  | some (.target (Target.card id)) =>
    (proposedDecreeOverOwnSpell.object! id).name == "Lightning Bolt"
  | _ => false

/-- Chandra proposes Confusticate with her own Bolt on the stack. -/
def proposedConfusticateOwnBolt : Game :=
  let g := withBlueMana (addToHand paidBolt confusticateAndBebother ⟨0⟩) ⟨0⟩ 3
  mustApply g ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Confusticate and Bebother").id)

-- Draw rather than counter your own spell.
#guard
  match Agent.choose proposedConfusticateOwnBolt ⟨0⟩ with
  | some (.chooseMode 1) => true
  | _ => false
#guard
  match proposedConfusticateOwnBolt.apply ⟨0⟩ (.chooseMode 1) with
  | .ok g' => g'.log.any (fun s => mentions s "chooses mode 2")
  | .error _ => false

/-- Nissa proposes Confusticate with Chandra's Bolt on the stack. -/
def proposedConfusticateOppBolt : Game :=
  let g := mustApply paidBolt ⟨0⟩ .pass
  let g := withBlueMana (addToHand g confusticateAndBebother ⟨1⟩) ⟨1⟩ 3
  mustApply g ⟨1⟩ (.cast (handCardNamed g ⟨1⟩ "Confusticate and Bebother").id)

-- Counter an opposing spell when that mode is available.
#guard
  match Agent.choose proposedConfusticateOppBolt ⟨1⟩ with
  | some (.chooseMode 0) => true
  | _ => false

/-- Pay the proposed spell or ability, then both players pass (resolve). -/
def payAndResolve (g : Game) (p : PlayerId) : Game :=
  passBoth (mustApply g p .pay)

/-- Keep the first listed legendary permanent in a CR 704.5j choice. -/
def keepFirstLegend (g : Game) : Game :=
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[0]!)
  | _ => panic! "expected a legend-rule choice"

/-- Put `aura` onto the battlefield already attached to `host`. -/
def addAttachedAura (g : Game) (aura : CardDef) (host : GameObject)
    (owner controller : PlayerId) : Game :=
  let (g, _) := g.allocObject aura owner .battlefield (some controller)
    (attachedTo := some host.id)
  g

/-- Keep the looked-at cards on top in their current order (CR 701.20). -/
def keepScry (g : Game) : Game :=
  match g.pending with
  | .scry p n => mustApply g p (.scry (g.scryLookedIds p n) #[])
  | _ => panic! "expected a pending scry"

/-- Gift of Strands in hand, Grizzly Bears on the battlefield, enough mana. -/
def giftSetup : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard giftSetup.canCast ⟨0⟩ (handCardNamed giftSetup ⟨0⟩ "Gift of Strands")
#guard giftSetup.asSorcery? ⟨0⟩
#guard giftOfStrands.keywords.flash
#guard !giftOfStrands.hasSorcerySpeed

-- An Aura cannot be cast with no creature on the battlefield.
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gift of Strands")
#guard
  let g := withGreenMana (addToHand afterDraw giftOfStrands ⟨0⟩) ⟨0⟩
  match g.apply ⟨0⟩ (.cast (handCardNamed g ⟨0⟩ "Gift of Strands").id) with
  | .error msg => mentions msg "requires a target"
  | .ok _ => false

-- Cast proposes the Aura; the target is announced as a later action (CR 601.2c).
#guard
  match giftSetup.apply ⟨0⟩ (.cast (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id) with
  | .ok g' =>
    match g'.pending with
    | .chooseTargets ⟨0⟩ => g'.stack.back!.targets.isEmpty
    | _ => false
  | .error _ => false

def proposedGift : Game :=
  proposeTargeted giftSetup ⟨0⟩
    (handCardNamed giftSetup ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent giftSetup "Grizzly Bears").id)

#guard proposedGift.pending == .activateManaAbilities ⟨0⟩
#guard proposedGift.stack.back!.targets ==
  #[Target.permanent (namedPermanent giftSetup "Grizzly Bears").id]
#guard proposedGift.log.any (fun s => mentions s "chooses Grizzly Bears as a target (CR 601.2c)")

def paidGift : Game := mustApply proposedGift ⟨0⟩ .pay

#guard paidGift.stack.size == 1
#guard paidGift.hasPriority ⟨0⟩

/-- The Aura enters attached and the creature is immediately +3/+3; scry waits on the stack. -/
def giftEntered : Game := passBoth paidGift

#guard (namedPermanent giftEntered "Gift of Strands").attachedTo ==
  some (namedPermanent giftEntered "Grizzly Bears").id
#guard giftEntered.power (namedPermanent giftEntered "Grizzly Bears") == 5
#guard giftEntered.toughness (namedPermanent giftEntered "Grizzly Bears") == 5
#guard (namedPermanent giftEntered "Grizzly Bears").power == 2
#guard giftEntered.stack.size == 1
#guard giftEntered.log.any (fun s => mentions s "attached to Grizzly Bears")
#guard giftEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def giftScrying : Game := passBoth giftEntered

#guard
  match giftScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard giftScrying.actor == some ⟨0⟩
#guard !giftScrying.hasPriority ⟨0⟩
#guard giftScrying.log.any (fun s => mentions s "scries 2")
#guard giftScrying.stack.isEmpty

def giftScried : Game := keepScry giftScrying

#guard giftScried.pending == .none
#guard giftScried.hasPriority ⟨0⟩
#guard giftScried.power (namedPermanent giftScried "Grizzly Bears") == 5

-- The agent keeps scried cards on top.
#guard
  match Agent.choose giftScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == giftScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Put the current top card on the bottom; the next stays on top. -/
def giftKnownLib : Game :=
  addToLibraryTop (addToLibraryTop giftEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def giftKnownScrying : Game := passBoth giftKnownLib

def giftBottomedElves : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- looked is [Forest, Llanowar Elves] with Elves on top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.pop #[looked.back!])

#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library.back!).name == "Forest"
#guard (giftBottomedElves.object! (giftBottomedElves.player ⟨0⟩).library[0]!).name ==
  "Llanowar Elves"
#guard giftBottomedElves.log.any (fun s =>
  mentions s "puts Llanowar Elves on the bottom of their library")

/-- The rest may be put on top in any order (CR 701.20). -/
def giftReorderedTop : Game :=
  let looked := giftKnownScrying.scryLookedIds ⟨0⟩ 2
  -- Reverse the two looked-at cards: Forest becomes the new top.
  mustApply giftKnownScrying ⟨0⟩ (.scry looked.reverse #[])

#guard (giftReorderedTop.object! (giftReorderedTop.player ⟨0⟩).library.back!).name == "Forest"
#guard
  let lib := (giftReorderedTop.player ⟨0⟩).library
  (giftReorderedTop.object! lib[lib.size - 2]!).name == "Llanowar Elves"
#guard giftReorderedTop.log.any (fun s => mentions s "puts Forest on top of their library")
#guard giftReorderedTop.log.any (fun s =>
  mentions s "puts Llanowar Elves on top of their library")
#guard !(giftReorderedTop.log.any (fun s => mentions s "on the bottom of their library"))

/-- The +3/+3 is a continuous effect, so it does not wear off in cleanup. -/
def afterGiftCleanup : Game := passBoth (skipTo giftScried .end 80)

#guard afterGiftCleanup.power (namedPermanent afterGiftCleanup "Grizzly Bears") == 5
#guard (namedPermanent afterGiftCleanup "Grizzly Bears").status.pumpPower == 0

/-- If the target leaves before the Aura resolves, the Aura goes to the graveyard (CR 608.3a). -/
def giftTargetGone : Game :=
  let id := (namedPermanent paidGift "Grizzly Bears").id
  let (g, _) := paidGift.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(giftTargetGone.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard giftTargetGone.log.any (fun s => mentions s "illegal Aura target")
#guard (giftTargetGone.player ⟨0⟩).graveyard.any (fun id =>
  (giftTargetGone.object! id).name == "Gift of Strands")

/-- If the enchanted creature leaves, the Aura becomes unattached and SBA 704.5n puts it
in the graveyard. -/
def afterHostLeaves : Game :=
  let id := (namedPermanent giftScried "Grizzly Bears").id
  let (g, _) := giftScried.move id (.graveyard ⟨0⟩) none
  g.checkSBA

#guard afterHostLeaves.log.any (fun s => mentions s "becomes unattached")
#guard afterHostLeaves.log.any (fun s => mentions s "704.5n")
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard !(afterHostLeaves.battlefield.any (fun o => o.name == "Grizzly Bears"))

/- Legend rule (CR 704.5j). -/

def twoBofurs : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    bofurReliableGuardian ⟨0⟩ ⟨0⟩

def twoBofursSBA : Game := twoBofurs.checkSBA

#guard (namedPermanent twoBofurs "Bofur, Reliable Guardian").isLegendary
#guard (twoBofurs.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 2
#guard twoBofurs.pending == .none
#guard twoBofurs.firstLegendRuleChoice?.isSome
#guard
  match twoBofursSBA.pending with
  | .chooseLegend p name ids =>
    p == ⟨0⟩ && name == "Bofur, Reliable Guardian" && ids.size == 2
  | _ => false
#guard twoBofursSBA.actor == some ⟨0⟩
#guard twoBofursSBA.legendChoicePending?
#guard twoBofursSBA.log.any (fun s => mentions s "704.5j")
#guard (twoBofursSBA.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 2

def keptOlderBofur : Game :=
  keepFirstLegend twoBofursSBA

#guard (keptOlderBofur.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard keptOlderBofur.pending == .none
#guard !keptOlderBofur.legendChoicePending?
#guard keptOlderBofur.log.any (fun s => mentions s "keeps Bofur, Reliable Guardian")
#guard keptOlderBofur.log.any (fun s =>
  mentions s "is put into its owner's graveyard (legend rule, CR 704.5j)")
#guard (keptOlderBofur.player ⟨0⟩).graveyard.any (fun id =>
  (keptOlderBofur.object! id).name == "Bofur, Reliable Guardian")
#guard keptOlderBofur.hasPriority ⟨0⟩

/-- Each player may control a copy of the same legend. -/
def eachControlsBofur : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    bofurReliableGuardian ⟨1⟩ ⟨1⟩

#guard (eachControlsBofur.checkSBA).pending == .none
#guard (eachControlsBofur.checkSBA.battlefield.filter
  (·.name == "Bofur, Reliable Guardian")).size == 2

/-- Different legendary names do not conflict. -/
def twoDifferentLegends : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨0⟩)
    landrovalHorizonWitness ⟨0⟩ ⟨0⟩

#guard (twoDifferentLegends.checkSBA).pending == .none
#guard (twoDifferentLegends.checkSBA.battlefield.filter (·.isLegendary)).size == 2

/-- Three copies: keep one, two go to the graveyard. -/
def threeBofursSBA : Game :=
  (addPermanent twoBofurs bofurReliableGuardian ⟨0⟩ ⟨0⟩).checkSBA

def keptOneOfThree : Game :=
  match threeBofursSBA.pending with
  | .chooseLegend p _ ids => mustApply threeBofursSBA p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard (keptOneOfThree.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard ((keptOneOfThree.player ⟨0⟩).graveyard.filter (fun id =>
  (keptOneOfThree.object! id).name == "Bofur, Reliable Guardian")).size == 2

/-- Indestructible does not save a legend from CR 704.5j. -/
def legendaryIndestructible : CardDef :=
  legendaryCreature "Unyielding Legend" ManaCost.empty #[] 2 2
    (keywords := Keyword.indestructible)

def twoIndestructibleLegends : Game :=
  let g :=
    addPermanent (addPermanent started legendaryIndestructible ⟨0⟩ ⟨0⟩)
      legendaryIndestructible ⟨0⟩ ⟨0⟩
  keepFirstLegend (g.checkSBA)

#guard (twoIndestructibleLegends.battlefield.filter
  (·.name == "Unyielding Legend")).size == 1
#guard (namedPermanent twoIndestructibleLegends "Unyielding Legend").printed.keywords.indestructible
#guard ((twoIndestructibleLegends.player ⟨0⟩).graveyard.filter (fun id =>
  (twoIndestructibleLegends.object! id).name == "Unyielding Legend")).size == 1

/-- The rest go to their owners' graveyards, not the controller's. -/
def nissaControlsTwoBofurs : Game :=
  addPermanent (addPermanent started bofurReliableGuardian ⟨0⟩ ⟨1⟩)
    bofurReliableGuardian ⟨1⟩ ⟨1⟩

def nissaKeepsOwnBofur : Game :=
  let g := nissaControlsTwoBofurs.checkSBA
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard nissaControlsTwoBofurs.checkSBA.actor == some ⟨1⟩
#guard (nissaKeepsOwnBofur.player ⟨0⟩).graveyard.any (fun id =>
  (nissaKeepsOwnBofur.object! id).name == "Bofur, Reliable Guardian")
#guard (nissaKeepsOwnBofur.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard (namedPermanent nissaKeepsOwnBofur "Bofur, Reliable Guardian").owner == ⟨1⟩

/-- Two legend pairs: after the first choice, the second pair is prompted. -/
def twoLegendPairs : Game :=
  addPermanent (addPermanent twoBofurs landrovalHorizonWitness ⟨0⟩ ⟨0⟩)
    landrovalHorizonWitness ⟨0⟩ ⟨0⟩

def afterFirstLegendPair : Game :=
  let g := twoLegendPairs.checkSBA
  match g.pending with
  | .chooseLegend p name ids =>
    if name == "Bofur, Reliable Guardian" then
      mustApply g p (.keepLegend ids[0]!)
    else panic! s!"expected Bofur first, got {name}"
  | _ => panic! "expected a legend-rule choice"

#guard
  match afterFirstLegendPair.pending with
  | .chooseLegend _ name ids =>
    name == "Landroval, Horizon Witness" && ids.size == 2
  | _ => false

-- The opponent cannot make the legend-rule choice.
#guard
  match twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    match twoBofursSBA.apply ⟨1⟩ (.keepLegend ids[0]!) with
    | .error msg => mentions msg "Only Chandra"
    | .ok _ => false
  | _ => false

/-- The heuristic keeps the newest copy. -/
def agentKeptLegend : Game :=
  match Agent.step twoBofursSBA with
  | .ok g => g
  | .error e => panic! e

#guard (agentKeptLegend.battlefield.filter (·.name == "Bofur, Reliable Guardian")).size == 1
#guard agentKeptLegend.pending == .none
#guard
  match twoBofursSBA.pending with
  | .chooseLegend _ _ ids =>
    (namedPermanent agentKeptLegend "Bofur, Reliable Guardian").id ==
      twoBofursSBA.defaultLegendToKeep ids
  | _ => false

/-- An Aura on the discarded legend is put into the graveyard (CR 704.5m). -/
def twoBofursWithAura : Game :=
  let host := (twoBofurs.battlefield.filter
    (·.name == "Bofur, Reliable Guardian"))[0]!
  addAttachedAura twoBofurs giftOfStrands host ⟨0⟩ ⟨0⟩

def afterLegendKillsEnchanted : Game :=
  let g := twoBofursWithAura.checkSBA
  match g.pending with
  | .chooseLegend p _ ids => mustApply g p (.keepLegend ids[1]!)
  | _ => panic! "expected a legend-rule choice"

#guard !(afterLegendKillsEnchanted.battlefield.any (fun o => o.name == "Gift of Strands"))
#guard afterLegendKillsEnchanted.log.any (fun s => mentions s "704.5n")
#guard (afterLegendKillsEnchanted.player ⟨0⟩).graveyard.any (fun id =>
  (afterLegendKillsEnchanted.object! id).name == "Gift of Strands")

-- CR 704.3: a 0-toughness creature dies in the same check, then the legend
-- rule still pauses; no player has priority until the choice is made.
def zeroAndTwoBofursSBA : Game :=
  (addPermanent twoBofurs zeroZero ⟨0⟩ ⟨0⟩).checkSBA

#guard !(zeroAndTwoBofursSBA.battlefield.any (·.name == "Zero/Zero"))
#guard
  match zeroAndTwoBofursSBA.pending with
  | .chooseLegend _ name ids =>
    name == "Bofur, Reliable Guardian" && ids.size == 2
  | _ => false
#guard !zeroAndTwoBofursSBA.hasPriority ⟨0⟩
#guard zeroAndTwoBofursSBA.actor == some ⟨0⟩

/-- Legendary creature with a dies trigger, for the CR 704.3 wait. -/
def legendaryFireleaper : CardDef :=
  legendaryCreature "Legendary Fireleaper" ManaCost.empty #["Goblin"] 2 1
    (triggeredAbilities := #[.onDiesDealDamageEqualToPowerToOppCreature])

def twoFireleapersSBA : Game :=
  let g := addPermanent started legendaryFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g legendaryFireleaper ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨1⟩ ⟨1⟩
  g.checkSBA

-- CR 704.3: the dies trigger waits until the legend-rule SBA is finished.
#guard twoFireleapersSBA.waitingTriggers.isEmpty
#guard twoFireleapersSBA.stack.isEmpty
#guard twoFireleapersSBA.legendChoicePending?
#guard !twoFireleapersSBA.hasPriority ⟨0⟩
#guard (twoFireleapersSBA.receivePriority ⟨0⟩).legendChoicePending?
#guard (twoFireleapersSBA.receivePriority ⟨0⟩).stack.isEmpty

def afterKeepFireleaper : Game :=
  keepFirstLegend twoFireleapersSBA

#guard afterKeepFireleaper.waitingTriggers.isEmpty
#guard afterKeepFireleaper.pending == .chooseTargets ⟨0⟩
#guard afterKeepFireleaper.stack.any (fun e =>
  (afterKeepFireleaper.object! e.objectId).triggeredAbility ==
    some .onDiesDealDamageEqualToPowerToOppCreature)
#guard !afterKeepFireleaper.hasPriority ⟨0⟩
#guard afterKeepFireleaper.actor == some ⟨0⟩

/-- A 0/0 creature survives while Gift of Strands is attached. -/
def zeroEnchanted : Game :=
  let g := addPermanent started zeroZero ⟨0⟩ ⟨0⟩
  addAttachedAura g giftOfStrands (namedPermanent g "Zero/Zero") ⟨0⟩ ⟨0⟩

#guard zeroEnchanted.power (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard zeroEnchanted.toughness (namedPermanent zeroEnchanted "Zero/Zero") == 3
#guard (zeroEnchanted.checkSBA).battlefield.any (fun o => o.name == "Zero/Zero")

/-- Combat uses the enchanted power. -/
def afterEnchantedCombat : Game :=
  let g := addPermanent started grizzlyBears ⟨0⟩ ⟨0⟩
  let g := addAttachedAura g giftOfStrands (namedPermanent g "Grizzly Bears") ⟨0⟩ ⟨0⟩
  let g := passBoth (skipTo g .beginningOfCombat 80)
  let g := mustApply g ⟨0⟩ (.declareAttackers #[(namedPermanent g "Grizzly Bears").id])
  let g := passBoth g
  let g := mustApply g ⟨1⟩ (.declareBlockers #[])
  passBoth g

#guard afterEnchantedCombat.log.any (fun s =>
  mentions s "Grizzly Bears deals 5 combat damage to Nissa")
#guard (afterEnchantedCombat.player ⟨1⟩).life == 15

/-- Flash lets Gift of Strands be cast when it is not a main phase. -/
def flashWindow : Game :=
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard flashWindow.hasPriority ⟨0⟩
#guard !flashWindow.asSorcery? ⟨0⟩
#guard flashWindow.canCast ⟨0⟩ (handCardNamed flashWindow ⟨0⟩ "Gift of Strands")
#guard
  let g := addToHand flashWindow grayOgre ⟨0⟩
  !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Gray Ogre")

def paidFlashGift : Game :=
  let g := proposeTargeted flashWindow ⟨0⟩
    (handCardNamed flashWindow ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent flashWindow "Grizzly Bears").id)
  mustApply g ⟨0⟩ .pay

def flashGiftEntered : Game := passBoth paidFlashGift

#guard flashGiftEntered.step == .upkeep
#guard flashGiftEntered.activePlayer == ⟨1⟩
#guard flashGiftEntered.power (namedPermanent flashGiftEntered "Grizzly Bears") == 5

/-- You may enchant an opponent's creature. -/
def giftOnNissa : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨1⟩ ⟨1⟩
  let g := withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩
  let g := proposeTargeted g ⟨0⟩
    (handCardNamed g ⟨0⟩ "Gift of Strands").id
    (Target.permanent (namedPermanent g "Grizzly Bears").id)
  let g := mustApply g ⟨0⟩ .pay
  keepScry (passBoth (passBoth g))

#guard giftOnNissa.power (namedPermanent giftOnNissa "Grizzly Bears") == 5
#guard (namedPermanent giftOnNissa "Grizzly Bears").controller == some ⟨1⟩
#guard (namedPermanent giftOnNissa "Gift of Strands").controller == some ⟨0⟩

/-- The agent casts Gift of Strands on its own creature when that is the
playable spell. -/
def agentGiftOnly : Game :=
  let g := addPermanent afterDraw grizzlyBears ⟨0⟩ ⟨0⟩
  let g := clearHandPlayedLand g ⟨0⟩
  withGreenMana (addToHand g giftOfStrands ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGiftOnly ⟨0⟩ with
  | some (.cast id) => (agentGiftOnly.object! id).name == "Gift of Strands"
  | _ => false

#guard
  let g := mustApply agentGiftOnly ⟨0⟩
    (.cast (handCardNamed agentGiftOnly ⟨0⟩ "Gift of Strands").id)
  match Agent.choose g ⟨0⟩ with
  | some (.target (Target.permanent tid)) => (g.object! tid).name == "Grizzly Bears"
  | _ => false

/-- Scrying 2 with one card looks at that card; an empty library still scries. -/
def scryOneCard : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := pl.library.extract (pl.library.size - 1) pl.library.size })
  g.beginScry ⟨0⟩ 2

#guard
  match scryOneCard.pending with
  | .scry ⟨0⟩ 1 => true
  | _ => false

def scryEmpty : Game :=
  let g := { giftEntered with pending := .none, stack := #[] }
  let g := g.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  g.beginScry ⟨0⟩ 2

#guard scryEmpty.pending == .none
#guard scryEmpty.log.any (fun s => mentions s "no cards to look at")

/-- Galadhrim Guide in hand with enough mana to cast it (CR 601.2). -/
def guideSetup : Game :=
  withGreenMana (addToHand afterDraw galadhrimGuide ⟨0⟩) ⟨0⟩

#guard guideSetup.canCast ⟨0⟩ (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide")
#guard guideSetup.asSorcery? ⟨0⟩
#guard !galadhrimGuide.keywords.flash
#guard galadhrimGuide.hasSorcerySpeed

-- A creature without flash cannot be cast when it is not a main phase.
#guard
  let g := applyIdle (passBoth (skipTo afterDraw .end 80))
  let g := withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩
  !g.asSorcery? ⟨0⟩ && !g.canCast ⟨0⟩ (handCardNamed g ⟨0⟩ "Galadhrim Guide")

def proposedGuide : Game :=
  mustApply guideSetup ⟨0⟩ (.cast (handCardNamed guideSetup ⟨0⟩ "Galadhrim Guide").id)

#guard proposedGuide.pending == .activateManaAbilities ⟨0⟩
#guard proposedGuide.log.any (fun s => mentions s "begins casting Galadhrim Guide")

def paidGuide : Game := mustApply proposedGuide ⟨0⟩ .pay

#guard paidGuide.stack.size == 1
#guard paidGuide.hasPriority ⟨0⟩
#guard paidGuide.log.any (fun s => mentions s "casts Galadhrim Guide")

/-- The creature enters; scry waits on the stack (CR 603.6a). -/
def guideEntered : Game := passBoth paidGuide

#guard (namedPermanent guideEntered "Galadhrim Guide").printed.power == some 3
#guard guideEntered.power (namedPermanent guideEntered "Galadhrim Guide") == 3
#guard guideEntered.toughness (namedPermanent guideEntered "Galadhrim Guide") == 4
#guard guideEntered.stack.size == 1
#guard (guideEntered.object! guideEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterScry 2)
#guard (guideEntered.object! guideEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent guideEntered "Galadhrim Guide").id
#guard guideEntered.log.any (fun s => mentions s "enters the battlefield")
#guard guideEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

def guideScrying : Game := passBoth guideEntered

#guard
  match guideScrying.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard guideScrying.actor == some ⟨0⟩
#guard !guideScrying.hasPriority ⟨0⟩
#guard guideScrying.log.any (fun s => mentions s "scries 2")
#guard guideScrying.stack.isEmpty
#guard guideScrying.battlefield.any (fun o => o.name == "Galadhrim Guide")

def guideScried : Game := keepScry guideScrying

#guard guideScried.pending == .none
#guard guideScried.hasPriority ⟨0⟩
#guard guideScried.battlefield.any (fun o => o.name == "Galadhrim Guide")

-- The agent keeps scried cards on top.
#guard
  match Agent.choose guideScrying ⟨0⟩ with
  | some (.scry top bottom) =>
    bottom.isEmpty && top == guideScrying.scryLookedIds ⟨0⟩ 2
  | _ => false

/-- Known library: Forest then Elves on top; scry 2 looks at both. -/
def guideKnownLib : Game :=
  addToLibraryTop (addToLibraryTop guideEntered forest ⟨0⟩) llanowarElves ⟨0⟩

def guideKnownScrying : Game := passBoth guideKnownLib

#guard
  let looked := guideKnownScrying.scryLookedIds ⟨0⟩ 2
  looked.size == 2 &&
    (guideKnownScrying.object! looked[0]!).name == "Forest" &&
    (guideKnownScrying.object! looked.back!).name == "Llanowar Elves"

/-- The trigger still scries if Galadhrim Guide has left the battlefield (CR 113.7a). -/
def guideLeftBeforeTrigger : Game :=
  let id := (namedPermanent guideEntered "Galadhrim Guide").id
  let (g, _) := guideEntered.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard
  match guideLeftBeforeTrigger.pending with
  | .scry ⟨0⟩ 2 => true
  | _ => false
#guard !(guideLeftBeforeTrigger.battlefield.any (fun o => o.name == "Galadhrim Guide"))
#guard (guideLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (guideLeftBeforeTrigger.object! id).name == "Galadhrim Guide")

/-- The agent casts Galadhrim Guide when that is the playable spell. -/
def agentGuideOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g galadhrimGuide ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentGuideOnly ⟨0⟩ with
  | some (.cast id) => (agentGuideOnly.object! id).name == "Galadhrim Guide"
  | _ => false

/-- Elvish Visionary in hand with enough mana to cast it (CR 601.2). -/
def visionarySetup : Game :=
  withGreenMana (addToHand afterDraw elvishVisionary ⟨0⟩) ⟨0⟩

#guard visionarySetup.canCast ⟨0⟩ (handCardNamed visionarySetup ⟨0⟩ "Elvish Visionary")
#guard visionarySetup.asSorcery? ⟨0⟩
#guard !elvishVisionary.keywords.flash
#guard elvishVisionary.hasSorcerySpeed

def proposedVisionary : Game :=
  mustApply visionarySetup ⟨0⟩ (.cast (handCardNamed visionarySetup ⟨0⟩ "Elvish Visionary").id)

#guard proposedVisionary.pending == .activateManaAbilities ⟨0⟩
#guard proposedVisionary.log.any (fun s => mentions s "begins casting Elvish Visionary")

def paidVisionary : Game := mustApply proposedVisionary ⟨0⟩ .pay

#guard paidVisionary.stack.size == 1
#guard paidVisionary.hasPriority ⟨0⟩
#guard paidVisionary.log.any (fun s => mentions s "casts Elvish Visionary")

/-- The creature enters; draw waits on the stack (CR 603.6a). -/
def visionaryEntered : Game := passBoth paidVisionary

#guard (namedPermanent visionaryEntered "Elvish Visionary").printed.power == some 1
#guard visionaryEntered.power (namedPermanent visionaryEntered "Elvish Visionary") == 1
#guard visionaryEntered.toughness (namedPermanent visionaryEntered "Elvish Visionary") == 1
#guard visionaryEntered.stack.size == 1
#guard (visionaryEntered.object! visionaryEntered.stack.back!.objectId).triggeredAbility ==
  some (.onEnterDraw 1)
#guard (visionaryEntered.object! visionaryEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent visionaryEntered "Elvish Visionary").id
#guard visionaryEntered.log.any (fun s => mentions s "enters the battlefield")
#guard visionaryEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

/-- Known library: Forest on top is drawn when the trigger resolves (CR 121). -/
def visionaryKnownLib : Game :=
  addToLibraryTop visionaryEntered forest ⟨0⟩

def visionaryDrew : Game := passBoth visionaryKnownLib

#guard visionaryDrew.pending == .none
#guard visionaryDrew.hasPriority ⟨0⟩
#guard visionaryDrew.stack.isEmpty
#guard visionaryDrew.battlefield.any (fun o => o.name == "Elvish Visionary")
#guard (visionaryDrew.player ⟨0⟩).hand.size == (visionaryKnownLib.player ⟨0⟩).hand.size + 1
#guard (visionaryDrew.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard visionaryDrew.log.any (fun s => mentions s "draws Forest")

-- Direct resolution of an enters-draw trigger draws that many cards (CR 121).
#guard
  let g := addToLibraryTop (addToLibraryTop afterDraw forest ⟨0⟩) llanowarElves ⟨0⟩
  let beforeHand := (g.player ⟨0⟩).hand.size
  let g := g.applyTriggeredAbility ⟨0⟩ (.onEnterDraw 2) none
  (g.player ⟨0⟩).hand.size == beforeHand + 2 &&
    g.log.any (fun s => mentions s "draws Llanowar Elves") &&
    g.log.any (fun s => mentions s "draws Forest")

/-- The trigger still draws if Elvish Visionary has left the battlefield (CR 113.7a). -/
def visionaryLeftBeforeTrigger : Game :=
  let id := (namedPermanent visionaryKnownLib "Elvish Visionary").id
  let (g, _) := visionaryKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(visionaryLeftBeforeTrigger.battlefield.any (fun o => o.name == "Elvish Visionary"))
#guard (visionaryLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (visionaryLeftBeforeTrigger.object! id).name == "Elvish Visionary")
#guard (visionaryLeftBeforeTrigger.handObjects ⟨0⟩).any (fun o => o.name == "Forest")
#guard visionaryLeftBeforeTrigger.log.any (fun s => mentions s "draws Forest")

/-- Drawing from an empty library is a state-based loss (CR 704.5b / 121.4). -/
def visionaryEmptyLib : Game :=
  let g := visionaryEntered.modifyPlayer ⟨0⟩ (fun pl => { pl with library := #[] })
  passBoth g

#guard visionaryEmptyLib.over
#guard visionaryEmptyLib.result == some (.won ⟨1⟩)
#guard (visionaryEmptyLib.player ⟨0⟩).lost
#guard visionaryEmptyLib.log.any (fun s => mentions s "tries to draw from an empty library")
#guard visionaryEmptyLib.log.any (fun s => mentions s "loses the game (drew from empty library)")
#guard visionaryEmptyLib.log.any (fun s => mentions s "Nissa wins the game")

/-- The agent casts Elvish Visionary when that is the playable spell. -/
def agentVisionaryOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g elvishVisionary ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentVisionaryOnly ⟨0⟩ with
  | some (.cast id) => (agentVisionaryOnly.object! id).name == "Elvish Visionary"
  | _ => false

/- Wood Elves: search for a Forest card, put it onto the battlefield, shuffle. -/

#guard isForestCard forest
#guard isBasicLandCard forest
#guard !isForestCard mountain
#guard isBasicLandCard mountain
#guard isLandTypeCard mountain "Mountain"
#guard isLandTypeCard swamp "Swamp"
#guard !isLandTypeCard mountain "Swamp"
#guard !isLandTypeCard swamp "Mountain"

/-- Nonbasic land with the Forest type; Wood Elves can find it (CR 305.7). -/
def tropicalIsland : CardDef :=
  land "Tropical Island" "" (subtypes := #["Forest", "Island"])

#guard isForestCard tropicalIsland
#guard !isBasicLandCard tropicalIsland
#guard !isForestCard roguesPassage

/-- Wood Elves in hand with enough mana to cast it (CR 601.2). -/
def woodElvesSetup : Game :=
  withGreenMana (addToHand afterDraw woodElves ⟨0⟩) ⟨0⟩

#guard woodElvesSetup.canCast ⟨0⟩ (handCardNamed woodElvesSetup ⟨0⟩ "Wood Elves")
#guard woodElvesSetup.asSorcery? ⟨0⟩
#guard !woodElves.keywords.flash
#guard woodElves.hasSorcerySpeed
#guard woodElves.power == some 1
#guard woodElves.toughness == some 1

def proposedWoodElves : Game :=
  mustApply woodElvesSetup ⟨0⟩ (.cast (handCardNamed woodElvesSetup ⟨0⟩ "Wood Elves").id)

#guard proposedWoodElves.pending == .activateManaAbilities ⟨0⟩
#guard proposedWoodElves.log.any (fun s => mentions s "begins casting Wood Elves")

def paidWoodElves : Game := mustApply proposedWoodElves ⟨0⟩ .pay

#guard paidWoodElves.stack.size == 1
#guard paidWoodElves.hasPriority ⟨0⟩
#guard paidWoodElves.log.any (fun s => mentions s "casts Wood Elves")

/-- The creature enters; the search waits on the stack (CR 603.6a). -/
def woodElvesEntered : Game := passBoth paidWoodElves

#guard (namedPermanent woodElvesEntered "Wood Elves").printed.power == some 1
#guard woodElvesEntered.power (namedPermanent woodElvesEntered "Wood Elves") == 1
#guard woodElvesEntered.toughness (namedPermanent woodElvesEntered "Wood Elves") == 1
#guard woodElvesEntered.stack.size == 1
#guard (woodElvesEntered.object! woodElvesEntered.stack.back!.objectId).triggeredAbility ==
  some .onEnterSearchForest
#guard (woodElvesEntered.object! woodElvesEntered.stack.back!.objectId).sourceId ==
  some (namedPermanent woodElvesEntered "Wood Elves").id
#guard woodElvesEntered.log.any (fun s => mentions s "enters the battlefield")
#guard woodElvesEntered.log.any (fun s => mentions s "enters trigger is put on the stack")

/-- Mountain on top, Forest below: search finds the Forest (CR 701.19). -/
def woodElvesKnownLib : Game :=
  addToLibraryTop (addToLibraryTop woodElvesEntered forest ⟨0⟩) mountain ⟨0⟩

def woodElvesResolved : Game := passBoth woodElvesKnownLib

#guard woodElvesResolved.pending == .none
#guard woodElvesResolved.hasPriority ⟨0⟩
#guard woodElvesResolved.stack.isEmpty
#guard woodElvesResolved.battlefield.any (fun o => o.name == "Wood Elves")
#guard woodElvesResolved.battlefield.any (fun o => o.name == "Forest")
#guard !(namedPermanent woodElvesResolved "Forest").status.tapped
#guard !(namedPermanent woodElvesResolved "Forest").status.summoningSick
#guard (woodElvesResolved.player ⟨0⟩).landsPlayedThisTurn ==
  (woodElvesKnownLib.player ⟨0⟩).landsPlayedThisTurn
#guard woodElvesResolved.log.any (fun s =>
  mentions s "puts Forest onto the battlefield" && !mentions s "tapped")
#guard woodElvesResolved.log.any (fun s => mentions s "shuffles their library")

-- A Mountain on top is not chosen; the Forest type is required (CR 305.7).
#guard !(woodElvesResolved.battlefield.any (fun o =>
  o.name == "Mountain" &&
    !(woodElvesKnownLib.battlefield.any (fun p => p.id == o.id))))

-- The fetched Forest can tap for {G} immediately.
#guard
  match woodElvesResolved.tapForMana ⟨0⟩
      (namedPermanent woodElvesResolved "Forest").id (.colored .green) with
  | .ok g =>
    (g.player ⟨0⟩).manaPool.green ==
      (woodElvesResolved.player ⟨0⟩).manaPool.green + 1 &&
      (namedPermanent g "Forest").status.tapped
  | .error _ => false

-- Direct resolution of an enters-search trigger puts a Forest onto the battlefield.
#guard
  let g := addToLibraryTop afterDraw forest ⟨0⟩
  let beforeLands := (g.player ⟨0⟩).landsPlayedThisTurn
  let g := g.applyTriggeredAbility ⟨0⟩ .onEnterSearchForest none
  g.battlefield.any (fun o => o.name == "Forest" && !o.status.tapped) &&
    (g.player ⟨0⟩).landsPlayedThisTurn == beforeLands &&
    g.log.any (fun s => mentions s "puts Forest onto the battlefield") &&
    g.log.any (fun s => mentions s "shuffles their library")

/-- The trigger still searches if Wood Elves has left the battlefield (CR 113.7a). -/
def woodElvesLeftBeforeTrigger : Game :=
  let id := (namedPermanent woodElvesKnownLib "Wood Elves").id
  let (g, _) := woodElvesKnownLib.move id (.graveyard ⟨0⟩) none
  passBoth g

#guard !(woodElvesLeftBeforeTrigger.battlefield.any (fun o => o.name == "Wood Elves"))
#guard (woodElvesLeftBeforeTrigger.player ⟨0⟩).graveyard.any (fun id =>
  (woodElvesLeftBeforeTrigger.object! id).name == "Wood Elves")
#guard woodElvesLeftBeforeTrigger.battlefield.any (fun o => o.name == "Forest")
#guard woodElvesLeftBeforeTrigger.log.any (fun s => mentions s "puts Forest onto the battlefield")

/-- No Forest in the library: the search fails and the library is still shuffled. -/
def woodElvesNoForest : Game := passBoth woodElvesEntered

#guard woodElvesNoForest.stack.isEmpty
#guard !(woodElvesNoForest.battlefield.any (fun o => o.name == "Forest"))
#guard woodElvesNoForest.log.any (fun s => mentions s "finds no Forest card")
#guard woodElvesNoForest.log.any (fun s => mentions s "shuffles their library")

/-- A nonbasic Forest card is a legal find (CR 305.7). -/
def woodElvesNonbasic : Game :=
  let g := addToLibraryTop woodElvesEntered tropicalIsland ⟨0⟩
  passBoth g

#guard woodElvesNonbasic.battlefield.any (fun o => o.name == "Tropical Island")
#guard !(namedPermanent woodElvesNonbasic "Tropical Island").status.tapped
#guard woodElvesNonbasic.log.any (fun s =>
  mentions s "puts Tropical Island onto the battlefield")

/-- Landfall triggers when the fetched Forest enters (CR 603.6a). -/
def woodElvesLandfallPending : Game :=
  let g := addPermanent woodElvesKnownLib beornsHospitality ⟨0⟩ ⟨0⟩
  let g := addPermanent g grizzlyBears ⟨0⟩ ⟨0⟩
  passBoth g

#guard woodElvesLandfallPending.pending == .chooseTargets ⟨0⟩
#guard woodElvesLandfallPending.battlefield.any (fun o => o.name == "Forest")
#guard (woodElvesLandfallPending.object! woodElvesLandfallPending.stack.back!.objectId).triggeredAbility ==
  some .onLandYouControlEntersPlusOnePlusOne
#guard woodElvesLandfallPending.log.any (fun s => mentions s "landfall trigger is put on the stack")

/-- The agent casts Wood Elves when that is the playable spell. -/
def agentWoodElvesOnly : Game :=
  let g := clearHandPlayedLand afterDraw ⟨0⟩
  withGreenMana (addToHand g woodElves ⟨0⟩) ⟨0⟩

#guard
  match Agent.choose agentWoodElvesOnly ⟨0⟩ with
  | some (.cast id) => (agentWoodElvesOnly.object! id).name == "Wood Elves"
  | _ => false

end Mtg.Engine.Tests
