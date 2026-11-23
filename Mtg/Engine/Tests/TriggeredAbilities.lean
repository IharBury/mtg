import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Catalog.RealityFractureCommander

/-!
# Phase 7 Unified `TriggerPattern` & Pattern-Driven `matchTriggers` Runtime Tests

Comprehensive gameplay `#guard` regression suite for Phase 7 of
`ABILITY_ALIGNMENT_PLAN.md` (anchored to the 25 September 2026 CR):
1. Pattern-driven `Core.matchTriggers` across zone changes, combat, damage/life,
   casts, counters, steps, player actions, and novel parsed triggered abilities.
2. Exact CR 603.10a–f look-back (`pre`) vs. non-look-back (`post`), including
   `.or .thisEnters .thisDies` (each disjunct independently consulting `pre` or
   `post`, single-event deduplication per CR 603.2c) and CR 603.2e `becomesTapped`.
3. CR 603.4 `interveningIf?` (checked on trigger AND rechecked on resolution) vs.
   CR 603.2 `.whenCond` (checked on trigger ONLY, not rechecked on resolution).
4. CR 605.1b triggered mana ability classification (`TriggeredAbility.isManaAbility`).
5. CR 700.1 `BatchGrouping` (`perOccurrence`, `oncePerBatch`, `perPlayerInBatch`,
   `perSourceInBatch`).
6. CR 714.2b/d/4 & 704.5s dynamic Layer-6 Saga chapter grants and removals
   updating `Game.finalChapterNumber`, `addLoreAfterDrawStep`, chapter triggers,
   and SBA sacrifice.
7. Two distinct modal triggers on one card with independent `ModalSpec` modes.
8. Path of Ancestry via `triggeredAbilities` (`isManaSpentCastCommanderTypeScry`):
   live, LKI departed, phased-out (CR 702.26d), Layer-6 ability removal, and copy.
9. `CardDef.modellingError?` trigger validation (empty `activeZones`, no-op
   resolutions, empty or unmodelled modal `modes`).
-/

namespace Mtg.Engine.Tests.TriggeredAbilitiesSuite

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

private def p0 : PlayerId := ⟨0⟩
private def p1 : PlayerId := ⟨1⟩

private def testCause : EventCause := .oneShotEffect none none

private def mustParse (raw : String) : CardDef :=
  match parseOracleCard raw with
  | .ok c => c
  | .error e => panic! s!"parseOracleCard failed: {e}"

private def namedPerm (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing permanent {name}"

private def mkCreature (name : String) (subs : Array String := #[])
    (mana : ManaCost := ManaCost.ofGeneric 2) (p t : Int := 2)
    (triggers : Array TriggeredAbility := #[])
    (statics : Array StaticAbility := #[])
    (kws : Array KeywordAbility := #[]) : CardDef :=
  { name := name
    manaCost := mana
    types := #[.creature]
    subtypes := subs
    power := some (.fixed p)
    toughness := some (.fixed t)
    triggeredAbilities := triggers
    staticAbilities := statics
    keywords := kws }

private def mkEnchantment (name : String) (triggers : Array TriggeredAbility) : CardDef :=
  { name := name
    manaCost := ManaCost.ofGeneric 2
    types := #[.enchantment]
    triggeredAbilities := triggers }

private def quietGame (g : Game) : Game :=
  g.change (.waitingTriggers #[])

private def lifeOf (g : Game) (p : PlayerId) : Int :=
  (g.player p).life

private def addToZone (g : Game) (card : CardDef) (owner : PlayerId) (z : Zone)
    (ctrl : Option PlayerId := some owner) (status : Status := {}) : Game × GameObject :=
  g.allocObject card owner z ctrl status

/-! ### 1. Pattern-Driven `Core.matchTriggers` Across Event Families & Novel Parsed Triggers -/

-- Novel triggered abilities parsed via `Parser.parseNovelTriggeredAbilityLine`
-- execute end-to-end in `Game`:
-- (a) "Whenever a Wizard creature you control becomes tapped, you gain 2 life."
-- (b) "Whenever a spell you control is countered, draw a card." (CR 603.10e)
#guard
  let tapWatcher := mustParse
    "Tap Scribe\n{1}{U}\nEnchantment\nWhenever a Wizard creature you control becomes tapped, you gain 2 life."
  let counterWatcher := mustParse
    "Arcane Rebuke\n{2}{U}\nEnchantment\nWhenever a spell you control is countered, draw a card."
  let wizard := mkCreature "Test Wizard" #["Wizard"]
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw tapWatcher p0 p0) counterWatcher p0 p0) wizard p0 p0)
  let wizObj := namedPerm g0 "Test Wizard"
  let gTapped := g0.becomeTapped wizObj (cause := some testCause)
  let tapMatched :=
    gTapped.waitingTriggers.size == 1 &&
    gTapped.waitingTriggers[0]!.source.name == "Tap Scribe"
  let gTapRes := (gTapped.receivePriority p0).resolveTop
  let tapGainedLife := lifeOf gTapRes p0 == lifeOf g0 p0 + 2
  -- Countered spell trigger (CR 603.10e):
  let (gSp0, spObj) := addToZone g0 { name := "Test Bolt", types := #[.instant], manaCost := ManaCost.ofColor .red } p0 .stack (some p0)
  let gSp1 := gSp0.putStackEntry p0 spObj.id
  let (gCountered, _) := gSp1.move spObj.id (.graveyard p0) none (verb := some .counter) (actor := some p1) (cause := some testCause)
  let counterMatched :=
    gCountered.waitingTriggers.size == 1 &&
    gCountered.waitingTriggers[0]!.source.name == "Arcane Rebuke"
  tapMatched && tapGainedLife && counterMatched

-- Player-action triggers: scry, surveil, proliferate, and CR 603.10f player loses the game.
#guard
  let actionsWatcher := mkEnchantment "Action Watcher" #[
    TriggeredAbility.ofPattern (.playerAction .you .scry) (Instruction.gainLifeFixed 1),
    TriggeredAbility.ofPattern (.playerAction .you .surveil) (Instruction.gainLifeFixed 2),
    TriggeredAbility.ofPattern (.playerAction .you .proliferate) (Instruction.gainLifeFixed 3),
    TriggeredAbility.ofPattern (.playerAction .opponent .losesGame) (Instruction.gainLifeFixed 4)
  ]
  let g0 := quietGame (addPermanent afterDraw actionsWatcher p0 p0)
  let gScry := g0.record (GameEvent.looked g0.turnNumber p0 1 (cause := some testCause))
  let gSurv := g0.record (GameEvent.looked g0.turnNumber p0 1 (surveil := true) (cause := some testCause))
  let gProl := g0.record (GameEvent.proliferated g0.turnNumber p0 (cause := some testCause))
  let gLose := g0.record (GameEvent.playerLost g0.turnNumber p1 .lifeZeroOrLess (cause := some testCause))
  gScry.waitingTriggers.any (·.pattern == .playerAction .you .scry) &&
    gSurv.waitingTriggers.any (·.pattern == .playerAction .you .surveil) &&
    gProl.waitingTriggers.any (·.pattern == .playerAction .you .proliferate) &&
    gLose.waitingTriggers.any (·.pattern == .playerAction .opponent .losesGame)

-- Combat triggers: blocks and becomes blocked.
#guard
  let combatWatcher := mkEnchantment "Combat Watcher" #[
    TriggeredAbility.mkTrigger (.blocks (.all #[.hasType .creature, .controlledBy .opponent])) (Effect.gainLife 1),
    TriggeredAbility.mkTrigger (.becomesBlocked (.all #[.hasType .creature, .controlledBy .you])) (Effect.gainLife 2)
  ]
  let atkDef := mkCreature "Attacker" #["Warrior"]
  let blkDef := mkCreature "Blocker" #["Soldier"]
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw combatWatcher p0 p0) atkDef p0 p0) blkDef p1 p1)
  let atkObj := namedPerm g0 "Attacker"
  let blkObj := namedPerm g0 "Blocker"
  let g1 := g0.markAttacking atkObj.id
  let gBlk := g1.withBatch (some testCause) fun g =>
    let g := g.record (GameEvent.blockersDeclared g.turnNumber p1 #[(g.snapshot blkObj, atkObj.id)] (cause := testCause))
    g.record (GameEvent.becameBlocked g.turnNumber (g.snapshot atkObj) #[blkObj.id] (cause := testCause))
  gBlk.waitingTriggers.size == 2 &&
    gBlk.waitingTriggers.any (·.pattern == .blocks (.all #[.hasType .creature, .controlledBy .opponent])) &&
    gBlk.waitingTriggers.any (·.pattern == .becomesBlocked (.all #[.hasType .creature, .controlledBy .you]))

/-! ### 2. Exact CR 603.10a–f Look-Back (`pre`) vs. Non-Look-Back (`post`) -/

-- `.or .thisEnters .thisDies` disjunction:
-- (a) Entering alone fires once (consulting `post`);
-- (b) Dying alone fires once (consulting `pre`);
-- (c) Entering AND dying in the SAME simultaneous batch fires TWICE (once via
--     `post` for entering, once via `pre` for dying);
-- (d) Casting an Equipment spell targeting your creature with
--     `youCastEquipmentOrTargetingCreatureYouControl` (`.or` where BOTH sides
--     match the SAME event) fires ONLY ONCE per CR 603.2c!
#guard
  let enterOrDiesAb : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.or .thisEnters .thisDies) (Effect.gainLife 1)
  let phoenix := mkCreature "Enter-Or-Dies Phoenix" #["Phoenix"] (triggers := #[enterOrDiesAb])
  let (g0, hObj) := addToZone (quietGame afterDraw) phoenix p0 (.hand p0) (some p0)
  -- (a) Enter alone:
  let (gEnt, bfId) := g0.putOntoBattlefield hObj.id p0
  let enterOnceOk := gEnt.waitingTriggers.size == 1 && gEnt.waitingTriggers[0]!.pattern == .thisEnters
  -- (b) Die alone:
  let gDie := (quietGame gEnt).moveToOwnerGraveyard (gEnt.object! bfId) "dies" (verb := some .destroy) (cause := some testCause)
  let dieOnceOk := gDie.waitingTriggers.size == 1 && gDie.waitingTriggers[0]!.pattern == .thisDies
  -- (c) Enter AND die in the same batch:
  let gBoth := g0.withBatch (some testCause) fun g =>
    let (g, newId) := g.putOntoBattlefield hObj.id p0
    g.moveToOwnerGraveyard (g.object! newId) "dies immediately" (verb := some .destroy) (cause := some testCause)
  let bothTwiceOk :=
    gBoth.waitingTriggers.size == 2 &&
    gBoth.waitingTriggers.any (·.pattern == .thisEnters) &&
    gBoth.waitingTriggers.any (·.pattern == .thisDies)
  -- (d) Single event matching BOTH sides of `.or` fires only ONCE (CR 603.2c):
  let orWatcher := mkEnchantment "Equipment Or Target Watcher" #[
    TriggeredAbility.mkTrigger .youCastEquipmentOrTargetingCreatureYouControl (Effect.gainLife 1)
  ]
  let bear := mkCreature "Friendly Bear" #["Bear"]
  let gOr0 := quietGame (addPermanent (addPermanent afterDraw orWatcher p0 p0) bear p0 p0)
  let bearObj := namedPerm gOr0 "Friendly Bear"
  let eqSpell : CardDef := {
    name := "Targeted Blade", manaCost := ManaCost.ofGeneric 1
    types := #[.artifact], subtypes := #["Equipment"]
  }
  let (gOr1, spObj) := addToZone gOr0 eqSpell p0 .stack (some p0)
  let gOr2 := gOr1.putStackEntry p0 spObj.id
  let gOr3 := gOr2.setStackEntryTargets spObj.id #[Target.permanent bearObj.id]
  let gOrCast := (quietGame gOr3).record (GameEvent.spellCast gOr3.turnNumber p0 (gOr3.snapshot (gOr3.object! spObj.id)) (.hand p0) (cause := testCause))
  let orDedupOk := gOrCast.waitingTriggers.size == 1
  enterOnceOk && dieOnceOk && bothTwiceOk && orDedupOk

-- CR 603.10c (`becomesUnattached`) and CR 603.10d (`controlLost`) look back to `pre`:
-- even if the watcher leaves the battlefield in the same batch as the unattach/control-loss,
-- it still triggers via Pass A (`pre`).
#guard
  let unattachAb := TriggeredAbility.mkTrigger (.becomesUnattached (.hasSubtype (.literal .equipment))) (Effect.gainLife 1)
  let ctrlLostAb := TriggeredAbility.mkTrigger (.controlLost (.hasType .creature) .you) (Effect.gainLife 2)
  let watcher := mkEnchantment "Lookback Watcher" #[unattachAb, ctrlLostAb]
  let host := mkCreature "Host Bear" #["Bear"]
  let blade : CardDef := { name := "Test Blade", manaCost := ManaCost.ofGeneric 1, types := #[.artifact], subtypes := #["Equipment"] }
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw watcher p0 p0) host p0 p0) blade p0 p0)
  let wObj := namedPerm g0 "Lookback Watcher"
  let hObj := namedPerm g0 "Host Bear"
  let bObj := namedPerm g0 "Test Blade"
  let gAtt := quietGame (g0.attachSourceTo bObj hObj (cause := some testCause))
  let gBatch := gAtt.withBatch (some testCause) fun g =>
    let g := g.record (GameEvent.unattached g.turnNumber (g.snapshot (g.object! bObj.id)) hObj.id (cause := testCause))
    let g := g.createEffect (.layered (.objects #[hObj.id]) (.control p1) .indefinite) (cause := some testCause)
    g.moveToOwnerGraveyard (g.object! wObj.id) "watcher destroyed" (verb := some .destroy) (cause := some testCause)
  gBatch.waitingTriggers.size == 2 &&
    gBatch.waitingTriggers.any (·.ability == unattachAb) &&
    gBatch.waitingTriggers.any (·.ability == ctrlLostAb)

-- CR 603.2e (`becomesTapped`) is NOT a look-back trigger and evaluates `post`:
-- if a creature becomes tapped AND leaves the battlefield in the same batch,
-- its `thisBecomesTapped` trigger is absent on `post` and does NOT trigger.
#guard
  let tapAb := TriggeredAbility.mkTrigger .thisBecomesTapped (Effect.gainLife 1)
  let tapper := mkCreature "Ephemeral Tapper" #["Elf"] (triggers := #[tapAb])
  let g0 := quietGame (addPermanent afterDraw tapper p0 p0)
  let tObj := namedPerm g0 "Ephemeral Tapper"
  -- Control check: tapping alone DOES trigger on `post`.
  let gTapOnly := g0.becomeTapped tObj (cause := some testCause)
  -- Tapping + leaving in the same batch: absent on `post`, so does NOT trigger.
  let gTapAndLeave := g0.withBatch (some testCause) fun g =>
    let g := g.becomeTapped (g.object! tObj.id) (cause := some testCause)
    g.moveToOwnerGraveyard (g.object! tObj.id) "destroyed in same batch" (verb := some .destroy) (cause := some testCause)
  gTapOnly.waitingTriggers.size == 1 && gTapAndLeave.waitingTriggers.isEmpty

/-! ### 3. CR 603.4 `interveningIf?` vs. CR 603.2 `.whenCond` -/

-- Compare two upkeep triggers with the SAME condition (`condYouAreMonarch`):
-- (a) `interveningIf?`: doesn't trigger when not monarch; triggers when monarch,
--     and if you lose the monarchy before resolution it DOES NOTHING on resolution!
-- (b) `.whenCond`: doesn't trigger when not monarch; triggers when monarch,
--     and even if you lose the monarchy before resolution it STILL RESOLVES!
#guard
  let setMonarch (g : Game) (who : PlayerId) (prev : Option PlayerId := none) : Game :=
    g.record (GameEvent.becameMonarch g.turnNumber who prev)
  let ifAb : TriggeredAbility :=
    TriggeredAbility.ofPattern .stepYourUpkeep
      (Instruction.gainLifeFixed 3) (interveningIf? := some TriggeredAbility.condYouAreMonarch)
  let whenCondAb : TriggeredAbility :=
    TriggeredAbility.ofPattern (.whenCond .stepYourUpkeep TriggeredAbility.condYouAreMonarch)
      (Instruction.gainLifeFixed 5)
  let ifCard := mkEnchantment "Intervening-If Crown" #[ifAb]
  let wcCard := mkEnchantment "WhenCond Crown" #[whenCondAb]
  let g0 := quietGame (addPermanent (addPermanent afterDraw ifCard p0 p0) wcCard p0 p0)
  -- Neither triggers when not the monarch:
  let gNoMonarch := g0.record (GameEvent.stepped g0.turnNumber .upkeep p0)
  let neitherWhenFalse := gNoMonarch.waitingTriggers.isEmpty
  -- Both trigger when `p0` is the monarch:
  let gMonIf := setMonarch (quietGame (addPermanent afterDraw ifCard p0 p0)) p0
  let gMonIfStack := (gMonIf.record (GameEvent.stepped gMonIf.turnNumber .upkeep p0)).receivePriority p0
  -- Lose monarchy before resolution -> intervening-if fizzles!
  let gMonIfLost := (setMonarch gMonIfStack p1 (some p0)).resolveTop
  -- Keep monarchy -> intervening-if resolves!
  let gMonIfKept := gMonIfStack.resolveTop
  let gMonWc := setMonarch (quietGame (addPermanent afterDraw wcCard p0 p0)) p0
  let gMonWcStack := (gMonWc.record (GameEvent.stepped gMonWc.turnNumber .upkeep p0)).receivePriority p0
  -- Lose monarchy before resolution -> `.whenCond` STILL resolves!
  let gMonWcLost := (setMonarch gMonWcStack p1 (some p0)).resolveTop
  neitherWhenFalse &&
    gMonIfStack.stack.size == 1 &&
    lifeOf gMonIfLost p0 == lifeOf gMonIf p0 &&
    lifeOf gMonIfKept p0 == lifeOf gMonIf p0 + 3 &&
    gMonWcStack.stack.size == 1 &&
    lifeOf gMonWcLost p0 == lifeOf gMonWc p0 + 5

/-! ### 4. CR 605.1b Triggered Mana Ability Classification -/

#guard
  let onManaAddMana : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.activateAbility .any .anyObject .manaAbility)
      { body := Instruction.addSimpleMana #[.colored .green] }
  let onManaAddedPool : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.playerAction .you .manaAdded)
      { body := Instruction.addSimpleMana #[.colored .red] }
  -- CR 605.1b has NO library-movement exclusion (unlike CR 605.1a):
  let onManaAddAndDraw : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.playerAction .you .manaAdded)
      { body := .seq #[Instruction.addSimpleMana #[.colored .blue], Instruction.drawFixed 1] }
  -- Fails criterion 1 (requires target):
  let targetedManaTrigger : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.playerAction .you .manaAdded)
      { targets := .creature, body := Instruction.addSimpleMana #[.colored .green] }
  -- Fails criterion 2 (does not trigger from mana ability or mana added):
  let etbAddMana : TriggeredAbility :=
    TriggeredAbility.mkTrigger .thisEnters
      { body := Instruction.addSimpleMana #[.colored .green] }
  -- Fails criterion 3 (cannot add mana):
  let onManaGainLife : TriggeredAbility :=
    TriggeredAbility.mkTrigger (.playerAction .you .manaAdded) (Effect.gainLife 1)
  -- Modal where one mode targets fails criterion 1:
  let modalTargetedMana : TriggeredAbility :=
    TriggeredAbility.mkModal (.playerAction .you .manaAdded) #[
      { body := Instruction.addSimpleMana #[.colored .green] },
      { targets := .creature, body := Instruction.tap (.target 0) }
    ]
  -- Modal where no mode targets and at least one adds mana succeeds:
  let modalUntargetedMana : TriggeredAbility :=
    TriggeredAbility.mkModal (.playerAction .you .manaAdded) #[
      { body := Instruction.addSimpleMana #[.colored .green] },
      Effect.gainLife 1
    ]
  onManaAddMana.isManaAbility &&
    onManaAddedPool.isManaAbility &&
    onManaAddAndDraw.isManaAbility &&
    !targetedManaTrigger.isManaAbility &&
    !etbAddMana.isManaAbility &&
    !onManaGainLife.isManaAbility &&
    !modalTargetedMana.isManaAbility &&
    modalUntargetedMana.isManaAbility

/-! ### 5. CR 700.1 `BatchGrouping` Semantics -/

-- `perOccurrence` vs. `oncePerBatch` on simultaneous vs. sequential deaths;
-- `perPlayerInBatch` on multi-player multi-card discard;
-- `perSourceInBatch` on multi-source multi-packet damage (summing damage per source).
#guard
  let perOccAb := TriggeredAbility.mkTrigger .otherCreaturesDie (Effect.gainLife 1) (grouping := .perOccurrence)
  let onceBatchAb := TriggeredAbility.mkTrigger .otherCreaturesDie (Effect.gainLife 2) (grouping := .oncePerBatch)
  let perPlayerAb := TriggeredAbility.mkTrigger (.discard .any) (Effect.gainLife 3) (grouping := .perPlayerInBatch)
  let perSourceAb := TriggeredAbility.mkTrigger
    (.damageDealt (.hasType .creature) (.player .any))
    (Effect.gainLife 4) (grouping := .perSourceInBatch)
  let watcher := mkEnchantment "Grouping Watcher" #[perOccAb, onceBatchAb, perPlayerAb, perSourceAb]
  let cA := mkCreature "Creature A" #["Bear"]
  let cB := mkCreature "Creature B" #["Wolf"]
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw watcher p0 p0) cA p0 p0) cB p0 p0)
  let idA := (namedPerm g0 "Creature A").id
  let idB := (namedPerm g0 "Creature B").id
  -- Simultaneous death: perOccurrence = 2, oncePerBatch = 1
  let gSimDie := g0.withBatch (some testCause) fun g =>
    let g := g.moveToOwnerGraveyard (g.object! idA) "A dies" (verb := some .destroy) (cause := some testCause)
    g.moveToOwnerGraveyard (g.object! idB) "B dies" (verb := some .destroy) (cause := some testCause)
  let dieGroupingOk :=
    (gSimDie.waitingTriggers.filter (·.ability == perOccAb)).size == 2 &&
    (gSimDie.waitingTriggers.filter (·.ability == onceBatchAb)).size == 1
  -- Multi-player multi-card discard in one batch: 2 cards from p0 + 2 cards from p1 -> 2 triggers (1 per player)
  let gDisc := g0.withBatch (some testCause) fun g =>
    let h0 := (g.player p0).hand
    let h1 := (g.player p1).hand
    let g := if h0.size >= 2 then
        let (g, _) := g.move h0[0]! (.graveyard p0) none (verb := some .discard) (actor := some p0) (cause := some testCause)
        (g.move h0[1]! (.graveyard p0) none (verb := some .discard) (actor := some p0) (cause := some testCause)).1
      else g
    if h1.size >= 2 then
      let (g, _) := g.move h1[0]! (.graveyard p1) none (verb := some .discard) (actor := some p1) (cause := some testCause)
      (g.move h1[1]! (.graveyard p1) none (verb := some .discard) (actor := some p1) (cause := some testCause)).1
    else g
  let discGroupingOk :=
    (gDisc.waitingTriggers.filter (·.ability == perPlayerAb)).size == 2
  -- Multi-source multi-packet damage in one batch: cA deals 1+2, cB deals 3+4 -> 2 triggers with summed damage 3 and 7
  let gDmg := g0.withBatch (some testCause) fun g =>
    let snapA := g.snapshotDamageSource (g.object! idA)
    let snapB := g.snapshotDamageSource (g.object! idB)
    let g := g.record (GameEvent.damagedPlayer g.turnNumber snapA p1 1 false (cause := testCause))
    let g := g.record (GameEvent.damagedPlayer g.turnNumber snapA p1 2 false (cause := testCause))
    let g := g.record (GameEvent.damagedPlayer g.turnNumber snapB p1 3 false (cause := testCause))
    g.record (GameEvent.damagedPlayer g.turnNumber snapB p1 4 false (cause := testCause))
  let dmgTrigs := gDmg.waitingTriggers.filter (·.ability == perSourceAb)
  let dmgGroupingOk :=
    dmgTrigs.size == 2 &&
    dmgTrigs.any (fun wt => wt.causeId == some idA && wt.lastKnownPower == some 3) &&
    dmgTrigs.any (fun wt => wt.causeId == some idB && wt.lastKnownPower == some 7)
  dieGroupingOk && discGroupingOk && dmgGroupingOk

/-! ### 6. CR 714.2b/d/4 & 704.5s Dynamic Layer-6 Saga chapters -/

-- Granting a Chapter III ability in Layer 6 dynamically raises `Game.finalChapterNumber`
-- from 2 → 3, prevents CR 704.5s SBA sacrifice at 2 lore counters, allows
-- `addLoreAfterDrawStep` to add the 3rd lore counter, fires Chapter III when crossing 2 → 3,
-- and sacrifices on SBA once lore ≥ 3 and no chapter ability is on the stack.
-- Removing all abilities in Layer 6 drops `Game.finalChapterNumber` to 0 and halts
-- both `addLoreAfterDrawStep` and CR 704.5s sacrifice.
#guard
  let twoChSaga : CardDef := {
    name := "Dynamic Tale"
    manaCost := ManaCost.ofGeneric 2
    types := #[.enchantment]
    subtypes := #["Saga"]
    triggeredAbilities := #[
      TriggeredAbility.sagaChapter 1 (Effect.gainLife 1),
      TriggeredAbility.sagaChapter 2 (Effect.gainLife 2)
    ]
  }
  let g0 := quietGame (addPermanent afterDraw twoChSaga p0 p0)
  let sagaId := (namedPerm g0 "Dynamic Tale").id
  let baseFinalOk := g0.finalChapterNumber (g0.object! sagaId) == 2
  -- Put 2 lore counters (without chapter on stack): normally sacrificed by 704.5s.
  let gAt2 := quietGame (g0.recordPutCounters sagaId .lore 2 (byPlayer := some p0) (cause := some testCause))
  let sacAt2Ok := !(gAt2.checkSBA).battlefield.any (·.id == sagaId)
  -- Grant Chapter III in Layer 6 BEFORE checking SBA:
  let ch3Ab := TriggeredAbility.sagaChapter 3 (Effect.gainLife 5)
  let gGranted := gAt2.createEffect (.grantedTriggered sagaId ch3Ab false) (cause := some testCause)
  let grantedFinalOk := gGranted.finalChapterNumber (gGranted.object! sagaId) == 3
  -- Survives SBA at 2 lore counters because finalChapterNumber is now 3!
  let gSurvivesAt2 := gGranted.checkSBA
  let survivesAt2Ok := gSurvivesAt2.battlefield.any (·.id == sagaId)
  -- `addLoreAfterDrawStep` advances 2 → 3 and queues Chapter III!
  let gStep3 := gSurvivesAt2.addLoreAfterDrawStep
  let chapter3TriggeredOk :=
    (gStep3.object! sagaId).status.lore == 3 &&
    gStep3.waitingTriggers.any (fun wt => wt.source.id == sagaId && wt.ability.chapterNumbers? == some #[3])
  -- Once Chapter III resolves and leaves the stack, SBA 704.5s sacrifices the Saga:
  let gAfterCh3 := ((gStep3.receivePriority p0).resolveTop).checkSBA
  let sacAfterCh3Ok :=
    lifeOf gAfterCh3 p0 == lifeOf g0 p0 + 5 &&
    !gAfterCh3.battlefield.any (·.id == sagaId)
  -- Layer-6 ability removal sets `finalChapterNumber == 0`, preventing lore addition and SBA sac:
  let gHum := gAt2.createEffect (.losesAbilitiesUntilEot sagaId) (cause := some testCause)
  let humFinalOk :=
    gHum.finalChapterNumber (gHum.object! sagaId) == 0 &&
    (gHum.checkSBA).battlefield.any (·.id == sagaId) &&
    ((gHum.addLoreAfterDrawStep).object! sagaId).status.lore == 2
  baseFinalOk && sacAt2Ok && grantedFinalOk && survivesAt2Ok &&
    chapter3TriggeredOk && sacAfterCh3Ok && humFinalOk

/-! ### 7. Two Distinct Modal Triggers on One Card (`Instruction.chooseModes`) -/

-- A single card with an enters modal trigger (`[gain 3 life, draw 1]`) and a dies
-- modal trigger (`[gain 5 life, scry 2]`) preserves independent modes for each.
#guard
  let etbModal : TriggeredAbility :=
    TriggeredAbility.mkModal .thisEnters #[
      { body := Instruction.gainLifeFixed 3 },
      { body := Instruction.drawFixed 1 }
    ]
  let diesModal : TriggeredAbility :=
    TriggeredAbility.mkModal .thisDies #[
      { body := Instruction.gainLifeFixed 5 },
      { body := Instruction.scryFixed 2 }
    ]
  let dualModalCard := mkCreature "Dual Modal Oracle" #["Sphinx"] (triggers := #[etbModal, diesModal])
  let (g0, hObj) := addToZone (quietGame afterDraw) dualModalCard p0 (.hand p0) (some p0)
  let (gEnt, bfId) := g0.putOntoBattlefield hObj.id p0
  let gEntPrompt := gEnt.receivePriority p0
  let etbModesSeen :=
    match gEntPrompt.stack.back? with
    | some se => gEntPrompt.triggerModesOf (gEntPrompt.object! se.objectId)
    | none => #[]
  let gEntDone := (mustApply gEntPrompt p0 (.chooseMode 0)).resolveTop
  let etbOk :=
    etbModesSeen == etbModal.modeEffects &&
    lifeOf gEntDone p0 == lifeOf g0 p0 + 3
  -- Now destroy it; dies modal trigger must offer `diesModal.modeEffects` (gain 5 life / scry 2)!
  let gDied := (quietGame gEntDone).moveToOwnerGraveyard (gEntDone.object! bfId) "dies" (verb := some .destroy) (cause := some testCause)
  let gDiePrompt := gDied.receivePriority p0
  let dieModesSeen :=
    match gDiePrompt.stack.back? with
    | some se => gDiePrompt.triggerModesOf (gDiePrompt.object! se.objectId)
    | none => #[]
  let gDieDone := (mustApply gDiePrompt p0 (.chooseMode 0)).resolveTop
  let dieOk :=
    dieModesSeen == diesModal.modeEffects &&
    lifeOf gDieDone p0 == lifeOf gEntDone p0 + 5
  etbOk && dieOk

/-! ### 8. Path of Ancestry via `triggeredAbilities` (`isManaSpentCastCommanderTypeScry`) -/

-- Tests live, LKI departed, phased-out (CR 702.26d), Layer-6 ability removal,
-- and copied Path of Ancestry.
#guard
  let cmdrDef : CardDef := {
    name := "Elf Commander", manaCost := ManaCost.ofColor .green
    supertypes := #[.legendary], types := #[.creature], subtypes := #["Elf", "Noble"]
    power := some (.fixed 2), toughness := some (.fixed 2)
  }
  let elfSpell := mkCreature "Llanowar Test" #["Elf"] (mana := ManaCost.ofGeneric 1)
  let ancestryLand : CardDef := {
    name := "Test Path of Ancestry"
    types := #[.land]
    triggeredAbilities := #[TriggeredAbility.onManaSpentCastCommanderTypeScry]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])]
  }
  let blankLand : CardDef := {
    name := "Blank Land", types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaAbility (.sequence #[(.colorless, .const 1)])]
  }
  let baseGame : Game :=
    match Start.start {
      seats := #[
        { name := "P0", deck := Array.replicate 60 forest, commanders := #[cmdrDef] },
        { name := "P1", deck := Array.replicate 60 mountain }
      ]
      format := .constructed
      seed := 1
      startingPlayer := some 0
    } with
    | .ok g => passBoth (keepOpeningHands g 8)
    | .error e => panic! e
  let setupBase : Game × ObjectId × ObjectId :=
    let g := addPermanent baseGame ancestryLand p0 p0
    let landId := (namedPerm g "Test Path of Ancestry").id
    let (g, spObj) := addToZone g elfSpell p0 (.hand p0) (some p0)
    (g, landId, spObj.id)
  let (gBase, landId, spId) := setupBase
  let didScry (g : Game) : Bool :=
    (g.stack.back?.any fun se => g.ancestryManaSpentOn se.objectId) &&
      match g.pending with
      | .scry p' 1 _ => p' == p0
      | _ => false
  -- Helper: produce 1 mana from `srcId`, optionally mutate `g`, then cast & pay `spId`.
  let castWithManaFrom (g : Game) (srcId : ObjectId) (beforeCast : Game → Game := id) : Game :=
    let g := g.addMana p0 .colorless 1 (source := some srcId)
    let g := beforeCast g
    let g := mustApply g p0 (.cast spId)
    mustApply g p0 .pay
  -- (a) Live Path of Ancestry triggers scry 1:
  let gLive := castWithManaFrom gBase landId
  let liveOk := didScry gLive
  -- (b) Departed before spell cast (LKI) still triggers scry 1:
  let gLki := castWithManaFrom gBase landId fun g =>
    (g.move landId (.graveyard p0) none (cause := some testCause)).1
  let lkiOk := didScry gLki
  -- (c) Phased out before spell cast (CR 702.26d) still triggers scry 1:
  let gPhased := castWithManaFrom gBase landId fun g =>
    g.phaseOut (g.object! landId) (cause := some testCause)
  let phasedOk := didScry gPhased
  -- (d) Layer-6 ability removal suppresses Path of Ancestry scry trigger:
  let gLostAb := castWithManaFrom
    (gBase.createEffect (.losesAbilitiesUntilEot landId) (cause := some testCause))
    landId
  let lostAbOk :=
    !(gLostAb.stack.back?.any fun se => gLostAb.ancestryManaSpentOn se.objectId) &&
    gLostAb.pending == .none
  -- (e) Layer-1 copy of Path of Ancestry onto `blankLand` inherits the trigger:
  let gCopy0 := addPermanent gBase blankLand p0 p0
  let blankId := (namedPerm gCopy0 "Blank Land").id
  let gCopy1 := gCopy0.createEffect
    (.layered (.objects #[blankId]) (.copy ancestryLand) .untilEndOfTurn) (cause := some testCause)
  let gCopied := castWithManaFrom gCopy1 blankId
  let copyOk := didScry gCopied
  liveOk && lkiOk && phasedOk && lostAbOk && copyOk

/-! ### 9. `CardDef.modellingError?` Trigger Validation -/

#guard
  let emptyZonesCard := mkEnchantment "Empty Zones" #[
    { TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1) with activeZones := #[] }
  ]
  let noopTriggerCard := mkEnchantment "Noop Trigger" #[
    TriggeredAbility.mkTrigger .thisEnters { body := .noop }
  ]
  let emptyModesCard := mkEnchantment "Empty Modes" #[
    TriggeredAbility.mkModal .thisEnters #[]
  ]
  let badModeCard := mkEnchantment "Bad Mode" #[
    TriggeredAbility.mkModal .thisEnters #[Effect.gainLife 1, { body := .noop }]
  ]
  let validCard := mkEnchantment "Valid Trigger" #[
    TriggeredAbility.mkTrigger .thisEnters (Effect.gainLife 1),
    TriggeredAbility.mkModal .thisDies #[Effect.gainLife 2, Effect.scry 1],
    TriggeredAbility.onManaSpentCastCommanderTypeScry
  ]
  let validSaga : CardDef := {
    name := "Valid Saga", types := #[.enchantment], subtypes := #["Saga"]
    triggeredAbilities := #[
      TriggeredAbility.sagaChapter 1 (Effect.gainLife 1),
      TriggeredAbility.sagaChapters #[2, 3] (Effect.scry 2)
    ]
  }
  emptyZonesCard.modellingError?.isSome &&
    noopTriggerCard.modellingError?.isSome &&
    emptyModesCard.modellingError?.isSome &&
    badModeCard.modellingError?.isSome &&
    validCard.modellingError?.isNone &&
    validSaga.modellingError?.isNone

/-! ### 10. Distributed `.whenCond` over `.or`, Cross-Pass `BatchGrouping`, Self-Countered Stack Triggers, `.controlLost` Dedup, & `matchesTriggerPattern` Constraints -/

-- (a) `.whenCond (.or .thisEnters .thisAttacks) cond` parsed from Oracle triggers on
-- both enters and attacks when `cond` holds, and does not trigger when `cond` fails;
-- mixed-lookback `.whenCond (.or .thisEnters .thisDies) cond` evaluates `cond` on `pre`
-- for the dies disjunct even if the Wizard dies in the same batch.
#guard
  let raider := mustParse
    "Arcane Raider\n{2}{U}\nCreature — Human\n2/2\nWhenever this creature enters or attacks while you control a Wizard, draw a card."
  let wizard := mkCreature "Partner Wizard" #["Wizard"]
  -- Enters WITHOUT a Wizard: 0 triggers.
  let (g0, hNoWiz) := addToZone (quietGame afterDraw) raider p0 (.hand p0) (some p0)
  let (gNoWiz, _) := g0.putOntoBattlefield hNoWiz.id p0
  let noWizOk := gNoWiz.waitingTriggers.isEmpty
  -- Enters WITH a Wizard: 1 trigger.
  let gWiz0 := addPermanent (quietGame afterDraw) wizard p0 p0
  let (gWiz1, hWithWiz) := addToZone gWiz0 raider p0 (.hand p0) (some p0)
  let (gEntWiz, raiderBfId) := gWiz1.putOntoBattlefield hWithWiz.id p0
  let entWizOk := gEntWiz.waitingTriggers.size == 1
  -- Attacks WITH a Wizard: 1 trigger.
  let preAtk := quietGame gEntWiz
  let atkSnap := preAtk.snapshot (preAtk.object! raiderBfId)
  let gAtk := preAtk.record (GameEvent.attackersDeclared preAtk.turnNumber p0 #[(atkSnap, .player p1)])
  let atkWizOk := gAtk.waitingTriggers.size == 1 && gAtk.waitingTriggers[0]!.source.name == "Arcane Raider"
  -- Mixed-lookback `.whenCond (.or .thisEnters .thisDies) (youControlWizard)`:
  -- Both the creature and the Wizard die in the same batch -> dies branch consults `pre`!
  let wizCond : Condition := .exists (.inZones .battlefield (.all #[.hasSubtype (.literal .wizard), .controlledBy .you]))
  let mixedCard := mkCreature "Mixed Raider" #["Human"] (triggers := #[
    TriggeredAbility.mkTrigger (.whenCond (.or .thisEnters .thisDies) wizCond) (Effect.gainLife 1)
  ])
  let gMix0 := quietGame (addPermanent (addPermanent afterDraw wizard p0 p0) mixedCard p0 p0)
  let mixObj := namedPerm gMix0 "Mixed Raider"
  let wizObj := namedPerm gMix0 "Partner Wizard"
  let gMixBatch := gMix0.withBatch (some testCause) fun g =>
    let g := g.moveToOwnerGraveyard (g.object! mixObj.id) "dies" (verb := some .destroy) (cause := some testCause)
    g.moveToOwnerGraveyard (g.object! wizObj.id) "dies" (verb := some .destroy) (cause := some testCause)
  let mixedLookBackOk :=
    gMixBatch.waitingTriggers.size == 1 &&
    gMixBatch.waitingTriggers[0]!.source.name == "Mixed Raider"
  noWizOk && entWizOk && atkWizOk && mixedLookBackOk

-- (b) Mixed-lookback `.or` with `oncePerBatch`, `perPlayerInBatch`, and `perSourceInBatch`
-- shares batch-grouping dedup across Pass A (`pre`) and Pass B (`post`).
#guard
  let onceWatcher := mustParse
    "Cycle Watcher\n{2}{G}\nEnchantment\nWhenever one or more creatures enter or die, you gain 1 life."
  let bearA := mkCreature "Dying Bear" #["Bear"]
  let bearB := mkCreature "Entering Bear" #["Bear"]
  let g0 := quietGame (addPermanent (addPermanent afterDraw onceWatcher p0 p0) bearA p0 p0)
  let (g1, handB) := addToZone g0 bearB p0 (.hand p0) (some p0)
  let bearAObj := namedPerm g1 "Dying Bear"
  let gOnce := g1.withBatch (some testCause) fun g =>
    let g := g.moveToOwnerGraveyard (g.object! bearAObj.id) "dies" (verb := some .destroy) (cause := some testCause)
    (g.putOntoBattlefield handB.id p0).1
  let onceOk := gOnce.waitingTriggers.size == 1 && gOnce.waitingTriggers[0]!.source.name == "Cycle Watcher"
  -- `perPlayerInBatch` across mixed-lookback `.or`: p0 has both a death and an enter,
  -- p1 has an enter -> fires once for p0 and once for p1 (total 2, not 3).
  let perPlayerWatcher := mkEnchantment "Per Player Mixed" #[
    TriggeredAbility.mkTrigger
      (.or (.permanentDies (.hasType .creature)) (.permanentEnters (.hasType .creature)))
      (Effect.gainLife 1)
      (grouping := .perPlayerInBatch)
  ]
  let bearC := mkCreature "P1 Entering Bear" #["Bear"]
  let gp0 := quietGame (addPermanent (addPermanent afterDraw perPlayerWatcher p0 p0) bearA p0 p0)
  let (gp1, handB2) := addToZone gp0 bearB p0 (.hand p0) (some p0)
  let (gp2, handC) := addToZone gp1 bearC p1 (.hand p1) (some p1)
  let bearA2 := namedPerm gp2 "Dying Bear"
  let gPerPlayer := gp2.withBatch (some testCause) fun g =>
    let g := g.moveToOwnerGraveyard (g.object! bearA2.id) "dies" (verb := some .destroy) (cause := some testCause)
    let g := (g.putOntoBattlefield handB2.id p0).1
    (g.putOntoBattlefield handC.id p1).1
  let perPlayerOk := gPerPlayer.waitingTriggers.size == 2
  -- `perSourceInBatch` across mixed-lookback `.or`: same creature loses control (`pre`)
  -- and becomes tapped (`post`) in one batch -> fires once (not twice).
  let perSrcWatcher := mkEnchantment "Per Source Mixed" #[
    TriggeredAbility.mkTrigger
      (.or (.controlLost (.hasType .creature) .you) (.becomesTapped (.hasType .creature)))
      (Effect.gainLife 1)
      (grouping := .perSourceInBatch)
  ]
  let gs0 := quietGame (addPermanent (addPermanent afterDraw perSrcWatcher p0 p0) bearA p0 p0)
  let sBear := namedPerm gs0 "Dying Bear"
  let gPerSrc := gs0.withBatch (some testCause) fun g =>
    let g := g.createEffect (.layered (.objects #[sBear.id]) (.control p1) .indefinite) (cause := some testCause)
    g.becomeTapped (g.object! sBear.id) (cause := some testCause)
  let perSrcOk := gPerSrc.waitingTriggers.size == 1
  onceOk && perPlayerOk && perSrcOk

-- (c) Self-spell `"When this spell is countered, draw a card."` parses with
-- `activeZones := #[.stack]` and fires on the CR 603.10e look-back pass when countered.
#guard
  let selfCounterSpell := mustParse
    "Unstoppable Insight\n{2}{U}\nSorcery\nDraw two cards.\nWhen this spell is countered, draw a card."
  let (g0, spObj) := addToZone (quietGame afterDraw) selfCounterSpell p0 .stack (some p0)
  let g1 := g0.putStackEntry p0 spObj.id
  let (gCountered, _) := g1.move spObj.id (.graveyard p0) none (verb := some .counter) (actor := some p1) (cause := some testCause)
  gCountered.waitingTriggers.size == 1 &&
    gCountered.waitingTriggers[0]!.source.name == "Unstoppable Insight" &&
    gCountered.waitingTriggers[0]!.pattern == .spellCountered (.sameAs .this)

-- (d) `.controlLost` uses a non-colliding per-object synthetic `eventIdx`, so a death
-- at batch index 0 never suppresses a simultaneous control loss (and vice versa), while
-- two `.controlLost` disjuncts matching the same permanent still deduplicate (CR 603.2c).
#guard
  let dieOrStealWatcher := mkEnchantment "Die Or Steal" #[
    TriggeredAbility.mkTrigger
      (.or (.permanentDies (.hasType .creature)) (.controlLost (.hasType .creature) .you))
      (Effect.gainLife 1)
  ]
  let victimA := mkCreature "Victim A" #["Bear"]
  let stolenB := mkCreature "Stolen B" #["Bear"]
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw dieOrStealWatcher p0 p0) victimA p0 p0) stolenB p0 p0)
  let objA := namedPerm g0 "Victim A"
  let objB := namedPerm g0 "Stolen B"
  let gBoth := g0.withBatch (some testCause) fun g =>
    let g := g.moveToOwnerGraveyard (g.object! objA.id) "dies" (verb := some .destroy) (cause := some testCause)
    g.createEffect (.layered (.objects #[objB.id]) (.control p1) .indefinite) (cause := some testCause)
  let noCollisionOk := gBoth.waitingTriggers.size == 2
  -- Two `.controlLost` disjuncts matching one artifact creature -> 1 trigger (CR 603.2c);
  -- two separate creatures stolen -> 2 triggers.
  let artOrCreaSteal := mkEnchantment "Steal Watcher" #[
    TriggeredAbility.mkTrigger
      (.or (.controlLost (.hasType .creature) .you) (.controlLost (.hasType .artifact) .you))
      (Effect.gainLife 1)
  ]
  let artCrea : CardDef := {
    name := "Clockwork Bear", types := #[.artifact, .creature], power := some (.fixed 2), toughness := some (.fixed 2)
  }
  let gs0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw artOrCreaSteal p0 p0) artCrea p0 p0) stolenB p0 p0)
  let objArt := namedPerm gs0 "Clockwork Bear"
  let objB2 := namedPerm gs0 "Stolen B"
  let gOne := gs0.createEffect (.layered (.objects #[objArt.id]) (.control p1) .indefinite) (cause := some testCause)
  let oneDedupOk := gOne.waitingTriggers.size == 1
  let gTwo := gs0.withBatch (some testCause) fun g =>
    let g := g.createEffect (.layered (.objects #[objArt.id]) (.control p1) .indefinite) (cause := some testCause)
    g.createEffect (.layered (.objects #[objB2.id]) (.control p1) .indefinite) (cause := some testCause)
  let twoDistinctOk := gTwo.waitingTriggers.size == 2
  noCollisionOk && oneDedupOk && twoDistinctOk

-- (e) `GameEvent.matchesTriggerPattern` enforces `castSpell` stateful constraints and
-- `.activateAbility` loyalty `minRemoved` instead of silently ignoring them.
#guard
  let spSnap : EventObject := {
    id := some ⟨42⟩, owner := p0, controller := some p0, zone := .stack
    name := "Test Bolt", types := #[.instant]
  }
  let castEv := GameEvent.spellCast 1 p0 spSnap (.hand p0) (cause := testCause)
  let secondSpellOk :=
    !castEv.matchesTriggerPattern p0 none .youCastSecondSpell &&
    !castEv.matchesTriggerPattern p0 none .youCastSecondSpell (castOrdinal? := some 1) &&
    castEv.matchesTriggerPattern p0 none .youCastSecondSpell (castOrdinal? := some 2)
  let treasurePat := TriggerPattern.castSpell .you .anyObject (manaSpent? := some .fromTreasure)
  let manaSpentOk :=
    !castEv.matchesTriggerPattern p0 none treasurePat &&
    castEv.matchesTriggerPattern p0 none treasurePat (manaSpentOk? := some true)
  let targetPat := TriggerPattern.castSpell .you .anyObject (targets? := some (.player .opponent))
  let targetsOk :=
    !castEv.matchesTriggerPattern p0 none targetPat &&
    castEv.matchesTriggerPattern p0 none targetPat (targetsOk? := some true)
  let pwSnap : EventObject := {
    id := some ⟨99⟩, owner := p0, controller := some p0, zone := .battlefield
    name := "Test Walker", types := #[.planeswalker]
  }
  let plusOneEv := GameEvent.abilityActivated 1 ⟨100⟩ pwSnap p0 (.nonMana (some 1) false false false) (cause := testCause)
  let minusTwoEv := GameEvent.abilityActivated 1 ⟨101⟩ pwSnap p0 (.nonMana (some (-2)) false false false) (cause := testCause)
  let minusThreeEv := GameEvent.abilityActivated 1 ⟨102⟩ pwSnap p0 (.nonMana (some (-3)) false false false) (cause := testCause)
  let rem3Pat := TriggerPattern.activateAbility .you .anyObject (.loyalty 3)
  let rem0Pat := TriggerPattern.activateAbility .you .anyObject (.loyalty 0)
  let loyaltyOk :=
    !plusOneEv.matchesTriggerPattern p0 none rem3Pat &&
    !minusTwoEv.matchesTriggerPattern p0 none rem3Pat &&
    minusThreeEv.matchesTriggerPattern p0 none rem3Pat &&
    plusOneEv.matchesTriggerPattern p0 none rem0Pat
  secondSpellOk && manaSpentOk && targetsOk && loyaltyOk

-- (f) Shared-event `.perPlayerInBatch` and `.perSourceInBatch` `.or` dedup:
-- one `DamageEvent.dealt` with packets for two different players (or two different sources)
-- across two `.or` disjuncts queues BOTH groups, while a duplicate packet for the same
-- player/source across disjuncts still deduplicates.
#guard
  let combatMirror := mustParse
    "Combat Mirror\n{2}{R}\nEnchantment\nWhenever one or more creatures you control deal combat damage to a player and whenever one or more creatures an opponent controls deal combat damage to a player, you gain 1 life."
  let myAtt := mkCreature "My Attacker" #["Human"]
  let oppAtt := mkCreature "Opp Attacker" #["Goblin"]
  let g0 := quietGame (addPermanent (addPermanent (addPermanent afterDraw combatMirror p0 p0) myAtt p0 p0) oppAtt p1 p1)
  let myObj := namedPerm g0 "My Attacker"
  let oppObj := namedPerm g0 "Opp Attacker"
  -- Single `.dealt` event: my creature hits p1, opp creature hits p0 (2 distinct players)
  -- AND opp creature also hits p1 (same player p1 across second disjunct -> deduped):
  let pkts : Array DamagePacket := #[
    { source := g0.snapshot myObj, recipient := .player p1, amount := 2, combat := true },
    { source := g0.snapshot oppObj, recipient := .player p0, amount := 2, combat := true },
    { source := g0.snapshot oppObj, recipient := .player p1, amount := 1, combat := true }
  ]
  let gDmg := g0.record (GameEvent.rules g0.turnNumber (.damage (.dealt pkts)) testCause)
  let perPlayerSharedEvOk := gDmg.waitingTriggers.size == 2
  -- `.perSourceInBatch` on one `.dealt` event hitting a Goblin and an Elf (2 distinct
  -- recipients across two disjuncts) vs. a Goblin Elf matching both disjuncts (1 trigger):
  let srcOrWatcher := mkEnchantment "Goblin Or Elf Hurt" #[
    TriggeredAbility.mkTrigger
      (.or
        (.damageDealt .anyObject (.object { zones := .battlefield, pred := .hasSubtype (.literal .goblin) }))
        (.damageDealt .anyObject (.object { zones := .battlefield, pred := .hasSubtype (.literal .elf) })))
      (Effect.gainLife 1)
      (grouping := .perSourceInBatch)
  ]
  let gob := mkCreature "Test Gob" #["Goblin"]
  let elf := mkCreature "Test Elf" #["Elf"]
  let gobElf := mkCreature "Hybrid GobElf" #["Goblin", "Elf"]
  let gs0 := quietGame (addPermanent (addPermanent (addPermanent (addPermanent afterDraw srcOrWatcher p0 p0) gob p0 p0) elf p0 p0) gobElf p0 p0)
  let gobObj := namedPerm gs0 "Test Gob"
  let elfObj := namedPerm gs0 "Test Elf"
  let hybObj := namedPerm gs0 "Hybrid GobElf"
  let pktsTwo : Array DamagePacket := #[
    { source := gs0.snapshot gobObj, recipient := .permanent (gs0.snapshot gobObj), amount := 1, combat := false },
    { source := gs0.snapshot gobObj, recipient := .permanent (gs0.snapshot elfObj), amount := 1, combat := false }
  ]
  let gTwoRecip := gs0.record (GameEvent.rules gs0.turnNumber (.damage (.dealt pktsTwo)) testCause)
  let pktsHyb : Array DamagePacket := #[
    { source := gs0.snapshot gobObj, recipient := .permanent (gs0.snapshot hybObj), amount := 1, combat := false }
  ]
  let gHyb := gs0.record (GameEvent.rules gs0.turnNumber (.damage (.dealt pktsHyb)) testCause)
  perPlayerSharedEvOk && gTwoRecip.waitingTriggers.size == 2 && gHyb.waitingTriggers.size == 1

-- (g) Runtime behavior of split heterogeneous `"and whenever"` triggers and uniform `.stack`
-- candidate collection for stack-active triggers.
#guard
  let hetGroup := mustParse
    "Split Group\n{2}{G}\nEnchantment\nWhenever a creature enters and whenever one or more creatures die, you gain 1 life."
  let bear1 := mkCreature "Bear One" #["Bear"]
  let bear2 := mkCreature "Bear Two" #["Bear"]
  let g0 := quietGame (addPermanent afterDraw hetGroup p0 p0)
  let (g1, h1) := addToZone g0 bear1 p0 (.hand p0) (some p0)
  let (g2, h2) := addToZone g1 bear2 p0 (.hand p0) (some p0)
  -- Two creatures enter in one batch -> `perOccurrence` triggers TWICE:
  let gTwoEnter := g2.withBatch (some testCause) fun g =>
    let (g, _) := g.putOntoBattlefield h1.id p0
    (g.putOntoBattlefield h2.id p0).1
  let twoEnterOk := gTwoEnter.waitingTriggers.size == 2
  -- Two creatures die in one batch -> `oncePerBatch` triggers ONCE:
  let gTwoDie := (quietGame gTwoEnter).withBatch (some testCause) fun g =>
    let o1 := namedPerm g "Bear One"
    let o2 := namedPerm g "Bear Two"
    let g := g.moveToOwnerGraveyard o1 "dies" (verb := some .destroy) (cause := some testCause)
    g.moveToOwnerGraveyard o2 "dies" (verb := some .destroy) (cause := some testCause)
  let twoDieOk := gTwoDie.waitingTriggers.size == 1
  -- Heterogeneous limit: `"Whenever a creature dies and whenever you draw your second card each turn, ..."`
  let hetLimit := mustParse
    "Split Limit\n{2}{U}\nEnchantment\nWhenever a creature dies and whenever you draw your second card each turn, you gain 1 life."
  let gl0 := quietGame (addPermanent afterDraw hetLimit p0 p0)
  let cardSnap : EventObject := { owner := p0, zone := .hand p0, name := "Drawn" }
  let draw1Ev := GameEvent.moved gl0.turnNumber cardSnap (.library p0) (.hand p0)
    (verb := some (.draw 1 true)) (actor := some p0) (cause := testCause)
  let draw2Ev := GameEvent.moved gl0.turnNumber cardSnap (.library p0) (.hand p0)
    (verb := some (.draw 2 false)) (actor := some p0) (cause := testCause)
  let draw1Ok := (gl0.record draw1Ev).waitingTriggers.isEmpty
  let draw2Ok := (gl0.record draw2Ev).waitingTriggers.size == 1
  -- Stack-active trigger (not cast/countered) on a spell on the stack fires on draw:
  let stackWatcher : CardDef := {
    name := "Stack Draw Watcher", types := #[.instant], manaCost := ManaCost.ofColor .blue
    triggeredAbilities := #[
      { TriggeredAbility.mkTrigger (.drawCard .you) (Effect.gainLife 1) with activeZones := #[.stack] }
    ]
  }
  let (gs0, spObj) := addToZone (quietGame afterDraw) stackWatcher p0 .stack (some p0)
  let gs1 := gs0.putStackEntry p0 spObj.id
  let stackDrawOk := (gs1.record draw1Ev).waitingTriggers.size == 1
  twoEnterOk && twoDieOk && draw1Ok && draw2Ok && stackDrawOk

end Mtg.Engine.Tests.TriggeredAbilitiesSuite
