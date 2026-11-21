import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.RealityFractureCommander

/-!
# Phase 5 Unified `ActivatedAbility` & CR 605.1a / 305.6–7 Mana Ability Runtime Tests

Comprehensive gameplay `#guard` regression suite for Phase 5 of
`ABILITY_ALIGNMENT_PLAN.md` (anchored to the 25 September 2026 CR):
1. CR 305.6 intrinsic basic-land mana synthesis (including Layer 3 text change
   `Mountain → Island`, Yavimaya-style Layer 4 `.addDedup` preserving rules text,
   and non-land basic-subtype negative check).
2. CR 305.7 subtype-setting ability removal (Blood Moon-style Layer 4 `.set`
   stripping rules text while preserving non-land types/supertypes, Chromatic
   Lantern Layer 6 grant surviving after Layer 4 `.set`, and Layer 6
   `AbilityRemoval.all` stripping even CR 305.6 intrinsic mana).
3. CR 605.1a all four mana-ability criteria at runtime:
   (a) targeted mana-producing ability uses the stack;
   (b) non-mana ability uses the stack;
   (c) loyalty mana-producing ability uses the stack (CR 606.2 / 606.3);
   (d) library-moving mana-producing ability (draw/exile-from-library) uses the stack;
   (e) valid CR 605.1a mana ability resolves without the stack, even under Split Second.
4. Per-ability activation limits & mechanics:
   - Per-ability Boast (CR 702.142a): two boast abilities on the same creature each
     have their own once-per-turn cap;
   - Per-ability Exhaust (CR 702.177a): two exhaust abilities on the same permanent
     each have their own once-per-lifetime cap;
   - General `turnLimit? := some 2` ("no more than two times each turn");
   - Power-up (CR 702.193a–b) entered-this-turn reduction + Wonder Man extra activation.
5. Extended `SpellRiderSpec` (`.cantBeCountered`, `.gainsHaste`,
   `.entersWithPlusOneCounters n`) in gameplay, including stacking multiple
   counter riders and combining with printed `entersWithPlusOneCounters`.
6. Compositional `ActivationCostReduction` (static & target-dependent) and
   `ActivatedAbility.condition?` (CR 602.2b / 602.5b).
7. CR 106.7 `Reflecting Pool` (`includeColorless := true`) vs. `Exotic Orchard`
   (`includeColorless := false`), cycle safety with two `Reflecting Pool`s,
   and `Mox Amber`.
-/

namespace Mtg.Engine.Tests.ActivatedManaSuite

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

private def p0 : PlayerId := ⟨0⟩
private def p1 : PlayerId := ⟨1⟩

private def testCause : EventCause := .oneShotEffect none none

private def namedPerm (g : Game) (name : String) : GameObject :=
  match g.battlefield.find? (·.name == name) with
  | some o => o
  | none => panic! s!"missing permanent {name}"

private def mustOk (r : Except String Game) : Game :=
  match r with
  | .ok g => g
  | .error e => panic! e

private def passBothPlayers (g : Game) : Game :=
  let g1 := mustOk (g.apply g.priority .pass)
  mustOk (g1.apply g1.priority .pass)

/-! ### 1. CR 305.6 Intrinsic Basic-Land Mana, Layer 3 Text Change & Layer 4 `.addDedup` -/

-- Every basic land has empty printed `activatedAbilities`, yet gets its exact CR 305.6
-- intrinsic `{T}: Add {M}` ability from Layer 4 basic land subtypes.
#guard
  [(plains, Color.white), (island, Color.blue), (swamp, Color.black),
   (mountain, Color.red), (forest, Color.green)].all fun (card, col) =>
    card.activatedAbilities.isEmpty &&
    let g := addPermanent afterDraw card p0 p0
    let o := namedPerm g card.name
    let abs := g.activatedAbilitiesOf o
    let defs := g.manaAbilityDefs o
    abs == #[ActivatedAbility.intrinsicBasicLandMana col] &&
    defs.size == 1 &&
    g.manaAbilitiesOf o == #[.colored col]

-- Layer 4 `.addDedup` adding `Forest` (Yavimaya style) to a nonbasic land preserves
-- its printed rules text AND synthesizes CR 305.6 `{T}: Add {G}`.
#guard
  let utilityLand : CardDef := {
    name := "P5 Utility Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaSimple .colorless]
  }
  let g0 := addPermanent afterDraw utilityLand p0 p0
  let lid := (namedPerm g0 utilityLand.name).id
  let g1 := g0.createEffect
    (.layered (.objects #[lid]) (.types .addDedup #[] #[.forest] #[]) .indefinite)
    (cause := some testCause)
  let o := g1.object! lid
  let l4 := g1.evalLayer4Full o
  let mana := g1.manaAbilitiesOf o
  !l4.strippedRulesTextByBasicLandSet &&
    l4.subtypes.contains .forest &&
    mana.contains .colorless &&
    mana.contains (.colored .green)

-- Layer 3 `TextChange.replaceCreatureType .mountain .island` on a Mountain changes its
-- basic land subtype before Layer 4, so Layer 6 synthesizes `{T}: Add {U}` instead of `{R}`.
#guard
  let g0 := addPermanent afterDraw mountain p0 p0
  let mid := (namedPerm g0 "Mountain").id
  let g1 := g0.createEffect
    (.layered (.objects #[mid]) (.text (.replaceCreatureType .mountain .island)) .indefinite)
    (cause := some testCause)
  let o := g1.object! mid
  g1.hasSubtype o .island &&
    !g1.hasSubtype o .mountain &&
    g1.manaAbilitiesOf o == #[.colored .blue]

-- Non-land permanent with a basic land subtype does NOT receive CR 305.6 intrinsic mana.
#guard
  let notALand : CardDef := {
    name := "P5 Mountain Bear"
    types := #[.creature]
    subtypes := #["Mountain"]
    power := some 2
    toughness := some 2
  }
  let g := addPermanent afterDraw notALand p0 p0
  let o := namedPerm g notALand.name
  (g.activatedAbilitiesOf o).isEmpty && (g.manaAbilityDefs o).isEmpty

/-! ### 2. CR 305.7 Subtype-Setting Ability Removal & Layer-6 Grants/Removal -/

-- Blood Moon-style Layer 4 `.set` (`subtypes := #[.mountain]`, empty `types`) on a
-- legendary snow artifact land:
-- * strips printed activated & static rules text;
-- * preserves non-land card types (`.artifact`) and supertypes (`.legendary`, `.snow`);
-- * replaces land subtypes with `.mountain` and synthesizes CR 305.6 `{T}: Add {R}`.
#guard
  let richLand : CardDef := {
    name := "P5 Ancient Spire"
    supertypes := #[.legendary, .snow]
    types := #[.artifact, .land]
    subtypes := #["Locus"]
    activatedAbilities := #[
      ActivatedAbility.manaSimple .colorless,
      { cost := CostSpec.ofGeneric 1, effect := Effect.gainLife 1 }
    ]
    staticAbilities := #[.otherCreaturesGet #[.elf] 1 1]
  }
  let g0 := addPermanent afterDraw richLand p0 p0
  let lid := (namedPerm g0 richLand.name).id
  let g1 := g0.createEffect
    (.layered (.objects #[lid]) (.types .set #[] #[.mountain] #[]) .indefinite)
    (cause := some testCause)
  let o := g1.object! lid
  let l4 := g1.evalLayer4Full o
  l4.strippedRulesTextByBasicLandSet &&
    l4.types.contains .land &&
    l4.types.contains .artifact &&
    l4.supertypes.contains .legendary &&
    l4.supertypes.contains .snow &&
    l4.subtypes == #[.mountain] &&
    (g1.staticAbilities o).isEmpty &&
    g1.activatedAbilitiesOf o == #[ActivatedAbility.intrinsicBasicLandMana .red] &&
    g1.manaAbilitiesOf o == #[.colored .red]

-- Chromatic Lantern Layer-6 grant survives after Layer 4 CR 305.7 `.set` (`Mountain`):
-- the nonbasic land has both intrinsic `{T}: Add {R}` and Lantern's `{T}: Add any color`.
#guard
  let utilityLand : CardDef := {
    name := "P5 Moonlit Land"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaSimple .colorless]
  }
  let g0 := addPermanent (addPermanent afterDraw utilityLand p0 p0) chromaticLantern p0 p0
  let lid := (namedPerm g0 utilityLand.name).id
  let g1 := g0.createEffect
    (.layered (.objects #[lid]) (.types .set #[] #[.mountain] #[]) .indefinite)
    (cause := some testCause)
  let o := g1.object! lid
  let mana := g1.manaAbilitiesOf o
  !mana.contains .colorless &&
    mana.contains (.colored .red) &&
    mana.contains (.colored .blue) &&
    mana.contains (.colored .green) &&
    (g1.manaAbilityDefs o).size == 2

-- Layer 6 `AbilityRemoval.all` (`losesAbilitiesUntilEot`) strips CR 305.6 intrinsic basic-land mana!
#guard
  let g0 := addPermanent afterDraw mountain p0 p0
  let mid := (namedPerm g0 "Mountain").id
  let g1 := g0.createEffect (.losesAbilitiesUntilEot mid) (cause := some testCause)
  let o := g1.object! mid
  (g1.activatedAbilitiesOf o).isEmpty && (g1.manaAbilityDefs o).isEmpty &&
    (g1.manaAbilitiesOf o).isEmpty

/-! ### 3. CR 605.1a All Four Criteria at Runtime (25 September 2026) -/

-- (a) Criterion 1: Targeted mana-producing ability is NOT a mana ability; uses stack & resolves.
#guard
  let targetedMana : CardDef := {
    name := "P5 Deathrite Style"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.tapOnly
      effect := {
        targeting := .of TargetSpec.creature
        resolution := .addMana #[.colored .green]
        phrase := "Target creature gets nothing; add {G}"
      }
    }]
  }
  let g0 := addPermanent (addPermanent afterDraw targetedMana p0 p0) grizzlyBears p0 p0
  let src := namedPerm g0 targetedMana.name
  let bearId := (namedPerm g0 "Grizzly Bears").id
  let ab := src.printed.activatedAbilities[0]!
  let gAct := mustOk (g0.apply p0 (.activate src.id 0))
  let gTgt := mustOk (gAct.apply p0 (.target (.permanent bearId)))
  let gRes := passBothPlayers gTgt
  !ab.isManaAbility &&
    (g0.manaAbilityDefs src).isEmpty &&
    gTgt.stack.size == 1 &&
    (gTgt.player p0).manaPool.green == 0 &&
    gRes.stack.isEmpty &&
    (gRes.player p0).manaPool.green == 1

-- (b) Criterion 3: Loyalty mana-producing ability (`[+1]: Add {R}`) is NOT a mana ability;
-- uses stack, obeys CR 606.3 once-per-turn loyalty rule, and resolves adding `{R}`.
#guard
  let loyaltyMana : CardDef := {
    name := "P5 Mana Walker"
    types := #[.planeswalker]
    loyalty := some 3
    activatedAbilities := #[{
      cost := CostSpec.ofLoyalty (.plus 1)
      timing := .loyalty
      effect := Effect.addMana #[.colored .red]
    }]
  }
  let gHand := insertObject afterDraw loyaltyMana p0 (.hand p0)
  let (g0, _) := gHand.move (gHand.player p0).hand.back! .battlefield (some p0) (cause := some testCause)
  let pw := namedPerm g0 loyaltyMana.name
  let ab := pw.printed.activatedAbilities[0]!
  let gAct := mustOk (g0.apply p0 (.activate pw.id 0))
  let gRes := passBothPlayers gAct
  !ab.isManaAbility &&
    ab.isLoyaltyAbility &&
    (g0.manaAbilityDefs pw).isEmpty &&
    gAct.stack.size == 1 &&
    (gAct.player p0).manaPool.red == 0 &&
    gRes.stack.isEmpty &&
    (gRes.player p0).manaPool.red == 1 &&
    (gRes.object! pw.id).status.loyaltyCounters == 4 &&
    !(gRes.apply p0 (.activate pw.id 0)).isOk

-- (c) Criterion 4 (25 September 2026 CR 605.1a): Library-moving mana ability
-- (`{T}: Add {G}. Draw a card.`) is NOT a mana ability; uses stack & resolves both parts.
-- Likewise, an exile-from-library cost fails criterion 4 via cost.
#guard
  let sphereStyle : CardDef := {
    name := "P5 Draw Sphere"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.tapOnly
      effect := {
        resolution := .sequence [.addMana #[.colored .green], .draw 1]
        phrase := "Add {G}. Draw a card"
      }
    }]
  }
  let exileLibCostMana : ActivatedAbility :=
    ActivatedAbility.manaAbility (.fixedOne (.colored .green))
      (CostSpec.ofItems #[.tapSelf, .exile (.exact 1) { zones := #[.library], owner := .ofPlayer .you } (.filter .isCard)])
  let g0 := addPermanent afterDraw sphereStyle p0 p0
  let src := namedPerm g0 sphereStyle.name
  let ab := src.printed.activatedAbilities[0]!
  let handBefore := (g0.player p0).hand.size
  let gAct := mustOk (g0.apply p0 (.activate src.id 0))
  let gRes := passBothPlayers gAct
  !ab.isManaAbility &&
    !exileLibCostMana.isManaAbility &&
    (g0.manaAbilityDefs src).isEmpty &&
    gAct.stack.size == 1 &&
    (gAct.player p0).manaPool.green == 0 &&
    gRes.stack.isEmpty &&
    (gRes.player p0).manaPool.green == 1 &&
    (gRes.player p0).hand.size == handBefore + 1

-- (d) Positive CR 605.1a / 605.3b / 702.61a: Pure `{T}: Add {G}` resolves immediately
-- without using the stack even while a Split Second spell is on the stack, whereas a
-- library-moving `{T}: Add {G}. Draw a card.` is blocked by Split Second!
#guard
  let splitSpell : CardDef := {
    name := "P5 Sudden Spell"
    manaCost := ManaCost.ofColor .red
    types := #[.instant]
    keywords := #[Keyword.splitSecond]
    spellEffect := some (Effect.gainLife 1)
  }
  let pureRock : CardDef := {
    name := "P5 Pure Emerald"
    types := #[.artifact]
    activatedAbilities := #[ActivatedAbility.manaSimple (.colored .green)]
  }
  let drawRock : CardDef := {
    name := "P5 Draw Emerald"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.tapOnly
      effect := { resolution := .sequence [.addMana #[.colored .green], .draw 1], phrase := "Add {G}. Draw a card" }
    }]
  }
  let splitEnabler : CardDef := {
    name := "P5 Split Second Enabler"
    types := #[.enchantment]
    staticAbilities := #[.instantSorcerySplitSecond]
  }
  let g0 :=
    ((insertObject
      (addPermanent (addPermanent (addPermanent afterDraw splitEnabler p0 p0) pureRock p0 p0) drawRock p0 p0)
      splitSpell p0 (.hand p0)).addMana p0 (.colored .red) 1)
  let spellId := (g0.player p0).hand.back!
  let gCast := mustOk (mustOk (g0.apply p0 (.cast spellId)) |>.apply p0 .pay)
  let pureId := (namedPerm gCast pureRock.name).id
  let drawId := (namedPerm gCast drawRock.name).id
  let gMana := mustOk (gCast.apply p0 (.activateManaAbility pureId 0 #[.colored .green] #[]))
  let drawBlocked := !(gCast.apply p0 (.activate drawId 0)).isOk
  gCast.splitSecondOnStack &&
    gCast.stack.size == 1 &&
    gMana.stack.size == 1 &&
    (gMana.player p0).manaPool.green == 1 &&
    drawBlocked

/-! ### 4. Per-Ability Limits & Mechanics (Boast, Exhaust, General `turnLimit?`, Power-up) -/

-- CR 702.142a: Boast restricts each boast ability individually (`turnLimit? = some 1`
-- plus `condSourceAttackedThisTurn`). Two boast abilities on the same creature can each
-- be activated once in the turn it attacked, while neither can be activated twice or
-- without attacking.
#guard
  let doubleBoast : CardDef := {
    name := "P5 Twin Boaster"
    types := #[.creature]
    power := some 2
    toughness := some 2
    activatedAbilities := #[
      { cost := CostSpec.empty
        effect := Effect.gainLife 1
        turnLimit? := some 1
        condition? := some ActivatedAbility.condSourceAttackedThisTurn
        tag? := some .boast },
      { cost := CostSpec.empty
        effect := Effect.gainLife 2
        turnLimit? := some 1
        condition? := some ActivatedAbility.condSourceAttackedThisTurn
        tag? := some .boast }
    ]
  }
  let g0 := addPermanent afterDraw doubleBoast p0 p0
  let cid := (namedPerm g0 doubleBoast.name).id
  let blockedBeforeAttack := !(g0.apply p0 (.activate cid 0)).isOk
  let gAtk := g0.record (GameEvent.attacked g0.turnNumber p0 (g0.snapshot (g0.object! cid)) p1)
  let g1 := passBothPlayers (mustOk (gAtk.apply p0 (.activate cid 0)))
  let firstBlockedAgain := !(g1.apply p0 (.activate cid 0)).isOk
  let g2 := passBothPlayers (mustOk (g1.apply p0 (.activate cid 1)))
  let secondBlockedAgain := !(g2.apply p0 (.activate cid 1)).isOk
  blockedBeforeAttack &&
    firstBlockedAgain &&
    secondBlockedAgain &&
    (g2.player p0).life == 23

-- CR 702.177a: Two Exhaust abilities on the same permanent each have their own
-- once-per-lifetime cap (`lifetimeLimit? = some 1`).
#guard
  let doubleExhaust : CardDef := {
    name := "P5 Twin Exhaust"
    types := #[.artifact]
    activatedAbilities := #[
      { cost := CostSpec.empty
        effect := Effect.gainLife 1
        lifetimeLimit? := some 1
        tag? := some .exhaust },
      { cost := CostSpec.empty
        effect := Effect.gainLife 3
        lifetimeLimit? := some 1
        tag? := some .exhaust }
    ]
  }
  let g0 := addPermanent afterDraw doubleExhaust p0 p0
  let aid := (namedPerm g0 doubleExhaust.name).id
  let g1 := passBothPlayers (mustOk (g0.apply p0 (.activate aid 0)))
  let firstBlocked := !(g1.apply p0 (.activate aid 0)).isOk
  let g2 := passBothPlayers (mustOk (g1.apply p0 (.activate aid 1)))
  let secondBlocked := !(g2.apply p0 (.activate aid 1)).isOk
  firstBlocked && secondBlocked && (g2.player p0).life == 24

-- General `turnLimit? := some 2`: activates twice in a single turn and fails on the 3rd!
#guard
  let twicePerTurn : CardDef := {
    name := "P5 Twice Engine"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.empty
      effect := Effect.gainLife 1
      turnLimit? := some 2
    }]
  }
  let g0 := addPermanent afterDraw twicePerTurn p0 p0
  let aid := (namedPerm g0 twicePerTurn.name).id
  let g1 := passBothPlayers (mustOk (g0.apply p0 (.activate aid 0)))
  let g2 := passBothPlayers (mustOk (g1.apply p0 (.activate aid 0)))
  let thirdBlocked := !(g2.apply p0 (.activate aid 0)).isOk
  thirdBlocked && (g2.player p0).life == 22

-- CR 702.193a–b: Power-up entered-this-turn cost reduction + Wonder Man extra activation.
#guard
  let heroDef : CardDef := {
    name := "P5 Power Hero"
    manaCost := ManaCost.ofGenericAndColor 1 .blue
    types := #[.creature]
    power := some 2
    toughness := some 2
    activatedAbilities := #[{
      cost := CostSpec.ofMana (ManaCost.ofGenericAndColor 3 .blue)
      effect := Effect.gainLife 1
      lifetimeLimit? := some 1
      tag? := some .powerUp
    }]
  }
  let gHand := insertObject (addPermanent afterDraw wonderManHollywoodHero p0 p0) heroDef p0 (.hand p0)
  let hid := (gHand.player p0).hand.back!
  let (gEnt, _) := gHand.move hid .battlefield (some p0) (cause := some testCause)
  let hObj := namedPerm gEnt heroDef.name
  let ab := hObj.printed.activatedAbilities[0]!
  -- `{3}{U}` reduced by `{1}{U}` = `{2}` while entered this turn; Wonder Man allows 2 activations.
  let reducedCost := gEnt.activationManaCost p0 ab (some hObj)
  let gPool := gEnt.addMana p0 .colorless 4
  let g1 := passBothPlayers (mustOk (mustOk (gPool.apply p0 (.activate hObj.id 0)) |>.apply p0 .pay))
  let g2 := passBothPlayers (mustOk (mustOk (g1.apply p0 (.activate hObj.id 0)) |>.apply p0 .pay))
  let thirdBlocked := !(g2.apply p0 (.activate hObj.id 0)).isOk
  reducedCost == ManaCost.ofGeneric 2 &&
    gEnt.powerUpActivationLimit p0 == 2 &&
    thirdBlocked &&
    (g2.player p0).life == 22

/-! ### 5. Extended `SpellRiderSpec` (`.cantBeCountered`, `.gainsHaste`, `.entersWithPlusOneCounters`) -/

-- `.gainsHaste` rider spent to cast a creature spell grants indefinite haste on ETB
-- (clearing summoning sickness immediately).
#guard
  let hasteLand : CardDef := {
    name := "P5 Hall of Haste"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .green)) (riders := #[.gainsHaste])
    ]
  }
  let g0 :=
    (insertObject (addPermanent afterDraw hasteLand p0 p0) grizzlyBears p0 (.hand p0)).addMana
      p0 .colorless 1
  let lid := (namedPerm g0 hasteLand.name).id
  let bearCardId := (g0.player p0).hand.back!
  let g1 := mustOk (g0.apply p0 (.activateManaAbility lid 0 #[.colored .green] #[]))
  let gCast := mustOk (mustOk (g1.apply p0 (.cast bearCardId)) |>.apply p0 .pay)
  let gRes := passBothPlayers gCast
  let bear := namedPerm gRes "Grizzly Bears"
  gRes.hasHaste bear && !gRes.hasSummoningSickness bear

-- `.entersWithPlusOneCounters n` riders stack across multiple mana units AND stack with
-- a creature's own printed `entersWithPlusOneCounters`!
#guard
  let counterLand1 : CardDef := {
    name := "P5 Forge One"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne (.colored .green))
        (riders := #[.entersWithPlusOneCounters 1])
    ]
  }
  let counterLand2 : CardDef := {
    name := "P5 Forge Two"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility (.fixedOne .colorless)
        (riders := #[.entersWithPlusOneCounters 2])
    ]
  }
  let alreadyBigBear : CardDef := {
    name := "P5 Counter Bear"
    manaCost := ManaCost.ofGenericAndColor 1 .green
    types := #[.creature]
    power := some 2
    toughness := some 2
    staticAbilities := #[.entersWithPlusOneCounters 1]
  }
  let g0 :=
    insertObject
      (addPermanent (addPermanent afterDraw counterLand1 p0 p0) counterLand2 p0 p0)
      alreadyBigBear p0 (.hand p0)
  let l1 := (namedPerm g0 counterLand1.name).id
  let l2 := (namedPerm g0 counterLand2.name).id
  let cid := (g0.player p0).hand.back!
  let g1 := mustOk (g0.apply p0 (.activateManaAbility l1 0 #[.colored .green] #[]))
  let g2 := mustOk (g1.apply p0 (.activateManaAbility l2 0 #[.colorless] #[]))
  let gCast := mustOk (mustOk (g2.apply p0 (.cast cid)) |>.apply p0 .pay)
  let gRes := passBothPlayers gCast
  let bear := namedPerm gRes alreadyBigBear.name
  -- 1 printed + 1 from Forge One + 2 from Forge Two = 4 counters -> 6/6!
  bear.status.plusOnePlusOne == 4 &&
    gRes.power bear == 6 &&
    gRes.toughness bear == 6

-- `.cantBeCountered` rider on `Delighted Halfling` makes the cast legendary spell uncounterable.
#guard
  let legBear : CardDef := {
    name := "P5 Legendary Bear"
    manaCost := ManaCost.ofColor .green
    supertypes := #[.legendary]
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  let g0 :=
    insertObject (addPermanent afterDraw delightedHalfling p0 p0) legBear p0 (.hand p0)
  let halflingId := (namedPerm g0 delightedHalfling.name).id
  let cid := (g0.player p0).hand.back!
  -- Def 1 on Delighted Halfling is `{T}: Add one mana of any color` (legendary-only + cantBeCountered).
  let g1 := mustOk (g0.apply p0 (.activateManaAbility halflingId 1 #[.colored .green] #[]))
  let gCast := mustOk (mustOk (g1.apply p0 (.cast cid)) |>.apply p0 .pay)
  let spellId := gCast.stack[0]!.objectId
  GameEvent.riderManaSpentOn gCast.events spellId .cantBeCountered &&
    gCast.uncounterableThisCast (gCast.object! spellId)

/-! ### 6. Compositional `ActivationCostReduction` & `ActivatedAbility.condition?` -/

-- Static (`ifControlLegendary`, `perEquipment`) and target-dependent
-- (`ifTargetPowerAtMost`, `perPlusOneOnTarget`) declarative cost reductions.
#guard
  let equipCard : CardDef := {
    name := "P5 Test Sword"
    types := #[.artifact]
    subtypes := #["Equipment"]
  }
  let legCard : CardDef := {
    name := "P5 Legend"
    supertypes := #[.legendary]
    types := #[.creature]
    power := some 4
    toughness := some 4
  }
  let abStatic : ActivatedAbility := {
    cost := CostSpec.ofGeneric 5
    effect := Effect.gainLife 1
    costReductions := #[
      ActivationCostReduction.ifControlLegendary 2,
      ActivationCostReduction.perEquipment 1
    ]
  }
  let abTarget : ActivatedAbility := {
    cost := CostSpec.ofGeneric 5
    effect := { targeting := .of TargetSpec.creature, resolution := .gainLife 1 }
    costReductions := #[
      ActivationCostReduction.ifTargetPowerAtMost 2 2,
      ActivationCostReduction.perPlusOneOnTarget
    ]
  }
  let gBase := addPermanent afterDraw grizzlyBears p0 p0
  let bearId := (namedPerm gBase "Grizzly Bears").id
  let gRich :=
    (addPermanent (addPermanent (addPermanent gBase equipCard p0 p0) equipCard p0 p0) legCard p0 p0)
      |>.recordPutCounters bearId .plusOnePlusOne 1 (some p0) (cause := some testCause)
  let legId := (namedPerm gRich legCard.name).id
  -- Static reductions: base = {5}, with 1 legend (-2) + 2 Equipment (-2) = {1}.
  gBase.activationManaCost p0 abStatic none == ManaCost.ofGeneric 5 &&
    gRich.activationManaCost p0 abStatic none == ManaCost.ofGeneric 1 &&
    -- Target reductions: before target = {5}; targeting 3/3 Bear (with +1/+1) -> power 3 > 2,
    -- only perPlusOneOnTarget (-1) -> {4}; targeting 2/2 Bear (base) -> ifTargetPowerAtMost (-2) -> {3};
    -- targeting 4/4 Legend (0 counters) -> {5}.
    gRich.activationManaCost p0 abTarget none == ManaCost.ofGeneric 5 &&
    gRich.activationManaCost p0 abTarget none (targets := #[.permanent bearId]) == ManaCost.ofGeneric 4 &&
    gBase.activationManaCost p0 abTarget none (targets := #[.permanent bearId]) == ManaCost.ofGeneric 3 &&
    gRich.activationManaCost p0 abTarget none (targets := #[.permanent legId]) == ManaCost.ofGeneric 5

-- Compositional `ActivatedAbility.condition?` (`condEnteredThisTurnOrControlBasicLand`).
#guard
  let condLand : CardDef := {
    name := "P5 Cond Dual"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaAbility
        (.oneOf (.explicit #[.colored .blue, .colored .red]) (.const 1))
        (condition? := some ActivatedAbility.condEnteredThisTurnOrControlBasicLand)
    ]
  }
  -- Placed directly on battlefield (not entered this turn) with NO basic land -> unusable!
  let gNoBasic := addPermanent afterDraw condLand p0 p0
  let cid := (namedPerm gNoBasic condLand.name).id
  let unusableWithoutBasic := (gNoBasic.manaAbilitiesOf (gNoBasic.object! cid)).isEmpty
  -- Adding a basic Forest satisfies the condition -> produces `{U}` and `{R}`!
  let gWithBasic := addPermanent gNoBasic forest p0 p0
  let usableWithBasic :=
    let ms := gWithBasic.manaAbilitiesOf (gWithBasic.object! cid)
    ms.contains (.colored .blue) && ms.contains (.colored .red)
  -- Entering this turn without any basic land ALSO satisfies the condition!
  let gHand := insertObject afterDraw condLand p0 (.hand p0)
  let hid := (gHand.player p0).hand.back!
  let (gEntered, _) := gHand.move hid .battlefield (some p0) (cause := some testCause)
  let enteredId := (namedPerm gEntered condLand.name).id
  let usableWhenEntered :=
    let ms := gEntered.manaAbilitiesOf (gEntered.object! enteredId)
    ms.contains (.colored .blue) && ms.contains (.colored .red)
  unusableWithoutBasic && usableWithBasic && usableWhenEntered

/-! ### 7. CR 106.7 `Reflecting Pool`, `Exotic Orchard`, Cycle Safety & `Mox Amber` -/

-- Two Reflecting Pools alone do not recurse infinitely and produce no mana;
-- alongside a colorless land, Reflecting Pool produces `{C}` (`includeColorless := true`),
-- whereas Exotic Orchard (`includeColorless := false`) ignores colorless and produces `{G}`
-- only once an opponent controls a Forest.
#guard
  let wastesLand : CardDef := {
    name := "P5 Wastes"
    types := #[.land]
    activatedAbilities := #[ActivatedAbility.manaSimple .colorless]
  }
  let gTwoPools :=
    addPermanent (addPermanent afterDraw reflectingPool p0 p0) reflectingPool p0 p0
  let pool0 := (gTwoPools.permanentsOf p0)[0]!
  let emptyPoolsOk := (gTwoPools.manaAbilityDefs pool0)[0]!.output.producibleTypes.isEmpty
  let gPoolWastes := addPermanent gTwoPools wastesLand p0 p0
  let poolWithWastes := (gPoolWastes.permanentsOf p0).find? (·.name == reflectingPool.name) |>.get!
  let poolProducesColorless :=
    (gPoolWastes.manaAbilityDefs poolWithWastes)[0]!.output.producibleTypes == #[.colorless]
  let gOrchardWastes :=
    addPermanent (addPermanent afterDraw exoticOrchard p0 p0) wastesLand p1 p1
  let orch0 := namedPerm gOrchardWastes exoticOrchard.name
  let orchardIgnoresColorless :=
    (gOrchardWastes.manaAbilityDefs orch0)[0]!.output.producibleTypes.isEmpty
  let gOrchardForest := addPermanent gOrchardWastes forest p1 p1
  let orch1 := namedPerm gOrchardForest exoticOrchard.name
  let orchardProducesGreen :=
    (gOrchardForest.manaAbilityDefs orch1)[0]!.output.producibleTypes == #[.colored .green]
  emptyPoolsOk && poolProducesColorless && orchardIgnoresColorless && orchardProducesGreen

-- `Mox Amber` produces colors only among legendary creatures and planeswalkers you control.
#guard
  let redLegend : CardDef := {
    name := "P5 Red Legend"
    manaCost := ManaCost.ofColor .red
    supertypes := #[.legendary]
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  let gEmpty := addPermanent afterDraw moxAmber p0 p0
  let m0 := namedPerm gEmpty moxAmber.name
  let emptyOk := (gEmpty.manaAbilityDefs m0)[0]!.output.producibleTypes.isEmpty
  let gNonLeg := addPermanent gEmpty grizzlyBears p0 p0
  let m1 := namedPerm gNonLeg moxAmber.name
  let nonLegStillEmpty := (gNonLeg.manaAbilityDefs m1)[0]!.output.producibleTypes.isEmpty
  let gWithLeg := addPermanent gNonLeg redLegend p0 p0
  let m2 := namedPerm gWithLeg moxAmber.name
  let withLegRed := (gWithLeg.manaAbilityDefs m2)[0]!.output.producibleTypes == #[.colored .red]
  emptyOk && nonLegStillEmpty && withLegRed

/-! ### 8. CR 305.7 Layer-4 Overwrites & Full CR 605.1a Modal / Zone / Extra-Cost Mana Abilities -/

-- CR 305.7 / 613.7: Later `.set` to a non-basic land subtype (`Locus`) clears
-- `strippedRulesTextByBasicLandSet` and restores printed abilities; mixed
-- `.set #[.mountain, .locus]` does NOT strip printed abilities; Blood Moon
-- followed by Yavimaya `.addDedup #[.forest]` preserves stripping and grants
-- both `{R}` and `{G}`; removing `.land` clears stripping.
#guard
  let utilityLand : CardDef := {
    name := "P5 Overwrite Land"
    types := #[.land]
    activatedAbilities := #[
      ActivatedAbility.manaSimple .colorless,
      { cost := CostSpec.ofGeneric 1, effect := Effect.gainLife 1 }
    ]
    staticAbilities := #[.otherCreaturesGet #[.elf] 1 1]
  }
  let g0 := addPermanent afterDraw utilityLand p0 p0
  let lid := (namedPerm g0 utilityLand.name).id
  -- Blood Moon (ts 1) then Locus-setter (ts 2): final subtype is Locus, printed abilities intact.
  let gMoon := g0.createEffect
    (.layered (.objects #[lid]) (.types .set #[] #[.mountain] #[]) .indefinite)
    (cause := some testCause)
  let gLocus := gMoon.createEffect
    (.layered (.objects #[lid]) (.types .set #[] #[.locus] #[]) .indefinite)
    (cause := some testCause)
  let oLocus := gLocus.object! lid
  let l4Locus := gLocus.evalLayer4Full oLocus
  let locusRestoresPrinted :=
    !l4Locus.strippedRulesTextByBasicLandSet &&
      l4Locus.subtypes == #[.locus] &&
      !(gLocus.staticAbilities oLocus).isEmpty &&
      gLocus.manaAbilitiesOf oLocus == #[.colorless]
  -- Mixed basic + non-basic `.set #[.mountain, .locus]` does NOT strip printed abilities.
  let gMixed := g0.createEffect
    (.layered (.objects #[lid]) (.types .set #[] #[.mountain, .locus] #[]) .indefinite)
    (cause := some testCause)
  let oMixed := gMixed.object! lid
  let l4Mixed := gMixed.evalLayer4Full oMixed
  let mixedKeepsPrinted :=
    !l4Mixed.strippedRulesTextByBasicLandSet &&
      !(gMixed.staticAbilities oMixed).isEmpty &&
      (gMixed.manaAbilitiesOf oMixed).contains .colorless &&
      (gMixed.manaAbilitiesOf oMixed).contains (.colored .red)
  -- Blood Moon (ts 1) + Yavimaya `.addDedup #[.forest]` (ts 2): stays stripped, adds `{R}` + `{G}`.
  let gMoonYav := gMoon.createEffect
    (.layered (.objects #[lid]) (.types .addDedup #[] #[.forest] #[]) .indefinite)
    (cause := some testCause)
  let oMoonYav := gMoonYav.object! lid
  let l4MoonYav := gMoonYav.evalLayer4Full oMoonYav
  let moonYavStripped :=
    l4MoonYav.strippedRulesTextByBasicLandSet &&
      (gMoonYav.staticAbilities oMoonYav).isEmpty &&
      !(gMoonYav.manaAbilitiesOf oMoonYav).contains .colorless &&
      (gMoonYav.manaAbilitiesOf oMoonYav).contains (.colored .red) &&
      (gMoonYav.manaAbilitiesOf oMoonYav).contains (.colored .green)
  -- Blood Moon (ts 1) + turn into non-land Artifact (ts 2): clears stripping, restores printed abilities.
  let gArt := gMoon.createEffect
    (.layered (.objects #[lid]) (.types .set #[.artifact] #[] #[]) .indefinite)
    (cause := some testCause)
  let oArt := gArt.object! lid
  let artClearsStripped :=
    !(gArt.evalLayer4Full oArt).strippedRulesTextByBasicLandSet &&
      !(gArt.staticAbilities oArt).isEmpty &&
      gArt.manaAbilitiesOf oArt == #[.colorless]
  locusRestoresPrinted && mixedKeepsPrinted && moonYavStripped && artClearsStripped

-- CR 605.1a modal mana abilities resolve immediately without using the stack
-- (both mana-producing modes and non-mana modes), whereas modal abilities with
-- a targeted or library-moving mode in `otherModes` use the stack.
#guard
  let dualModalMana : CardDef := {
    name := "P5 Dual Modal Rock"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.tapOnly
      effect := Effect.addMana #[.colored .red]
      otherModes := #[Effect.addMana #[.colored .green]]
    }]
  }
  let hybridModalMana : CardDef := {
    name := "P5 Hybrid Modal Rock"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.tapOnly
      effect := Effect.gainLife 2
      otherModes := #[Effect.addMana #[.colored .green]]
    }]
  }
  let badModalTarget : ActivatedAbility := {
    cost := CostSpec.tapOnly
    effect := Effect.addMana #[.colored .green]
    otherModes := #[{ targeting := .of TargetSpec.creature, resolution := .gainLife 1 }]
  }
  let badModalDraw : ActivatedAbility := {
    cost := CostSpec.tapOnly
    effect := Effect.addMana #[.colored .green]
    otherModes := #[Effect.draw 1]
  }
  let gDual := addPermanent afterDraw dualModalMana p0 p0
  let dualId := (namedPerm gDual dualModalMana.name).id
  let gDualRed := mustOk (gDual.apply p0 (.activateManaAbility dualId 0 #[.colored .red] #[]))
  let gDualGreen := mustOk (gDual.apply p0 (.activateManaAbility dualId 0 #[.colored .green] #[]))
  let dualRejectsBlue := !(gDual.apply p0 (.activateManaAbility dualId 0 #[.colored .blue] #[])).isOk
  let gHyb := addPermanent afterDraw hybridModalMana p0 p0
  let hybId := (namedPerm gHyb hybridModalMana.name).id
  let gHybMana := mustOk (gHyb.apply p0 (.activateManaAbility hybId 0 #[.colored .green] #[]))
  let gHybLife := mustOk (gHyb.apply p0 (.activateManaAbility hybId 0 #[] #[]))
  gDualRed.stack.isEmpty && (gDualRed.player p0).manaPool.red == 1 &&
    gDualGreen.stack.isEmpty && (gDualGreen.player p0).manaPool.green == 1 &&
    dualRejectsBlue &&
    gHybMana.stack.isEmpty && (gHybMana.player p0).manaPool.green == 1 &&
    gHybLife.stack.isEmpty && (gHybLife.player p0).life == 22 &&
    !Game.isManaActivation badModalTarget &&
    !Game.isManaActivation badModalDraw

-- CR 605.1a / 605.3a hand exile (`Elvish Spirit Guide` style), hand discard,
-- and graveyard exile mana abilities resolve immediately without the stack
-- and work during CR 601.2g spell payment!
#guard
  let spiritGuide : CardDef := {
    name := "P5 Spirit Guide"
    manaCost := ManaCost.ofGenericAndColor 2 .green
    types := #[.creature]
    power := some 2
    toughness := some 2
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.exile (.exact 1) .yourHand .self]
      activeZones := #[.hand]
      mana? := some { spec := .fixedOne (.colored .green) }
    }]
  }
  let cheapGreenSpell : CardDef := {
    name := "P5 Tiny Elf"
    manaCost := ManaCost.ofColor .green
    types := #[.creature]
    power := some 1
    toughness := some 1
  }
  let discardMana : CardDef := {
    name := "P5 Red Simian"
    types := #[.creature]
    power := some 2
    toughness := some 2
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.discard (.exact 1) .self]
      activeZones := #[.hand]
      mana? := some { spec := .fixedOne (.colored .red) }
    }]
  }
  let gyMana : CardDef := {
    name := "P5 Crypt Spirit"
    types := #[.creature]
    power := some 1
    toughness := some 1
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.exile (.exact 1) .yourGraveyard .self]
      activeZones := #[.graveyard]
      effect := Effect.addMana #[.colorless]
    }]
  }
  -- Hand exile during CR 601.2g spell casting (0 lands on battlefield!):
  let g0 := insertObject (insertObject afterDraw spiritGuide p0 (.hand p0)) cheapGreenSpell p0 (.hand p0)
  let guideId := (g0.player p0).hand.find? (fun id => (g0.object! id).name == spiritGuide.name) |>.get!
  let elfId := (g0.player p0).hand.find? (fun id => (g0.object! id).name == cheapGreenSpell.name) |>.get!
  let gCastStart := mustOk (g0.apply p0 (.cast elfId))
  let gExiledGuide := mustOk (gCastStart.apply p0 (.activateManaAbility guideId 0 #[.colored .green] #[]))
  let gPaid := mustOk (gExiledGuide.apply p0 .pay)
  let guideInExile := (gPaid.followMovedToZone? guideId (· == .exile)).isSome
  -- Hand discard mana ability (direct without stack):
  let gDisc0 := insertObject afterDraw discardMana p0 (.hand p0)
  let discId := (gDisc0.player p0).hand.back!
  let gDisc1 := mustOk (gDisc0.apply p0 (.activate discId 0))
  let discInGy := (gDisc1.followMovedToZone? discId (· == .graveyard p0)).isSome
  -- Graveyard exile mana ability (direct without stack):
  let gGy0 := insertObject afterDraw gyMana p0 (.graveyard p0)
  let gyId := (gGy0.player p0).graveyard.back!
  let gGy1 := mustOk (gGy0.apply p0 (.activateManaAbility gyId 0 #[.colorless] #[]))
  let gyInExile := (gGy1.followMovedToZone? gyId (· == .exile)).isSome
  g0.hasUsableNonPlainManaAbility p0 &&
    gCastStart.pending == .activateManaAbilities p0 &&
    gExiledGuide.pending == .activateManaAbilities p0 &&
    (gExiledGuide.player p0).manaPool.green == 1 &&
    gPaid.stack.size == 1 &&
    guideInExile &&
    gDisc1.stack.isEmpty && (gDisc1.player p0).manaPool.red == 1 && discInGy &&
    gGy1.stack.isEmpty && (gGy1.player p0).manaPool.colorless == 1 && gyInExile

-- CR 605.1a extra-cost mana abilities (`removeAnyNumberPlusOne`, `crewPower?`,
-- and `exileManaSymbols?`) all pay their costs and add mana without the stack.
#guard
  let counterManaCreature : CardDef := {
    name := "P5 Crystalline Crawler"
    types := #[.artifact, .creature]
    power := some 1
    toughness := some 1
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.tapSelf, .removeCounters .anyNumber (some .plusOnePlusOne) .self]
      mana? := some { spec := .sequence #[(.colored .green, .chosenX)] }
    }]
  }
  let crewManaVehicle : CardDef := {
    name := "P5 Solar Barge"
    types := #[.artifact]
    subtypes := #["Vehicle"]
    activatedAbilities := #[{
      cost := CostSpec.crewCost 2
      mana? := some { spec := .fixed #[.colored .red, .colored .red] }
    }]
  }
  let exileSymMana : CardDef := {
    name := "P5 Shadow Altar"
    types := #[.artifact]
    activatedAbilities := #[{
      cost := CostSpec.ofItems #[.exile (.totalManaSymbolsAtLeast (some .black) (.const 2)) .yourGraveyard (.filter (.all #[.hasColor (.literal .black), .isKind .card]))]
      mana? := some { spec := .fixed #[.colored .black, .colored .black, .colored .black] }
    }]
  }
  let bbCard : CardDef := {
    name := "P5 Dark Ritualist"
    manaCost := { symbols := #[.colored .black, .colored .black] }
    types := #[.creature]
    power := some 2
    toughness := some 2
  }
  -- `removeAnyNumberPlusOne`: 3 counters -> remove 2 for `{G}{G}` (leaves 1), reject 4.
  let gCnt0 := addPermanent afterDraw counterManaCreature p0 p0
  let cntId := (namedPerm gCnt0 counterManaCreature.name).id
  let gCnt3 := gCnt0.recordPutCounters cntId .plusOnePlusOne 3 (some p0) (cause := some testCause)
  let cntTooMany := !(gCnt3.apply p0 (.activateManaAbility cntId 0 #[.colored .green, .colored .green, .colored .green, .colored .green] #[])).isOk
  let gCnt2 := mustOk (gCnt3.apply p0 (.activateManaAbility cntId 0 #[.colored .green, .colored .green] #[]))
  -- `crewPower?`: tap 2/2 Grizzly Bears -> adds `{R}{R}` without stack; empty costIds fails.
  let gCrew0 := addPermanent (addPermanent afterDraw crewManaVehicle p0 p0) grizzlyBears p0 p0
  let bargeId := (namedPerm gCrew0 crewManaVehicle.name).id
  let bearId := (namedPerm gCrew0 "Grizzly Bears").id
  let crewNoIdsFails := !(gCrew0.apply p0 (.activateManaAbility bargeId 0 #[.colored .red, .colored .red] #[])).isOk
  let gCrew1 := mustOk (gCrew0.apply p0 (.activateManaAbility bargeId 0 #[.colored .red, .colored .red] #[bearId]))
  -- `exileManaSymbols?`: exile `{B}{B}` card from graveyard -> adds `{B}{B}{B}` without stack; empty fails.
  let gSym0 := insertObject (addPermanent afterDraw exileSymMana p0 p0) bbCard p0 (.graveyard p0)
  let altarId := (namedPerm gSym0 exileSymMana.name).id
  let bbId := (gSym0.player p0).graveyard.back!
  let symNoIdsFails := !(gSym0.apply p0 (.activateManaAbility altarId 0 #[.colored .black, .colored .black, .colored .black] #[])).isOk
  let gSym1 := mustOk (gSym0.apply p0 (.activateManaAbility altarId 0 #[.colored .black, .colored .black, .colored .black] #[bbId]))
  cntTooMany &&
    gCnt2.stack.isEmpty && (gCnt2.player p0).manaPool.green == 2 &&
    (gCnt2.object! cntId).status.plusOnePlusOne == 1 && (gCnt2.object! cntId).status.tapped &&
    crewNoIdsFails &&
    gCrew1.stack.isEmpty && (gCrew1.player p0).manaPool.red == 2 && (gCrew1.object! bearId).status.tapped &&
    symNoIdsFails &&
    gSym1.stack.isEmpty && (gSym1.player p0).manaPool.black == 3 &&
    (gSym1.followMovedToZone? bbId (· == .exile)).isSome

end Mtg.Engine.Tests.ActivatedManaSuite
