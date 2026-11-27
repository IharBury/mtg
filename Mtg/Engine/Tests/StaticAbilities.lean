import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.Catalog.RealityFractureCommander

/-!
# Stratified `StaticAbility` Runtime Tests (CR 604 / 613 / 614–616)

Comprehensive gameplay `#guard` regression suite for stratified static abilities
(see `docs/card-and-ability-model.md` and `docs/game-evaluation.md`, anchored
to the 6 November 2026 CR):
1. Layer 3 text changes (`TextChange.replaceCreatureType`) on previously-bypassed
   static abilities: `costReductionIfYouControl`, `flashIfYouControlSubtype`,
   `entersTappedUnlessBehold`, `extraLandIfOtherSubtype`, command-zone
   `eminenceSubtypeSpellsCostLess`, and `armiesYouControlHaveTrample`.
2. Layer 6 ability removal (`losesAbilitiesUntilEot` / Humility) on previously-
   bypassed static abilities (`firstCreatureHasFlash`, `firstCreatureCostsLess`,
   `noncreatureSpellsHaveImprovise`, `tokenDoubling`, `opponentsCantGainLife`,
   `corruptedToxicLifelink`, `protectionFromChosenCardType`) plus CR 613.8
   dependency ordering (a later-timestamp toxic grant still enables lifelink).
3. CR 707.9d P/T CDA stripping on token copies with `CopyModification.setBasePT`.
4. Layer 7a printed CDA vs. Layer 7b `setBasePTUntilEot` vs. Layer 7b granted CDA
   timestamp ordering (CR 613.4a–b / 613.7).
5. Command-zone static abilities (CR 113.6 / 114.4): Eminence cost reduction in
   `.command` (other matching spells only, not self), stacking Elspeth emblems,
   and a command-zone Platinum Angel emblem (`cantLoseAndOpponentsCantWin`).
6. CR 303.4a Aura `enchantRestriction`: `enchantArtifactOrNonAuraEnchantment`,
   `enchantCreatureYouControl`, and novel `"Enchant nonland permanent"` (legality
   and CR 704.5m SBA fall-off).
7. Migrated keywords (`Improvise`, `Extort`, `Sneak`), Baron Helmut Zemo's `Boast`
   on `activatedAbilities`, and `instantSorcerySplitSecond` (stack keyword grant
   + Layer 6 removal).
8. Novel compositional static abilities parsed via `parseOracleCard` and executed
   end-to-end in `Game` (Wizard lord, Goblin cost reducer, opponent spell tax,
   conditional Dragon buff, 3x token multiplier, and player protection from red).
-/

namespace Mtg.Engine.Tests.StaticAbilitiesSuite

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

private def mkCreature (name : String) (subs : Array String)
    (mana : ManaCost := ManaCost.ofGeneric 2) (p t : Int := 2)
    (statics : Array StaticAbility := #[]) (kws : Array KeywordAbility := #[]) : CardDef :=
  { name := name
    manaCost := mana
    types := #[.creature]
    subtypes := subs
    power := some (.fixed p)
    toughness := some (.fixed t)
    staticAbilities := statics
    keywords := kws }

private def mkEmblem (name : String) (statics : Array StaticAbility) : CardDef :=
  { name := name
    types := #[]
    subtypes := #[]
    staticAbilities := statics }

private def addToZone (g : Game) (card : CardDef) (owner : PlayerId) (z : Zone)
    (ctrl : Option PlayerId := some owner) (status : Status := {}) : Game × GameObject :=
  g.allocObject card owner z ctrl status

/-! ### 1. Layer 3 Text Changes on Previously-Bypassed Static Abilities -/

-- `costReductionIfYouControl`: Layer 3 `.dragon` → `.elf` rewrites the self-cost-reduction
-- condition so controlling an Elf reduces the spell's cost by `{2}` while controlling
-- a Dragon does not.
#guard
  let spellCard := mkCreature "P6 Dragon-Scaled Spell" #["Spellshaper"]
    (ManaCost.ofGenericAndColor 3 .red) 3 3
    (statics := #[.costReductionIfYouControl 2 .dragon])
  let dragonCard := mkCreature "P6 Test Dragon" #["Dragon"]
  let elfCard := mkCreature "P6 Test Elf" #["Elf"]
  let (g0, spellObj) := addToZone afterDraw spellCard p0 (.hand p0) (some p0)
  -- Base: Dragon reduces {3}{R} → {1}{R}; Elf does not.
  let gWithDragon := addPermanent g0 dragonCard p0 p0
  let gWithElf := addPermanent g0 elfCard p0 p0
  let baseDragonCost := gWithDragon.playManaCost (gWithDragon.object! spellObj.id) spellCard
  let baseElfCost := gWithElf.playManaCost (gWithElf.object! spellObj.id) spellCard
  -- Apply Layer 3 text change `.dragon` → `.elf` to the spell in hand.
  let tcEff : ContinuousEffectSpec := .layered (.objects #[spellObj.id])
    (.text (.replaceCreatureType .dragon .elf)) .indefinite
  let gTcDragon := gWithDragon.createEffect tcEff (cause := some testCause)
  let gTcElf := gWithElf.createEffect tcEff (cause := some testCause)
  let tcDragonCost := gTcDragon.playManaCost (gTcDragon.object! spellObj.id) spellCard
  let tcElfCost := gTcElf.playManaCost (gTcElf.object! spellObj.id) spellCard
  baseDragonCost == ManaCost.ofGenericAndColor 1 .red &&
    baseElfCost == ManaCost.ofGenericAndColor 3 .red &&
    tcDragonCost == ManaCost.ofGenericAndColor 3 .red &&
    tcElfCost == ManaCost.ofGenericAndColor 1 .red

-- `flashIfYouControlSubtype`: Layer 3 `.dragon` → `.elf` allows casting a sorcery-speed
-- creature spell during the opponent's step (or upkeep) when controlling an Elf.
#guard
  let flashCard := mkCreature "P6 Dragon Ambush" #["Warrior"]
    (ManaCost.ofGenericAndColor 2 .red) 3 2
    (statics := #[.flashIfYouControlSubtype .dragon])
  let dragonCard := mkCreature "P6 Flash Dragon" #["Dragon"]
  let elfCard := mkCreature "P6 Flash Elf" #["Elf"]
  -- `started` is in `.upkeep` where sorcery-speed casting is disallowed for p0.
  let (g0, cardObj) := addToZone started flashCard p0 (.hand p0) (some p0)
  let gDragon := addPermanent g0 dragonCard p0 p0
  let gElf := addPermanent g0 elfCard p0 p0
  let tcEff : ContinuousEffectSpec := .layered (.objects #[cardObj.id])
    (.text (.replaceCreatureType .dragon .elf)) .indefinite
  let gTcDragon := gDragon.createEffect tcEff (cause := some testCause)
  let gTcElf := gElf.createEffect tcEff (cause := some testCause)
  gDragon.timingAllowsCast p0 flashCard (card? := some (gDragon.object! cardObj.id)) &&
    !(gElf.timingAllowsCast p0 flashCard (card? := some (gElf.object! cardObj.id))) &&
    !(gTcDragon.timingAllowsCast p0 flashCard (card? := some (gTcDragon.object! cardObj.id))) &&
    gTcElf.timingAllowsCast p0 flashCard (card? := some (gTcElf.object! cardObj.id))

-- `entersTappedUnlessBehold`: Layer 3 `.dragon` → `.elf` transforms the land's
-- behold replacement subtype on `g.staticAbilities`.
#guard
  let beholdLand : CardDef := {
    name := "P6 Behold Haven"
    types := #[.land]
    staticAbilities := #[.entersTappedUnlessBehold .dragon]
  }
  let g0 := addPermanent afterDraw beholdLand p0 p0
  let lid := (namedPerm g0 beholdLand.name).id
  let g1 := g0.createEffect
    (.layered (.objects #[lid]) (.text (.replaceCreatureType .dragon .elf)) .indefinite)
    (cause := some testCause)
  g0.staticAbilities (g0.object! lid) == #[.entersTappedUnlessBehold .dragon] &&
    g1.staticAbilities (g1.object! lid) == #[.entersTappedUnlessBehold .elf]

-- `extraLandIfOtherSubtype`: Layer 3 `.elf` → `.goblin` updates `landPlaysAllowed`.
#guard
  let scout := mkCreature "P6 Extra Land Scout" #["Scout"]
    (statics := #[.extraLandIfOtherSubtype .elf])
  let elfCard := mkCreature "P6 Peer Elf" #["Elf"]
  let goblinCard := mkCreature "P6 Peer Goblin" #["Goblin"]
  let gBase := addPermanent afterDraw scout p0 p0
  let sid := (namedPerm gBase scout.name).id
  let gElf := addPermanent gBase elfCard p0 p0
  let gGob := addPermanent gBase goblinCard p0 p0
  let tcEff : ContinuousEffectSpec := .layered (.objects #[sid])
    (.text (.replaceCreatureType .elf .goblin)) .indefinite
  let gTcElf := gElf.createEffect tcEff (cause := some testCause)
  let gTcGob := gGob.createEffect tcEff (cause := some testCause)
  gElf.landPlaysAllowed p0 == 2 &&
    gGob.landPlaysAllowed p0 == 1 &&
    gTcElf.landPlaysAllowed p0 == 1 &&
    gTcGob.landPlaysAllowed p0 == 2

-- `eminenceSubtypeSpellsCostLess` in `.command` zone: Layer 3 `.sphinx` → `.goblin`
-- switches which tribal spells receive the `{1}` cost reduction from the command zone!
#guard
  let cmdr := mkCreature "P6 Eminence Commander" #["Sphinx"]
    (ManaCost.ofGenericAndColor 4 .blue) 5 5
    (statics := #[.eminenceSubtypeSpellsCostLess .sphinx 1])
  let sphinxSpell := mkCreature "P6 Other Sphinx" #["Sphinx"] (ManaCost.ofGenericAndColor 3 .blue)
  let goblinSpell := mkCreature "P6 Other Goblin" #["Goblin"] (ManaCost.ofGenericAndColor 3 .red)
  let (g0, cmdrObj) := addToZone afterDraw cmdr p0 .command (some p0)
  let (g1, sphinxObj) := addToZone g0 sphinxSpell p0 (.hand p0) (some p0)
  let (g2, goblinObj) := addToZone g1 goblinSpell p0 (.hand p0) (some p0)
  let gTc := g2.createEffect
    (.layered (.objects #[cmdrObj.id]) (.text (.replaceCreatureType .sphinx .goblin)) .indefinite)
    (cause := some testCause)
  g2.playManaCost (g2.object! sphinxObj.id) sphinxSpell == ManaCost.ofGenericAndColor 2 .blue &&
    g2.playManaCost (g2.object! goblinObj.id) goblinSpell == ManaCost.ofGenericAndColor 3 .red &&
    gTc.playManaCost (gTc.object! sphinxObj.id) sphinxSpell == ManaCost.ofGenericAndColor 3 .blue &&
    gTc.playManaCost (gTc.object! goblinObj.id) goblinSpell == ManaCost.ofGenericAndColor 2 .red

-- `armiesYouControlHaveTrample`: Layer 3 `.army` → `.elf` moves the trample grant
-- from Armies to Elves.
#guard
  let lord := mkCreature "P6 Army Banner" #["Orc"] (statics := #[.armiesYouControlHaveTrample])
  let armyC := mkCreature "P6 Test Army" #["Orc", "Army"]
  let elfC := mkCreature "P6 Test Elf" #["Elf"]
  let g0 := addPermanent (addPermanent (addPermanent afterDraw lord p0 p0) armyC p0 p0) elfC p0 p0
  let lid := (namedPerm g0 lord.name).id
  let aid := (namedPerm g0 armyC.name).id
  let eid := (namedPerm g0 elfC.name).id
  let gTc := g0.createEffect
    (.layered (.objects #[lid]) (.text (.replaceCreatureType .army .elf)) .indefinite)
    (cause := some testCause)
  g0.hasSimpleKeyword (g0.object! aid) .trample &&
    !(g0.hasSimpleKeyword (g0.object! eid) .trample) &&
    !(gTc.hasSimpleKeyword (gTc.object! aid) .trample) &&
    gTc.hasSimpleKeyword (gTc.object! eid) .trample

/-! ### 2. Layer 6 Ability Removal (Humility) & CR 613.8 Dependency Ordering -/

-- `firstCreatureHasFlash` + `firstCreatureCostsLess`: active before Humility,
-- both stripped when the source loses all abilities in Layer 6.
#guard
  let guide := mkCreature "P6 First-Creature Guide" #["Elf"]
    (statics := #[.firstCreatureCostsLess 1, .firstCreatureHasFlash])
  let bear := mkCreature "P6 Grizzly" #["Bear"] (ManaCost.ofGenericAndColor 2 .green)
  let g0 := addPermanent started guide p0 p0
  let gid := (namedPerm g0 guide.name).id
  let (g1, bearObj) := addToZone g0 bear p0 (.hand p0) (some p0)
  let gHum := g1.createEffect (.losesAbilitiesUntilEot gid) (cause := some testCause)
  g1.playManaCost (g1.object! bearObj.id) bear == ManaCost.ofGenericAndColor 1 .green &&
    g1.timingAllowsCast p0 bear (card? := some (g1.object! bearObj.id)) &&
    gHum.playManaCost (gHum.object! bearObj.id) bear == ManaCost.ofGenericAndColor 2 .green &&
    !(gHum.timingAllowsCast p0 bear (card? := some (gHum.object! bearObj.id)))

-- `noncreatureSpellsHaveImprovise`: grants Improvise to noncreature spells before
-- Humility, stripped after `losesAbilitiesUntilEot`.
#guard
  let artificer := mkCreature "P6 Gearsmith" #["Artificer"]
    (statics := #[.noncreatureSpellsHaveImprovise])
  let g0 := addPermanent afterDraw artificer p0 p0
  let aid := (namedPerm g0 artificer.name).id
  let gHum := g0.createEffect (.losesAbilitiesUntilEot aid) (cause := some testCause)
  g0.spellHasImprovise lightningBolt p0 && !(gHum.spellHasImprovise lightningBolt p0)

-- `tokenDoubling`: doubles created tokens before Humility, creates 1 token after
-- `losesAbilitiesUntilEot`.
#guard
  let doubler := mkCreature "P6 Token Doubler" #["Spirit"] (statics := #[.tokenDoubling])
  let g0 := addPermanent afterDraw doubler p0 p0
  let did := (namedPerm g0 doubler.name).id
  let (gDoubled, _) := g0.createToken p0 bearToken
  let gHum := g0.createEffect (.losesAbilitiesUntilEot did) (cause := some testCause)
  let (gSingle, _) := gHum.createToken p0 bearToken
  let countBears (g : Game) := (g.battlefield.filter (·.name == bearToken.name)).size
  countBears gDoubled == 2 && countBears gSingle == 1

-- `opponentsCantGainLife`: blocks opponent life gain before Humility, allows life
-- gain after `losesAbilitiesUntilEot`.
#guard
  let blocker := mkCreature "P6 Life Blocker" #["Knight"] (statics := #[.opponentsCantGainLife])
  let g0 := addPermanent afterDraw blocker p0 p0
  let bid := (namedPerm g0 blocker.name).id
  let gBlocked := g0.gainLife p1 3
  let gHum := g0.createEffect (.losesAbilitiesUntilEot bid) (cause := some testCause)
  let gAllowed := gHum.gainLife p1 3
  (gBlocked.player p1).life == 20 && (gAllowed.player p1).life == 23

-- `corruptedToxicLifelink` + CR 613.8 dependency ordering:
-- 1. With p1 at 3 poison counters, a creature with printed `toxic 1` gains `lifelink`.
-- 2. Even when the Corrupted source entered EARLIER and another creature receives
--    `toxic 1` LATER via `.keywordsUntilEot`, CR 613.8 dependency still grants `lifelink`!
-- 3. `losesAbilitiesUntilEot` on the Corrupted source strips the lifelink grant.
#guard
  let priest := mkCreature "P6 Corrupted Priest" #["Cleric"]
    (statics := #[.corruptedToxicLifelink])
  let plainBear := mkCreature "P6 Plain Bear" #["Bear"]
  let g0 := (addPermanent (addPermanent afterDraw priest p0 p0) plainBear p0 p0).addPlayerCounters p1 .poison 3
  let pid := (namedPerm g0 priest.name).id
  let bid := (namedPerm g0 plainBear.name).id
  -- Before toxic grant: plainBear has no lifelink.
  let noLifelinkBefore := !(g0.hasSimpleKeyword (g0.object! bid) .lifelink)
  -- Grant `toxic 1` at a LATER timestamp than `priest`!
  let gToxic := g0.createEffect (.keywordsUntilEot bid #[.toxic 1]) (cause := some testCause)
  let hasLifelinkByDep := gToxic.hasSimpleKeyword (gToxic.object! bid) .lifelink
  -- Humility on `priest` strips the lifelink grant while keeping `toxic 1`.
  let gHum := gToxic.createEffect (.losesAbilitiesUntilEot pid) (cause := some testCause)
  let lostLifelinkAfterHum := !(gHum.hasSimpleKeyword (gHum.object! bid) .lifelink) &&
    gHum.hasKeyword (gHum.object! bid) (fun | .toxic _ => true | _ => false)
  noLifelinkBefore && hasLifelinkByDep && lostLifelinkAfterHum

-- `protectionFromChosenCardType`: protects player and creatures you control (NOT
-- noncreature artifacts) from the chosen card type, and `losesAbilitiesUntilEot`
-- strips both player and creature protection cleanly.
#guard
  let emissary := mkCreature "P6 Chosen Prot Angel" #["Angel"]
    (statics := #[.asEntersChooseCardType, .protectionFromChosenCardType])
  let bear := mkCreature "P6 Protected Bear" #["Bear"]
  let relic : CardDef := { name := "P6 Unprotected Relic", types := #[.artifact] }
  let (g0, emObj) := addToZone afterDraw emissary p0 .battlefield (some p0)
    (status := { chosenCardType := some .instant })
  let g1 := addPermanent (addPermanent g0 bear p0 p0) relic p0 p0
  let (g2, boltObj) := addToZone g1 lightningBolt p1 .stack (some p1)
  let bid := (namedPerm g2 bear.name).id
  let rid := (namedPerm g2 relic.name).id
  let bolt := g2.object! boltObj.id
  let gHum := g2.createEffect (.losesAbilitiesUntilEot emObj.id) (cause := some testCause)
  -- Before Humility: player p0 and Bear are protected from Instant, Relic is NOT.
  !(g2.playerCanBeTargetedBy p1 p0 (some boltObj.id)) &&
    g2.protectedFrom (g2.object! bid) bolt &&
    !(g2.protectedFrom (g2.object! rid) bolt) &&
    -- After Humility on emissary: neither player nor Bear is protected.
    gHum.playerCanBeTargetedBy p1 p0 (some boltObj.id) &&
    !(gHum.protectedFrom (gHum.object! bid) bolt)

/-! ### 3. CR 707.9d P/T CDA Stripping on Token Copy with `setBasePT` -/

-- Copying a `*/*` CDA creature with `CopyModification.setBasePT 4 4` strips the P/T-
-- defining CDA (CR 707.9d) while keeping non-PT statics (`cantBeBlocked`), so the
-- resulting token is a 4/4 regardless of land count.
#guard
  let cdaCreature : CardDef := {
    name := "P6 Land-Bound Stalker"
    types := #[.creature]
    subtypes := #["Elemental"]
    power := some (.star 0)
    toughness := some (.star 0)
    staticAbilities := #[.powerToughnessEqualLandsYouControl, .cantBeBlocked]
  }
  let g0 := addPermanent (addPermanent afterDraw cdaCreature p0 p0) forest p0 p0
  let srcId := (namedPerm g0 cdaCreature.name).id
  match g0.resolveCopyTokenForObject? srcId #[.setBasePT 4 4] with
  | none => false
  | some copiedDef =>
    let (g1, tok) := g0.createToken p0 copiedDef
    copiedDef.power == some (.fixed 4) &&
      copiedDef.toughness == some (.fixed 4) &&
      !(copiedDef.staticAbilities.any StaticAbility.isPTDefiningCDA) &&
      copiedDef.staticAbilities.contains .cantBeBlocked &&
      g1.power (g1.object! tok.id) == 4 &&
      g1.toughness (g1.object! tok.id) == 4

/-! ### 4. Layer 7a Printed CDA vs. Layer 7b `setBasePTUntilEot` vs. Granted CDA -/

-- A creature with printed Layer 7a `powerToughnessEqualLandsYouControl` and 3 Forests:
-- * Base: 3/3 (Layer 7a).
-- * After `setBasePTUntilEot (1, 1)` (Layer 7b): overridden to 1/1.
-- * After granting a second P/T CDA via `.grantedStatic` at a LATER timestamp (Layer 7b):
--   the later-timestamp Layer 7b granted CDA wins over `setBasePTUntilEot (1, 1)` → 3/3!
#guard
  let landElem : CardDef := {
    name := "P6 Layer7 Elemental"
    types := #[.creature]
    subtypes := #["Elemental"]
    power := some (.star 0)
    toughness := some (.star 0)
    staticAbilities := #[.powerToughnessEqualLandsYouControl]
  }
  let g0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw landElem p0 p0)
    forest p0 p0) forest p0 p0) forest p0 p0
  let eid := (namedPerm g0 landElem.name).id
  let gSet11 := g0.createEffect (.setBasePTUntilEot eid (1, 1)) (cause := some testCause)
  let gGrantLater := gSet11.createEffect
    (.grantedStatic eid .powerToughnessEqualLandsYouControl) (cause := some testCause)
  g0.power (g0.object! eid) == 3 && g0.toughness (g0.object! eid) == 3 &&
    gSet11.power (gSet11.object! eid) == 1 && gSet11.toughness (gSet11.object! eid) == 1 &&
    gGrantLater.power (gGrantLater.object! eid) == 3 &&
    gGrantLater.toughness (gGrantLater.object! eid) == 3

/-! ### 5. Command-Zone Statics (CR 113.6 / 114.4) -/

-- Eminence in `.command` reduces OTHER Sphinx spells by `{1}`, does NOT reduce its own
-- cost when cast from the command zone, and does NOT reduce non-Sphinx spells.
#guard
  let cmdr := mkCreature "P6 Sphinx Sovereign" #["Sphinx"]
    (ManaCost.ofGenericAndColor 4 .blue) 5 5
    (statics := #[.eminenceSubtypeSpellsCostLess .sphinx 1])
  let otherSphinx := mkCreature "P6 Peer Sphinx" #["Sphinx"] (ManaCost.ofGenericAndColor 3 .blue)
  let bear := mkCreature "P6 Plain Bear" #["Bear"] (ManaCost.ofGenericAndColor 3 .green)
  let (g0, cmdrObj) := addToZone afterDraw cmdr p0 .command (some p0)
  let (g1, otherObj) := addToZone g0 otherSphinx p0 (.hand p0) (some p0)
  let (g2, bearObj) := addToZone g1 bear p0 (.hand p0) (some p0)
  g2.playManaCost (g2.object! cmdrObj.id) cmdr == ManaCost.ofGenericAndColor 4 .blue &&
    g2.playManaCost (g2.object! otherObj.id) otherSphinx == ManaCost.ofGenericAndColor 2 .blue &&
    g2.playManaCost (g2.object! bearObj.id) bear == ManaCost.ofGenericAndColor 3 .green

-- Two Elspeth emblems in `.command` stack to give a 2/2 Bear +4/+4 (6/6) and flying.
#guard
  let elspethEmblem := mkEmblem "Elspeth Emblem"
    #[.creaturesYouControlGetAndHave 2 2 #[Keyword.flying]]
  let bear := mkCreature "P6 Emblem Bear" #["Bear"] (p := 2) (t := 2)
  let g0 := addPermanent afterDraw bear p0 p0
  let (g1, _) := addToZone g0 elspethEmblem p0 .command (some p0)
  let (g2, _) := addToZone g1 elspethEmblem p0 .command (some p0)
  let b := namedPerm g2 bear.name
  g2.power b == 6 && g2.toughness b == 6 && g2.hasSimpleKeyword b .flying

-- Platinum Angel emblem (`cantLoseAndOpponentsCantWin`) in `.command`:
-- p0 survives 0 life across `checkSBA`, and `playerCantWin p1` is true.
#guard
  let angelEmblem := mkEmblem "Platinum Emblem" #[.cantLoseAndOpponentsCantWin]
  let (g0, _) := addToZone afterDraw angelEmblem p0 .command (some p0)
  let gZero := g0.setLifeTotal p0 0
  let gAfterSba := gZero.checkSBA
  !gAfterSba.over && gAfterSba.playerCantWin p1

/-! ### 6. CR 303.4a Aura `enchantRestriction` & CR 704.5m SBA Fall-Off -/

-- `enchantArtifactOrNonAuraEnchantment` and `enchantCreatureYouControl` enforce
-- exact CR 303.4a host legality.
#guard
  let relicAura : CardDef := {
    name := "P6 Relic Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantArtifactOrNonAuraEnchantment]
  }
  let loyalAura : CardDef := {
    name := "P6 Loyal Aura"
    types := #[.enchantment]
    subtypes := #["Aura"]
    staticAbilities := #[.enchantCreatureYouControl]
  }
  let plainArtifact : CardDef := { name := "P6 Artifact", types := #[.artifact] }
  let plainEnch : CardDef := { name := "P6 Enchantment", types := #[.enchantment] }
  let otherAura : CardDef := { name := "P6 Other Aura", types := #[.enchantment], subtypes := #["Aura"] }
  let myBear := mkCreature "P6 My Bear" #["Bear"]
  let oppBear := mkCreature "P6 Opp Bear" #["Bear"]
  let g0 := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent
    (addPermanent (addPermanent afterDraw relicAura p0 p0) loyalAura p0 p0)
    plainArtifact p0 p0) plainEnch p0 p0) otherAura p0 p0) myBear p0 p0) oppBear p1 p1
  let rA := namedPerm g0 relicAura.name
  let lA := namedPerm g0 loyalAura.name
  g0.auraObjCanEnchant (namedPerm g0 plainArtifact.name) rA &&
    g0.auraObjCanEnchant (namedPerm g0 plainEnch.name) rA &&
    !(g0.auraObjCanEnchant (namedPerm g0 otherAura.name) rA) &&
    !(g0.auraObjCanEnchant (namedPerm g0 myBear.name) rA) &&
    g0.auraObjCanEnchant (namedPerm g0 myBear.name) lA &&
    !(g0.auraObjCanEnchant (namedPerm g0 oppBear.name) lA)

-- Novel `"Enchant nonland permanent"` parsed via `parseOracleCard`: legal on a Bear
-- or Artifact, illegal on a Mountain, and CR 704.5m SBA sends it to the graveyard
-- when attached to a Mountain.
#guard
  let wardAura := mustParse
    "Ward of Permanence\n{1}{W}\nEnchantment — Aura\nEnchant nonland permanent\nEnchanted permanent has hexproof."
  let myBear := mkCreature "P6 Hex Bear" #["Bear"]
  let g0 := addPermanent (addPermanent afterDraw myBear p0 p0) mountain p0 p0
  let bearId := (namedPerm g0 myBear.name).id
  let mtnId := (namedPerm g0 "Mountain").id
  let (gOnBear, a1) := g0.allocObject wardAura p0 .battlefield (some p0)
    (attachedTo := some bearId)
  let (gOnMtn, a2) := g0.allocObject wardAura p0 .battlefield (some p0)
    (attachedTo := some mtnId)
  let gAfterSba := gOnMtn.checkSBA
  gOnBear.auraObjCanEnchant (gOnBear.object! bearId) (gOnBear.object! a1.id) &&
    gOnBear.hasKeyword (gOnBear.object! bearId) (· == Keyword.hexproof) &&
    !(gOnMtn.auraObjCanEnchant (gOnMtn.object! mtnId) (gOnMtn.object! a2.id)) &&
    !(gAfterSba.battlefield.any (·.id == a2.id)) &&
    (gAfterSba.player p0).graveyard.any (fun id => (gAfterSba.object! id).name == wardAura.name)

/-! ### 7. Migrated Keywords (`Improvise`, `Extort`, `Sneak`), Zemo `Boast`, & Split Second -/

-- `Improvise`, `Extort`, and `Sneak` live on `keywords` (not `staticAbilities`) and
-- expand via `KeywordAbility.expand`; `spellHasImprovise` honors `KeywordAbility.simple .improvise`.
#guard
  let impCard := mustParse "P6 Imp Spell\n{4}{U}\nArtifact\nImprovise"
  let extCard := mustParse "P6 Extort Cleric\n{1}{W}\nCreature — Cleric\n2/2\nExtort"
  let snkCard := mustParse "P6 Sneak Ninja\n{3}{U}\nCreature — Ninja\n3/2\nSneak {1}{U}"
  impCard.staticAbilities.isEmpty &&
    afterDraw.spellHasImprovise impCard p0 &&
    extCard.staticAbilities.isEmpty &&
    !(KeywordAbility.expand (.simple .extort)).triggeredAbilities.isEmpty &&
    snkCard.staticAbilities.isEmpty &&
    !(KeywordAbility.expand (.sneak (CostSpec.ofMana (ManaCost.ofGenericAndColor 1 .blue)))).alternativeCosts.isEmpty

-- Baron Helmut Zemo's Boast lives on `activatedAbilities` (`isBoast`), not
-- `staticAbilities`; `canActivateBoast` is false before attacking and true after.
#guard
  let zemo := mustParse
    "Baron Helmut Zemo\n{2}{B}\nLegendary Creature — Human Villain\n3/3\nBoast — Exile any number of black cards from your graveyard with fifteen or more black mana symbols among their mana costs: Copy those exiled cards. You may cast up to three of the copies without paying their mana costs."
  let g0 := addPermanent afterDraw zemo p0 p0
  let zid := (namedPerm g0 zemo.name).id
  let gAttacked := g0.record
    (GameEvent.attackersDeclared g0.turnNumber p0 #[(g0.snapshot (g0.object! zid), AttackTarget.player p1)])
  zemo.staticAbilities.isEmpty &&
    zemo.activatedAbilities.any ActivatedAbility.isBoast &&
    !(g0.canActivateBoast (g0.object! zid)) &&
    gAttacked.canActivateBoast (gAttacked.object! zid)

-- `instantSorcerySplitSecond` grants `Keyword.splitSecond` to instant/sorcery spells
-- you control on the stack (`g.splitSecondOnStack`), and `losesAbilitiesUntilEot` removes it.
#guard
  let weaver := mkCreature "P6 Split-Second Weaver" #["Wizard"]
    (statics := #[.instantSorcerySplitSecond])
  let g0 := addPermanent afterDraw weaver p0 p0
  let wid := (namedPerm g0 weaver.name).id
  let (g1, boltObj) := addToZone g0 lightningBolt p0 .stack (some p0)
  let g1 := { g1 with stack := g1.stack.push { objectId := boltObj.id, controller := p0, targets := #[] } }
  let gHum := g1.createEffect (.losesAbilitiesUntilEot wid) (cause := some testCause)
  g1.hasSimpleKeyword (g1.object! boltObj.id) .splitSecond &&
    g1.splitSecondOnStack &&
    !(gHum.hasSimpleKeyword (gHum.object! boltObj.id) .splitSecond) &&
    !(gHum.splitSecondOnStack)

/-! ### 8. Novel Compositional Static Abilities Parsed & Executed End-to-End -/

-- Novel Wizard lord: `"Other Wizard creatures you control get +2/+1 and have vigilance and lifelink."`
#guard
  let lord := mustParse
    "Archmage Tutor\n{2}{U}\nCreature — Human Wizard\n2/2\nOther Wizard creatures you control get +2/+1 and have vigilance and lifelink."
  let peerWiz := mkCreature "P6 Peer Wizard" #["Wizard"] (p := 1) (t := 1)
  let peerBear := mkCreature "P6 Peer Bear" #["Bear"] (p := 2) (t := 2)
  let g0 := addPermanent (addPermanent (addPermanent afterDraw lord p0 p0) peerWiz p0 p0) peerBear p0 p0
  let lObj := namedPerm g0 lord.name
  let wObj := namedPerm g0 peerWiz.name
  let bObj := namedPerm g0 peerBear.name
  -- Self is NOT buffed; peer Wizard IS 3/2 with vigilance & lifelink; peer Bear is untouched.
  g0.power lObj == 2 && g0.toughness lObj == 2 && !(g0.hasSimpleKeyword lObj .vigilance) &&
    g0.power wObj == 3 && g0.toughness wObj == 2 &&
    g0.hasSimpleKeyword wObj .vigilance && g0.hasSimpleKeyword wObj .lifelink &&
    g0.power bObj == 2 && g0.toughness bObj == 2 && !(g0.hasSimpleKeyword bObj .lifelink)

-- Novel Goblin cost reducer + Opponent noncreature spell tax parsed via `parseOracleCard`.
#guard
  let reducer := mustParse
    "Goblin Costcutter\n{1}{R}\nCreature — Goblin Shaman\n1/1\nGoblin spells you cast cost {2} less to cast."
  let taxer := mustParse
    "Dampening Arbiter\n{2}{W}\nCreature — Human Advisor\n2/3\nNoncreature spells your opponents cast cost {2} more to cast."
  let goblinSpell := mkCreature "P6 Big Goblin" #["Goblin"] (ManaCost.ofGenericAndColor 3 .red)
  let bearSpell := mkCreature "P6 Plain Bear" #["Bear"] (ManaCost.ofGenericAndColor 3 .green)
  let g0 := addPermanent (addPermanent afterDraw reducer p0 p0) taxer p0 p0
  let (g1, gObj) := addToZone g0 goblinSpell p0 (.hand p0) (some p0)
  let (g2, bObj) := addToZone g1 bearSpell p0 (.hand p0) (some p0)
  let (g3, myBolt) := addToZone g2 lightningBolt p0 (.hand p0) (some p0)
  let (g4, oppBolt) := addToZone g3 lightningBolt p1 (.hand p1) (some p1)
  let (g5, oppBear) := addToZone g4 bearSpell p1 (.hand p1) (some p1)
  g5.playManaCost (g5.object! gObj.id) goblinSpell == ManaCost.ofGenericAndColor 1 .red &&
    g5.playManaCost (g5.object! bObj.id) bearSpell == ManaCost.ofGenericAndColor 3 .green &&
    g5.playManaCost (g5.object! myBolt.id) lightningBolt == ManaCost.ofColor .red &&
    g5.playManaCost (g5.object! oppBolt.id) lightningBolt ==
      lightningBolt.manaCost.addCost (ManaCost.ofGeneric 2) &&
    g5.playManaCost (g5.object! oppBear.id) bearSpell == ManaCost.ofGenericAndColor 3 .green

-- Novel conditional Dragon buff: `"As long as you control a Dragon, this creature gets +3/+3 and has flying and trample."`
#guard
  let warden := mustParse
    "Dragonkin Warden\n{2}{R}\nCreature — Human Warrior\n2/2\nAs long as you control a Dragon, this creature gets +3/+3 and has flying and trample."
  let dragon := mkCreature "P6 Ally Dragon" #["Dragon"]
  let gNo := addPermanent afterDraw warden p0 p0
  let gYes := addPermanent gNo dragon p0 p0
  let wNo := namedPerm gNo warden.name
  let wYes := namedPerm gYes warden.name
  gNo.power wNo == 2 && gNo.toughness wNo == 2 && !(gNo.hasSimpleKeyword wNo .flying) &&
    gYes.power wYes == 5 && gYes.toughness wYes == 5 &&
    gYes.hasSimpleKeyword wYes .flying && gYes.hasSimpleKeyword wYes .trample

-- Novel 3x token multiplier: `"If one or more tokens would be created under your control, three times that many of those tokens are created instead."`
#guard
  let tripler := mustParse
    "Tripling Procession\n{4}{W}\nEnchantment\nIf one or more tokens would be created under your control, three times that many of those tokens are created instead."
  let g0 := addPermanent afterDraw tripler p0 p0
  let (g1, _) := g0.createToken p0 bearToken
  (g1.battlefield.filter (·.name == bearToken.name)).size == 3

-- Novel player protection parsed via `parseOracleCard`: `"You have protection from red."`
#guard
  let ward := mustParse
    "Circle of Ember Ward\n{1}{W}\nEnchantment\nYou have protection from red."
  let greenSpell : CardDef := {
    name := "P6 Green Instant"
    manaCost := ManaCost.ofColor .green
    types := #[.instant]
  }
  let g0 := addPermanent afterDraw ward p0 p0
  let (g1, redSrc) := addToZone g0 lightningBolt p1 .stack (some p1)
  let (g2, greenSrc) := addToZone g1 greenSpell p1 .stack (some p1)
  !(g2.playerCanBeTargetedBy p1 p0 (some redSrc.id)) &&
    g2.playerCanBeTargetedBy p1 p0 (some greenSrc.id)

-- Catalog Null Summoner `renderFullOracle` round-trip preserves `castExiledWithSevenInGraveyard`.
#guard
  match parseOracleCard (renderFullOracle nullSummoner) with
  | .ok d => d.staticAbilities == nullSummoner.staticAbilities &&
      d.staticAbilities.contains .castExiledWithSevenInGraveyard
  | .error _ => false

-- Novel Layer 7a CDAs with `.aggregate .sum (.stat .power)` and `.aggregate .max (.stat .power)`
-- evaluate cycle-safely (including counters on other creatures!) instead of returning 0 or count.
#guard
  let sumAvatar := mustParse
    "Total Power Avatar\n{3}{G}\nCreature — Avatar\n*/2\nTotal Power Avatar's power is equal to the total power of creatures you control."
  let maxAvatar := mustParse
    "Greatest Power Avatar\n{3}{G}\nCreature — Avatar\n*/2\nGreatest Power Avatar's power is equal to the greatest power among creatures you control."
  let bear := mkCreature "P6 Stat Bear" #["Bear"] (p := 2) (t := 2)
  let giant := mkCreature "P6 Stat Giant" #["Giant"] (p := 3) (t := 3)
  let g0 := addPermanent (addPermanent afterDraw bear p0 p0) giant p0 p0
  let giantId := (namedPerm g0 giant.name).id
  -- Put a +1/+1 counter on Giant so its power is 4 (Bear = 2, Giant = 4).
  let g1 := g0.record (GameEvent.rules g0.turnNumber
    (.permanent (.counters (.object (g0.snapshot (g0.object! giantId))) .plusOnePlusOne (.put 1) none))
    (.gameRule .staticAbility))
  let gSum := addPermanent g1 sumAvatar p0 p0
  let gMax := addPermanent g1 maxAvatar p0 p0
  let sumObj := namedPerm gSum sumAvatar.name
  let maxObj := namedPerm gMax maxAvatar.name
  -- Bear (2) + Giant (4) + self (0 while undetermined) = 6; max(2, 4, 0) = 4.
  gSum.power sumObj == 6 && gSum.toughness sumObj == 2 &&
    gMax.power maxObj == 4 && gMax.toughness maxObj == 2

-- Layer 7c `.objectStat`, `.aggregate .min`, and `.aggregate .countDistinct` over `.stat .power`.
#guard
  let creaturesYouCtrl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])
  let minPump : StaticAbility :=
    .continuous none StaticAbility.scopeSelf
      (.modifyPT (.aggregate .min (.stat .power) creaturesYouCtrl) (.const 0))
  let distinctPump : StaticAbility :=
    .continuous none StaticAbility.scopeSelf
      (.modifyPT (.aggregate .countDistinct (.stat .power) creaturesYouCtrl) (.const 0))
  let equipHostPower : StaticAbility :=
    .continuous none StaticAbility.scopeEquippedCreature
      (.modifyPT (.objectStat .power .attachedHost) (.const 0))
  let minCreature := mkCreature "P6 Min Pump" #["Elf"] (p := 1) (t := 1) (statics := #[minPump])
  let distCreature := mkCreature "P6 Distinct Pump" #["Elf"] (p := 1) (t := 1) (statics := #[distinctPump])
  let powerSword : CardDef := {
    name := "P6 Power Doubler Sword"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[equipHostPower]
  }
  let bear1 := mkCreature "P6 Bear A" #["Bear"] (p := 2) (t := 2)
  let bear2 := mkCreature "P6 Bear B" #["Bear"] (p := 2) (t := 2)
  let giant := mkCreature "P6 Giant C" #["Giant"] (p := 5) (t := 5)
  let g0 := addPermanent (addPermanent (addPermanent afterDraw bear1 p0 p0) bear2 p0 p0) giant p0 p0
  let gMin := addPermanent g0 minCreature p0 p0
  let gDist := addPermanent g0 distCreature p0 p0
  -- For gMin: powers among creatures are 2, 2, 5, and self base 1 -> min = 1, so 1 + 1 = 2.
  -- For gDist: distinct powers are {2, 5, 1} -> countDistinct = 3, so 1 + 3 = 4.
  let bear1Id := (namedPerm g0 bear1.name).id
  let (gEq, _) := g0.allocObject powerSword p0 .battlefield (some p0) (attachedTo := some bear1Id)
  -- Attached to 2/2 Bear A: `.objectStat .power .attachedHost` sees Bear A's base 2 -> 2 + 2 = 4.
  gMin.power (namedPerm gMin minCreature.name) == 2 &&
    gDist.power (namedPerm gDist distCreature.name) == 4 &&
    gEq.power (gEq.object! bear1Id) == 4

-- Layer 6/7c conditions: `.eventOccurredLastTurn`, this-turn `.gainedLife`, and `.castPred (.wasKicked .this)`.
#guard
  let mourning := mustParse
    "Mourning Banner\n{2}{B}\nEnchantment\nAs long as a creature died last turn, creatures you control get +1/+1."
  let chorus := mustParse
    "Soul Chorus\n{2}{W}\nEnchantment\nAs long as you gained life this turn, creatures you control get +1/+1."
  let kickedLord := mkCreature "P6 Kicked Champion" #["Knight"] (p := 2) (t := 2)
    (statics := #[
      .continuous (some (.castPred (.wasKicked .this))) StaticAbility.scopeSelf
        (.all #[.modifyPT (.const 2) (.const 2), .grantKeywords #[Keyword.vigilance]])
    ])
  let bear := mkCreature "P6 Cond Bear" #["Bear"] (p := 2) (t := 2)
  let fodder := mkCreature "P6 Dying Fodder" #["Goblin"] (p := 1) (t := 1)
  -- 1. Last-turn creature death: off on turn 1 when fodder dies, ON on turn 2, OFF on turn 3.
  let g0 := addPermanent (addPermanent (addPermanent afterDraw mourning p0 p0) bear p0 p0) fodder p0 p0
  let fodderId := (namedPerm g0 fodder.name).id
  let (gDiedT1, _) := g0.move fodderId (.graveyard p0) none (verb := some .destroy) (cause := some testCause)
  let gTurn2 := gDiedT1.record (GameEvent.turnBegan (gDiedT1.turnNumber + 1) p1 false)
  let gTurn3 := gTurn2.record (GameEvent.turnBegan (gTurn2.turnNumber + 1) p0 false)
  let b1 := namedPerm gDiedT1 bear.name
  let b2 := namedPerm gTurn2 bear.name
  let b3 := namedPerm gTurn3 bear.name
  -- 2. This-turn life gain: off before `gainLife`, ON after `gainLife`.
  let gLife0 := addPermanent (addPermanent afterDraw chorus p0 p0) bear p0 p0
  let gLife1 := gLife0.gainLife p0 2
  -- 3. `.castPred (.wasKicked .this)`: off when un-kicked, ON when cast kicked.
  let gKick0 := addPermanent afterDraw kickedLord p0 p0
  let kickId := (namedPerm gKick0 kickedLord.name).id
  let gKick1 := gKick0.record (GameEvent.rules gKick0.turnNumber
    (.cast (.announced kickId #[] none #[.kicker])) testCause)
  gDiedT1.power b1 == 2 &&
    gTurn2.power b2 == 3 && gTurn2.toughness b2 == 3 &&
    gTurn3.power b3 == 2 &&
    gLife0.power (namedPerm gLife0 bear.name) == 2 &&
    gLife1.power (namedPerm gLife1 bear.name) == 3 &&
    gKick0.power (gKick0.object! kickId) == 2 && !(gKick0.hasSimpleKeyword (gKick0.object! kickId) .vigilance) &&
    gKick1.power (gKick1.object! kickId) == 4 && gKick1.hasSimpleKeyword (gKick1.object! kickId) .vigilance

-- Keyword predicates (`.hasKeyword`, `.not (.hasKeyword ...)`) in CDAs, Layer 6/7c scopes,
-- and static conditions, including CR 613.8 dependency on flying counters and Equipment.
#guard
  let skyAvatar := mustParse
    "Sky Power Avatar\n{3}{U}\nCreature — Avatar\n*/2\nSky Power Avatar's power is equal to the total power of creatures you control with flying."
  let grounded := mustParse
    "Grounded Sanctuary\n{2}{G}\nEnchantment\nCreatures you control without flying get +1/+1 and have hexproof."
  let skywatch := mustParse
    "Skywatch Banner\n{2}{W}\nEnchantment\nAs long as you control a creature with flying, creatures you control get +1/+1 and have vigilance."
  let flyBoots : CardDef := {
    name := "P6 Winged Boots"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[.continuous none StaticAbility.scopeEquippedCreature (.grantKeywords #[Keyword.flying])]
  }
  let bear := mkCreature "P6 Ground Bear" #["Bear"] (p := 2) (t := 2)
  let hawk := mkCreature "P6 Sky Hawk" #["Bird"] (p := 3) (t := 2) (kws := #[Keyword.flying])
  -- 1. CDA "total power of creatures you control with flying": Bear (2, no flying) excluded, Hawk (3, flying) included -> 3.
  let gAv0 := addPermanent (addPermanent (addPermanent afterDraw bear p0 p0) hawk p0 p0) skyAvatar p0 p0
  let bearAvId := (namedPerm gAv0 bear.name).id
  let (gAvEq, _) := gAv0.allocObject flyBoots p0 .battlefield (some p0) (attachedTo := some bearAvId)
  -- After equipping Bear with Winged Boots, Bear has flying -> total flying power = 3 + 2 = 5.
  -- 2. "Creatures you control without flying get +1/+1 and have hexproof":
  let gGr0 := addPermanent (addPermanent (addPermanent afterDraw grounded p0 p0) bear p0 p0) hawk p0 p0
  let grBearId := (namedPerm gGr0 bear.name).id
  let grHawkId := (namedPerm gGr0 hawk.name).id
  -- Put a flying counter on Bear -> CR 613.8 dependency removes both hexproof and +1/+1.
  let gGrFly := gGr0.record (GameEvent.rules gGr0.turnNumber
    (.permanent (.counters (.object (gGr0.snapshot (gGr0.object! grBearId))) .flying (.put 1) none))
    (.gameRule .staticAbility))
  -- 3. "As long as you control a creature with flying, creatures you control get +1/+1 and have vigilance":
  let gSw0 := addPermanent (addPermanent afterDraw skywatch p0 p0) bear p0 p0
  let swBearId := (namedPerm gSw0 bear.name).id
  let gSwFly := gSw0.record (GameEvent.rules gSw0.turnNumber
    (.permanent (.counters (.object (gSw0.snapshot (gSw0.object! swBearId))) .flying (.put 1) none))
    (.gameRule .staticAbility))
  let gSwHawk := addPermanent gSw0 hawk p0 p0
  gAv0.power (namedPerm gAv0 skyAvatar.name) == 3 &&
    gAvEq.power (namedPerm gAvEq skyAvatar.name) == 5 &&
    gGr0.power (gGr0.object! grBearId) == 3 && gGr0.hasKeyword (gGr0.object! grBearId) (· == Keyword.hexproof) &&
    gGr0.power (gGr0.object! grHawkId) == 3 && !(gGr0.hasKeyword (gGr0.object! grHawkId) (· == Keyword.hexproof)) &&
    gGrFly.power (gGrFly.object! grBearId) == 2 && !(gGrFly.hasKeyword (gGrFly.object! grBearId) (· == Keyword.hexproof)) &&
    gSw0.power (gSw0.object! swBearId) == 2 && !(gSw0.hasSimpleKeyword (gSw0.object! swBearId) .vigilance) &&
    gSwFly.power (gSwFly.object! swBearId) == 3 && gSwFly.hasSimpleKeyword (gSwFly.object! swBearId) .vigilance &&
    gSwHawk.power (gSwHawk.object! swBearId) == 3 && gSwHawk.hasSimpleKeyword (gSwHawk.object! swBearId) .vigilance

-- Layer 7c cycle breaking preserves +1/+1 counters and non-dependent static pumps (CR 613.7 / 613.8).
#guard
  let equipHostPower : StaticAbility :=
    .continuous none StaticAbility.scopeEquippedCreature
      (.modifyPT (.objectStat .power .attachedHost) (.const 0))
  let powerSword : CardDef := {
    name := "P6 Counter-Aware Power Sword"
    types := #[.artifact]
    subtypes := #["Equipment"]
    staticAbilities := #[equipHostPower]
  }
  let anthem := mustParse
    "P6 Honor Banner\n{1}{W}\nEnchantment\nCreatures you control get +1/+1."
  let bear := mkCreature "P6 Counter Bear" #["Bear"] (p := 2) (t := 2)
  let g0 := addPermanent afterDraw bear p0 p0
  let bearId := (namedPerm g0 bear.name).id
  -- Put a +1/+1 counter on Bear (power 3 before Equipment).
  let g1 := g0.record (GameEvent.rules g0.turnNumber
    (.permanent (.counters (.object (g0.snapshot (g0.object! bearId))) .plusOnePlusOne (.put 1) none))
    (.gameRule .staticAbility))
  let (gEq, _) := g1.allocObject powerSword p0 .battlefield (some p0) (attachedTo := some bearId)
  -- 2/2 + 1/1 counter = 3/3 -> Sword adds +3/+0 -> 6/3 (not 5/3!).
  let gEqAnthem := addPermanent gEq anthem p0 p0
  -- With Anthem (+1/+1) applying first: 2/2 + 1/1 counter + 1/1 anthem = 4/4 -> Sword adds +4/+0 -> 8/4!
  -- Also test `min` self-pump with a +1/+1 counter on `minCreature` (1/1 + counter = 2/2).
  let creaturesYouCtrl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])
  let minCreature := mkCreature "P6 Counter Min Pump" #["Elf"] (p := 1) (t := 1)
    (statics := #[.continuous none StaticAbility.scopeSelf
      (.modifyPT (.aggregate .min (.stat .power) creaturesYouCtrl) (.const 0))])
  let giant := mkCreature "P6 Giant D" #["Giant"] (p := 5) (t := 5)
  let gMin0 := addPermanent (addPermanent (addPermanent afterDraw bear p0 p0) giant p0 p0) minCreature p0 p0
  let minId := (namedPerm gMin0 minCreature.name).id
  let gMin1 := gMin0.record (GameEvent.rules gMin0.turnNumber
    (.permanent (.counters (.object (gMin0.snapshot (gMin0.object! minId))) .plusOnePlusOne (.put 1) none))
    (.gameRule .staticAbility))
  -- Pre-static powers: Bear=2, Giant=5, minCreature=2 -> min=2 -> 2 + 2 = 4.
  gEq.power (gEq.object! bearId) == 6 && gEq.toughness (gEq.object! bearId) == 3 &&
    gEqAnthem.power (gEqAnthem.object! bearId) == 8 && gEqAnthem.toughness (gEqAnthem.object! bearId) == 4 &&
    gMin1.power (gMin1.object! minId) == 4

-- Post-Layer-7 callers (`entersWithCounters` and combat-rule conditions) evaluate full P/T
-- including counters, pumps, and CDAs rather than printed box values.
#guard
  let creaturesYouCtrl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])
  let powerHydra := mkCreature "P6 Power Hydra" #["Hydra"] (p := 0) (t := 0)
    (statics := #[
      StaticAbility.entersWithCounters .plusOnePlusOne
        (.aggregate .sum (.stat .power) creaturesYouCtrl)
    ])
  let landCda := mkCreature "P6 Land Avatar" #["Elemental"] (p := 0) (t := 2)
    (statics := #[StaticAbility.powerToughnessEqualLandsYouControl])
  let bear := mkCreature "P6 Buffed Bear" #["Bear"] (p := 2) (t := 2)
  let forest : CardDef := { name := "P6 Forest", types := #[.land], subtypes := #["Forest"] }
  let g0 := addPermanent (addPermanent (addPermanent (addPermanent (addPermanent afterDraw bear p0 p0)
    landCda p0 p0) forest p0 p0) forest p0 p0) forest p0 p0
  let bearId := (namedPerm g0 bear.name).id
  -- Put two +1/+1 counters on Bear -> Bear power = 4; Land Avatar power = 3 -> total = 7.
  let g1 := g0.record (GameEvent.rules g0.turnNumber
    (.permanent (.counters (.object (g0.snapshot (g0.object! bearId))) .plusOnePlusOne (.put 2) none))
    (.gameRule .staticAbility))
  let (g2, hydraObj) := g1.allocObject powerHydra p0 (.hand p0)
  let etb := g2.applyEtbReplacements { hydraObj with controller := some p0 }
  -- Combat-rule condition checking evaluated power >= 4 on another creature:
  let stalker := mkCreature "P6 Ferocious Stalker" #["Rogue"] (p := 1) (t := 1)
    (statics := #[
      .ruleModifying
        (some (.exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .stat .power .ge (.const 4)]))))
        (.combat (.cantBeBlocked .self))
    ])
  let gSt0 := addPermanent (addPermanent afterDraw bear p0 p0) stalker p0 p0
  let stBearId := (namedPerm gSt0 bear.name).id
  let gSt1 := gSt0.record (GameEvent.rules gSt0.turnNumber
    (.permanent (.counters (.object (gSt0.snapshot (gSt0.object! stBearId))) .plusOnePlusOne (.put 2) none))
    (.gameRule .staticAbility))
  etb.entersWith.count .plusOnePlusOne == 7 &&
    !(gSt0.hasCantBeBlocked (namedPerm gSt0 stalker.name)) &&
    gSt1.hasCantBeBlocked (namedPerm gSt1 stalker.name)

-- Defending player predicates (`PlayerPred.isDefendingPlayer` and `PlayerExpr.defendingPlayer`).
#guard
  let defAnthem := mustParse
    "Defender's Anthem\n{2}{W}\nEnchantment\nCreatures the defending player controls get +1/+1."
  let defAvatar := mustParse
    "Defending Life Avatar\n{4}{B}\nCreature — Avatar\n*/2\nDefending Life Avatar's power is equal to the defending player's life total."
  let myBear := mkCreature "P6 Active Bear" #["Bear"] (p := 2) (t := 2)
  let oppBear := mkCreature "P6 Defending Bear" #["Bear"] (p := 2) (t := 2)
  let g0 := addPermanent (addPermanent (addPermanent (addPermanent afterDraw defAnthem p0 p0)
    defAvatar p0 p0) myBear p0 p0) oppBear p1 p1
  -- Set defending player (p1) life to 17 while active player (p0) has 20.
  let g1 := g0.loseLife p1 3
  -- Active player's bear is 2/2, defending player's bear gets +1/+1 (3/3), avatar power = 17.
  g1.power (namedPerm g1 myBear.name) == 2 &&
    g1.power (namedPerm g1 oppBear.name) == 3 &&
    g1.power (namedPerm g1 defAvatar.name) == 17

-- Exhaustive `ObjectPred` atoms: `.statParity` (with counter-aware Layer 7c `predReadsPT`),
-- `.attackedThisTurn`, `.wasCast`/`.castFrom`, `.combatRole` (`attackingAlone`/`attackingPlayer`/
-- `blockingObject`), `.shares`, general `.attachedTo`, and `.hasColor .commanderIdentity`.
#guard
  let evenPump : CardDef := {
    name := "P6 Even Power Anthem"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .statParity .power .even]))
        (.modifyPT (.const 2) (.const 0))
    ]
  }
  let bear := mkCreature "P6 Parity Bear" #["Bear"] (p := 2) (t := 2)
  let gPar0 := addPermanent (addPermanent afterDraw evenPump p0 p0) bear p0 p0
  let parBearId := (namedPerm gPar0 bear.name).id
  -- 2/2 Bear has even power (2) -> gets +2/+0 -> 4/2.
  -- With a +1/+1 counter, pre-static power is 3 (odd!) -> loses +2/+0 -> 3/3!
  let gPar1 := gPar0.record (GameEvent.rules gPar0.turnNumber
    (.permanent (.counters (.object (gPar0.snapshot (gPar0.object! parBearId))) .plusOnePlusOne (.put 1) none))
    (.gameRule .staticAbility))
  -- `.attackedThisTurn` and `.combatRole .attackingAlone` / `.attackingPlayer` / `.blockingObject`:
  let atkBuff : CardDef := {
    name := "P6 Attack Tracker"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .attackedThisTurn]))
        (.modifyPT (.const 1) (.const 0)),
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .combatRole .attackingAlone]))
        (.modifyPT (.const 2) (.const 0)),
      .continuous none (.onBattlefield (.all #[.hasType .creature, .combatRole (.attackingPlayer .defendingPlayer)]))
        (.modifyPT (.const 1) (.const 0))
    ]
  }
  let bear2 := mkCreature "P6 Second Attacker" #["Bear"] (p := 2) (t := 2)
  let gAtk0 := addPermanent (addPermanent (addPermanent afterDraw atkBuff p0 p0) bear p0 p0) bear2 p0 p0
  let a1Id := (namedPerm gAtk0 bear.name).id
  let a2Id := (namedPerm gAtk0 bear2.name).id
  let a1Snap := gAtk0.snapshot (gAtk0.object! a1Id)
  let gAtk1 := { gAtk0.record (GameEvent.rules gAtk0.turnNumber
    (.combat (.attackersDeclared p0 #[(a1Snap, .player p1)])) testCause) with
    objects := gAtk0.objects.map fun (o : GameObject) =>
      if o.id == a1Id then { o with status := { o.status with attacking := true, attackingTarget := some (.player p1) } }
      else o }
  -- a1 attacked alone targeting p1: +1 (attackedThisTurn) +2 (attackingAlone) +1 (attackingPlayer) = 2 + 4 = 6.
  let gAtk2 : Game := { gAtk1 with
    objects := gAtk1.objects.map fun (o : GameObject) =>
      if o.id == a2Id then { o with status := { o.status with attacking := true, attackingTarget := some (.player p1) } }
      else o }
  -- With a2 also attacking, a1 is no longer attacking alone: 2 + 1 + 1 = 4.
  -- `.combatRole (.blockingObject ...)`:
  let blkBuff : CardDef := {
    name := "P6 Blocker Tracker"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .combatRole (.blockingObject (.inZones .battlefield (.hasType .creature)))]))
        (.modifyPT (.const 3) (.const 0))
    ]
  }
  let oppBlk := mkCreature "P6 Opp Blocker" #["Soldier"] (p := 1) (t := 3)
  let gBlk0 := addPermanent (addPermanent gAtk1 blkBuff p0 p0) oppBlk p1 p1
  let blkId := (namedPerm gBlk0 oppBlk.name).id
  let gBlk1 : Game := { gBlk0 with
    objects := gBlk0.objects.map fun (o : GameObject) =>
      if o.id == blkId then { o with status := { o.status with blocking := #[a1Id] } }
      else o }
  -- `.shares .creatureType .this`, general `.attachedTo`, `.castFrom .exile` / `.wasCast`, and `.hasColor .commanderIdentity`:
  let tribalElf := mkCreature "P6 Tribal Elf" #["Elf"] (p := 1) (t := 1)
    (statics := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .otherThan .this, .shares .creatureType .this]))
        (.modifyPT (.const 1) (.const 1))
    ])
  let peerElf := mkCreature "P6 Peer Elf" #["Elf"] (p := 2) (t := 2)
  let gTri := addPermanent (addPermanent (addPermanent afterDraw tribalElf p0 p0) peerElf p0 p0) bear p0 p0
  let castExileAnthem : CardDef := {
    name := "P6 Exile Cast Anthem"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .wasCast, .castFrom .exile]))
        (.modifyPT (.const 2) (.const 2))
    ]
  }
  let gEx0 := addPermanent (addPermanent afterDraw castExileAnthem p0 p0) bear p0 p0
  let exBear := namedPerm gEx0 bear.name
  let exSnap := gEx0.snapshot exBear
  let gEx1 := gEx0.record (GameEvent.rules gEx0.turnNumber
    (.cast (.spellCast exSnap p0 .exile)) testCause)
  let attCheck : CardDef := {
    name := "P6 Attached Aura Watcher"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous (some (.exists (.inZones .battlefield (.all #[.hasSubtype (.literal .aura),
          .attachedTo (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))]))))
        (.onBattlefield (.all #[.hasType .creature, .controlledBy .you]))
        (.modifyPT (.const 1) (.const 1))
    ]
  }
  let dummyAura : CardDef := { name := "P6 Dummy Aura", types := #[.enchantment], subtypes := #["Aura"] }
  let gAtt0 := addPermanent (addPermanent afterDraw attCheck p0 p0) bear p0 p0
  let attBearId := (namedPerm gAtt0 bear.name).id
  let (gAtt1, _) := gAtt0.allocObject dummyAura p0 .battlefield (some p0) (attachedTo := some attBearId)
  let cmdAnthem : CardDef := {
    name := "P6 Identity Anthem"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you, .hasColor .commanderIdentity]))
        (.modifyPT (.const 2) (.const 0))
    ]
  }
  let redGob : CardDef := { name := "P6 Red Gob", manaCost := ManaCost.ofColor .red, types := #[.creature], subtypes := #["Goblin"], power := some (.fixed 1), toughness := some (.fixed 1) }
  let blueFish : CardDef := { name := "P6 Blue Fish", manaCost := ManaCost.ofColor .blue, types := #[.creature], subtypes := #["Fish"], power := some (.fixed 1), toughness := some (.fixed 1) }
  let gCmd0 := addPermanent (addPermanent (addPermanent afterDraw cmdAnthem p0 p0) redGob p0 p0) blueFish p0 p0
  let gCmd1 : Game := { gCmd0 with
    players := gCmd0.players.map fun (pl : Player) =>
      if pl.id == p0 then { pl with hasCommander := true, commanderColorIdentity := ColorSet.singleton .red } else pl }
  gPar0.power (gPar0.object! parBearId) == 4 &&
    gPar1.power (gPar1.object! parBearId) == 3 &&
    gAtk0.power (gAtk0.object! a1Id) == 2 &&
    gAtk1.power (gAtk1.object! a1Id) == 6 &&
    gAtk2.power (gAtk2.object! a1Id) == 4 &&
    gBlk0.power (gBlk0.object! blkId) == 1 &&
    gBlk1.power (gBlk1.object! blkId) == 4 &&
    gTri.power (namedPerm gTri peerElf.name) == 3 &&
    gTri.power (namedPerm gTri bear.name) == 2 &&
    gEx0.power exBear == 2 &&
    gEx1.power (gEx1.object! exBear.id) == 4 &&
    gAtt0.power (gAtt0.object! attBearId) == 2 &&
    gAtt1.power (gAtt1.object! attBearId) == 3 &&
    gCmd1.power (namedPerm gCmd1 redGob.name) == 3 &&
    gCmd1.power (namedPerm gCmd1 blueFish.name) == 1

-- `.dealtDamageThisTurn` recipient filtering (opponent vs. creature vs. self) and
-- non-combat across-turns tracking (`thisTurnOnly = false`).
#guard
  let oppDmgBuff : CardDef := {
    name := "P6 Opp Combat Damage Anthem"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you,
          .dealtDamageThisTurn true (some (.player .opponent)) true]))
        (.modifyPT (.const 2) (.const 2))
    ]
  }
  let anyEverDmgBuff : CardDef := {
    name := "P6 Ever Dealt Damage Anthem"
    types := #[.enchantment]
    staticAbilities := #[
      .continuous none (.onBattlefield (.all #[.hasType .creature, .controlledBy .you,
          .dealtDamageThisTurn false none false]))
        (.modifyPT (.const 1) (.const 1))
    ]
  }
  let bear := mkCreature "P6 Damage Bear" #["Bear"] (p := 2) (t := 2)
  let targetCreature := mkCreature "P6 Dummy Target" #["Wall"] (p := 0) (t := 5)
  let g0 := addPermanent (addPermanent (addPermanent afterDraw oppDmgBuff p0 p0) bear p0 p0) targetCreature p1 p1
  let bearObj := namedPerm g0 bear.name
  let bearSnap := g0.snapshot bearObj
  let wallSnap := g0.snapshot (namedPerm g0 targetCreature.name)
  -- Combat damage dealt to a creature (not an opponent) -> must NOT match!
  let gToWall := g0.record (GameEvent.rules g0.turnNumber
    (.damage (.dealt #[{ source := bearSnap, recipient := .permanent wallSnap, amount := 2, combat := true }]))
    testCause)
  -- Combat damage dealt to yourself (not an opponent) -> must NOT match!
  let gToYou := g0.record (GameEvent.rules g0.turnNumber
    (.damage (.dealt #[{ source := bearSnap, recipient := .player p0, amount := 2, combat := true }]))
    testCause)
  -- Combat damage dealt to opponent p1 -> MUST match!
  let gToOpp := g0.record (GameEvent.rules g0.turnNumber
    (.damage (.dealt #[{ source := bearSnap, recipient := .player p1, amount := 2, combat := true }]))
    testCause)
  -- Non-combat damage dealt on turn 1 stays matched on turn 2 when `thisTurnOnly = false`:
  let gEver0 := addPermanent (addPermanent afterDraw anyEverDmgBuff p0 p0) bear p0 p0
  let everBear := namedPerm gEver0 bear.name
  let gEver1 := gEver0.record (GameEvent.rules gEver0.turnNumber
    (.damage (.dealt #[{ source := gEver0.snapshot everBear, recipient := .player p1, amount := 1, combat := false }]))
    testCause)
  let gEverT2 := gEver1.record (GameEvent.turnBegan (gEver1.turnNumber + 1) p1 false)
  gToWall.power (gToWall.object! bearObj.id) == 2 &&
    gToYou.power (gToYou.object! bearObj.id) == 2 &&
    gToOpp.power (gToOpp.object! bearObj.id) == 4 &&
    gEver0.power everBear == 2 &&
    gEverT2.power (gEverT2.object! everBear.id) == 3

end Mtg.Engine.Tests.StaticAbilitiesSuite
