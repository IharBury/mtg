import Mtg.Engine.Tests.Helpers

/-!
# Phase 2 Expression Algebra, Stage-4 Sub-Grammars, and `EvalExpr` Tests

Comprehensive `#guard` regression suite for Phase 2 of `ABILITY_ALIGNMENT_PLAN.md`:
1. Stage-4 expression parsers (`parseNounPhrase`, `parseValueExpr`,
   `parseCondition`, `parseDuration`) and canonical `ToOracle` round-trips.
2. Live Layer 1–7d evaluation in `Game/EvalExpr.lean` (`PlayerFilter`/`PlayerExpr`,
   `ObjectPred`/`ObjectFilter`/`ObjectExpr`, `ValueExpr`, `Condition`,
   `DurationExpr`, `LibraryPosSpec`).
3. CR 603.10 / CR 608.2h LKI & `GameSnapshot` look-back evaluation.
4. Generalized `TokenSpec` (dynamic `ValueExpr` P/T and `ObjectExpr` `copyOf`)
   and generalized `ManaSpec` / `ManaPoolPalette` (`Game.evalManaSpec`, CR 106.7).
-/

namespace Mtg.Engine.Tests.EvalExprSuite

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Parser
open Mtg.Engine.Tests

/-! ### 1. Stage-4 Compositional Expression Parsers & `ToOracle` Round-Trips -/

-- `parseNounPhrase` across quantifiers, `target`, status, colors, supertypes, subtypes,
-- types, controllers, zones, `with`/`without` clauses, and `that` history/relation clauses.
#guard
  match parseNounPhrase "another tapped nontoken green legendary Elf creature you control with power 4 or greater" with
  | some np =>
    np.quantifier == .singular && !np.isTarget && np.filter.zones == .battlefield &&
    np.filter.pred == .all #[
      .otherThan .this, .tapped true, .isToken false, .hasColor (.literal .green),
      .hasSupertype .legendary, .hasSubtype (.literal .elf), .hasType .creature,
      .controlledBy .you, .stat .power .ge (.const 4)
    ]
  | none => false

#guard
  match parseNounPhrase "up to two target untapped artifact or enchantment cards in your graveyard with mana value 3 or less" with
  | some np =>
    np.quantifier == .upTo 2 && np.isTarget && np.filter.zones == .yourGraveyard &&
    np.filter.pred == .all #[
      .tapped false,
      .any #[.hasType .artifact, .hasType .enchantment],
      .stat .manaValue .le (.const 3)
    ]
  | none => false

#guard
  match parseNounPhrase "any number of non-Human Time Lord creatures an opponent controls without flying" with
  | some np =>
    np.quantifier == .anyNumber && !np.isTarget &&
    np.filter.pred == .all #[
      .not (.hasSubtype (.literal .human)),
      .hasSubtype (.literal .timeLord),
      .hasType .creature,
      .controlledBy .opponent,
      .not (.hasKeyword .flying)
    ]
  | none => false

#guard
  match parseNounPhrase "each historic permanent you control with a +1/+1 counter on it that entered this turn" with
  | some np =>
    np.quantifier == .each &&
    np.filter.pred == .all #[
      ObjectPred.historic,
      .controlledBy .you,
      .counterCount (some .plusOnePlusOne) .ge (.const 1),
      .enteredThisTurn
    ]
  | none => false

#guard
  match parseNounPhrase "target multicolored nonland spell on the stack with odd mana value" with
  | some np =>
    np.isTarget && np.filter.zones == .stack &&
    np.filter.pred == .all #[
      .colorCount .ge 2,
      .not (.hasType .land),
      .statParity .manaValue .odd
    ]
  | none => false

#guard
  match parseNounPhrase "a creature that dealt combat damage to an opponent this turn" with
  | some np =>
    np.filter.pred == .all #[
      .hasType .creature,
      .dealtDamageThisTurn true (some (.player .opponent))
    ]
  | none => false

#guard
  match parseNounPhrase "a permanent card in an opponent's graveyard that was cast from exile" with
  | some np =>
    np.filter.zones == .opponentGraveyard &&
    np.filter.pred == .all #[.isPermanentCard, .castFrom .exile]
  | none => false

#guard
  match parseNounPhrase "other Goblin or Orc creatures of the chosen color that share a creature type with this permanent" with
  | some np =>
    np.quantifier == .plural &&
    np.filter.pred == .all #[
      .otherThan .this,
      .any #[.hasSubtype (.literal .goblin), .hasSubtype (.literal .orc)],
      .hasType .creature,
      .hasColor .chosenOnSource,
      .shares .creatureType .this
    ]
  | none => false

#guard
  match parseNounPhrase "white, blue, or black Time Lord or Human creatures" with
  | some np =>
    np.quantifier == .plural &&
    np.filter.pred == .all #[
      .any #[.hasColor (.literal .white), .hasColor (.literal .blue), .hasColor (.literal .black)],
      .any #[.hasSubtype (.literal .timeLord), .hasSubtype (.literal .human)],
      .hasType .creature
    ]
  | none => false

#guard
  match parseNounPhrase "target non-Time Lord creature" with
  | some np =>
    np.isTarget &&
    np.filter.pred == .all #[.not (.hasSubtype (.literal .timeLord)), .hasType .creature]
  | none => false

-- Unrecognized words inside a noun phrase are rejected cleanly.
#guard (parseNounPhrase "target flibbertigibbet creature").isNone

-- Bidirectional `ToOracle` → `parseNounPhrase` round-trips.
#guard
  let fs : Array ObjectFilter := #[
    ObjectFilter.creaturesYouControl,
    ObjectFilter.landsOpponentsControl,
    { zones := .battlefield
      pred := .all #[.otherThan .this, .tapped false, .isToken false, .hasColor (.literal .white),
        .hasSupertype .legendary, .hasSubtype (.literal .human), .hasType .creature,
        .controlledBy .you, .hasKeyword .firstStrike, .stat .power .ge (.const 3)] },
    { zones := .yourGraveyard
      pred := .all #[.any #[.hasType .instant, .hasType .sorcery], .stat .manaValue .le (.const 2)] },
    { zones := .stack
      pred := .all #[.not (.hasType .creature), .statParity .manaValue .even] },
    { zones := .battlefield
      pred := .all #[.hasType .creature, .controlledBy .opponent,
        .counterCount (some .stun) .ge (.const 1), .attackedThisTurn] }
  ]
  fs.all fun f =>
    match parseNounPhrase (toOracleStr f) with
    | some np => np.filter == f
    | none => false

-- `parseValueExpr` and `ToOracle` round-trips.
#guard parseValueExpr "4" == some (.const 4)
#guard parseValueExpr "X" == some .chosenX
#guard parseValueExpr "where X is twice your life total" ==
  some (.binary .mul (.const 2) (.playerMetric .life .you))
#guard parseValueExpr "half the number of cards in your library, rounded down" ==
  some (.binary .divFloor (.playerMetric .librarySize .you) (.const 2))
#guard parseValueExpr "half your life total, rounded up" ==
  some (.binary .divFloor (.binary .add (.playerMetric .life .you) (.const 1)) (.const 2))
#guard parseValueExpr "for each Elf creature you control" ==
  some (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .elf), .hasType .creature, .controlledBy .you])))
#guard parseValueExpr "the greatest power among creatures you control" ==
  some (.aggregate .max (.stat .power) ObjectExpr.creaturesYouControl)
#guard parseValueExpr "the number of different powers among creatures you control" ==
  some (.aggregate .countDistinct (.stat .power) ObjectExpr.creaturesYouControl)
#guard parseValueExpr "the number of basic land types among lands you control" ==
  some (.basicLandTypeCount ObjectExpr.landsYouControl)
#guard parseValueExpr "the number of card types among cards in your graveyard" ==
  some (.cardTypeCount (.inZones .yourGraveyard .anyObject))
#guard parseValueExpr "the number of planeswalker types among planeswalkers you control" ==
  some (.subtypeCount .planeswalker (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])))
#guard parseValueExpr "your devotion to blue" ==
  some (.manaSymbols (some .blue) (.inZones .battlefield (.controlledBy .you)))
#guard parseValueExpr "the number of +1/+1 counters on this permanent plus 2" ==
  some (.binary .add (.counterCount (some .plusOnePlusOne) .this) (.const 2))
#guard parseValueExpr "this permanent's power" == some (.objectStat .power .this)

#guard
  let vs : Array ValueExpr := #[
    .const 5,
    .chosenX,
    .objectStat .power .this,
    .counterCount (some .loyalty) .this,
    .counterCount none (.target 0),
    .aggregate .count .one ObjectExpr.creaturesYouControl,
    .aggregate .sum (.stat .power) ObjectExpr.creaturesYouControl,
    .aggregate .max (.stat .manaValue) (.inZones .yourGraveyard .anyObject),
    .aggregate .min (.stat .toughness) ObjectExpr.creaturesYouControl,
    .aggregate .countDistinct (.stat .power) ObjectExpr.creaturesYouControl,
    .basicLandTypeCount ObjectExpr.landsYouControl,
    .cardTypeCount (.inZones .yourGraveyard .anyObject),
    .subtypeCount .planeswalker (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .you])),
    .playerMetric .life .you,
    .playerMetric .handSize .you,
    .playerMetric .cardsDrawnThisTurn .you,
    .playerMetric .spellsCastThisTurn .you,
    .playerMetric .lifeGainedThisTurn .you,
    .playerMetric .poisonCounters .you,
    .manaSymbols (some .black) (.inZones .battlefield (.controlledBy .you)),
    .binary .mul (.const 2) (.objectStat .power .this),
    .binary .divFloor (.playerMetric .life .you) (.const 2)
  ]
  vs.all fun v => parseValueExpr (toOracleStr v) == some v

-- `parseCondition` and `ToOracle` round-trips.
#guard parseCondition "if you control a legendary creature" ==
  some (.exists (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you])))
#guard parseCondition "as long as you control three or more artifacts" ==
  some (.cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))) (.const 3))
#guard parseCondition "unless it's your turn" == some (.not .isYourTurn)
#guard parseCondition "if you've scried this turn or you've surveilled this turn" ==
  some (.any #[.turnHistory (.scriedThisTurn .you), .turnHistory (.surveilledThisTurn .you)])
#guard parseCondition "if a creature died this turn" ==
  some (.turnHistory (.eventOccurredThisTurn .any (.permanentDied (.hasType .creature))))
#guard parseCondition "if an opponent was dealt noncombat damage last turn" ==
  some (.turnHistory (.eventOccurredLastTurn .opponent (.dealtDamage false true)))
#guard parseCondition "if you have 5 or less life" ==
  some (.cmp .le (.playerMetric .life .you) (.const 5))
#guard parseCondition "if you have 7 or more cards in your graveyard" ==
  some (.cmp .ge (.playerMetric .graveyardSize .you) (.const 7))

#guard
  let cs : Array Condition := #[
    .isYourTurn,
    .not .isYourTurn,
    .isNight,
    .not .isNight,
    .duringStep .upkeep,
    .duringPhase .combat,
    .playerPred .you (.hasDesignation .citysBlessing),
    .playerPred .you (.hasDesignation .enduringStory),
    .playerPred .you .isMonarch,
    .castPred (.wasKicked .this),
    .castPred (.giftPromised .this),
    .castPred (.impendingPaid .this),
    .castPred (.castFrom .graveyard .this),
    .castPred (.manaSpentMatches .fromTreasure .this),
    .turnHistory (.scriedThisTurn .you),
    .turnHistory (.surveilledThisTurn .you),
    .turnHistory (.eventOccurredThisTurn .any (.permanentDied (.hasType .creature))),
    .turnHistory (.eventOccurredThisTurn .you (.permanentEntered (.hasType .artifact))),
    .turnHistory (.eventOccurredThisTurn .you (.attackedWith (.hasSubtype (.literal .hero)))),
    .turnHistory (.eventOccurredLastTurn .opponent (.dealtDamage false true)),
    .cmp .ge (.playerMetric .cardsDrawnThisTurn .you) (.const 3),
    .all #[.isYourTurn, .playerPred .you .isMonarch]
  ]
  cs.all fun c => parseCondition (toOracleStr c) == some c

-- `parseDuration` across all 11 `DurationExpr` constructors and `ToOracle` round-trips.
#guard
  let ds : Array DurationExpr := #[
    .untilEndOfTurn,
    .untilEndOfCombat,
    .untilEndOfStepOrPhase (.step .upkeep),
    .untilEndOfStepOrPhase (.phase .combat),
    .untilStepOrPhase (.step .declareAttackers),
    .untilStepOrPhase (.phase .ending),
    .untilNextTurnOf .you,
    .untilNextTurnOf (.target 0),
    .untilEndOfNextTurnOf .you,
    .whileOnBattlefield .this,
    .untilLeavesBattlefield .this,
    .whileHasCounter .this .time,
    .whileInZone .triggerSubject .exile,
    .whileInZone .this .graveyard,
    .indefinite
  ]
  ds.all fun d => parseDuration (toOracleStr d) == some d

/-! ### 2. Live, LKI (`EventObject` / `GameSnapshot`), TokenSpec, and ManaSpec Evaluation -/

private def elf22 : CardDef := {
  name := "Test Elf"
  manaCost := ManaCost.ofGenericAndColors 1 [.green, .green]
  types := #[.creature]
  subtypes := #["Elf", "Warrior"]
  power := some 2
  toughness := some 2
  keywords := Keyword.vigilance
}

private def legendDragon : CardDef := {
  name := "Test Dragon"
  manaCost := ManaCost.ofGenericAndColors 3 [.red, .white]
  supertypes := #[.legendary]
  types := #[.creature]
  subtypes := #["Dragon"]
  power := some 5
  toughness := some 4
  keywords := Keyword.flying
}

private def testArtifact : CardDef := {
  name := "Test Relic"
  manaCost := ManaCost.ofGeneric 2
  types := #[.artifact]
}

private def testPw : CardDef := {
  name := "Test Jace"
  manaCost := ManaCost.ofGenericAndColors 2 [.blue, .blue]
  supertypes := #[.legendary]
  types := #[.planeswalker]
  subtypes := #["Jace"]
  loyalty := some 4
}

private def testIsland : CardDef := {
  name := "Island"
  supertypes := #[.basic]
  types := #[.land]
  subtypes := #["Island"]
  tapAddMana := #[.colored .blue]
}

private def testSwamp : CardDef := {
  name := "Swamp"
  supertypes := #[.basic]
  types := #[.land]
  subtypes := #["Swamp"]
  tapAddMana := #[.colored .black]
}

#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw
  -- Build a rich board: p0 has Elf (2/2), Dragon (5/4 legendary), Relic (noncreature),
  -- Jace (planeswalker w/ 4 loyalty counters), Mountain, Forest; p1 has Island, Swamp, Grizzly Bears.
  let g1 := addPermanent g0 elf22 p0 p0
  let elfId := (lastPermanent g1).id
  let g2 := addPermanent g1 legendDragon p0 p0
  let dragonId := (lastPermanent g2).id
  let g3 := addPermanent g2 testArtifact p0 p0
  let relicId := (lastPermanent g3).id
  let g4 := insertObject g3 testPw p0 .battlefield (controller := some p0)
    (status := { counters := #[(.loyalty, 4)], chosenCreatureType := some .elf,
                 chosenColor := some .green, chosenName := some "Test Dragon",
                 chosenOdd := some true })
  let pwId := (lastPermanent g4).id
  let g5 := addPermanent g4 mountain p0 p0
  let g6 := addPermanent g5 forest p0 p0
  let g7 := addPermanent g6 testIsland p1 p1
  let g8 := addPermanent g7 testSwamp p1 p1
  let g9 := addPermanent g8 grizzlyBears p1 p1
  let oppBearId := (lastPermanent g9).id
  -- Put a +1/+1 counter on Elf (now 3/3) and tap Relic.
  let g10 := g9.recordPutCounters elfId .plusOnePlusOne 1 (byPlayer := some p0)
  let g11 := setTapped g10 relicId true
  -- Put two cards in p0's graveyard (an instant and an artifact creature) for Delirium tests.
  let g12 := insertObject g11 lightningBolt p0 (.graveyard p0)
  let g13 := insertObject g12 { testArtifact with name := "GY Artifact Creature", types := #[.artifact, .creature] } p0 (.graveyard p0)
  -- Make p0 the monarch and give p0 a commander color identity (B/R) and 2 poison counters.
  let g14 := g13.becomeMonarch p0 |>.addPlayerCounters p0 .poison 2
  let g15 := { g14 with
    players := g14.players.modify 0 fun pl =>
      { pl with hasCommander := true, commanderColorIdentity := ColorSet.ofList [.black, .red] }
  }
  -- Give p0 a Ring-bearer designation on Elf.
  let g16 := g15.setRingBearer p0 (some elfId)
  let env : EvalEnv := {
    controller := p0
    sourceId := some pwId
    targetSlots := #[#[.permanent dragonId], #[.player p1]]
    chosenX := 3
    stepEnv := #[(⟨0⟩, { objects := #[elfId, dragonId], movedCount := 2, excessDamage := 4, succeeded := true })]
  }

  -- Player queries
  let playerOk :=
    EvalExpr.evalPlayer g16 env .you == #[p0] &&
    EvalExpr.evalPlayer g16 env .activePlayer == #[p0] &&
    EvalExpr.evalPlayer g16 env .monarch == #[p0] &&
    EvalExpr.evalPlayer g16 env (.target 1) == #[p1] &&
    EvalExpr.evalPlayer g16 env (.controllerOf (.target 0)) == #[p0] &&
    EvalExpr.evalPlayer g16 env (.matching .opponent .any) == #[p1] &&
    EvalExpr.evalPlayer g16 env (.matching .anyPlayer .isMonarch) == #[p0]

  -- Object predicates: Layer 1–7d, CR 208.3 noncreature stat exclusion, chosenOnSource,
  -- colorless never sharing a color (CR 105.2c), Ring-bearer designation, topOfLibrary order,
  -- extremum, diff.
  let relicView := (EvalExpr.resolveObjectView? g16 env relicId).get!
  let elfView := (EvalExpr.resolveObjectView? g16 env elfId).get!
  let dragonView := (EvalExpr.resolveObjectView? g16 env dragonId).get!
  let pwView := (EvalExpr.resolveObjectView? g16 env pwId).get!
  let oppBearView := (EvalExpr.resolveObjectView? g16 env oppBearId).get!
  let topCardExpected := (g16.player p0).library.back!
  let predOk :=
    -- Noncreature without printed P/T fails power comparison (CR 208.3)
    !EvalExpr.evalObjectPred g16 env relicView (.stat .power .le (.const 2)) &&
    !EvalExpr.evalObjectPred g16 env relicView (.statParity .power .even) &&
    -- Elf has 3/3 (2/2 + +1/+1 counter), vigilance, Ring-bearer, chosen subtype/color
    EvalExpr.evalObjectPred g16 env elfView (.stat .power .eq (.const 3)) &&
    EvalExpr.evalObjectPred g16 env elfView (.statParity .power .chosenOnSource) &&
    EvalExpr.evalObjectPred g16 env elfView (.hasKeyword .vigilance) &&
    EvalExpr.evalObjectPred g16 env elfView (.hasDesignation .ringBearer) &&
    EvalExpr.evalObjectPred g16 env elfView (.hasSubtype .chosenOnSource) &&
    EvalExpr.evalObjectPred g16 env elfView (.hasColor .chosenOnSource) &&
    EvalExpr.evalObjectPred g16 env elfView (.counterCount (some .plusOnePlusOne) .ge (.const 1)) &&
    -- Dragon is legendary, flying, multicolored (2 colors), chosen name, commander identity match (red)
    EvalExpr.evalObjectPred g16 env dragonView (.colorCount .ge 2) &&
    EvalExpr.evalObjectPred g16 env dragonView (.hasKeyword .flying) &&
    EvalExpr.evalObjectPred g16 env dragonView (.named .chosenOnSource) &&
    EvalExpr.evalObjectPred g16 env dragonView (.hasColor .commanderIdentity) &&
    -- Planeswalker loyalty is counter count on battlefield (CR 209.2 / 306.5b)
    EvalExpr.evalObjectPred g16 env pwView (.stat .loyalty .eq (.const 4)) &&
    -- Colorless objects do not share a color (CR 105.2c)
    !EvalExpr.evalObjectPred g16 env relicView (.shares .color (.inZones .battlefield (.hasType .artifact))) &&
    -- Elf and opponent's Bear share green
    EvalExpr.evalObjectPred g16 env elfView (.shares .color (.inZones .battlefield (.controlledBy .opponent))) &&
    -- Tapped status
    EvalExpr.evalObjectPred g16 env relicView (.tapped true) &&
    !EvalExpr.evalObjectPred g16 env elfView (.tapped true) &&
    -- topOfLibrary returns top (`library.back!`), not bottom (`library[0]!`)
    EvalExpr.evalObjectId? g16 env (.topOfLibrary .you (.const 1)) == some topCardExpected &&
    -- extremum picks Dragon (power 5) as max and Elf (power 3) as min among p0's creatures
    EvalExpr.evalObjectId? g16 env (.extremum .max .power ObjectExpr.creaturesYouControl) == some dragonId &&
    EvalExpr.evalObjectId? g16 env (.extremum .min .power ObjectExpr.creaturesYouControl) == some elfId &&
    -- diff removes Dragon from creaturesYouControl leaving only Elf
    (EvalExpr.evalObjects g16 env (.diff ObjectExpr.creaturesYouControl (.target 0))).filterMap ObjectView.id? == #[elfId] &&
    -- Opponent bear is controlled by opponent
    EvalExpr.evalObjectPred g16 env oppBearView (.controlledBy .opponent)

  -- ValueExpr queries: aggregates, countDistinct powers, Domain, Delirium, planeswalker types,
  -- devotion/manaSymbols, player metrics, step metrics, binary arithmetic (incl. divFloor by 0).
  let valOk :=
    EvalExpr.evalValue g16 env .chosenX == 3 &&
    EvalExpr.evalValue g16 env (.objectStat .power (.target 0)) == 5 &&
    EvalExpr.evalValue g16 env (.counterCount (some .loyalty) .this) == 4 &&
    EvalExpr.evalValue g16 env (.aggregate .count .one ObjectExpr.creaturesYouControl) == 2 &&
    EvalExpr.evalValue g16 env (.aggregate .sum (.stat .power) ObjectExpr.creaturesYouControl) == 8 &&
    EvalExpr.evalValue g16 env (.aggregate .max (.stat .power) ObjectExpr.creaturesYouControl) == 5 &&
    EvalExpr.evalValue g16 env (.aggregate .min (.stat .power) ObjectExpr.creaturesYouControl) == 3 &&
    EvalExpr.evalValue g16 env (.aggregate .countDistinct (.stat .power) ObjectExpr.creaturesYouControl) == 2 &&
    EvalExpr.evalValue g16 env (.basicLandTypeCount ObjectExpr.landsYouControl) == 2 &&
    EvalExpr.evalValue g16 env (.cardTypeCount (.inZones .yourGraveyard .anyObject)) == 3 &&
    EvalExpr.evalValue g16 env (.subtypeCount .planeswalker (.inZones .battlefield (.controlledBy .you))) == 1 &&
    EvalExpr.evalValue g16 env (.manaSymbols (some .green) (.inZones .battlefield (.controlledBy .you))) == 2 &&
    EvalExpr.evalValue g16 env (.manaSymbols (some .blue) (.inZones .battlefield (.controlledBy .you))) == 2 &&
    EvalExpr.evalValue g16 env (.playerMetric .life .you) == 20 &&
    EvalExpr.evalValue g16 env (.playerMetric .graveyardSize .you) == 2 &&
    EvalExpr.evalValue g16 env (.playerMetric .poisonCounters .you) == 2 &&
    EvalExpr.evalValue g16 env (.playerMetric .opponentsCount .you) == 1 &&
    EvalExpr.evalValue g16 env (.stepMetric .movedCount ⟨0⟩) == 2 &&
    EvalExpr.evalValue g16 env (.stepMetric .excessDamage ⟨0⟩) == 4 &&
    EvalExpr.evalValue g16 env (.binary .divFloor (.const 5) (.const 2)) == 2 &&
    EvalExpr.evalValue g16 env (.binary .divFloor (.const 5) (.const 0)) == 0

  -- Condition & DurationExpr & LibraryPosSpec queries
  let condDurOk :=
    EvalExpr.evalCondition g16 env .isYourTurn &&
    !EvalExpr.evalCondition g16 env .isNight &&
    EvalExpr.evalCondition g16 env (.duringStep .precombatMain) &&
    EvalExpr.evalCondition g16 env (.duringPhase .precombatMain) &&
    EvalExpr.evalCondition g16 env (.playerPred .you .isMonarch) &&
    EvalExpr.evalCondition g16 env (.stepSucceeded ⟨0⟩) &&
    !EvalExpr.evalCondition g16 env (.turnHistory (.eventOccurredLastTurn .any (.permanentDied (.hasType .creature)))) &&
    EvalExpr.evalDuration g16 env .untilEndOfTurn == some .untilEndOfTurn &&
    EvalExpr.evalDuration g16 env (.untilNextTurnOf .you) == some (.untilNextTurnOf p0) &&
    EvalExpr.evalDuration g16 env (.whileOnBattlefield .this) == some (.whileSourceOnBattlefield pwId) &&
    EvalExpr.evalDuration g16 env (.untilLeavesBattlefield (.target 0)) == some (.untilSourceLeaves dragonId) &&
    EvalExpr.evalDuration g16 env (.whileHasCounter .this .loyalty) == some (.whileSourceHasCounter pwId .loyalty) &&
    EvalExpr.evalDuration g16 env (.whileInZone (.target 0) .graveyard) == some (.whileInZone dragonId (.graveyard p0)) &&
    EvalExpr.evalLibraryPos g16 env (.fromTop (.const 3)) == .fromTop 3

  -- CR 603.10 / CR 608.2h LKI & GameSnapshot evaluation after Elf dies
  let (gAfterDie, _) := g16.move elfId (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let envLki : EvalEnv := { env with triggerSubjectId := some elfId }
  let envSnap : EvalEnv := { env with lookBackState? := some g16 }
  -- Explicit frozen snapshot overrides even a live object's current characteristics (CR 113.7a / 608.2h)
  let dragonLkiSnap : EventObject := {
    (g16.snapshot (g16.findObject? dragonId).get!) with power := some 9
  }
  let envExplicitSnap : EvalEnv := {
    env with triggerSubjectId := some dragonId, triggerSubjectSnapshot := some dragonLkiSnap
  }
  -- Owner-scoped shared zone query (cards you own in exile vs opponent's)
  let gWithExile := insertObject (insertObject g16 lightningBolt p0 .exile) grizzlyBears p1 .exile
  let yourExile : ObjectExpr :=
    .inZones { zones := #[.exile], owner := .ofPlayer .you } .anyObject
  let lkiOk :=
    -- Elf left the battlefield (CR 400.7), yet LKI preserves its 3 power and +1/+1 counter (CR 608.2h)
    (gAfterDie.findObject? elfId).isNone &&
    EvalExpr.evalValue gAfterDie envLki (.objectStat .power .triggerSubject) == 3 &&
    EvalExpr.evalValue gAfterDie envLki (.counterCount (some .plusOnePlusOne) .triggerSubject) == 1 &&
    EvalExpr.evalPlayer gAfterDie envLki (.controllerOf .triggerSubject) == #[p0] &&
    EvalExpr.evalCondition gAfterDie envLki (.turnHistory (.eventOccurredThisTurn .you (.permanentDied (.hasType .creature)))) &&
    -- Look-back snapshot sees pre-death board count (2 creatures) while post-death board has 1
    EvalExpr.evalValue gAfterDie env (.aggregate .count .one ObjectExpr.creaturesYouControl) == 1 &&
    EvalExpr.evalValue gAfterDie envSnap (.aggregate .count .one ObjectExpr.creaturesYouControl) == 2 &&
    -- Explicit frozen snapshot takes precedence over live power (9 vs 5)
    EvalExpr.evalValue g16 envExplicitSnap (.objectStat .power .triggerSubject) == 9 &&
    -- Owner-scoped exile sees only p0's exiled card
    (EvalExpr.evalObjects gWithExile env yourExile).size == 1

  -- Generalized `TokenSpec`: dynamic `ValueExpr` P/T & general `ObjectExpr` `copyOf`
  let dynTokenSpec : TokenSpec := .custom {
    name? := some "Pack Avatar"
    types := #[.creature]
    subtypes := #[.avatar]
    colors := ColorSet.singleton .green
    power? := some (.aggregate .count .one ObjectExpr.creaturesYouControl)
    toughness? := some (.aggregate .count .one ObjectExpr.creaturesYouControl)
  }
  let maxPowerCopySpec : TokenSpec :=
    .copyOf (.extremum .max .power ObjectExpr.creaturesYouControl) #[.removeSupertype .legendary]
  let gDynTok := g16.createKindTokens p0 dynTokenSpec 1
  let dynObj := lastPermanent gDynTok
  let tokenOk :=
    -- Context-independent `tokenPrinted?` returns `none` for dynamic `ValueExpr` P/T
    (Game.tokenPrinted? dynTokenSpec).isNone &&
    -- `resolveTokenPrinted?` & `createKindTokens` evaluate dynamic P/T = 2/2 (p0 controls 2 creatures)
    (g16.resolveTokenPrinted? dynTokenSpec (controller := p0)).map (fun c => (c.power, c.toughness)) ==
      some (some 2, some 2) &&
    dynObj.name == "Pack Avatar" && gDynTok.power dynObj == 2 && gDynTok.toughness dynObj == 2 &&
    -- Generalized `.copyOf (.extremum .max .power .creaturesYouControl)` copies Dragon without legendary
    (g16.resolveTokenPrinted? maxPowerCopySpec (controller := p0)).map
      (fun c => (c.name, c.power, c.supertypes.contains .legendary, c.isToken)) ==
      some ("Test Dragon", some 5, false, true)

  -- Generalized `ManaSpec` / `ManaPoolPalette` via `Game.evalManaSpec`
  let elfCountMana : ManaSpec :=
    .sequence #[(ManaType.colored .green, .aggregate .count .one (.controlledOfSubtype .elf))]
  let distinctPowerMana : ManaSpec :=
    .oneOf .anyColor (.aggregate .countDistinct (.stat .power) ObjectExpr.creaturesYouControl)
  let cmdIdMana : ManaSpec := .colorAmong (.commanderColorIdentity .you)
  let moxAmberMana : ManaSpec := .colorAmong (.colorsAmong .legendaryCreaturesAndPlaneswalkersYouControl)
  let exoticOrchardMana : ManaSpec := .colorAmong (.typesLandsCouldProduce .landsOpponentsControl)
  let reflectingPoolMana : ManaSpec := .colorAmong (.typesLandsCouldProduce .otherLandsYouControl)
  let manaSpecOk :=
    g16.evalManaSpec env elfCountMana == .fixed #[.colored .green] &&
    g16.evalManaSpec env distinctPowerMana == .oneOf anyColorMana 2 &&
    g16.evalManaSpec env cmdIdMana == .colorAmong #[.colored .black, .colored .red] &&
    g16.evalManaSpec env moxAmberMana == .colorAmong #[.colored .white, .colored .blue, .colored .red] &&
    g16.evalManaSpec env exoticOrchardMana == .colorAmong #[.colored .blue, .colored .black] &&
    g16.evalManaSpec env reflectingPoolMana == .colorAmong #[.colored .red, .colored .green]

  playerOk && predOk && valOk && condDurOk && lkiOk && tokenOk && manaSpecOk

end Mtg.Engine.Tests.EvalExprSuite
