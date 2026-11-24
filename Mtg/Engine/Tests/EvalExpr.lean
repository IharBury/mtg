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
      .isKind .card,
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
      .isKind .spell,
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
    np.filter.pred == .all #[.isKind .permanentCard, .castFrom .exile]
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
    { zones := .battlefield
      pred := .all #[.hasType .creature, .isKind .card, .controlledBy .you] },
    { zones := .battlefield
      pred := .all #[.isKind .permanentCard, .controlledBy .you] },
    { zones := .yourGraveyard
      pred := .all #[.any #[.hasType .instant, .hasType .sorcery], .isKind .card,
        .stat .manaValue .le (.const 2)] },
    { zones := .stack
      pred := .all #[.not (.hasType .creature), .isKind .spell, .statParity .manaValue .even] },
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
  some (.cardTypeCount (.inZones .yourGraveyard .isCard))
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
    .aggregate .max (.stat .manaValue) (.inZones .yourGraveyard .isCard),
    .aggregate .min (.stat .toughness) ObjectExpr.creaturesYouControl,
    .aggregate .countDistinct (.stat .power) ObjectExpr.creaturesYouControl,
    .basicLandTypeCount ObjectExpr.landsYouControl,
    .cardTypeCount (.inZones .yourGraveyard .isCard),
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
  power := some (.fixed 2)
  toughness := some (.fixed 2)
  keywords := #[Keyword.vigilance]
}

private def legendDragon : CardDef := {
  name := "Test Dragon"
  manaCost := ManaCost.ofGenericAndColors 3 [.red, .white]
  supertypes := #[.legendary]
  types := #[.creature]
  subtypes := #["Dragon"]
  power := some (.fixed 5)
  toughness := some (.fixed 4)
  keywords := #[Keyword.flying]
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
}

private def testSwamp : CardDef := {
  name := "Swamp"
  supertypes := #[.basic]
  types := #[.land]
  subtypes := #["Swamp"]
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
  -- Explicit frozen snapshot is used ONLY after the object leaves its zone (CR 113.7a / 608.2h)
  let dragonLkiSnap : EventObject := {
    (g16.snapshot (g16.findObject? dragonId).get!) with power := some 9
  }
  let envExplicitSnap : EvalEnv := {
    env with triggerSubjectId := some dragonId, triggerSubjectSnapshot := some dragonLkiSnap
  }
  let (gAfterDragonDies, _) :=
    g16.move dragonId (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
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
    -- While Dragon is still live on the battlefield, read live Layer 1–7d power (5);
    -- only after Dragon leaves its zone does the explicit LKI snapshot (9) apply (CR 113.7a / 608.2h).
    EvalExpr.evalValue g16 envExplicitSnap (.objectStat .power .triggerSubject) == 5 &&
    EvalExpr.evalValue gAfterDragonDies envExplicitSnap (.objectStat .power .triggerSubject) == 9 &&
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
      some (some (.fixed 2), some (.fixed 2)) &&
    dynObj.name == "Pack Avatar" && gDynTok.power dynObj == 2 && gDynTok.toughness dynObj == 2 &&
    -- Generalized `.copyOf (.extremum .max .power .creaturesYouControl)` copies Dragon without legendary
    (g16.resolveTokenPrinted? maxPowerCopySpec (controller := p0)).map
      (fun c => (c.name, c.power, c.supertypes.contains .legendary, c.isToken)) ==
      some ("Test Dragon", some (.fixed 5), false, true)

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

/-! ### 3. Regression Tests for CR Edge Cases (208.3, 112.1, 108.2/111.6, 506.5, 509.1h, 707.2 Ties) -/

private def testVehicle : CardDef := {
  name := "Test Skyship"
  manaCost := ManaCost.ofGeneric 3
  types := #[.artifact]
  subtypes := #["Vehicle"]
  power := some (.fixed 4)
  toughness := some (.fixed 4)
}

private def testColossus : CardDef := {
  name := "Test Colossus"
  manaCost := ManaCost.ofGenericAndColors 4 [.green]
  types := #[.creature]
  subtypes := #["Giant"]
  power := some (.fixed 5)
  toughness := some (.fixed 5)
}

-- CR 208.3: uncrewed Vehicle has NO power or toughness (both live and LKI), even with printed 4/4.
#guard
  let p0 : PlayerId := ⟨0⟩
  let g0 := afterDraw
  let g1 := addPermanent g0 testVehicle p0 p0
  let vehId := (lastPermanent g1).id
  let vehLiveView := (EvalExpr.resolveObjectView? g1 { controller := p0 } vehId).get!
  let vehSnap : EventObject := g1.snapshot (g1.findObject? vehId).get!
  let g2 := insertObject g1 elf22 p0 (.graveyard p0)
  let gyElfId := (g2.player p0).graveyard.back!
  let gyElfView := (EvalExpr.resolveObjectView? g2 { controller := p0 } gyElfId).get!
  let env : EvalEnv := { controller := p0 }
  -- Live uncrewed Vehicle has no power/toughness (CR 208.3)
  (EvalExpr.viewStat? g1 vehLiveView .power).isNone &&
  (EvalExpr.viewStat? g1 vehLiveView .toughness).isNone &&
  !EvalExpr.evalObjectPred g1 env vehLiveView (.stat .power .ge (.const 1)) &&
  !EvalExpr.evalObjectPred g1 env vehLiveView (.stat .power .le (.const 10)) &&
  !EvalExpr.evalObjectPred g1 env vehLiveView (.statParity .power .even) &&
  -- LKI snapshot of uncrewed Vehicle also has no power/toughness even if `eo.power` was populated
  (EvalExpr.viewStat? g1 (.lki { vehSnap with power := some 4, toughness := some 4 }) .power).isNone &&
  (EvalExpr.viewStat? g1 (.lki { vehSnap with power := some 4, toughness := some 4 }) .toughness).isNone &&
  !EvalExpr.evalObjectPred g1 env (.lki { vehSnap with power := some 4 }) (.stat .power .eq (.const 4)) &&
  -- Creature card in graveyard DOES have printed power/toughness
  EvalExpr.viewStat? g2 gyElfView .power == some 2 &&
  EvalExpr.viewStat? g2 gyElfView .toughness == some 2

-- CR 112.1 ("spell" excludes stack abilities) & CR 108.2 / 111.6 ("card"/"permanent card" excludes tokens).
#guard
  let p0 : PlayerId := ⟨0⟩
  let g0 := afterDraw
  let g1 := addPermanent g0 elf22 p0 p0
  let elfObj := lastPermanent g1
  let g2 := g1.createKindTokens p0 .bear 1
  let tokId := (lastPermanent g2).id
  -- Put a real instant spell AND a stack ability onto the stack.
  let g3 := insertObject g2 lightningBolt p0 .stack (controller := some p0)
  let boltId := (g3.objects.back!).id
  let g4 := g3.putStackEntry p0 boltId
  let (g5, abObj) := g4.putStackAbility elfObj p0 (abilityEffect := some (.draw 1))
  let env : EvalEnv := { controller := p0 }
  let spellFilter := (parseNounPhrase "target spell").get!.filter
  let noncreatureSpellFilter := (parseNounPhrase "target noncreature spell").get!.filter
  let permCardFilter := (parseNounPhrase "permanent card you control").get!.filter
  let creatureCardsFilter := (parseNounPhrase "creature cards you control").get!.filter
  let spellsMatched := (EvalExpr.evalObjects g5 env spellFilter.toExpr).filterMap ObjectView.id?
  let noncreatureMatched := (EvalExpr.evalObjects g5 env noncreatureSpellFilter.toExpr).filterMap ObjectView.id?
  let permCardsMatched := (EvalExpr.evalObjects g5 env permCardFilter.toExpr).filterMap ObjectView.id?
  let creatureCardsMatched := (EvalExpr.evalObjects g5 env creatureCardsFilter.toExpr).filterMap ObjectView.id?
  -- Both "target spell" and "target noncreature spell" match Bolt and REJECT the stack ability
  spellsMatched == #[boltId] &&
  !spellsMatched.contains abObj.id &&
  noncreatureMatched == #[boltId] &&
  !noncreatureMatched.contains abObj.id &&
  -- Both "permanent card you control" and "creature cards you control" include Elf and REJECT the Bear token
  permCardsMatched.contains elfObj.id && !permCardsMatched.contains tokId &&
  creatureCardsMatched == #[elfObj.id] && !creatureCardsMatched.contains tokId

-- CR 506.5 (LKI `attackingAlone`) & CR 509.1h (LKI `.blocked` / `.unblocked` via `becameBlocked`).
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw
  -- Case A: Solo attacker declared, marked blocked via `Game.markBlocked`, then dies.
  let gA1 := addPermanent g0 elf22 p0 p0
  let soloId := (lastPermanent gA1).id
  let soloSnap := gA1.snapshot (gA1.findObject? soloId).get!
  let gA2 := gA1.record (GameEvent.attackersDeclared gA1.turnNumber p0 #[(soloSnap, .player p1)])
  let gA3 := gA2.markBlocked soloId #[]
  let (gA4, _) := gA3.move soloId (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let envSolo : EvalEnv := { controller := p0, triggerSubjectId := some soloId }
  let soloLki := (EvalExpr.resolveObjectView? gA4 envSolo soloId).get!
  let caseA :=
    EvalExpr.evalObjectPred gA4 envSolo soloLki (.combatRole .attackingAlone) &&
    EvalExpr.evalObjectPred gA4 envSolo soloLki (.combatRole .blocked) &&
    !EvalExpr.evalObjectPred gA4 envSolo soloLki (.combatRole .unblocked)

  -- Case B: Two co-attackers declared; attacker 1 dies while attacker 2 stays on board (unblocked).
  let gB1 := addPermanent (addPermanent g0 elf22 p0 p0) legendDragon p0 p0
  let a1Id := (gB1.objects[gB1.objects.size - 2]!).id
  let a2Id := (gB1.objects[gB1.objects.size - 1]!).id
  let gB2 := gB1.record (GameEvent.attackersDeclared gB1.turnNumber p0 #[
    (gB1.snapshot (gB1.findObject? a1Id).get!, .player p1),
    (gB1.snapshot (gB1.findObject? a2Id).get!, .player p1)
  ])
  let (gB3, _) := gB2.move a1Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let envB : EvalEnv := { controller := p0, triggerSubjectId := some a1Id }
  let a1LkiB := (EvalExpr.resolveObjectView? gB3 envB a1Id).get!
  let caseB :=
    !EvalExpr.evalObjectPred gB3 envB a1LkiB (.combatRole .attackingAlone) &&
    !EvalExpr.evalObjectPred gB3 envB a1LkiB (.combatRole .blocked) &&
    EvalExpr.evalObjectPred gB3 envB a1LkiB (.combatRole .unblocked)

  -- Case C: Both co-attackers die simultaneously in the same batch (0 attackers left on board);
  -- NEITHER was attacking alone!
  let gC := gB2.withBatch (some (.gameRule .leavingZone)) fun g =>
    let (g, _) := g.move a1Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
    let (g, _) := g.move a2Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
    g
  let a1LkiC := (EvalExpr.resolveObjectView? gC { controller := p0 } a1Id).get!
  let a2LkiC := (EvalExpr.resolveObjectView? gC { controller := p0 } a2Id).get!
  let caseC :=
    !EvalExpr.evalObjectPred gC { controller := p0 } a1LkiC (.combatRole .attackingAlone) &&
    !EvalExpr.evalObjectPred gC { controller := p0 } a2LkiC (.combatRole .attackingAlone)

  -- Case D: Extra combat phase starts later on the same turn — earlier combat's LKI
  -- `attackingAlone` and `becameBlocked` must remain anchored on the combat phase where
  -- those creatures departed, while a solo unblocked attacker in combat 2 stays isolated.
  let gD0 := addPermanent (addPermanent g0 elf22 p0 p0) legendDragon p0 p0
  let d1Id := (gD0.objects[gD0.objects.size - 2]!).id
  let d2Id := (gD0.objects[gD0.objects.size - 1]!).id
  let gD1 := gD0.record (GameEvent.phaseBegan gD0.turnNumber .combat)
  let gD2 := gD1.record (GameEvent.attackersDeclared gD1.turnNumber p0 #[
    (gD1.snapshot (gD1.findObject? d1Id).get!, .player p1),
    (gD1.snapshot (gD1.findObject? d2Id).get!, .player p1)
  ])
  let gD3 := gD2.markBlocked d1Id #[]
  let gD4 := gD3.withBatch (some (.gameRule .leavingZone)) fun g =>
    let (g, _) := g.move d1Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
    let (g, _) := g.move d2Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
    g
  -- Start a second combat phase on the same turn with a fresh solo unblocked attacker.
  let gD5 := addPermanent (gD4.record (GameEvent.phaseBegan gD4.turnNumber .combat)) grizzlyBears p0 p0
  let d3Id := (lastPermanent gD5).id
  let gD6 := gD5.record (GameEvent.attackersDeclared gD5.turnNumber p0 #[
    (gD5.snapshot (gD5.findObject? d3Id).get!, .player p1)
  ])
  let (gD7, _) := gD6.move d3Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let d1LkiD := (EvalExpr.resolveObjectView? gD7 { controller := p0 } d1Id).get!
  let d3LkiD := (EvalExpr.resolveObjectView? gD7 { controller := p0 } d3Id).get!
  let caseD :=
    -- `d1` from combat 1 was NOT attacking alone and WAS blocked, even after combat 2 started
    !EvalExpr.evalObjectPred gD7 { controller := p0 } d1LkiD (.combatRole .attackingAlone) &&
    EvalExpr.evalObjectPred gD7 { controller := p0 } d1LkiD (.combatRole .blocked) &&
    !EvalExpr.evalObjectPred gD7 { controller := p0 } d1LkiD (.combatRole .unblocked) &&
    -- `d3` from combat 2 WAS attacking alone and WAS unblocked
    EvalExpr.evalObjectPred gD7 { controller := p0 } d3LkiD (.combatRole .attackingAlone) &&
    !EvalExpr.evalObjectPred gD7 { controller := p0 } d3LkiD (.combatRole .blocked) &&
    EvalExpr.evalObjectPred gD7 { controller := p0 } d3LkiD (.combatRole .unblocked)

  -- Case E: Earlier-turn death (`.eventOccurredLastTurn` & direct LKI on the next turn):
  -- `e1` attacks alongside co-attacker `e2`, becomes blocked via `Game.markBlocked`, and dies on
  -- turn `T`; `e2` is removed from combat so turn `T + 1` has 0 live attackers. On turn `T + 1`,
  -- both direct LKI evaluation and `.eventOccurredLastTurn` queries (including parsed Oracle text)
  -- must still reconstruct `e1`'s turn-`T` combat window (NOT attacking alone, blocked, NOT
  -- unblocked), even if a fresh solo unblocked creature `e3` attacks and dies on turn `T + 1`.
  let gE0 := addPermanent (addPermanent g0 elf22 p0 p0) legendDragon p0 p0
  let e1Id := (gE0.objects[gE0.objects.size - 2]!).id
  let e2Id := (gE0.objects[gE0.objects.size - 1]!).id
  let gE1 := gE0.record (GameEvent.phaseBegan gE0.turnNumber .combat)
  let gE2 := gE1.record (GameEvent.attackersDeclared gE1.turnNumber p0 #[
    (gE1.snapshot (gE1.findObject? e1Id).get!, .player p1),
    (gE1.snapshot (gE1.findObject? e2Id).get!, .player p1)
  ])
  let gE3 := gE2.markBlocked e1Id #[]
  let (gE4, _) := gE3.move e1Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let gE5 := gE4.clearCombat
  -- Advance to turn `T + 1` (0 live attackers on board).
  let gE6 := { gE5 with turnNumber := gE5.turnNumber + 1 }
  let envE : EvalEnv := { controller := p0 }
  let e1LkiE := (EvalExpr.resolveObjectView? gE6 envE e1Id).get!
  let parsedAloneLastTurn := (parseCondition "a creature attacking alone died last turn").get!
  let parsedBlockedLastTurn := (parseCondition "a blocked creature died last turn").get!
  let caseEBase :=
    -- Direct LKI evaluation on turn `T + 1`
    !EvalExpr.evalObjectPred gE6 envE e1LkiE (.combatRole .attackingAlone) &&
    EvalExpr.evalObjectPred gE6 envE e1LkiE (.combatRole .blocked) &&
    !EvalExpr.evalObjectPred gE6 envE e1LkiE (.combatRole .unblocked) &&
    -- `.eventOccurredLastTurn` via both AST and parsed Oracle conditions
    !EvalExpr.evalCondition gE6 envE (.turnHistory (.eventOccurredLastTurn .any (.permanentDied (.combatRole .attackingAlone)))) &&
    EvalExpr.evalCondition gE6 envE (.turnHistory (.eventOccurredLastTurn .any (.permanentDied (.combatRole .blocked)))) &&
    !EvalExpr.evalCondition gE6 envE (.turnHistory (.eventOccurredLastTurn .any (.permanentDied (.combatRole .unblocked)))) &&
    !EvalExpr.evalCondition gE6 envE parsedAloneLastTurn &&
    EvalExpr.evalCondition gE6 envE parsedBlockedLastTurn
  -- Also verify a fresh solo unblocked death on turn `T + 1` stays isolated from turn `T`.
  let gE7 := addPermanent (gE6.record (GameEvent.phaseBegan gE6.turnNumber .combat)) grizzlyBears p0 p0
  let e3Id := (lastPermanent gE7).id
  let gE8 := gE7.record (GameEvent.attackersDeclared gE7.turnNumber p0 #[
    (gE7.snapshot (gE7.findObject? e3Id).get!, .player p1)
  ])
  let (gE9, _) := gE8.move e3Id (.graveyard p0) none (verb := some .destroy) (cause := some (.gameRule .leavingZone))
  let caseE :=
    caseEBase &&
    !EvalExpr.evalCondition gE9 envE parsedAloneLastTurn &&
    EvalExpr.evalCondition gE9 envE parsedBlockedLastTurn &&
    EvalExpr.evalCondition gE9 envE (.turnHistory (.eventOccurredThisTurn .any (.permanentDied (.combatRole .attackingAlone)))) &&
    !EvalExpr.evalCondition gE9 envE (.turnHistory (.eventOccurredThisTurn .any (.permanentDied (.combatRole .blocked)))) &&
    EvalExpr.evalCondition gE9 envE (.turnHistory (.eventOccurredThisTurn .any (.permanentDied (.combatRole .unblocked))))

  caseA && caseB && caseC && caseD && caseE

-- CR 707.2 / 707.9 / 508.4: tied `ObjectExpr.extremum` in `TokenSpec.copyOf` prompts
-- controller to choose, and attacking copies continue through per-token `promptEnteringAttackItems`.
#guard
  let p0 : PlayerId := ⟨0⟩
  let p1 : PlayerId := ⟨1⟩
  let g0 := afterDraw
  let g1 := addPermanent g0 legendDragon p0 p0
  let dragonId := (lastPermanent g1).id
  let g2 := addPermanent g1 testColossus p0 p0
  let colossusId := (lastPermanent g2).id
  let maxPowerCopySpec : TokenSpec :=
    .copyOf (.extremum .max .power ObjectExpr.creaturesYouControl) #[.removeSupertype .legendary]
  let cands :=
    g2.resolveCopyTokenCandidates (.extremum .max .power ObjectExpr.creaturesYouControl)
      #[.removeSupertype .legendary] (controller := p0)
  let gPaused := g2.createKindTokens p0 maxPowerCopySpec 1
  let pausedOk :=
    match gPaused.pending with
    | .resolutionChoice who (.chooseTokenCopyObject ids _ 1 false false none ..) =>
      who == p0 && ids == #[dragonId, colossusId]
    | _ => false
  -- Choose the SECOND tied creature (`colossusId`), proving the player's choice (not board order) wins.
  let chosenOk :=
    match gPaused.answerResolutionChoice p0 (.objects #[colossusId]) with
    | .ok gDone =>
      let tok := lastPermanent gDone
      gDone.pending == .none &&
      tok.name == "Test Colossus" && tok.printed.isToken &&
      gDone.power tok == 5 && gDone.toughness tok == 5
    | .error _ => false
  -- Tied attacking copies (`count := 2`) with an opponent planeswalker must offer per-token
  -- CR 508.4 `chooseEnteringAttackTarget` prompts after choosing which tied creature to copy.
  let gWithOppPw := (insertObject g2 testPw p1 .battlefield (controller := some p1)
    (status := { counters := #[(.loyalty, 4)] })).beginStep .declareAttackers
  let oppPwId := (lastPermanent gWithOppPw).id
  let gAtkTie := gWithOppPw.createAndMarkTokensAttacking p0 maxPowerCopySpec 2
    (tapped := true) (holds := true)
  let atkTieOk :=
    match gAtkTie.pending with
    | .resolutionChoice who (.chooseTokenCopyObject ids _ 2 true true none ..) =>
      who == p0 && ids == #[dragonId, colossusId] &&
      match gAtkTie.answerResolutionChoice p0 (.objects #[colossusId]) with
      | .ok gNeedAtk1 =>
        match gNeedAtk1.pending with
        | .resolutionChoice who1 (.chooseEnteringAttackTarget rem1 _ _) =>
          who1 == p0 && rem1.size == 2 &&
          rem1[0]!.options.contains (.player p1) &&
          rem1[0]!.options.contains (.planeswalker oppPwId) &&
          -- Send token 1 at opponent's planeswalker, token 2 at opponent player
          match gNeedAtk1.answerResolutionChoice p0 (.objects #[oppPwId]) with
          | .ok gNeedAtk2 =>
            match gNeedAtk2.pending with
            | .resolutionChoice who2 (.chooseEnteringAttackTarget rem2 _ _) =>
              who2 == p0 && rem2.size == 1 &&
              match gNeedAtk2.answerResolutionChoice p0 (.mode 0) with
              | .ok gDone =>
                let toks := gDone.objects.filter fun o =>
                  o.isOnBattlefield && o.printed.isToken && o.name == "Test Colossus"
                gDone.pending == .none &&
                toks.size == 2 &&
                toks.any (fun t => t.status.attacking && t.status.attackingTarget == some (.planeswalker oppPwId)) &&
                toks.any (fun t => t.status.attacking && t.status.attackingTarget == some (.player p1))
              | .error _ => false
            | _ => false
          | .error _ => false
        | _ => false
      | .error _ => false
    | _ => false
  cands.size == 2 &&
  (g2.resolveTokenPrinted? maxPowerCopySpec (controller := p0)).isNone &&
  pausedOk && chosenOk && atkTieOk

end Mtg.Engine.Tests.EvalExprSuite
