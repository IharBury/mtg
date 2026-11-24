import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect

/-!
# Spell and activated-ability effect constructors (Phase 8 unified `Instruction`)

`Effect.mkSpell` / `Effect.mkAbility` / `Effect.fraSpell` / `FraCandidates.ab`
plus the named constructors for every printed spell, activated-ability, and
Reality Fracture effect the engine models, all lowered directly onto unified
`Instruction` values (pure computed
`Effect.classifyForAgent` / `Effect.classifyAbilityForAgent`).
-/

namespace Mtg.Engine

namespace Effect

/-! ### Core Effect Builders & Reusable `ObjectExpr` Shorthands -/

private def creaturesYouControlExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])

private def allCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.hasType .creature)

private def oppCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent])

/-- Destroy one target of `spec`. -/
def destroyTarget (spec : TargetSpec) : Effect :=
  { targets := spec, body := Instruction.destroy (.target 0) }

/-- The canonical destroy-one-target effect for `spec`. -/
def canonicalDestroy (spec : TargetSpec) : Effect :=
  destroyTarget spec

/-! ### Printed Spell Effect Constructors -/

def destroyCreatureWithFlying : Effect :=
  destroyTarget .creatureWithFlying

def destroyCreature : Effect :=
  destroyTarget .creature

def plusOnePlusOneTrampleHexproof : Effect :=
  mkSpell .creatureYouControl
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.hexproof, Keyword.trample]
    ])

/-- Deal `amount` damage. The creature loses indestructible until end of turn.
If it would die this turn, exile it instead. -/
def dealDamageLoseIndestructibleExile (amount : Nat) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) amount,
      Instruction.loseKeywords (.target 0) #[Keyword.indestructible],
      Instruction.exileIfDiesThisTurn (.target 0)
    ])

def creatureYouControlDealsPowerToOppCreature : Effect :=
  mkSpell .creatureYouControlThenOppCreature
    (.damage (.fight (.target 0) (.target 1) true))

def playAdditionalLandThisTurn : Effect :=
  mkSpell .none
    (Instruction.extraLand .you 1)

def destroyArtifactOrLandNonflyersCantBlock : Effect :=
  mkSpell .artifactOrLand
    (.seq #[
      Instruction.destroy (.target 0),
      .installEffect (.applyRule .untilEndOfTurn
        (.combat (.cantBlock (.matching {
          zones := .battlefield
          pred := .all #[.hasType .creature, .not (.hasKeyword .flying)]
        }) none)))
    ])

def destroyTargetCreatureControllerLosesLife (life : Nat) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.loseLifeFixed life (.controllerOf (.target 0))
    ])
   
def allCreaturesGet (power toughness : Int) : Effect :=
  mkSpell .none
    (Instruction.pumpFixed allCreaturesExpr power toughness)

def drawAndLoseLife (cards life : Nat) : Effect :=
  mkSpell .none
    (.seq #[Instruction.drawFixed cards, Instruction.loseLifeFixed life])

def targetPlayerDrawLoseLife (cards life : Nat) : Effect :=
  mkSpell .player
    (.seq #[Instruction.drawFixed cards (.target 0), Instruction.loseLifeFixed life (.target 0)])

def creaturesTargetPlayerGet (power toughness : Int) : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  mkSpell .player
    (Instruction.pumpFixed targetPlayerCreatures power toughness)

def pumpAndLifelink (power toughness : Int) : Effect :=
  mkSpell .creature
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.all #[.modifyPT (.const power) (.const toughness), .grantKeywords #[Keyword.lifelink]])))

/-- Until-end-of-turn +P/+T. If the creature would die this turn, exile it instead. -/
def pumpAndExileIfDies (power toughness : Int) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.exileIfDiesThisTurn (.target 0)
    ])
   
def exileGraveyardCreaturesGrantCast : Effect :=
  mkSpell .player
    (.moveZone (.inZones (.graveyardOf (.target 0)) (.all #[.hasType .creature, .isKind .card])) .exile .exile {
      grantPlayPerm? := some {
        duration := .whileInZone .this .exile
        landsAllowed := false
        anyManaColor := true
      }
    })

def drawThenDiscard (n : Nat) : Effect :=
  mkSpell .none
    (.seq #[Instruction.drawFixed n, Instruction.discardFixed 1])

def scry (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.scryFixed n)

/-- Tap the target, then scry `scryN` and draw `drawN` (Hithlain Knots).
The draw waits until the scry finishes. An illegal target means none of
the steps happen. -/
def tapScryDraw (scryN drawN : Nat) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.tap (.target 0),
      Instruction.scryFixed scryN,
      Instruction.drawFixed drawN
    ])

def tapOneOrTwoCreatures : Effect :=
  mkSpell (TargetSpec.creature.asBetween 1 2)
    (Instruction.tap .allTargets)

/-- Put `counters` of `kind` on up to one target creature, then the targeted
player gains `life`. Defaults are one +1/+1 counter (Meager Meal). -/
def plusOneUpToOneAndPlayerGainsLife (life : Nat)
    (kind : CounterKind := .plusOnePlusOne) (counters : Nat := 1) : Effect :=
  mkSpell .upToOneCreatureThenPlayer
    (.seq #[
      Instruction.putCounters (.target 0) kind (.const (Int.ofNat counters)),
      Instruction.gainLifeFixed life (.target 1)
    ])

def counterSpell : Effect :=
  mkSpell .spell
    (Instruction.counter (.target 0))

/-- Counter the targeted spell unless its controller pays `{n}`. -/
def counterUnlessPays (n : Nat) : Effect :=
  mkSpell .spell
    (.unlessPays (.controllerOf (.target 0)) (CostSpec.ofGeneric n) (Instruction.counter (.target 0)))

/-- The owner puts the targeted creature on the top or bottom of their library. -/
def putOnTopOrBottom : Effect :=
  mkSpell .creature
    (.moveZone (.target 0) (.library .owner .top true) .put {})

def untapPumpMaybeAttach (power toughness : Int) : Effect :=
  let equipYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])
  mkSpell .creatureYouControl
    (.seq #[
      Instruction.untap (.target 0),
      Instruction.pumpFixed (.target 0) power toughness,
      Instruction.ifThen (.exists (.filter (.target 0) (.hasSubtype (.literal .dwarf))))
        (Instruction.may .you none (.permanent (.attach equipYouControl (.target 0) true)))
    ])

def exchangeControlSharingType : Effect :=
  mkSpell .twoNonlandsSharingType
    (.installEffect (.applyContinuous .indefinite (.target 0) (.exchangeControl (.target 1))))

def returnSpellDraw : Effect :=
  mkSpell .spell
    (.seq #[Instruction.bounce (.target 0), Instruction.drawFixed 1])

def creaturesYouControlGet (power toughness : Int) : Effect :=
  mkSpell .none
    (Instruction.pumpFixed creaturesYouControlExpr power toughness)

def destroyArtifactOrEnchantmentGainLife (life : Nat) : Effect :=
  mkSpell .artifactOrEnchantment
    (.seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed life])

def amassGoblins (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.amassFixed n .goblin)

def drawLoseLifeThenAmass (n : Nat) : Effect :=
  mkSpell .none
    (.seq #[Instruction.drawFixed 1, Instruction.loseLifeFixed 1, Instruction.amassFixed n .goblin])

def returnCreatureFromGyThenAmass (n : Nat) : Effect :=
  mkSpell (TargetSpec.creatureCardInYourGraveyard.asUpTo 1)
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.amassFixed n .goblin
    ])

/-- Counter the targeted spell. If its mana value was `n` or less, recruit.
The mana value includes `{X}` from when the spell was on the stack. -/
def counterThenRecruitIfMvAtMost (n : Nat) : Effect :=
  mkSpell .spell
    (.seq #[
      Instruction.counter (.target 0),
      Instruction.ifThen (.cmp .le (.objectStat .manaValue (.target 0)) (.const (Int.ofNat n)))
        Instruction.recruit
    ])

def plusOneThenFight (n : Nat) : Effect :=
  mkSpell .creatureYouControlThenOppCreature
    (.seq #[
      Instruction.putPlusOne (.target 0) n,
      .damage (.fight (.target 0) (.target 1) false)
    ])

/-- Put a +1/+1 counter on the targeted creature you control. If this spell
was cast from a graveyard, also put one on each other creature you control. -/
def plusOneThenEachOtherIfFromGy : Effect :=
  let otherCreaturesYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .otherThan (.target 0)])
  mkSpell .creatureYouControl
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.ifThen (.castPred (.castFrom .graveyard .this))
        (Instruction.putPlusOne otherCreaturesYouControl 1)
    ])

/-- Draw `n` cards, or `fromGy` cards if this spell was cast from a graveyard. -/
def drawIfFromGy (n fromGy : Nat) : Effect :=
  mkSpell .none
    (.ifCond (.castPred (.castFrom .graveyard .this))
      (Instruction.drawFixed fromGy) (Instruction.drawFixed n))

/-- Amass Goblins `n`, or `fromGy` if this spell was cast from a graveyard. -/
def amassGoblinsOrFromGy (n fromGy : Nat) : Effect :=
  mkSpell .none
    (.ifCond (.castPred (.castFrom .graveyard .this))
      (Instruction.amassFixed fromGy .goblin) (Instruction.amassFixed n .goblin))

def dealDamageToEachOppCreature (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.dealDamageFixed (.objects oppCreaturesExpr) n)

def destroyTargetArtifact : Effect :=
  destroyTarget .artifact

def targetPlayerDraw (n : Nat) : Effect :=
  mkSpell .player
    (Instruction.drawFixed n (.target 0))

def dealDamageToCreatureExileIfDies (n : Nat) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.exileIfDiesThisTurn (.target 0),
      Instruction.dealDamageFixed (.targetSlot 0) n
    ])

def dealDamageToEachNonDragon (n : Nat) : Effect :=
  let nonDragons : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal .dragon))])
  mkSpell .none
    (Instruction.dealDamageFixed (.objects nonDragons) n)

def chooseTypeReturnOthers : Effect :=
  mkSpell .none
    (.bind ⟨0⟩ (.player (.choose .you .creatureType))
      (Instruction.bounce (.inZones .battlefield (.all #[
        .hasType .creature, .not (.hasSubtype (.fromStep ⟨0⟩))
      ]))))

def drawEqualToughnessThenPutCreatures : Effect :=
  mkSpell .none
    (.seq #[
      Instruction.draw (.aggregate .max (.stat .toughness) creaturesYouControlExpr),
      .moveZone (.inZones (.handOf .you) (.hasType .creature)) (.battlefield .controller) .put {
        choice? := some { chooser := .controller, count := .anyNumber }
      }
    ])

def millThenPutInstantOrSorcery (n : Nat) : Effect :=
  mkSpell .none
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasType .instant, .hasType .sorcery]) (.exact (.const 1))
        (.hand .controller)
      rest := .leaveInPlace
    }))

def millThenPutLands (n max : Nat) : Effect :=
  mkSpell .none
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.hasType .land) (.upTo (.const (Int.ofNat max)))
        (.hand .controller)
      rest := .leaveInPlace
    }))

def exileThenReturnYouControl : Effect :=
  mkSpell .twoCreaturesOrLandsYouControl
    (.moveZone .allTargets .exile .exile {
      delayedReturn? := some (.immediately false .owner)
    })

def millThenPutAllInstantsOrSorceries (n : Nat) : Effect :=
  mkSpell .none
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasType .instant, .hasType .sorcery]) .anyNumber
        (.hand .controller)
      rest := .leaveInPlace
    }))

def exileAttackersSearchBasics : Effect :=
  let targetPlayerAttackers : ObjectExpr :=
    .inZones .battlefield (.all #[
      .combatRole .attacking, .hasType .creature, .controlledBy (.ofExpr (.target 0))
    ])
  mkSpell .player
    (.bind ⟨0⟩ (Instruction.exile targetPlayerAttackers)
      (Instruction.may (.target 0) none
        (.player (.searchLibrary {
          searcher := .target 0
          zones := .libraryOf (.target 0)
          filter := .all #[.hasSupertype .basic, .hasType .land]
          count := .upTo (.stepMetric .movedCount ⟨0⟩)
          dest := .battlefield (.player (.target 0))
          mods := { tapped := true }
          reveal := false
          shuffle := true
        }))))

def createTokensX (kind : TokenSpec) : Effect :=
  mkSpell .none
    (Instruction.createTokens kind .chosenX)

def exileTopPlayIfYouControlSubtype (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkSpell .none
    (.moveZone (.topOfLibrary .you (.const (Int.ofNat n))) .exile .exile {
      enterFaceDown := true
      grantPlayPerm? := some {
        duration := .indefinite
        landsAllowed := true
        condition? := some (.exists (.inZones .battlefield (.all #[
          .hasSubtype (.literal sub), .controlledBy .you
        ])))
      }
    })

def exileTopXOppPlayForLife : Effect :=
  mkSpell .opponent
    (.moveZone (.topOfLibrary (.target 0) .chosenX) .exile .exile {
      grantPlayPerm? := some {
        duration := .untilEndOfTurn
        landsAllowed := true
        payLifeInsteadOfMana := true
      }
    })

def riddlesInTheDark : Effect :=
  mkSpell .none
    (.player (.inspectLibrary {
      source := .topCards .you (.const 4) false
      action := .splitIntoPiles .you .opponents 2 (.hand .controller) .graveyard
      rest := .leaveInPlace
    }))

def supperForSpiders : Effect :=
  mkSpell .none
    (.moveZone
      (.inZones (.graveyardOf .opponents) (.all #[.hasType .creature, .putIntoGraveyardFromBattlefieldThisTurn]))
      (.battlefield .controller) .put {
        enterTypeMod? := some { types := #[.artifact], subtypes := #[.food] }
        enterAsPredefined? := some .food
      })

def eaglesAreComing : Effect :=
  mkSpell (.ofDomain (.object .battlefield (.all #[.hasType .creature, .ownedBy .you])))
    (.bind ⟨0⟩ (Instruction.bounce .allTargets)
      (.installEffect (.createDelayedTrigger {
        pattern := .stepEachUpkeep
        duration := .indefinite
        oneShot := true
        effect := {
          body := Instruction.createTokens .birdSoldier (.stepMetric .movedCount ⟨0⟩)
        }
      })))

def lookAtTopLandsGainLife (n life : Nat) : Effect :=
  mkSpell .none
    (.seq #[
      .player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) false
        action := .takeMatching (.hasType .land) .anyNumber (.battlefield .controller) { tapped := true }
        rest := .shuffleIntoLibrary
      }),
      Instruction.gainLifeFixed life
    ])

def damageOppCreaturesEqualOtherSpellsMv : Effect :=
  mkSpell .none
    (Instruction.dealDamage (.objects oppCreaturesExpr)
      (.playerMetric .otherSpellsManaValueThisTurn .you))

def phaseOutKicker : Effect :=
  let targetCtrlCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  mkSpell { slots := #[{
      domain := .object .battlefield (.hasType .creature)
      altDomainIf? := some (.castPred (.wasKicked .this), .player .any)
    }] }
    (.ifCond (.castPred (.wasKicked .this))
      (.permanent (.phaseOut targetCtrlCreatures none))
      (.permanent (.phaseOut (.target 0) none)))

def dealDamageThenControllerIfTeamwork (n extra : Nat) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) n,
      Instruction.ifThen (.castPred (.teamworkPaid .this))
        (Instruction.dealDamageFixed (.players (.controllerOf (.target 0))) extra)
    ])

def exileCreatureMvAtMostOrAnyIfTeamwork (n life : Nat) : Effect :=
  mkSpell (.creatureMvAtMostOrAnyIfTeamwork n)
    (.ifCond (.castPred (.teamworkPaid .this))
      (.seq #[Instruction.exile (.target 0), Instruction.gainLifeFixed life])
      (Instruction.exile (.target 0)))

def returnGyCreatureMvAtMostOrAny (n : Nat) : Effect :=
  mkSpell (.creatureCardInYourGraveyardMvAtMostOrAnyIfTeamwork n)
    (.moveZone (.target 0) (.battlefield .controller) .put {})

def revealTopPutCreatures (n : Nat) : Effect :=
  mkSpell .none
    (.ifCond (.castPred (.teamworkPaid .this))
      (.player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) true
        action := .takeMatching (.hasType .creature) .anyNumber (.battlefield .controller)
        rest := .graveyard
      }))
      (.player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) true
        action := .takeMatching (.hasType .creature) (.upTo (.const 1)) (.battlefield .controller)
        rest := .graveyard
      })))

def createTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.createTokensFixed kind n)

def exileCreatureToughnessAtLeast (n : Int) : Effect :=
  let spec := TargetSpec.creatureToughnessAtLeast n
  mkSpell spec
    (Instruction.exile (.target 0))

def returnOneOrTwoNonlands : Effect :=
  mkSpell (TargetSpec.nonland.asBetween 1 2)
    (Instruction.bounce .allTargets)

def targetPlayerCreatesTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkSpell .player
    (Instruction.createTokensFixed kind n (.target 0))

def destroyCreatureSurveil : Effect :=
  mkSpell .creature
    (.seq #[Instruction.destroy (.target 0), Instruction.surveilFixed 1])

def investigatePumpFlyingUntap : Effect :=
  mkSpell .playerThenCreature
    (.seq #[
      Instruction.createTokensFixed .clue 1 (.target 0),
      Instruction.grantKeywords (.target 1) #[Keyword.flying],
      Instruction.untap (.target 1),
      Instruction.pumpFixed (.target 1) 1 0
    ])

def plusOneLifelinkIndestructible : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.lifelink, Keyword.indestructible]
    ])

def dealDamageToEachCreature (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.dealDamageFixed (.objects allCreaturesExpr) n)

def destroyLandSearchBasic : Effect :=
  mkSpell .artifactOrLand
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.may (.controllerOf (.target 0)) none
        (.player (.searchLibrary {
          searcher := .controllerOf (.target 0)
          zones := .libraryOf (.controllerOf (.target 0))
          filter := .all #[.hasSupertype .basic, .hasType .land]
          count := .upTo (.const 1)
          dest := .battlefield (.player (.controllerOf (.target 0)))
          mods := { tapped := true }
          reveal := false
          shuffle := true
        }))
    ])

def doublePowerAndToughness : Effect :=
  mkSpell .creature
    (Instruction.doublePT (.target 0))

def returnGySubtypeToHand (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkSpell (.ofDomain (.object .yourGraveyard (.all #[.hasSubtype (.literal sub), .isKind .card])))
    (.moveZone (.target 0) (.hand .controller) .returnToHand {})

def grantVigilanceUnblockable : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.grantKeywords (.target 0) #[Keyword.vigilance],
      Instruction.cantBeBlocked (.target 0),
      Instruction.drawFixed 1
    ])

def becomeArtifactCreature44Flying : Effect :=
  mkSpell .artifactOrCreatureYouControl
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.all #[
        .modifyTypes { types := #[.artifact, .creature] },
        .setBasePT (some (.const 4)) (some (.const 4)),
        .grantKeywords #[Keyword.flying]
      ])))

def drawThreeDiscardUnlessArtifact : Effect :=
  mkSpell .none
    (.seq #[
      Instruction.drawFixed 3,
      .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard {
        choice? := some {
          chooser := .controller
          count := .exact (.const 2)
          unlessMatching? := some (.hasType .artifact)
        }
      }
    ])

def eachOpponentLosesLife (n : Nat) : Effect :=
  mkSpell .none
    (Instruction.loseLifeFixed n .opponents)

def fight : Effect :=
  mkSpell .creatureYouControlThenOppCreature
    (.damage (.fight (.target 0) (.target 1) false))

def fightUpToOne : Effect :=
  mkSpell (.ofSlots #[.of .creatureYouControl, { domain := .anotherCreature, count := .upTo 1 }])
    (.damage (.fight (.target 0) (.target 1) false))

def pumpThenDraw (power toughness : Int) : Effect :=
  mkSpell .creature
    (.seq #[Instruction.pumpFixed (.target 0) power toughness, Instruction.drawFixed 1])

def pumpThenExileTopPlay (power toughness : Int) : Effect :=
  mkSpell .creature
    (.seq #[
      Instruction.pumpFixed (.target 0) power toughness,
      .moveZone (.topOfLibrary .you (.const 1)) .exile .exile {
        grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
      }
    ])

def creatureYouControlDealsTwicePower (k : Nat := 2) : Effect :=
  let dmg : ValueExpr :=
    if k == 1 then .objectStat .power (.target 0)
    else .binary .mul (.const (Int.ofNat k)) (.objectStat .power (.target 0))
  mkSpell .creatureYouControlThenOppCreature
    (Instruction.dealDamage (.targetSlot 1) dmg (.target 0))

def createTokensThenTeamPump (kind : TokenSpec) (n : Nat) (power toughness : Int) : Effect :=
  mkSpell .none
    (.seq #[
      Instruction.createTokensFixed kind n,
      Instruction.pumpFixed creaturesYouControlExpr power toughness
    ])

def creaturesYouControlGetAndGrant (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  mkSpell .none
    (.seq #[
      Instruction.pumpFixed creaturesYouControlExpr power toughness,
      Instruction.grantKeywords creaturesYouControlExpr k
    ])

def createGalactus : Effect :=
  mkSpell .none
    (Instruction.createTokensFixed .galactus 1)

def worldsWithinWorlds : Effect :=
  mkSpell .none
    (.bind ⟨0⟩ (Instruction.exile allCreaturesExpr)
      (.seq #[
        .forEach (.eachPlayer .any) ⟨1⟩
          (.moveZone (.inZones (.handOf (.stepPlayers ⟨1⟩)) (.hasType .creature))
            (.battlefield (.player (.stepPlayers ⟨1⟩))) .put {
              choice? := some { chooser := .player (.stepPlayers ⟨1⟩), count := .anyNumber }
            }),
        .moveZone (.stepObjects ⟨0⟩) (.hand .owner) .put {},
        .installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack)
      ]))

def exileHandDrawPlayUntilNext : Effect :=
  mkSpell .none
    (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .exile .exile {
        grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
      })
      (Instruction.draw (.stepMetric .movedCount ⟨0⟩)))

def copyNontokenCreaturesYouControl : Effect :=
  let nontokenCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .isToken false])
  mkSpell .none
    (.forEach (.eachObject nontokenCreatures) ⟨0⟩
      (Instruction.createTokens (.copyOf (.stepObjects ⟨0⟩) #[.removeSupertype .legendary])))

def gainControlUntilEotOrNextIfVillain : Effect :=
  let biggerVillain : Condition :=
    .exists (.inZones .battlefield (.all #[
      .hasSubtype (.literal .villain),
      .controlledBy .you,
      .stat .manaValue .gt (.objectStat .manaValue (.target 0))
    ]))
  mkSpell .creature
    (.seq #[
      .ifCond biggerVillain
        (.installEffect (.applyContinuous (.untilEndOfNextTurnOf .you) (.target 0) (.gainControl .you)))
        (.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.gainControl .you))),
      Instruction.untap (.target 0),
      Instruction.grantKeywords (.target 0) #[Keyword.haste]
    ])

def gainLifeSearchBasicPlusOne (life : Nat) : Effect :=
  mkSpell .upToOneCreatureThenPlayer
    (.seq #[
      Instruction.gainLifeFixed life (.target 1),
      .player (.searchLibrary {
        searcher := .target 1
        zones := .libraryOf (.target 1)
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield (.player (.target 1))
        mods := { tapped := true }
        reveal := false
        shuffle := true
      }),
      Instruction.putPlusOne (.target 0) 1
    ])

def nextFreeRGCreature : Effect :=
  mkSpell .none
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod
        (.spells .you (.all #[
          .hasType .creature,
          .any #[.hasColor (.literal .red), .hasColor (.literal .green)]
        ]))
        .alternativeFree true)))

def ownerPutsLibraryThenConnive : Effect :=
  mkSpell .oppCreatureThenUpToOneCreatureYouControl
    (.seq #[
      .moveZone (.target 0) (.library .owner (.fromTop (.const 2)) true) .put {},
      .player (.connive (.target 1))
    ])

def mayDrawPerArtifactOppsDraw : Effect :=
  let artifactsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
  mkSpell .none
    (Instruction.may .you none
      (.seq #[
        Instruction.draw artifactsCount,
        Instruction.drawFixed 1 .opponents
      ]))

def maySacArtifactOrDiscardDraw (cards : Nat) : Effect :=
  mkSpell .none
    (Instruction.may .you (some CostSpec.sacrificeArtifactOrDiscardCard)
      (Instruction.drawFixed cards))

def returnUpToTwoGyModal : Effect :=
  mkSpell (.single {
      domain := .object .yourGraveyard (.all #[
        .any #[.hasType .artifact, .hasType .creature, .hasType .enchantment, .hasType .land],
        .isKind .card])
      count := .upTo 2 })
    (.moveZone .allTargets (.hand .controller) .returnToHand {})

def artifactSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell .none
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod (.spells .you (.hasType .artifact)) (.reduceGeneric (.const (Int.ofNat n))))))

def supertypeSpellsCostLessThisTurn (n : Nat) : Effect :=
  mkSpell .none
    (.installEffect (.applyRule .untilEndOfTurn
      (.costMod (.spells .you (.hasSupertype .legendary)) (.reduceGeneric (.const (Int.ofNat n))))))

/-! ### Printed Activated-Ability Effect Constructors -/

def exileTopPlayUntilEndOfNextTurn : Effect :=
  mkAbility .none
    (.moveZone (.topOfLibrary .you (.const 1)) .exile .exile {
      grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
    })

def dealDamageToTargetCreature (amount : Nat) : Effect :=
  mkAbility .creature
    (Instruction.dealDamageFixed (.targetSlot 0) amount)

def destroyTargetColorlessNonland : Effect :=
  destroyTarget .colorlessNonland

def becomeSubtypeWithLandsPT (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let landsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you]))
  mkAbility .none
    (.installEffect (.applyContinuous .indefinite .this
      (.all #[
        .modifyTypes { types := #[.creature], subtypes := #[sub] },
        .grantStatic #[.characteristicDefining (.setPT landsCount landsCount)]
      ])))

def becomeBearCreatureWithLandsPT : Effect :=
  becomeSubtypeWithLandsPT "Bear"

def returnFromGraveyardTapped : Effect :=
  mkAbility .none
    (.moveZone .this (.battlefield .controller) .put { tapped := true })

def returnFromGraveyardToHand : Effect :=
  mkAbility .none
    (.moveZone .this (.hand .owner) .returnToHand {})

def destroyTargetArtifactOrEnchantment : Effect :=
  destroyTarget .artifactOrEnchantment

def addAnyColor : Effect :=
  mkAbility .none
    (Instruction.addMana { spec := .oneOf .anyColor (.const 1) })

def destroyTargetPermanent : Effect :=
  destroyTarget .permanent

def plusOneOnTarget (n : Nat) (subtypes : Array String := #[]) : Effect :=
  let spec : TargetSpec :=
    if subtypes.isEmpty then .creatureYouControl
    else .creatureYouControlAnySubtype (CardSubtype.ofSubtypes subtypes)
  mkAbility spec
    (Instruction.putPlusOne (.target 0) n)

def targetCantBeBlockedPowerAtMost (n : Int) : Effect :=
  let spec := TargetSpec.creaturePowerAtMost n
  mkAbility spec
    (Instruction.cantBeBlocked (.target 0))

def recruit : Effect :=
  mkAbility .none
    Instruction.recruit

def ownerShuffleSourceDraw (n : Nat) : Effect :=
  mkAbility .none
    (.bind ⟨0⟩
      (.moveZone .this (.library .owner .bottom false) .shuffleIntoLibrary { shuffleAfter := true })
      (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed n (.ownerOf .this))))

def returnFromGyAttachPowerAtMost (n : Int) : Effect :=
  let spec := TargetSpec.creatureYouControlPowerAtMost n
  mkAbility spec
    (.moveZone .this (.battlefield .controller) .put { attachTo? := some (.target 0) })

def addMana (types : Array ManaType) : Effect :=
  mkAbility .none
    (Instruction.addSimpleMana types)

def searchTwoBasicsSplit : Effect :=
  mkAbility .none
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 2)
      dest := .battlefield .controller
      mods := { tapped := true }
      secondDest? := some (.hand .controller, {})
      reveal := true
      shuffle := true
    }))

def creaturesYouControlGetOppsLoseLife (power toughness : Int) (life : Nat) : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.pumpFixed creaturesYouControlExpr power toughness,
      Instruction.loseLifeFixed life .opponents
    ])

def subtypesGainMenace (subtypes : Array String) : Effect :=
  let subs := CardSubtype.ofSubtypes subtypes
  let scope : ObjectExpr :=
    .inZones .battlefield (.all #[
      .any (subs.map fun s => .hasSubtype (.literal s)),
      .controlledBy .you
    ])
  mkAbility .none
    (Instruction.grantKeywords scope #[Keyword.menace])

def exileThenReturnNextEnd : Effect :=
  mkAbility .twoCreaturesOrLandsYouControl
    (.moveZone .allTargets .exile .exile {
      delayedReturn? := some (.atNextEndStep false .owner)
    })

def searchBasicBeholdSubtypeUntap (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility .none
    (.bind ⟨0⟩ (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .battlefield .controller
        mods := { tapped := true }
        reveal := false
        shuffle := true
      }))
      (Instruction.may .you (some (CostSpec.ofItem (.behold sub)))
        (Instruction.untap (.stepObjects ⟨0⟩))))

def searchBasicBeholdElfUntap : Effect :=
  searchBasicBeholdSubtypeUntap "Elf"

def twoPlayersDraw : Effect :=
  mkAbility .twoPlayers
    (.seq #[Instruction.drawFixed 1 (.target 0), Instruction.drawFixed 1 (.target 1)])

def drawEqualSacrificedPowerThenDiscard : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.draw (.aggregate .sum (.stat .power) .costPaidObjects),
      Instruction.discardFixed 1
    ])

def arwenShare : Effect :=
  mkAbility .anotherCreature
    (.seq #[
      Instruction.grantKeywords (.target 0) #[Keyword.indestructible],
      Instruction.putPlusOne (.target 0) 1,
      Instruction.putCounters (.target 0) .lifelink,
      Instruction.putPlusOne .this 1,
      Instruction.putCounters .this .lifelink
    ])

def putShadowCounter : Effect :=
  mkAbility .creature
    (.seq #[
      Instruction.putCounters (.target 0) .shadow,
      .installEffect (.applyContinuous (.whileHasCounter (.target 0) .shadow) (.target 0)
        (.modifyTypes { subtypes := #[.wraith] }))
    ])

def chooseTwoDestroyRest : Effect :=
  mkAbility .none
    (.moveZone allCreaturesExpr .graveyard .destroy {
      choice? := some {
        chooser := .controller
        count := .upTo (.const 2)
        invertSelection := true
      }
    })

def blackGateUnblockable : Effect :=
  mkAbility .creature
    (.bind ⟨0⟩ (.player (.choose .you .playerWithMostLife))
      (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
        (.applyRule (.combat (.cantBeBlockedBy .self (.controlledBy (.ofExpr (.stepPlayers ⟨0⟩)))))))))

def burdenThenDraw : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.putCounters .this .burden,
      Instruction.draw (.counterCount (some .burden) .this)
    ])

def teamGain (k : Array KeywordAbility) : Effect :=
  mkAbility .none
    (Instruction.grantKeywords creaturesYouControlExpr k)

def sourceGainsIndestructibleTap : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.grantKeywords .this #[Keyword.indestructible],
      Instruction.tap .this
    ])

def plusOneOnEachOtherSubtype (subtype : String) (n : Nat) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let scope : ObjectExpr :=
    .inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])
  mkAbility .none
    (Instruction.putPlusOne scope n)

def plusOneAndIndestructibleCounter : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.putPlusOne .this 1,
      Instruction.putCounters .this .indestructible
    ])

def plusOneAndDraw (plus cards : Nat) : Effect :=
  mkAbility .none
    (.seq #[Instruction.putPlusOne .this plus, Instruction.drawFixed cards])

def plusOneAndExtraTurn : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.putPlusOne .this 1,
      .turn (.extraTurn .you (some (.player (.forbidAbilityActivation .any .powerUp))))
    ])

def eachOppDiscardThenPlusOne : Effect :=
  mkAbility .none
    (.seq #[
      .forEach (.eachPlayer .opponent) ⟨0⟩ (Instruction.discardFixed 1 (.stepPlayers ⟨0⟩)),
      Instruction.putPlusOne .this 1
    ])

def lookAtTopPutTypes (n : Nat) (types : Array String) : Effect :=
  let subs := CardSubtype.ofSubtypes types
  mkAbility .none
    (.seq #[
      Instruction.putPlusOne .this 2,
      .player (.inspectLibrary {
        source := .topCards .you (.const (Int.ofNat n)) false
        action := .takeMatching
          (.any (subs.map fun s => .hasSubtype (.literal s)))
          (.upTo (.const 1)) (.battlefield .controller) { mayTransformOnEnter := true }
        rest := .bottomRandom
      })
    ])

def transform : Effect :=
  mkAbility .none
    (.permanent (.transform .this))

def lookAtTopRevealArtifact (n : Nat) : Effect :=
  mkAbility .none
    (.player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) false
      action := .takeMatching (.hasType .artifact) (.upTo (.const 1)) (.hand .controller) {} true
      rest := .bottomRandom
    }))

def connive : Effect :=
  mkAbility .none
    (.player (.connive .this))

def addAnyColorSpendOnlySubtype (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility .none
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 1)
      restriction := some (.subtypeSpellOrSource sub)
    })

def addAnyColorSpendOnlyHero : Effect :=
  addAnyColorSpendOnlySubtype "Hero"

def addAnyColorSpendOnlyVillain : Effect :=
  addAnyColorSpendOnlySubtype "Villain"

def addAnyColorSpendOnlyArtifactSpell : Effect :=
  mkAbility .none
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 1)
      restriction := some (.onlyForSpells (.hasType .artifact))
    })

def addTwoAnyColorCreatureSources : Effect :=
  mkAbility .none
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 2)
      restriction := some (.onlyForAbilities (.sourceMatches (.hasType .creature)))
    })

def addBlueCantNonartifact : Effect :=
  mkAbility .none
    (Instruction.addMana {
      spec := .fixedOne (.colored .blue)
      restriction := some (.cantSpendOnSpells (.not (.hasType .artifact)))
    })

def addAnyColorEqualToSourcePower : Effect :=
  mkAbility .none
    (Instruction.addMana {
      spec := .oneOf .anyColor (.objectStat .power .this)
    })

def addTwoAnyColorEquipment : Effect :=
  mkAbility .none
    (Instruction.addMana {
      spec := .oneOf .anyColor (.const 2)
      restriction := some (.onlyForSpellsOrAbilities (.hasSubtype .equipment) .equip)
    })

def drawPerDiscardedThisTurn : Effect :=
  mkAbility .none
    (Instruction.draw (.playerMetric .cardsDiscardedThisTurn .you))

def exileTopXPlayThisTurn : Effect :=
  mkAbility .none
    (.moveZone (.topOfLibrary .you (.objectStat .power .this)) .exile .exile {
      grantPlayPerm? := some { duration := .untilEndOfTurn, landsAllowed := true }
    })

def copyControlledAbility (ty : CardType) : Effect :=
  mkAbility (.stackAbilityFromSource ty)
    (.stack (.copyStackObject (.target 0) (.const 1) true))

def createTokensEqualSubtype (kind : TokenSpec) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let cnt : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you]))
  mkAbility .none
    (Instruction.createTokens kind cnt)

def createTappedTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkAbility .none
    (Instruction.createTokensFixed kind n .you true)

def destroyUpToOneThenPlusOne : Effect :=
  mkAbility (TargetSpec.artifactOrEnchantment.asUpTo 1)
    (.seq #[Instruction.destroy (.target 0), Instruction.putPlusOne .this 1])

def equipmentBecomesConstructHero : Effect :=
  let artifactsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
  mkAbility .none
    (Instruction.ifThen (.exists (.filter .this (.not (.hasType .creature))))
      (.installEffect (.applyContinuous .untilEndOfTurn .this
        (.all #[
          .modifyTypes { mode := .setAndKeepNoncreatureSubtypes, types := #[.artifact, .creature], subtypes := #[.construct, .hero] },
          .setBasePT (some (.const 0)) (some (.const 0)),
          .grantKeywords #[Keyword.flying],
          .modifyPT artifactsCount artifactsCount
        ]))))

def lookAtTopRevealSubtype (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility .none
    (.player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) false
      action := .takeMatching (.hasSubtype (.literal sub)) (.upTo (.const 1)) (.hand .controller) {} true
      rest := .bottomAnyOrder
    }))

def millThenPutSubtypeOrEnchantment (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  mkAbility .none
    (.player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.any #[.hasSubtype (.literal sub), .hasType .enchantment])
        (.upTo (.const 1)) (.hand .controller)
      rest := .leaveInPlace
    }))

def plusOneAndDoubleStrikeCounter : Effect :=
  mkAbility .none
    (.seq #[Instruction.putPlusOne .this 1, Instruction.putCounters .this .doubleStrike])

def plusOneThenFightUpToOne : Effect :=
  mkAbility (TargetSpec.oppCreature.asUpTo 1)
    (.seq #[
      Instruction.putPlusOne .this 1,
      .damage (.fight .this (.target 0) false)
    ])

def plusOneAndGrant (k : Array KeywordAbility) : Effect :=
  mkAbility .none
    (.seq #[Instruction.putPlusOne .this 1, Instruction.grantKeywords .this k])

def plusOneAndCreateTigerGod : Effect :=
  mkAbility .none
    (.seq #[Instruction.putPlusOne .this 1, Instruction.createTokensFixed .tigerGod 1])

def plusOneAndCreateTokens (n : Nat) (kind : TokenSpec) : Effect :=
  mkAbility .none
    (.seq #[Instruction.putPlusOne .this n, Instruction.createTokensFixed kind 1])

def plusTwoThenOddEvenDestroy : Effect :=
  mkAbility .none
    (.seq #[
      Instruction.putPlusOne .this 2,
      .bind ⟨0⟩ (.player (.choose .you .oddOrEven))
        (Instruction.destroy (.inZones .battlefield (.all #[
          .hasType .creature, .otherThan .this, .statParity .manaValue (.fromStep ⟨0⟩)
        ])))
    ])

def returnFromGyFinalityAttach : Effect :=
  let equipYouControl : ObjectExpr :=
    .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy .you])
  mkAbility .none
    (.bind ⟨0⟩ (.moveZone .this (.battlefield .controller) .put {
        enterCounters := #[(.finality, .const 1)]
      })
      (Instruction.may .you none (.permanent (.attach equipYouControl (.stepObjects ⟨0⟩) true))))

def returnGyCreatureThenPlusOne (n : Nat) : Effect :=
  mkAbility (TargetSpec.creatureCardInYourGraveyard.asUpTo 1)
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.putPlusOne .this n
    ])

def revealTopDrawIfArtifact : Effect :=
  mkAbility .none
    (.bind ⟨0⟩ (.player (.reveal .you (.topOfLibrary .you (.const 1))))
      (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.hasType .artifact)))
        (Instruction.drawFixed 1)))

def copyArtifactYouControlNotLegendary : Effect :=
  mkAbility .twoArtifactsYouControl
    (.installEffect (.applyContinuous .untilEndOfTurn (.target 0)
      (.becomeCopyOf (.target 1) #[.removeSupertype .legendary])))

def pumpAttackingAloneGainLife : Effect :=
  mkAbility .attackingAloneCreatureYouControl
    (.seq #[Instruction.pumpFixed (.target 0) 1 0, Instruction.gainLifeFixed 1])

def becomeTypes (types : Array String) (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  let subs := CardSubtype.ofSubtypes types
  mkAbility .none
    (.installEffect (.applyContinuous .untilEndOfTurn .this
      (.all #[
        .modifyTypes { mode := .setAndKeepNoncreatureSubtypes, types := #[.creature], subtypes := subs },
        .setBasePT (some (.const power)) (some (.const toughness)),
        .grantKeywords k
      ])))

def becomeDinosaurHero (power toughness : Int) (k : Array KeywordAbility) : Effect :=
  becomeTypes #["Dinosaur", "Hero"] power toughness k

def nextInstantSorceryCopyIfMvAtMostSourcePower : Effect :=
  mkAbility .none
    (.installEffect (.createDelayedTrigger {
      pattern := .castSpell .you (.all #[
        .any #[.hasType .instant, .hasType .sorcery],
        .stat .manaValue .le (.objectStat .power .this)
      ])
      duration := .untilEndOfTurn
      oneShot := true
      effect := { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
    }))

def harnessInfinityStone : Effect :=
  mkAbility .none
    (.permanent (.setDesignation .this .harnessed true))

def destroyTargetNoncreatureArtOrEnch : Effect :=
  destroyTarget .noncreatureArtifactOrEnchantment

/-! ### Ability-Phrased Factories for Names That Overlap Spells -/

def abilityCreateTokens (kind : TokenSpec) (n : Nat) : Effect :=
  mkAbility .none
    (Instruction.createTokensFixed kind n)

def abilityCreateTokensX (kind : TokenSpec) : Effect :=
  mkAbility .none
    (Instruction.createTokens kind .chosenX)

def abilityDrawThenDiscard (n : Nat) : Effect :=
  mkAbility .none
    (.seq #[Instruction.drawFixed n, Instruction.discardFixed 1])

def abilityTargetPlayerDraw (n : Nat) : Effect :=
  mkAbility .player
    (Instruction.drawFixed n (.target 0))

/-! ### Reality Fracture Ability & Spell Effects -/

def targetCreatureBecomesPrepared : Effect :=
  mkAbility .creature
    (Instruction.becomePrepared (.target 0))

def eachCreatureYouControlBecomesPrepared : Effect :=
  mkAbility .none
    (Instruction.becomePrepared creaturesYouControlExpr)

def mayDiscardDraw (n : Nat) : Effect :=
  mkAbility .none
    (Instruction.may .you (some (CostSpec.ofItem (.discard (.count (.const 1)) (.matching .anyObject))))
      (Instruction.drawFixed n))

def createTokensThenSurveil (kind : TokenSpec) (n s : Nat) : Effect :=
  mkAbility .none
    (.seq #[Instruction.createTokensFixed kind n, Instruction.surveilFixed s])

def setBasePT (power toughness : Int) : Effect :=
  mkAbility .creature
    (Instruction.setBasePTFixed (.target 0) power toughness)

def jaceLoyaltyAtInstantSpeed : Effect :=
  mkAbility .none
    (.installEffect (.applyRule .untilEndOfTurn
      (.play (.activateLoyaltyAsInstant .you (.hasSubtype (.literal .jace))))))

def emblemCastSpellDamage (n : Nat) : Effect :=
  mkAbility .none
    (.create (.emblem .you {
      triggeredAbilities := #[{
        word := .whenever
        pattern := .castSpell .you .anyObject
        effect := {
          targets := .anyTarget
          body := Instruction.dealDamageFixed (.targetSlot 0) n
        }
      }]
    }))

def copyNextInstantSorceryThisTurn : Effect :=
  mkAbility .none
    (.installEffect (.createDelayedTrigger {
      pattern := .castSpell .you (.any #[.hasType .instant, .hasType .sorcery])
      duration := .untilEndOfTurn
      oneShot := true
      effect := { body := .stack (.copyStackObject .triggerSubject (.const 1) true) }
    }))

def copyEachCreatureOfTargetPlayer : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])
  let sacEndStep : GrantedAbility :=
    .triggered {
      word := .at
      pattern := .stepEachEndStep
      interveningIf? := some (.not (.exists (.inZones .battlefield (.all #[
        .hasType .planeswalker, .controlledBy .you
      ]))))
      effect := { body := Instruction.sacrifice .this }
    }
  mkAbility .player
    (.forEach (.eachObject targetPlayerCreatures) ⟨0⟩
      (Instruction.createTokens (.copyOf (.stepObjects ⟨0⟩) #[
        .addKeywords #[Keyword.haste],
        .addAbilities #[sacEndStep]
      ])))

/-! ### Reality Fracture Named Spell Effects (Unified `Instruction`) -/

/-- Build a spell `Effect` from targeting and unified `Instruction` body. -/
def fraSpell (spec : TargetSpec) (body : Instruction) : Effect :=
  { targets := spec, body }

def fraSpellOn (d : TargetDomain) (body : Instruction) : Effect :=
  fraSpell (.ofDomain d) body

def fraUntargeted (body : Instruction) : Effect :=
  fraSpell .none body

/-! ## White -/

def generousRevival : Effect :=
  fraSpell (.creatureCardInYourGraveyardMvAtMost 3)
    (.moveZone (.target 0) (.battlefield .controller) .put {
      enterCounters := #[(.plusOnePlusOne, .const 1)]
    })

def hexhavenBattalion : Effect :=
  fraUntargeted (Instruction.createTokensFixed .cadet 3)

def kindredJudgment : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (.player (.choose .you .creatureType))
      (Instruction.destroy (.inZones .battlefield (.all #[
        .hasType .creature, .not (.hasSubtype (.fromStep ⟨0⟩))
      ]))))

def loyalTutor : Effect :=
  fraUntargeted
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasType .planeswalker
      count := .upTo (.const 1)
      dest := .library .owner .top false
      reveal := true
      shuffle := true
    }))

def predictivePreparations : Effect :=
  fraSpell (.single { domain := .creature, count := .between 1 2 })
    (Instruction.putPlusOne .allTargets 1)

def prophesiedEnd : Effect :=
  fraSpell .creature
    (.bind ⟨0⟩ (Instruction.destroy (.target 0))
      (Instruction.ifThen (.exists (.filter (.target 0) (.not (.combatRole .attacking))))
        (Instruction.drawFixed 1 (.controllerOf (.target 0)))))

def refuteDestiny : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .any #[.hasColor (.literal .green), .hasColor (.literal .blue)]]))
    (.seq #[Instruction.exile (.target 0), Instruction.surveilFixed 1])

def returnToTheLightRealms : Effect :=
  fraUntargeted
    (.moveZone (.inZones (.graveyardOf .you) (.all #[.isKind .permanentCard, .not (.hasType .land)]))
      (.battlefield .controller) .put {})

def yourFateEndsHere : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .stat .manaValue .ge (.const 3)]))
    (.seq #[Instruction.destroy (.target 0), Instruction.surveilFixed 1])

/-! ## Blue -/

def cruelCalculations : Effect :=
  fraSpell .player
    (Instruction.draw (.playerMetric .cardsMilledThisTurn (.target 0)))

def preciseRedaction : Effect :=
  fraSpellOn (.object .stack (.all #[
      .any #[.hasColor (.literal .white), .hasColor (.literal .black)],
      .isKind .spell]))
    (Instruction.counter (.target 0))

def sphinxsApproach : Effect :=
  fraUntargeted
    (.seq #[
      Instruction.drawFixed 2,
      Instruction.may .you
        (some (CostSpec.ofItems #[
          .exile (.count (.const 1)) .stack .self,
          .exile (.count (.const 4)) .yourGraveyard (.filter (.named (.literal "Sphinx's Approach")))
        ]))
        (.player (.searchLibrary {
          zones := .libraryOf .you
          filter := .all #[.hasType .creature, .hasSubtype (.literal .sphinx)]
          count := .upTo (.const 1)
          dest := .battlefield .controller
          reveal := false
          shuffle := true
        }))
    ])

def unsummon : Effect :=
  fraSpell .creature (Instruction.bounce (.target 0))

def unwindHistory : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .hasType .creature, .controlledBy .opponent, .stat .manaValue .le (.const 3)]))
    (.seq #[Instruction.bounce (.target 0), Instruction.surveilFixed 1])

def arcOfFortune : Effect :=
  fraUntargeted
    (.forEach (.eachPlayer .any) ⟨0⟩
      (Instruction.may (.stepPlayers ⟨0⟩) none
        (.seq #[
          .moveZone (.inZones (.handOf (.stepPlayers ⟨0⟩)) .anyObject) .graveyard .discard {},
          Instruction.drawFixed 7 (.stepPlayers ⟨0⟩)
        ])))

/-! ## Black -/

def castAwayDoubt : Effect :=
  fraUntargeted
    (.seq #[Instruction.drawFixed 2, Instruction.dealDamageFixed (.players .eachPlayer) 2])

def extendedAbsence : Effect :=
  fraSpell .creatureOrPlaneswalker
    (.seq #[
      Instruction.exile (.target 0),
      Instruction.dealDamageFixed (.players .opponents) 1,
      Instruction.gainLifeFixed 1
    ])

def extrapolateTheImpossible : Effect :=
  fraUntargeted
    (Instruction.may .you none
      (.player (.inspectLibrary {
        source := .outsideTheGame .you 2
        action := .takeMatching .anyObject (.exact (.const 1)) (.hand .controller)
        rest := .leaveInPlace
        chooser := .opponents
      })))

def overwriteTheMultiverse : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.exile allCreaturesExpr)
      (Instruction.empower .jace (.stepMetric .movedCount ⟨0⟩)))

def rewriteRegrets : Effect :=
  fraSpellOn (.object .yourGraveyard (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .isKind .card,
      .stat .manaValue .le (.const 6)]))
    (.moveZone (.target 0) (.battlefield .controller) .put {})

def solveForDisappointment : Effect :=
  fraSpell .opponent
    (.moveZone (.inZones (.handOf (.target 0)) (.all #[.isKind .permanentCard, .not (.hasType .land)]))
      .graveyard .discard {
        choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true }
      })

def terminalCriticism : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasType .creature, .hasType .planeswalker],
      .any #[.hasColor (.literal .blue), .hasColor (.literal .red)]]))
    (.seq #[Instruction.destroy (.target 0), Instruction.gainLifeFixed 1])

/-! ## Red -/

def artifistAcumen : Effect :=
  fraUntargeted
    (.seq #[
      Instruction.grantKeywords creaturesYouControlExpr #[Keyword.firstStrike],
      Instruction.drawFixed 1
    ])

def awakenTheInferno : Effect :=
  fraSpell (.ofSlots #[.of .oppCreatureOrPlaneswalker, { domain := .creatureYouControl, count := .upTo 1 }])
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) 6,
      Instruction.putPlusOne (.target 1) 1
    ])

def commandTheStage : Effect :=
  let wizardTokens : ObjectExpr :=
    .inZones .battlefield (.all #[.isToken true, .hasSubtype (.literal .wizard), .controlledBy .you])
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.createTokensFixed .cadet 1)
      (Instruction.putPlusOne (.diff wizardTokens (.stepObjects ⟨0⟩)) 1))

def essenceBurn : Effect :=
  fraSpellOn (.object .battlefield (.all #[
      .any #[.hasColor (.literal .black), .hasColor (.literal .green)],
      .any #[.hasType .creature, .hasType .planeswalker]]))
    (.seq #[
      Instruction.exileIfDiesThisTurn (.target 0),
      Instruction.dealDamageFixed (.targetSlot 0) 5
    ])

def moltenTide : Effect :=
  fraUntargeted
    (.installEffect (.createDelayedTrigger {
      pattern := .activateAbility .you (.all #[.hasSubtype (.literal .mountain), .controlledBy .you]) .manaAbility
      duration := .untilEndOfTurn
      oneShot := false
      effect := { body := Instruction.addSimpleMana #[.colored .red] }
    }))

/-! ## Green -/

def enroot : Effect :=
  fraUntargeted
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasType .land
      count := .upTo (.const 1)
      dest := .graveyard
      reveal := false
      shuffle := true
    }))

def flourishingGrapple : Effect :=
  fraSpell (.ofSlots #[
      .of (.object .battlefield (.all #[
        .any #[.hasType .creature, .hasType .planeswalker],
        .controlledBy .opponent,
        .any #[.hasColor (.literal .red), .hasColor (.literal .white)]])),
      .of .creatureYouControl])
    (.seq #[
      Instruction.loseAllAbilities (.target 0),
      Instruction.dealDamage (.targetSlot 0) (.objectStat .power (.target 1)) (.target 1)
    ])

def restoreWithEmpathy : Effect :=
  fraSpell .permanentCardInYourGraveyard
    (.seq #[
      .moveZone (.target 0) (.hand .controller) .returnToHand {},
      Instruction.gainLifeFixed 4
    ])

def somethingWorthSaving : Effect :=
  fraUntargeted
    (.seq #[
      .player (.inspectLibrary {
        source := .millCards .you (.const 4)
        action := .takeMatching (.isKind .permanentCard) (.upTo (.const 1)) (.hand .controller)
        rest := .leaveInPlace
      }),
      Instruction.gainLifeFixed 1
    ])

def tethermagesAdvantage : Effect :=
  fraSpell .creature
    (.seq #[
      Instruction.pumpFixed (.target 0) 2 2,
      Instruction.grantKeywords (.target 0) #[Keyword.reach],
      Instruction.untap (.target 0)
    ])

/-! ## Multicolor -/

def clashOfElements : Effect :=
  fraSpell .nonland
    (.optional (.ownerOf (.target 0)) none
      (.seq #[
        Instruction.putOnLibrary (.target 0) .top,
        Instruction.dealDamageFixed (.players (.ownerOf (.target 0))) 2
      ])
      (Instruction.putOnLibrary (.target 0) .bottom))

def entrustTheSpark : Effect :=
  fraUntargeted
    (Instruction.may .you
      (some (CostSpec.ofItem (.sacrifice (.count (.const 1)) (.filter (.hasType .planeswalker)))))
      (.player (.searchLibrary {
        zones := .libraryOf .you
        filter := .hasType .planeswalker
        count := .upTo (.const 1)
        dest := .battlefield .controller
        reveal := false
        shuffle := true
      })))

def plusOneThenGrant (n : Nat) (k : Array KeywordAbility) (upToOne := false) : Effect :=
  let spec : TargetSpec :=
    if upToOne then .single { domain := .creature, count := .upTo 1 } else .creature
  fraSpell spec
    (.seq #[Instruction.putPlusOne (.target 0) n, Instruction.grantKeywords (.target 0) k])

def recursiveRecruitment : Effect :=
  fraUntargeted
    (.bind ⟨0⟩ (Instruction.createTokensFixed .cadet 2)
      (Instruction.ifThen (.castPred (.castFrom .graveyard .this))
        (Instruction.putCounters (.stepObjects ⟨0⟩) .plusOnePlusOne
          (.binary .divFloor (.playerMetric .graveyardSize .you) (.const 3)))))

def stingingVitriol : Effect :=
  fraSpell .opponent
    (.seq #[
      Instruction.dealDamageFixed (.targetSlot 0) 2,
      .moveZone (.inZones (.handOf (.target 0)) (.not (.hasType .land))) .graveyard .discard {
        choice? := some { chooser := .controller, count := .exact (.const 1), revealFirst := true }
      }
    ])

def twinnedVision : Effect :=
  fraUntargeted
    (.ifCond (.not (.castPred (.castFrom .hand .this)))
      (Instruction.drawFixed 2) (Instruction.drawFixed 1))

def twistedFates : Effect :=
  let targetPlayerCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 1))])
  fraSpell (.ofSlots #[.of .nonland, .of .anyPlayer])
    (.seq #[
      Instruction.destroy (.target 0),
      Instruction.putPlusOne targetPlayerCreatures 1
    ])

def vindictiveTriumph : Effect :=
  fraSpell .creatureOrPlaneswalker
    (.moveZone (.target 0) .exile .exile {
      delayedReturn? := some (.returnIfThenExileAtEndStep (.stat .manaValue .le (.const 3)) true .controller)
    })

def tamsResistance : Effect := plusOneThenGrant 1 #[Keyword.vigilance] (upToOne := true)

/-! ## Modes of modal triggered abilities -/

end Effect

namespace ActivatedAbility

/-- Build an activated ability from effect and cost. -/
def fra (effect : Effect) (cost : CostSpec)
    (timing : ActivationTiming := .instant)
    (activeZones : Array ZoneKind := #[.battlefield])
    (condition? : Option Condition := none)
    (lifetimeLimit? : Option Nat := none)
    (tag? : Option ActivationMechanicTag := none)
    (costReductions : Array ActivationCostReduction := #[]) : ActivatedAbility :=
  { cost, effect, timing, activeZones, condition?,
    lifetimeLimit? := lifetimeLimit?.orElse fun _ => if tag? == some .exhaust then some 1 else none,
    tag?, costReductions }

end ActivatedAbility

namespace FraCandidates

/-- Shorthand for an ability effect lowered directly onto `Instruction`. -/
def ab (body : Instruction) (spec : TargetSpec := .none) : Effect :=
  { targets := spec, body }

end FraCandidates

end Mtg.Engine
