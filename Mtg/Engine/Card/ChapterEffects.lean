import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger

/-!
# Saga-chapter effect constructors (CR 714.2)

All 23 Saga chapter effects lowered directly onto unified `Instruction` values.
-/

namespace Mtg.Engine

namespace Effect

/-- Chapter: `"this Saga deals n damage to target creature an opponent controls"`. -/
def chapterDealDamageToOppCreature (n : Nat) : Effect :=
  { targeting := .of .oppCreature
    body := Instruction.dealDamageFixed (.targetSlot 0) n
    phrase := s!"this Saga deals {n} damage to target creature an opponent controls" }

/-- Chapter: `"destroy target artifact an opponent controls"`. -/
def chapterDestroyOppArtifact : Effect :=
  { targeting := .of .oppArtifact
    body := Instruction.destroy (.target 0)
    phrase := "destroy target artifact an opponent controls" }

/-- Chapter: `"add {mana}"`. -/
def chapterAddMana (mana : ManaType) : Effect :=
  { body := Instruction.addSimpleMana #[mana]
    phrase := s!"add {mana}" }

/-- Chapter: `"search your library for a basic land card, reveal it, put it into your hand, then shuffle"`. -/
def chapterSearchBasicLandToHand : Effect :=
  { body := .player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .hand .owner
      reveal := true
      shuffle := true
    })
    phrase := searchLibraryToHandPhrase "a basic land card" }

/-- Chapter: `"this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""`. -/
def chapterGainLandfallCreateElf : Effect :=
  let landfall : TriggeredAbility := {
    word := .whenever
    pattern := .landYouControlEnters
    effect := { body := Instruction.createTokensFixed .elf 1 }
  }
  { body := .installEffect (.applyContinuous .indefinite .this (.grantTriggered #[landfall]))
    phrase := "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"" }

/-- Chapter: `"Elves you control get +P/+0 and gain vigilance until end of turn"`. -/
def chapterElvesGetVigilance (power : Int) : Effect :=
  let elves : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .hasSubtype (.literal .elf), .controlledBy .you])
  { body := .seq #[
      Instruction.pumpFixed elves power 0,
      Instruction.grantKeywords elves #[Keyword.vigilance]
    ]
    phrase := s!"Elves you control get {signedStat power}/+0 and gain vigilance until end of turn" }

/-- Chapter: `"target opponent reveals their hand. You choose a nonland card from it. That player discards that card"`. -/
def chapterOpponentDiscardsNonland : Effect :=
  { targeting := .of .opponent
    body := .moveZone (.inZones (.handOf (.target 0)) (.not (.hasType .land))) .graveyard .discard {
      choice? := some {
        chooser := .controller
        count := .exact (.const 1)
        revealFirst := true
      }
    }
    phrase := "target opponent reveals their hand. You choose a nonland card from it. That player discards that card" }

/-- Chapter: `"amass Goblins n"`. -/
def chapterAmassGoblins (n : Nat) : Effect :=
  { body := Instruction.amassFixed n .goblin
    phrase := s!"amass Goblins {n}" }

/-- Chapter: `"target opponent loses n life and you gain n life"`. -/
def chapterOpponentLosesYouGain (n : Nat) : Effect :=
  { targeting := .of .opponent
    body := .seq #[
      Instruction.loseLifeFixed n (.target 0),
      Instruction.gainLifeFixed n
    ]
    phrase := s!"target opponent loses {n} life and you gain {n} life" }

/-- Chapter: `"target creature you control gains hexproof for as long as this Saga remains on the battlefield"`. -/
def chapterGrantHexproofWhileRemains : Effect :=
  { targeting := .of .creatureYouControl
    body := Instruction.grantKeywords (.target 0) #[Keyword.hexproof] (.whileOnBattlefield .this)
    phrase := "target creature you control gains hexproof for as long as this Saga remains on the battlefield" }

/-- Chapter: `"prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield"`. -/
def chapterPreventDamageWhileRemains : Effect :=
  { targeting := .of .creature
    allowsZeroTargets := true
    body := .installEffect (.applyReplacement (.whileOnBattlefield .this)
      (.preventDamage (.matching { zones := .battlefield, pred := .sameAs (.target 0) }) none))
    phrase := "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield" }

/-- Chapter: `"draw n card(s)"`. -/
def chapterDraw (n : Nat) : Effect :=
  { body := Instruction.drawFixed n
    phrase := s!"draw {cardPhrase n}" }

/-- Chapter: `"search your library for up to max basic Plains cards, exile them, then shuffle. You gain life life"`. -/
def chapterSearchBasicPlainsExileGainLife (max life : Nat) : Effect :=
  { body := .seq #[
      .player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasSubtype (.literal .plains)]
        count := .upTo (.const (Int.ofNat max))
        dest := .exile
        mods := { linkToSource := true }
        reveal := false
        shuffle := true
      }),
      Instruction.gainLifeFixed life
    ]
    phrase := s!"search your library for up to {max} basic Plains cards, exile them, then shuffle. You gain {life} life" }

/-- Chapter: `"put a card exiled with this Saga into its owner's hand"` (CR 607.2a / 714.4). -/
def chapterReturnLinkedExileToHand : Effect :=
  { body := .moveZone (.linkedExile .this) (.hand .owner) .put {
      choice? := some { chooser := .controller, count := .exact (.const 1) }
    }
    phrase := "put a card exiled with this Saga into its owner's hand" }

/-- Chapter: `"whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"`. -/
def chapterGrantAttackPumpPerPlainsThisTurn : Effect :=
  let plainsCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .plains), .controlledBy .you]))
  { body := .installEffect (.createDelayedTrigger {
      pattern := .youAttack
      grouping := .oncePerBatch
      duration := .untilEndOfTurn
      oneShot := false
      effect := {
        targeting := .of .creatureYouControl
        body := Instruction.pump (.target 0) plainsCount plainsCount
      }
    })
    phrase := "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control" }

/-- Chapter: `"exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step"`. -/
def chapterBlinkUntilEndStep : Effect :=
  { targeting := .of .creatureOrLandYouControl
    allowsZeroTargets := true
    body := .moveZone (.target 0) .exile .exile {
      delayedReturn? := some (.atNextEndStep false .owner)
    }
    phrase := "exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step" }

/-- Chapter: `"create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying"`. -/
def chapterTreasureThenDragonIfFour : Effect :=
  let treasuresCount : ValueExpr :=
    .aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .treasure), .controlledBy .you]))
  { body := .seq #[
      Instruction.createTokensFixed .treasure 1,
      Instruction.ifThen (.cmp .ge treasuresCount (.const 4))
        (.bind ⟨0⟩ (Instruction.sacrifice .this)
          (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.createTokensFixed .dragon 1)))
    ]
    phrase := "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying" }

/-- Chapter: `"recruit"`. -/
def chapterRecruit : Effect :=
  { body := Instruction.recruit
    phrase := "recruit" }

/-- Chapter: `"return target creature card with mana value n or less from your graveyard to the battlefield"`. -/
def chapterReturnCreatureFromGyMvAtMost (n : Nat) : Effect :=
  { targeting := .of (.creatureCardInYourGraveyardMvAtMost n)
    body := .moveZone (.target 0) (.battlefield (.player .you)) .put {}
    phrase := s!"return target creature card with mana value {n} or less from your graveyard to the battlefield" }

/-- Chapter: `"put a +1/+1 counter on up to one target creature"`. -/
def chapterPlusOneUpToOne : Effect :=
  { targeting := .of .creature
    allowsZeroTargets := true
    body := Instruction.putPlusOne (.target 0) 1
    phrase := "put a +1/+1 counter on up to one target creature" }

/-- Chapter: `"Gain control of up to two target creatures with total mana value n or less for as long as this Saga remains on the battlefield"`. -/
def chapterGainControlOfUpToTwoCreaturesTotalMvAtMost (n : Nat) : Effect :=
  { targeting := .of (.upToTwoCreaturesTotalMvAtMost n)
    allowsZeroTargets := true
    body := .installEffect (.applyContinuous (.whileOnBattlefield .this) .allTargets (.gainControl .you))
    phrase :=
      s!"Gain control of up to two target creatures with total mana value {n} or less for as long as this Saga remains on the battlefield" }

/-- Chapter: `"This Saga deals n damage to each non-{subtype} creature and each opponent"`. -/
def chapterDealDamageToEachNonSubtypeAndOpponents (n : Nat) (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  let nonSubCreatures : ObjectExpr :=
    .inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.literal sub))])
  { body := Instruction.dealDamageFixed (.both nonSubCreatures .opponents) n
    phrase := s!"This Saga deals {n} damage to each non-{sub} creature and each opponent" }

/-- Chapter: `"This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"`. -/
def chapterDealXDamageToTargetOpponentGreatestArtifactMv : Effect :=
  let greatestArtMv : ValueExpr :=
    .aggregate .max (.stat .manaValue) (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))
  { targeting := .of .opponent
    body := Instruction.dealDamage (.players (.target 0)) greatestArtMv
    phrase :=
      "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control" }

end Effect

end Mtg.Engine
