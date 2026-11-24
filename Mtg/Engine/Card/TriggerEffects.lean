import Mtg.Engine.Card.Trigger

/-!
# Unified trigger `Effect` constructors (CR 603 / 608)

All reusable and specialized trigger effects expressed directly as unified
`Instruction`-backed `Effect` values.
-/

namespace Mtg.Engine

namespace Effect

/-! ### Common object/value shorthands -/

private def creaturesYouControlExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])

private def otherCreaturesYouControlExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy .you])

private def oppCreaturesExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .opponent])

private def subtypeYouControlExpr (sub : CardSubtype) : ObjectExpr :=
  .inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy .you])

private def otherSubtypeYouControlExpr (sub : CardSubtype) : ObjectExpr :=
  .inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy .you])

def typeOrSubtypePred (s : String) : ObjectPred :=
  if s.toLower == "permanent" then .isKind .permanentCard
  else
    match CardType.ofOracle? s with
    | some ty => .hasType ty
    | none =>
      match CardSubtype.ofOracle? s with
      | some sub => .hasSubtype (.literal sub)
      | none => .anyObject

/-! ### Reusable parameterized trigger effects -/

/-- Scry `n`. -/
def triggerScry (n : Nat) : Effect :=
  { body := Instruction.scryFixed n }

/-- Draw `n` cards. -/
def triggerDraw (n : Nat) : Effect :=
  { body := Instruction.drawFixed n }

/-- Create `n` tokens of `kind` (`tapped`). -/
def triggerCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) : Effect :=
  { body := Instruction.createTokensFixed kind n .you tapped }

/-- Create one `kind` token, then attach this source to it. -/
def triggerCreateThenAttach (kind : TokenSpec) : Effect :=
  { body := .bind ⟨0⟩ (Instruction.createTokensFixed kind 1)
      (.permanent (.attach .this (.stepObjects ⟨0⟩))) }

/-- Amass `subtype` `n`. -/
def triggerAmass (n : Nat) (subtype : CardSubtype := .goblin) : Effect :=
  { body := Instruction.amassFixed n subtype }

/-- Amass `subtype` X, where X is this creature's power (CR 608.2h LKI). -/
def triggerAmassSourcePower (subtype : CardSubtype := .goblin) : Effect :=
  { body := Instruction.amass (.objectStat .power .this) subtype }

/-- Amass `subtype` `n`, then attach this Equipment to the amassed Army. -/
def triggerAmassThenAttach (n : Nat) (subtype : CardSubtype := .goblin) : Effect :=
  { body := .bind ⟨0⟩ (Instruction.amassFixed n subtype)
      (.permanent (.attach .this (.stepObjects ⟨0⟩))) }

/-- Recruit (draw a card, discard a card; if nonland, create a 1/1 white Human Soldier). -/
def triggerRecruit : Effect :=
  { body := Instruction.recruit .you }

/-- Deal `amount` damage divided as you choose among one to `maxTargets` targets (CR 601.2d). -/
def triggerDividedDamage (amount maxTargets : Nat) : Effect :=
  { targets := TargetSpec.dividedDamage .anyTarget amount maxTargets
    body := Instruction.dealDamage .allTargets (.const (Int.ofNat amount)) .this { divided := true } }

/-- You gain `n` life. -/
def triggerGainLife (n : Nat) : Effect :=
  { body := Instruction.gainLifeFixed n }

/-- This permanent connives (CR 701.50). -/
def triggerConniveSource : Effect :=
  { body := .player (.connive .this) }

/-- Target of `kind` connives (CR 701.50). -/
def triggerConniveTarget (kind : TargetSpec) : Effect :=
  { targets := kind
    body := .player (.connive (.target 0)) }

/-- Exile target of `kind` until this permanent leaves the battlefield (CR 610.3). -/
def triggerExileUntilLeaves (kind : TargetSpec) (allowsZeroTargets : Bool := false) : Effect :=
  { targets := if allowsZeroTargets then kind.asUpTo 1 else kind
    body := Instruction.exile (.target 0) { exileUntilSourceLeaves := true } }

/-- Deal `n` damage to target opponent. -/
def triggerDamageTargetOpponent (n : Nat) : Effect :=
  { targets := .opponent
    body := Instruction.dealDamageFixed (.players (.target 0)) n }

/-- Deal `n` damage to each opponent. -/
def triggerDamageEachOpponent (n : Nat) : Effect :=
  { body := Instruction.dealDamageFixed (.players .opponents) n }

/-- Attach this Equipment to target of `kind`. -/
def triggerAttachTo (kind : TargetSpec) : Effect :=
  { targets := kind
    body := .permanent (.attach .this (.target 0)) }

/-- Target opponent sacrifices a creature of their choice. -/
def triggerOpponentSacrificesCreature : Effect :=
  { targets := .opponent
    body := .moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))]))
      .graveyard .sacrifice
      { choice? := some { chooser := .player (.target 0), count := .exact (.const 1) } } }

/-- Exile the top card of your library. Until the end of your next turn, you may play that card. -/
def triggerExileTop : Effect :=
  { body := Instruction.exile (.topOfLibrary .you (.const 1)) {
      grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
    } }

/-- You may discard a card. If you do, draw `n` card(s). -/
def triggerMayDiscardDraw (n : Nat) : Effect :=
  { body := Instruction.may .you (some CostSpec.discardCard) (Instruction.drawFixed n) }

/-- Each opponent discards `n` card(s). -/
def triggerEachOpponentDiscards (n : Nat := 1) : Effect :=
  { body := .forEach (.eachPlayer .opponent) ⟨0⟩ (Instruction.discardFixed n (.stepPlayers ⟨0⟩)) }

/-- Target opponent discards `n` card(s). -/
def triggerTargetOpponentDiscards (n : Nat) : Effect :=
  { targets := .opponent
    body := Instruction.discardFixed n (.target 0) }

/-- Target player mills `n` cards. -/
def triggerMillPlayer (n : Nat) : Effect :=
  { targets := .player
    body := Instruction.millFixed n (.target 0) }

/-- Investigate (create a Clue token; CR 701.16). -/
def triggerInvestigate : Effect :=
  { body := Instruction.createTokensFixed .clue 1 }

/-- Search your library for a Forest card, put it onto the battlefield, then shuffle. -/
def triggerSearchForest : Effect :=
  { body := .player (.searchLibrary {
      zones := .libraryOf .you
      filter := .hasSubtype (.literal .forest)
      count := .upTo (.const 1)
      dest := .battlefield .controller
      reveal := false
      shuffle := true
    }) }

/-- Search your library for a basic land card, reveal it, put it into your hand, then shuffle. -/
def triggerSearchBasicLandToHand : Effect :=
  { body := .player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .hand .controller
      reveal := true
      shuffle := true
    }) }

/-- Each player sacrifices a creature of their choice. -/
def triggerEachPlayerSacrificesCreature : Effect :=
  { body := .forEach (.eachPlayer .any) ⟨0⟩
      (.moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.stepPlayers ⟨0⟩))]))
        .graveyard .sacrifice
        { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } }) }

/-- Exile target of `kind` (linked to source for leave-the-battlefield return). -/
def triggerExileTarget (kind : TargetSpec) (allowsZeroTargets : Bool := false) : Effect :=
  { targets := if allowsZeroTargets then kind.asUpTo 1 else kind
    body := Instruction.exile (.target 0) { linkToSource := true } }

/-- Return target creature card from your graveyard to your hand. -/
def triggerReturnCreatureFromGyToHand : Effect :=
  { targets := .creatureCardInYourGraveyard
    body := Instruction.bounce (.target 0) }

/-- Put a +1/+1 counter on each creature you control. -/
def triggerPlusOneEachYouControl : Effect :=
  { body := Instruction.putPlusOne creaturesYouControlExpr 1 }

/-- Put a +1/+1 counter on each creature you control, or two if you have the city's blessing. -/
def triggerPlusOneEachCitysBlessing : Effect :=
  { body := .ifCond (.playerPred .you (.hasDesignation .citysBlessing))
      (Instruction.putPlusOne creaturesYouControlExpr 2)
      (Instruction.putPlusOne creaturesYouControlExpr 1) }

/-- Put a hone counter on each Equipment you control. -/
def triggerHoneEachEquipment : Effect :=
  { body := Instruction.putCounters (subtypeYouControlExpr .equipment) .hone (.const 1) }

/-- Put a +1/+1 counter on each other creature you control. You gain 1 life for each. -/
def triggerPlusOneEachOtherGainLife : Effect :=
  { body := .seq #[
      Instruction.putPlusOne otherCreaturesYouControlExpr 1,
      Instruction.gainLife (.aggregate .count .one otherCreaturesYouControlExpr)
    ] }

/-- You may have this creature's base power and toughness become P/T until end of turn. -/
def triggerBecomePT (power toughness : Int) : Effect :=
  { body := Instruction.may .you none
      (.installEffect (.applyContinuous .untilEndOfTurn .this
        (.setBasePT (some (.const power)) (some (.const toughness))))) }

/-- Target creature you control gets +1/+1 until end of turn for each Plains you control. -/
def triggerPumpTargetPerPlains : Effect :=
  let plainsCount := ValueExpr.count (subtypeYouControlExpr .plains)
  { targets := .creatureYouControl
    body := Instruction.pump (.target 0) plainsCount plainsCount }

/-- You may discard your hand. If you do, draw `n` cards. -/
def triggerMayDiscardHandDraw (n : Nat) : Effect :=
  { body := Instruction.may .you none
      (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard)
        (Instruction.drawFixed n)) }

/-- This creature gets +1/+1 until end of turn for each card looked at while scrying this way. -/
def triggerPumpByLookedAt : Effect :=
  { body := Instruction.pump .this .eventAmount .eventAmount }

/-- This creature gets +X/+0 until end of turn, where X is the greatest power among creatures you control. -/
def triggerPumpGreatestPower : Effect :=
  { body := Instruction.pump .this (.aggregate .max (.stat .power) creaturesYouControlExpr) (.const 0) }

/-- This creature deals `n` damage to each creature blocking it. -/
def triggerDamageBlockers (n : Nat) : Effect :=
  { body := Instruction.dealDamageFixed
      (.objects (.inZones .battlefield (.all #[.hasType .creature, .combatRole (.blockingObject .this)])))
      n }

/-- Return the cards exiled with this permanent to the battlefield under their owners' control. -/
def triggerReturnLinkedExile : Effect :=
  { body := .moveZone (.linkedExile .this) (.battlefield .owner) .put }

/-- You gain `n` life. You may search your library for a basic land card, reveal it, then shuffle and put it on top. -/
def triggerGainLifeSearchBasicOnTop (n : Nat) : Effect :=
  { body := .seq #[
      Instruction.gainLifeFixed n,
      .player (.searchLibrary {
        zones := .libraryOf .you
        filter := .all #[.hasSupertype .basic, .hasType .land]
        count := .upTo (.const 1)
        dest := .library .owner .top
        reveal := true
        shuffle := true
      })
    ] }

/-- Add `types` mana. -/
def triggerAddMana (types : Array ManaType) : Effect :=
  { body := Instruction.addSimpleMana types }

/-- Create an Axe Equipment token (optionally with a reflexive trigger to attach it). -/
def triggerCreateAxe (attach : Bool := false) : Effect :=
  if attach then
    { body := .bind ⟨0⟩ (Instruction.createTokensFixed .axe 1)
        (Instruction.ifThen (.exists (.stepObjects ⟨0⟩))
          (.queueReflexiveTrigger {
            word := .when
            pattern := .thisEnters
            effect := {
              targets := .creatureYouControl
              body := .permanent (.attach .triggerSubject (.target 0))
            }
          })) }
  else
    { body := Instruction.createTokensFixed .axe 1 }

/-- Choose one — Tap target creature an opponent controls; or Untap target creature you control. -/
def triggerTapOppOrUntapYours : Effect :=
  { body := .chooseModes {
      modes := #[
        { targets := .oppCreature, body := Instruction.tap (.target 0) },
        { targets := .creatureYouControl, body := Instruction.untap (.target 0) }
      ]
    } }

/-- You may pay `{1}{G}{U}`. If you do, return this card from your graveyard to your hand. -/
def triggerPayReturnFromGy : Effect :=
  { body := Instruction.may .you
      (some (CostSpec.ofMana { symbols := #[.generic 1, .colored .green, .colored .blue] }))
      (Instruction.bounce .this) }

/-- Target opponent loses `n` life. -/
def triggerTargetOpponentLosesLife (n : Nat) : Effect :=
  { targets := .opponent
    body := Instruction.loseLifeFixed n (.target 0) }

/-- You may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard `n` cards. -/
def triggerMayDrawXDiscard (n : Nat) : Effect :=
  { body := Instruction.may .you none
      (.seq #[
        Instruction.draw (.manaSpent .triggerSubject),
        Instruction.ifThen (.cmp .gt (.manaSpent .triggerSubject) (.const 0))
          (Instruction.discardFixed n)
      ]) }

/-- The Ring tempts you. -/
def triggerRingTempts : Effect :=
  { body := .player (.temptWithRing .you) }

/-- Choose up to one other target creature you control. Its base P/T become equal to this creature's P/T until end of turn. -/
def triggerSetOtherBasePT : Effect :=
  { targets := TargetSpec.anotherCreatureYouControl.asUpTo 1
    body := Instruction.setBasePT (.target 0) (.objectStat .power .this) (.objectStat .toughness .this) }

/-- Return target Elf card from your graveyard to your hand. You gain life equal to that card's power. -/
def triggerReturnElfGainLife : Effect :=
  { targets := .elfInYourGraveyard
    body := .bind ⟨0⟩ (Instruction.bounce (.target 0))
      (Instruction.gainLife (.stepMetric .sumPower ⟨0⟩)) }

/-- This creature deals damage equal to its power (LKI) to target creature an opponent controls. -/
def triggerDamageFromLastKnownPower : Effect :=
  { targets := .oppCreature
    body := Instruction.dealDamage (.targetSlot 0) (.objectStat .power .this) }

/-- You may pay `{n}`. If you do, (optionally put a +1/+1 counter on this creature and) draw a card. -/
def triggerMayPayGenericDraw (n : Nat) (plusOneOnSource : Bool := false) : Effect :=
  { body := Instruction.may .you (some (CostSpec.ofGeneric n))
      (if plusOneOnSource then .seq #[Instruction.putPlusOne .this 1, Instruction.drawFixed 1]
       else Instruction.drawFixed 1) }

/-- Draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library. -/
def triggerDrawThenBottomIfNoLegendary : Effect :=
  { body := .seq #[
      Instruction.drawFixed 1,
      Instruction.ifThen
        (.not (.exists (.inZones .battlefield (.all #[.hasSupertype .legendary, .hasType .creature, .controlledBy .you]))))
        (.moveZone (.inZones .yourHand .anyObject) (.library .owner .bottom) .put {
          choice? := some { chooser := .controller, count := .exact (.const 1) }
        })
    ] }

/-- Remove a hope counter from this. If you do, draw a card. Then if it has no hope counters, sacrifice it and gain 4 life. -/
def triggerRemoveHopeDrawSac : Effect :=
  { body := .seq #[
      .bind ⟨0⟩ (.permanent (.modifyCounters (.remove (some .hope) (.exact (.const 1))) .this))
        (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed 1)),
      Instruction.ifThen (.all #[.exists .this, .cmp .eq (.counterCount (some .hope) .this) (.const 0)])
        (.seq #[Instruction.sacrifice .this, Instruction.gainLifeFixed 4])
    ] }

/-- You may tap any number of untapped Humans you control. Draw a card for each Human tapped this way. -/
def triggerTapHumansDraw : Effect :=
  { body := .bind ⟨0⟩
      (.permanent (.setTapped
        (.inZones .battlefield (.all #[.tapped false, .hasSubtype (.literal .human), .controlledBy .you]))
        true (choice? := some { chooser := .controller, count := .anyNumber })))
      (Instruction.draw (.stepMetric .movedCount ⟨0⟩)) }

/-- Destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way. -/
def triggerDestroyOppArtifactsEnchantmentsGainLife : Effect :=
  { body := .bind ⟨0⟩
      (Instruction.destroy (.inZones .battlefield (.all #[
        .any #[.hasType .artifact, .hasType .enchantment], .controlledBy .opponent])))
      (Instruction.gainLife (.stepMetric .movedCount ⟨0⟩)) }

/-- This creature deals damage equal to the number of `subtype`s you control to each opponent. -/
def triggerDamageEqualSubtypeToEachOpponent (subtype : CardSubtype) : Effect :=
  { body := Instruction.dealDamage (.players .opponents) (ValueExpr.count (subtypeYouControlExpr subtype)) }

/-- This creature deals damage equal to the number of Treasures you control to any target. -/
def triggerDamageEqualTreasures : Effect :=
  { targets := .anyTarget
    body := Instruction.dealDamage (.targetSlot 0) (ValueExpr.count (subtypeYouControlExpr .treasure)) }

/-- This creature deals `n` damage to any target. If a `subtype` is dealt damage this way, destroy it. -/
def triggerDealDamageDestroyIfSubtype (n : Nat) (subtype : CardSubtype) : Effect :=
  { targets := .anyTarget
    body := .bind ⟨0⟩ (Instruction.dealDamageFixed (.targetSlot 0) n)
      (Instruction.ifThen (.cmp .gt (.stepMetric .damageDealt ⟨0⟩) (.const 0))
        (Instruction.destroy (.filter (.stepObjects ⟨0⟩) (.hasSubtype (.literal subtype))))) }

/-- Attach target Equipment you control to up to one target creature you control. -/
def triggerAttachEquipmentToCreature : Effect :=
  { targets := .equipmentYouControlThenCreatureYouControl
    body := .permanent (.attach (.target 0) (.target 1)) }

/-- Defending player sacrifices a creature with the least power among creatures they control. -/
def triggerDefenderSacsLeastPower : Effect :=
  { body := .moveZone
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .defendingPlayer]))
      .graveyard .sacrifice
      { choice? := some {
          chooser := .player .defendingPlayer
          count := .exact (.const 1)
          extremeMetric? := some (false, .stat .power)
        } } }

/-- Return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature. -/
def triggerReturnOtherPlusOne : Effect :=
  { targets := (.single {
      domain := .object .battlefield (.all #[.otherThan .this, .controlledBy .you])
      count := .upTo 1 })
    body := .bind ⟨0⟩ (Instruction.bounce (.target 0))
      (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.putPlusOne .this 1)) }

/-- Look at the top `n` cards of your library. You may reveal a card of one of `types` and put it into your hand. Rest on bottom random. -/
def triggerLookAtTopRevealTypes (n : Nat) (types : Array String) : Effect :=
  let pred : ObjectPred :=
    match types.toList.map typeOrSubtypePred with
    | [p] => p
    | ps => .any ps.toArray
  { body := .player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) false
      action := .takeMatching pred (.upTo (.const 1)) (.hand .controller) {} true
      rest := .bottomRandom
    }) }

/-- Create a tapped Treasure token for each artifact your opponents control. -/
def triggerCreateTappedTreasuresEqualOppArtifacts : Effect :=
  { body := Instruction.createTokens .treasure
      (ValueExpr.count (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .opponent])))
      .you { tapped := true } }

/-- Put up to one target nonland permanent card with mana value `mv` or less from a graveyard onto the battlefield under its owner's control. -/
def triggerPutNonlandMvAtMostFromGy (mv : Nat) : Effect :=
  { targets := (.single {
      domain := .object .anyGraveyard (.all #[
        .not (.hasType .land), .isKind .permanentCard, .stat .manaValue .le (.const (Int.ofNat mv))])
      count := .upTo 1 })
    body := .moveZone (.target 0) (.battlefield .owner) .put }

/-- Other creatures of `subtypes` you control get +P/+T; creatures opponents control get +oppP/+oppT. -/
def triggerOthersGetAndOppsGet (subtypes : Array CardSubtype) (power toughness oppP oppT : Int) : Effect :=
  let subPred : ObjectPred :=
    match subtypes.toList with
    | [s] => .hasSubtype (.literal s)
    | _ => .any (subtypes.map fun s => .hasSubtype (.literal s))
  let yours : ObjectExpr :=
    .inZones .battlefield (.all #[.otherThan .this, .hasType .creature, subPred, .controlledBy .you])
  { body := .seq #[
      Instruction.pumpFixed yours power toughness,
      Instruction.pumpFixed oppCreaturesExpr oppP oppT
    ] }

/-- Choose one — Put a +1/+1 counter on target Wolf you control; or Create a Treasure token. -/
def triggerWolfPlusOneOrTreasure : Effect :=
  { body := .chooseModes {
      modes := #[
        { targets := (.creatureYouControlAnySubtype #[.wolf])
          body := Instruction.putPlusOne (.target 0) 1 },
        { body := Instruction.createTokensFixed .treasure 1 }
      ]
    } }

/-- Put a trample counter on up to one target creature you control. It becomes a Bear. Then if you control 3+ Bears, draw 2. -/
def triggerTrampleCounterBecomeBear : Effect :=
  { targets := TargetSpec.creatureYouControl.asUpTo 1
    body := .seq #[
      Instruction.putCounters (.target 0) .trample (.const 1),
      .installEffect (.applyContinuous .indefinite (.target 0) (.modifyTypes { subtypes := #[.bear] })),
      Instruction.ifThen (.cmp .ge (ValueExpr.count (subtypeYouControlExpr .bear)) (.const 3))
        (Instruction.drawFixed 2)
    ] }

/-- Mill `n` cards, then put all `subtype` cards from among them into your hand. -/
def triggerMillThenSubtypeToHand (n : Nat) (subtype : CardSubtype) : Effect :=
  { body := .player (.inspectLibrary {
      source := .millCards .you (.const (Int.ofNat n))
      action := .takeMatching (.hasSubtype (.literal subtype)) .anyNumber (.hand .controller)
      rest := .leaveInPlace
    }) }

/-- For each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield. -/
def triggerExileOppNonlandEachUntilLeaves : Effect :=
  { targets := (.forEachOpponentControlled (.not (.hasType .land)) (.upTo 1))
    body := Instruction.exile .allTargets { exileUntilSourceLeaves := true } }

/-- Put X +1/+1 counters on target creature you control, where X is that spell's mana value. -/
def triggerPlusOneEqualLastKnownMv : Effect :=
  { targets := .creatureYouControl
    body := Instruction.putCounters (.target 0) .plusOnePlusOne (.objectStat .manaValue .triggerSubject) }

/-- Put a quest counter on this; if 6+, sacrifice it and search hand/library for a Dragon onto the battlefield. -/
def triggerMountainQuestDragon : Effect :=
  { body := .seq #[
      Instruction.putCounters .this .quest (.const 1),
      Instruction.ifThen (.cmp .ge (.counterCount (some .quest) .this) (.const 6))
        (.bind ⟨0⟩ (Instruction.sacrifice .this)
          (Instruction.ifThen (.stepSucceeded ⟨0⟩)
            (.player (.searchLibrary {
              zones := { zones := #[.hand, .library], owner := .ofPlayer .you }
              filter := .hasSubtype (.literal .dragon)
              count := .upTo (.const 1)
              dest := .battlefield .controller
              reveal := false
              shuffle := true
            }))))
    ] }

/-- Choose a creature type. Create a Treasure token for each creature you control of that type. -/
def triggerTreasuresPerChosenType : Effect :=
  { body := .bind ⟨0⟩ (.player (.choose .you .creatureType))
      (Instruction.createTokens .treasure
        (ValueExpr.count (.inZones .battlefield (.all #[
          .hasType .creature, .hasSubtype (.fromStep ⟨0⟩), .controlledBy .you])))) }

/-- Reveal until a creature card; put onto battlefield if MV ≤ lands you control, else into hand; rest on bottom random. -/
def triggerRevealUntilCreature : Effect :=
  let landsCount := ValueExpr.count (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you]))
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .revealUntil .you (.hasType .creature) (.const 1)
        action := .none
        rest := .bottomRandom
      }))
      (.ifCond (.exists (.filter (.stepObjects ⟨0⟩) (.stat .manaValue .le landsCount)))
        (.moveZone (.stepObjects ⟨0⟩) (.battlefield .controller) .put)
        (.moveZone (.stepObjects ⟨0⟩) (.hand .owner) .put)) }

/-- You may sacrifice another creature. If you do, put +1/+1 counters on this equal to its power. -/
def triggerAttackSacPlusOneEqualPower : Effect :=
  { body := Instruction.may .you
      (some { CostSpec.sacrificeAnotherCreature with bindVar? := some ⟨0⟩ })
      (Instruction.putCounters .this .plusOnePlusOne (.stepMetric .sumPower ⟨0⟩)) }

/-- Draw a card, then discard a card. If you discard a land card this way, put it onto the battlefield tapped. -/
def triggerLootLandEntersTapped : Effect :=
  { body := .seq #[
      Instruction.drawFixed 1,
      .bind ⟨0⟩ (Instruction.discardFixed 1)
        (.moveZone (.filter (.stepObjects ⟨0⟩) (.hasType .land)) (.battlefield .controller) .put { tapped := true })
    ] }

/-- That player mills cards equal to the life lost. -/
def triggerMillThatManyLost : Effect :=
  { body := Instruction.mill .eventAmount (.triggerPlayer .actor) }

/-- Draw a card for each graveyard with seven or more cards in it. -/
def triggerDrawPerFatGraveyard : Effect :=
  { body := Instruction.draw (.playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7)))) }

/-- You may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token. -/
def triggerMaySacDrawTreasure : Effect :=
  { body := Instruction.may .you (some CostSpec.sacrificeAnotherCreatureOrArtifactSpec)
      (.seq #[Instruction.drawFixed 1, Instruction.createTokensFixed .treasure 1]) }

/-- You may cast an instant or sorcery from hand with MV ≤ twice legendary Wizards you control without paying. -/
def triggerCastInstantSorceryFromHand : Effect :=
  let maxMv : ValueExpr := .binary .mul (.const 2)
    (ValueExpr.count (.inZones .battlefield (.all #[
      .hasSupertype .legendary, .hasSubtype (.literal .wizard), .controlledBy .you])))
  { body := .stack (.mayCastOrPlay
      (.inZones (.handOf .you) (.any #[.hasType .instant, .hasType .sorcery]))
      { freeCast := true, landsAllowed := false, castNow := true, maxTotalManaValue? := some maxMv }) }

/-- You may cast an instant or sorcery from hand with MV ≤ that damage without paying. -/
def triggerCastInstantSorceryMvAtMost : Effect :=
  { body := .stack (.mayCastOrPlay
      (.inZones (.handOf .you) (.any #[.hasType .instant, .hasType .sorcery]))
      { freeCast := true, landsAllowed := false, castNow := true, maxTotalManaValue? := some .eventAmount }) }

/-- Each opponent mills 2; when 1+ milled, reflexive exile + copy + free cast enchantment/instant/sorcery with MV ≤ spell MV. -/
def triggerMillThenCopy : Effect :=
  { body := .bind ⟨0⟩ (Instruction.millFixed 2 .opponents)
      (Instruction.ifThen (.cmp .ge (.stepMetric .movedCount ⟨0⟩) (.const 1))
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisEnters
          effect := {
            targets := (.ofDomain (.object .opponentGraveyard (ObjectPred.andAll #[
              .isKind .card,
              .any #[.hasType .enchantment, .hasType .instant, .hasType .sorcery],
              .stat .manaValue .le (.objectStat .manaValue .triggerSubject)
            ])))
            body := .bind ⟨1⟩ (.moveZone (.target 0) .exile .exile {})
              (.stack (.mayCastOrPlay (.stepObjects ⟨1⟩) {
                freeCast := true, landsAllowed := false, copyAndCast := true, castNow := true, maxCasts? := some 1
              }))
          }
        })) }

/-- Another target creature you control gets +X/+0 until end of turn, where X is this creature's power. -/
def triggerPumpTargetBySourcePower : Effect :=
  { targets := .anotherCreatureYouControl
    body := Instruction.pump (.target 0) (.objectStat .power .this) (.const 0) }

/-- Create a 1/1 red Alien token, put +1/+1 counters on it equal to invasion counters on this, then put an invasion counter on this. -/
def triggerCreateAlienPerInvasion : Effect :=
  { body := .seq #[
      .bind ⟨0⟩ (Instruction.createTokensFixed .alien 1)
        (Instruction.putCounters (.stepObjects ⟨0⟩) .plusOnePlusOne (.counterCount (some .invasion) .this)),
      Instruction.putCounters .this .invasion (.const 1)
    ] }

/-- You may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature. -/
def triggerMayPutArtifactAttachEquipment : Effect :=
  { body := Instruction.may .you none
      (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) (.hasType .artifact)) (.battlefield .controller) .put {
          choice? := some { chooser := .controller, count := .exact (.const 1) }
        })
        (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.hasSubtype (.literal .equipment))))
          (.permanent (.attach (.stepObjects ⟨0⟩) .this)))) }

/-- Cascade (CR 702.85a). -/
def triggerCascade : Effect :=
  let cheaperNonland : ObjectPred :=
    .all #[.not (.hasType .land), .stat .manaValue .lt (.objectStat .manaValue .this)]
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .revealUntil .you cheaperNonland (.const 1) (exileWhileRevealing := true)
        action := .none
        rest := .leaveInPlace
      }))
      (.seq #[
        .stack (.mayCastOrPlay (.filter (.stepObjects ⟨0⟩) cheaperNonland) {
          freeCast := true, landsAllowed := false, castNow := true
          maxTotalManaValue? := some (.binary .sub (.objectStat .manaValue .this) (.const 1))
        }),
        .moveZone (.stepObjects ⟨0⟩) (.library .owner .bottomRandom) .put
      ]) }

/-- Belladonna Took: 1st resolve gain 1 life, 2nd draw 1, 3rd +1/+1 on each creature you control. -/
def triggerBelladonnaTokenReward : Effect :=
  { body := .seq #[
      Instruction.ifThen (.turnHistory (.nthResolutionThisTurn 1)) (Instruction.gainLifeFixed 1),
      Instruction.ifThen (.turnHistory (.nthResolutionThisTurn 2)) (Instruction.drawFixed 1),
      Instruction.ifThen (.turnHistory (.nthResolutionThisTurn 3)) (Instruction.putPlusOne creaturesYouControlExpr 1)
    ] }

/-- Bolg reflexive damage + excess amass Goblins. -/
def triggerBolgDealSacrificedPower : Effect :=
  { targets := .anotherCreature
    body := .bind ⟨0⟩
      (Instruction.dealDamage (.targetSlot 0) (.objectStat .power .triggerSubject) .this { trackExcess := true })
      (Instruction.ifThen (.cmp .gt (.stepMetric .excessDamage ⟨0⟩) (.const 0))
        (Instruction.amass (.stepMetric .excessDamage ⟨0⟩) .goblin)) }

/-- Bolg enters: you may sacrifice another creature; when you do, deal its power to another creature and amass excess. -/
def triggerBolgMaySacrifice : Effect :=
  { body := Instruction.may .you
      (some { CostSpec.sacrificeAnotherCreature with bindVar? := some ⟨0⟩ })
      (.queueReflexiveTrigger {
        word := .when
        pattern := .youSacrificeOtherCreature
        effect := triggerBolgDealSacrificedPower
      }) }

/-- Create two tapped 1/1 white Spirit tokens with flying (tapped and attacking if equipped creature is legendary). -/
def triggerCreateSpiritsForEquipped : Effect :=
  { body := .ifCond (.exists (.filter .attachedHost (.hasSupertype .legendary)))
      (Instruction.createTokens .spirit (.const 2) .you { tapped := true, attacking := true })
      (Instruction.createTokens .spirit (.const 2) .you { tapped := true }) }

/-- Create a Treasure token for each artifact the damaged player controls. -/
def triggerCreateTreasuresEqualDamagedPlayerArtifacts : Effect :=
  { body := Instruction.createTokens .treasure
      (ValueExpr.count (.inZones .battlefield (.all #[
        .hasType .artifact, .controlledBy (.ofExpr (.triggerPlayer .damagedPlayer))]))) }

/-- Deal 1 damage to any target, then amass Orcs 1. -/
def triggerDeal1ThenAmassOrcs : Effect :=
  { targets := .anyTarget
    body := .seq #[Instruction.dealDamageFixed (.targetSlot 0) 1, Instruction.amassFixed 1 .orc] }

/-- Untap all attacking creatures and add an additional combat phase. -/
def triggerUntapAttackersExtraCombat : Effect :=
  { body := .seq #[
      Instruction.untap (.inZones .battlefield (.all #[.hasType .creature, .combatRole .attacking])),
      .turn (.extraPhase .combat true)
    ] }

/-- Alliance modal trigger (one unused this turn): add {G}{G}{G}, +1/+1 each creature, or scry 2 then draw. -/
def triggerAllianceMode : Effect :=
  { body := .chooseModes {
      unusedThisTurn := true
      modes := #[
        { body := Instruction.addSimpleMana #[.colored .green, .colored .green, .colored .green] },
        { body := Instruction.putPlusOne creaturesYouControlExpr 1 },
        { body := .seq #[Instruction.scryFixed 2, Instruction.drawFixed 1] }
      ]
    } }

/-- Azog: destroy up to one other target creature; its controller amasses Goblins X (its power); if you controlled it, draw. -/
def triggerDestroyOtherAmassControllerPower : Effect :=
  { targets := TargetSpec.anotherCreature.asUpTo 1
    body := Instruction.ifThen (.exists (.target 0))
      (.seq #[
        Instruction.destroy (.target 0),
        Instruction.amass (.objectStat .power (.target 0)) .goblin (.controllerOf (.target 0)),
        Instruction.ifThen (.playerPred (.controllerOf (.target 0)) (.matchesExpr .you))
          (Instruction.drawFixed 1)
      ]) }

/-- Gollum modal trigger (one unused ever): +1/+1 on Gollum, drain 2, or draw 1. -/
def triggerGollumMode : Effect :=
  { body := .chooseModes {
      unusedEver := true
      modes := #[
        { body := Instruction.putPlusOne .this 1 },
        { body := .seq #[Instruction.loseLifeFixed 2 .opponents, Instruction.gainLifeFixed 2] },
        { body := Instruction.drawFixed 1 }
      ]
    } }

/-- Balin: you may discard your hand; draw X; if enduring story, deal X to each opponent. -/
def triggerDiscardHandDrawDamageIfStory : Effect :=
  { body := Instruction.may .you none
      (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard)
        (.seq #[
          Instruction.draw (.stepMetric .movedCount ⟨0⟩),
          Instruction.ifThen (.all #[
              .playerPred .you (.hasDesignation .enduringStory),
              .cmp .gt (.stepMetric .movedCount ⟨0⟩) (.const 0)
            ])
            (Instruction.dealDamage (.players .opponents) (.stepMetric .movedCount ⟨0⟩))
        ])) }

/-- Bilbo: you may cast an artifact, instant, or sorcery from your graveyard (exile instant/sorcery instead of GY). -/
def triggerCastFromGyArtifactInstantSorcery : Effect :=
  { body := .stack (.mayCastOrPlay
      (.inZones (.graveyardOf .you) (.any #[.hasType .artifact, .hasType .instant, .hasType .sorcery]))
      { freeCast := false, landsAllowed := false, castNow := true, exileOnResolveInstead := true }) }

/-- Each equipped attacking creature gains double strike until end of turn. -/
def triggerEquippedAttackersGainDoubleStrike : Effect :=
  { body := Instruction.grantKeywords
      (.inZones .battlefield (.all #[
        .hasType .creature, .combatRole .attacking,
        .hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }
      ]))
      #[Keyword.doubleStrike] }

/-- Tap enchanted creature and remove all counters from it. -/
def triggerTapEnchantedRemoveCounters : Effect :=
  { body := .seq #[
      Instruction.tap .attachedHost,
      .permanent (.modifyCounters (.remove none .anyNumber) .attachedHost)
    ] }

/-- Reveal top `n` cards, put a random creature card from among them onto the battlefield, rest on bottom random. -/
def triggerRevealTopPutRandomCreature (n : Nat) : Effect :=
  { body := .player (.inspectLibrary {
      source := .topCards .you (.const (Int.ofNat n)) true
      action := .takeMatching (.hasType .creature) (.exact (.const 1)) (.battlefield .controller) {} false true
      rest := .bottomRandom
    }) }

/-- Another target creature you control gets +3/+0 and gains first strike until end of turn. -/
def triggerBeginCombatIfDrawnTwoPump : Effect :=
  { targets := .anotherCreatureYouControl
    body := .seq #[
      Instruction.pumpFixed (.target 0) 3 0,
      Instruction.grantKeywords (.target 0) #[Keyword.firstStrike]
    ] }

/-- Create two nonlegendary token copies of this permanent. -/
def triggerCopySelfNonlegendary : Effect :=
  { body := Instruction.createTokens (.copyOf .this #[.removeSupertype .legendary]) (.const 2) }

/-- Thorin: attach any number of Equipment you control to target creature you control; when 1+ attached, reflexive bite. -/
def triggerAttachEquipmentThenFight : Effect :=
  { targets := .creatureYouControl
    body := .bind ⟨0⟩
      (.permanent (.attach (subtypeYouControlExpr .equipment) (.target 0) true))
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisEnters
          effect := {
            targets := TargetSpec.creature.asUpTo 1
            body := .damage (.fight .triggerSubject (.target 0) true)
          }
        })) }

/-- Tom, Bert, and William: return from graveyard onto battlefield as an artifact. -/
def triggerReturnAsArtifact : Effect :=
  { body := .moveZone (.inZones .anyGraveyard (.sameAs .this)) (.battlefield .owner) .put {
      enterTypeMod? := some { mode := .set, types := #[.artifact] }
    } }

/-- Gandalf: exile up to three target lands you control, then return them tapped under their owners' control. -/
def triggerExileLandsThenReturnTapped : Effect :=
  { targets := (.single {
      domain := .object .battlefield (.all #[.hasType .land, .controlledBy .you])
      count := .upTo 3 })
    body := Instruction.exile .allTargets { delayedReturn? := some (.immediately true .owner) } }

/-- Gríma: damaged player exiles until instant/sorcery, you may cast free, rest on bottom random. -/
def triggerGrimaImpulse : Effect :=
  let instOrSorc : ObjectPred := .any #[.hasType .instant, .hasType .sorcery]
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .revealUntil (.triggerPlayer .damagedPlayer) instOrSorc (.const 1) (exileWhileRevealing := true)
        action := .none
        rest := .leaveInPlace
      }))
      (.seq #[
        .stack (.mayCastOrPlay (.filter (.stepObjects ⟨0⟩) instOrSorc) {
          freeCast := true, landsAllowed := false, castNow := true
        }),
        .moveZone (.stepObjects ⟨0⟩) (.library .owner .bottomRandom) .put
      ]) }

/-- Palantír of Orthanc: influence counter, scry 2, target opponent may have you draw; if not, mill X and lose total MV. -/
def triggerPalantir : Effect :=
  { targets := .opponent
    body := .seq #[
      Instruction.putCounters .this .influence (.const 1),
      Instruction.scryFixed 2,
      .optional (.target 0) none
        (Instruction.drawFixed 1)
        (.bind ⟨0⟩ (Instruction.mill (.counterCount (some .influence) .this))
          (.life (.lose (.target 0) (.aggregate .sum (.stat .manaValue) (.stepObjects ⟨0⟩)))))
    ] }

/-- You gain protection from everything until your next turn. -/
def triggerProtectionEverything : Effect :=
  { body := .installEffect (.applyRule (.untilNextTurnOf .you) (.player (.protectionFrom .you .everything))) }

/-- You lose 1 life for each burden counter on this permanent. -/
def triggerLoseLifePerBurden : Effect :=
  { body := Instruction.loseLife (.counterCount (some .burden) .this) }

/-- Reveal until a Saga card, put it onto the battlefield, rest on bottom random. -/
def triggerRevealSaga : Effect :=
  { body := .player (.inspectLibrary {
      source := .revealUntil .you (.hasSubtype (.literal .saga)) (.const 1)
      action := .moveAll (.battlefield .controller)
      rest := .bottomRandom
    }) }

/-- Each opponent sacrifices a creature that dealt combat damage to you this turn. The Ring tempts you. -/
def triggerSacDamagersRingTempts : Effect :=
  { body := .seq #[
      .forEach (.eachPlayer .opponent) ⟨0⟩
        (.moveZone (.inZones .battlefield (.all #[
            .hasType .creature, .controlledBy (.ofExpr (.stepPlayers ⟨0⟩)),
            .dealtDamageThisTurn true (some (.player .you)) true]))
          .graveyard .sacrifice
          { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } }),
      .player (.temptWithRing .you)
    ] }

/-- Each other `subtype` you control gets +X/+X until end of turn, where X is this creature's toughness. -/
def triggerOthersOfSubtypeGetEqualSourceToughness (subtype : CardSubtype) : Effect :=
  { body := Instruction.pump (otherSubtypeYouControlExpr subtype)
      (.objectStat .toughness .this) (.objectStat .toughness .this) }

/-- Plan counter + scry `n`. -/
def triggerScryAndPlan (n : Nat) : Effect :=
  { body := .seq #[Instruction.putCounters .this .plan (.const 1), Instruction.scryFixed n] }

/-- Plan counter + each opponent loses `n` life and you gain `n` life. -/
def triggerDrainAndPlan (n : Nat) : Effect :=
  { body := .seq #[
      Instruction.putCounters .this .plan (.const 1),
      Instruction.loseLifeFixed n .opponents,
      Instruction.gainLifeFixed n
    ] }

/-- Plan counter + draw 1, lose 1 life. -/
def triggerDrawLoseLifeAndPlan : Effect :=
  { body := .seq #[Instruction.putCounters .this .plan (.const 1), Instruction.drawFixed 1, Instruction.loseLifeFixed 1] }

/-- Plan counter + put a +1/+1 counter on target creature you control. -/
def triggerPlusOneOnTargetAndPlan : Effect :=
  { targets := .creatureYouControl
    body := .seq #[Instruction.putCounters .this .plan (.const 1), Instruction.putPlusOne (.target 0) 1] }

/-- Plan finish: sacrifice this, draw a card, put a +1/+1 counter on each creature you control. -/
def triggerPlanFinishDrawPlusOneEach : Effect :=
  { body := .seq #[Instruction.sacrifice .this, Instruction.drawFixed 1, Instruction.putPlusOne creaturesYouControlExpr 1] }

/-- Plan finish: sacrifice this; when you do, return up to two target instant/sorcery cards from your graveyard to hand. -/
def triggerPlanFinishReturnInstants : Effect :=
  { body := .bind ⟨0⟩ (Instruction.sacrifice .this)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisLeaves
          effect := {
            targets := (.single {
              domain := .object .yourGraveyard (.any #[.hasType .instant, .hasType .sorcery])
              count := .upTo 2
            })
            body := Instruction.bounce .allTargets
          }
        })) }

/-- Plan finish: sacrifice this; when you do, you control target opponent during their next turn (CR 723). -/
def triggerPlanFinishControlOpponent : Effect :=
  { body := .bind ⟨0⟩ (Instruction.sacrifice .this)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisLeaves
          effect := {
            targets := .opponent
            body := .installEffect (.applyRule (.untilNextTurnOf (.target 0))
              (.player (.controlPlayer { relation := .opponent, pred := .matchesExpr (.target 0) })))
          }
        })) }

/-- Plan finish: sacrifice this; when you do, target opponent exiles top 5 and you may cast up to two free. -/
def triggerPlanFinishExileTopCast : Effect :=
  { body := .bind ⟨0⟩ (Instruction.sacrifice .this)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisLeaves
          effect := {
            targets := .opponent
            body := .bind ⟨1⟩ (Instruction.exile (.topOfLibrary (.target 0) (.const 5)))
              (.stack (.mayCastOrPlay (.stepObjects ⟨1⟩) {
                freeCast := true, landsAllowed := false, castNow := true, maxCasts? := some 2
              }))
          }
        })) }

/-- Plan finish: sacrifice this and create `n` 2/2 colorless Robot Villain artifact creature tokens. -/
def triggerPlanFinishCreateRobots (n : Nat) : Effect :=
  { body := .seq #[Instruction.sacrifice .this, Instruction.createTokensFixed .robotVillain22 n] }

/-- Plan finish: sacrifice this; when you do, deal `n` damage divided among one or two targets. -/
def triggerPlanFinishDividedDamage (n : Nat) : Effect :=
  { body := .bind ⟨0⟩ (Instruction.sacrifice .this)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisLeaves
          effect := {
            targets := TargetSpec.dividedDamage .anyTarget n 2
            body := Instruction.dealDamage .allTargets (.const (Int.ofNat n)) .this { divided := true }
          }
        })) }

/-- Plan finish: sacrifice this; when you do, put an indestructible counter on target creature you control. -/
def triggerPlanFinishIndestructibleOnTarget : Effect :=
  { body := .bind ⟨0⟩ (Instruction.sacrifice .this)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisLeaves
          effect := {
            targets := .creatureYouControl
            body := Instruction.putCounters (.target 0) .indestructible (.const 1)
          }
        })) }

/-- Surveil `n` (CR 701.25). -/
def triggerSurveil (n : Nat) : Effect :=
  { body := Instruction.surveilFixed n }

/-- Empower Jace `n`. -/
def triggerEmpowerJace (n : Nat) : Effect :=
  { body := Instruction.empowerJace n }

/-- This creature becomes prepared. -/
def triggerPrepareSource : Effect :=
  { body := Instruction.becomePrepared .this }

/-- Target permanent you control gains `k`; +1/+1 counter if creature, loyalty counter if planeswalker. -/
def triggerGrantThenCounterByType (k : Array KeywordAbility) : Effect :=
  { targets := .permanentYouControl
    body := .seq #[
      Instruction.grantKeywords (.target 0) k,
      Instruction.ifThen (.exists (.filter (.target 0) (.hasType .creature)))
        (Instruction.putPlusOne (.target 0) 1),
      Instruction.ifThen (.exists (.filter (.target 0) (.hasType .planeswalker)))
        (Instruction.putCounters (.target 0) .loyalty (.const 1))
    ] }

/-- Destroy target permanent an opponent controls; its controller creates a Treasure token. -/
def triggerDestroyOppPermanentIfSixLands : Effect :=
  { targets := .oppPermanent
    body := .bind ⟨0⟩ (Instruction.destroy (.target 0))
      (Instruction.createTokensFixed .treasure 1 (.controllerOf (.target 0))) }

/-- Another target creature you control gets +1/+1, or a +1/+1 counter if you've scried or surveilled this turn. -/
def triggerPumpOrCounterIfScried : Effect :=
  { targets := .anotherCreatureYouControl
    body := .ifCond (.any #[.turnHistory (.scriedThisTurn .you), .turnHistory (.surveilledThisTurn .you)])
      (Instruction.putPlusOne (.target 0) 1)
      (Instruction.pumpFixed (.target 0) 1 1) }

/-- Add `{G}` for each charge counter on this permanent. -/
def triggerAddGreenPerChargeCounter : Effect :=
  { body := Instruction.addMana { spec := .sequence #[(.colored .green, .counterCount (some .charge) .this)] } }

/-- Fblthp: draw two; if library empty, win the game; else owner shuffles this into library. -/
def triggerDrawTwoWinIfEmptyShuffleSource : Effect :=
  { body := .seq #[
      Instruction.drawFixed 2,
      .ifCond (.cmp .eq (.playerMetric .librarySize .you) (.const 0))
        (.player (.setStatus .you .winGame))
        (.moveZone .this (.library .owner .shuffledIn) .put)
    ] }

/-- Surveil 1; if a card with MV ≤ life gained this turn is put into your graveyard this way, put it into your hand. -/
def triggerSurveilReturnIfGainedLife : Effect :=
  { body := .bind ⟨0⟩ (Instruction.surveilFixed 1)
      (.moveZone (.filter (.stepObjects ⟨0⟩) (.stat .manaValue .le (.playerMetric .lifeGainedThisTurn .you)))
        (.hand .owner) .put) }

/-- Exile up to one target creature until this Aura leaves; enchanted creature becomes a copy of it until this leaves. -/
def triggerExileOtherCopyEnchanted : Effect :=
  { targets := TargetSpec.creature.asUpTo 1
    body := .bind ⟨0⟩ (Instruction.exile (.target 0) { exileUntilSourceLeaves := true })
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.installEffect (.applyContinuous (.untilLeavesBattlefield .this) .attachedHost
          (.becomeCopyOf (.stepObjects ⟨0⟩) #[])))) }

/-- Exile up to one target creature you control; return it at the beginning of the next end step. -/
def triggerExileUntilNextEndStep : Effect :=
  { targets := TargetSpec.creatureYouControl.asUpTo 1
    body := Instruction.exile (.target 0) { delayedReturn? := some (.atNextEndStep false .owner) } }

/-- Choose one — Tap target nonland permanent; or Untap target nonland permanent. -/
def triggerTapOrUntapNonland : Effect :=
  { targets := .nonland
    body := .chooseModes {
      modes := #[
        { targets := .nonland, body := Instruction.tap (.target 0) },
        { targets := .nonland, body := Instruction.untap (.target 0) }
      ]
    } }

/-- Create a Food token or a Treasure token. -/
def triggerCreateFoodOrTreasure : Effect :=
  { body := .chooseModes {
      chooseAtResolution := true
      modes := #[
        { body := Instruction.createTokensFixed .food 1 },
        { body := Instruction.createTokensFixed .treasure 1 }
      ]
    } }

/-- Create a tapped 2/1 black Villain with menace if 2+ creature cards in your graveyard; else mill 2. -/
def triggerVillainIfGyElseMill : Effect :=
  { body := .ifCond (.cmp .ge (ValueExpr.count (.inZones (.graveyardOf .you) (.hasType .creature))) (.const 2))
      (Instruction.createTokensFixed .villain21menace 1 .you true)
      (Instruction.millFixed 2) }

/-- Draw a card, then you may put a land card from your hand onto the battlefield tapped. -/
def triggerDrawMayPutLandTapped : Effect :=
  { body := .seq #[
      Instruction.drawFixed 1,
      Instruction.may .you none
        (.moveZone (.inZones (.handOf .you) (.hasType .land)) (.battlefield .controller) .put {
          tapped := true
          choice? := some { chooser := .controller, count := .exact (.const 1) }
        })
    ] }

/-- Draw a card. If you control another Hero, you gain 2 life. -/
def triggerDrawGainLifeIfAnotherHero : Effect :=
  { body := .seq #[
      Instruction.drawFixed 1,
      Instruction.ifThen (TriggeredAbility.condControlAnotherSubtype .hero) (Instruction.gainLifeFixed 2)
    ] }

/-- Put a +1/+1 counter on target creature, or two if that creature is another Hero. -/
def triggerPlusOneOrTwoIfAnotherHero : Effect :=
  { targets := .creature
    body := .ifCond (.exists (.filter (.target 0) (.all #[.otherThan .this, .hasSubtype (.literal .hero)])))
      (Instruction.putPlusOne (.target 0) 2)
      (Instruction.putPlusOne (.target 0) 1) }

/-- You may sacrifice an artifact or discard a card. If you do, draw a card. -/
def triggerMaySacArtifactOrDiscardDraw : Effect :=
  { body := Instruction.may .you (some CostSpec.sacrificeArtifactOrDiscardCard) (Instruction.drawFixed 1) }

/-! ### Specialized formerly-leftover trigger effects -/

def enterDestroy (kind : TargetSpec) : Effect :=
  { targets := kind
    body := Instruction.destroy (.target 0) }

def enterDealDamageUpToOne (n : Nat) : Effect :=
  { targets := TargetSpec.creature.asUpTo 1
    body := Instruction.dealDamageFixed (.targetSlot 0) n }

def enterFightUpToOne : Effect :=
  { targets := TargetSpec.anotherCreature.asUpTo 1
    body := .damage (.fight .this (.target 0)) }

def enterReturnNonlandNontoken : Effect :=
  { targets := TargetSpec.nonlandNontoken.asUpTo 1
    body := Instruction.bounce (.target 0) }

def enterCreateZabu : Effect :=
  { body := Instruction.createTokensFixed .zabu 1 }

def enterOppCreatesTheVoid : Effect :=
  { targets := .opponent
    body := Instruction.createTokensFixed .theVoid 1 (.target 0) }

def enterCreateSturdyShieldAttach : Effect :=
  { body := .bind ⟨0⟩ (Instruction.createTokensFixed .sturdyShield 1)
      (.permanent (.attach (.stepObjects ⟨0⟩) .this)) }

def enterExileGyPlayUntilNextTurn : Effect :=
  { targets := .equipmentInstantOrSorceryInYourGraveyard
    body := Instruction.exile (.target 0) {
      grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
    } }

def enterReturnGyPermanentThisTurn : Effect :=
  { targets := .permanentCardInYourGraveyard
    body := Instruction.bounce (.target 0) }

def enterTapOppCantUntapWhileControl : Effect :=
  { targets := .oppCreature
    body := .seq #[
      Instruction.tap (.target 0),
      .installEffect (.applyContinuous (.whileOnBattlefield .this) (.target 0)
        (.applyRule (.game (.cantBecomeUntapped .self))))
    ] }

def enterMaySacAnotherThenDestroyOppNonland : Effect :=
  { body := Instruction.may .you (some CostSpec.sacrificeAnotherCreature)
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targets := .oppNonland
          body := Instruction.destroy (.target 0)
        }
      }) }

def enterMaySacOrDiscardNonlandThenDamage : Effect :=
  { body := Instruction.may .you (some CostSpec.sacrificeArtifactOrDiscardNonland)
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targets := .anyTarget
          body := Instruction.dealDamageFixed (.targetSlot 0) 2
        }
      }) }

def enterRevealHandExileUntilLeaves : Effect :=
  { targets := TargetSpec.opponent.asUpTo 1
    body := .seq #[
      .player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject)),
      Instruction.ifThen (.exists .this)
        (Instruction.exile (.target 1) { exileUntilSourceLeaves := true })
    ] }

def enterPlusOnesOrReturnArtEnch : Effect :=
  { targets := TargetSpec.creature.asUpTo 2
    body := .chooseModes {
      chooseAtResolution := true
      modes := #[
        { targets := TargetSpec.creature.asUpTo 2
          body := Instruction.putPlusOne .allTargets 1 },
        { targets := .artEnchCardInYourGraveyard
          body := Instruction.bounce (.target 0) }
      ]
    } }

def enterChooseUpToXModes : Effect :=
  { body := .chooseModes {
      minModes := .const 0
      maxModes := .chosenX
      modes := #[
        { body := .seq #[Instruction.drawFixed 1, Instruction.discardFixed 1] },
        { targets := .opponent
          body := Instruction.loseLifeFixed 2 (.target 0) },
        { targets := (.ofDomain (.object .battlefield (.isToken true)))
          body := Instruction.destroy (.target 0) },
        { body := triggerEachPlayerSacrificesCreature.body }
      ]
    } }

def enterMayTapThenGrantIndestructible : Effect :=
  { body := Instruction.may .you (some CostSpec.tapOnly)
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisEnters
        effect := {
          targets := (.ofDomain (.object .battlefield (.all #[
            .otherThan .this, .hasType .creature, .not (.combatRole .attacking), .controlledBy .you])))
          body := Instruction.grantKeywords (.target 0) #[Keyword.indestructible]
        }
      }) }

def enterTapLoseAbilitiesWhileSource : Effect :=
  { targets := TargetSpec.creature.asUpTo 1
    body := .seq #[
      Instruction.tap (.target 0),
      Instruction.ifThen (.exists .this)
        (Instruction.loseAllAbilities (.target 0) (.whileOnBattlefield .this))
    ] }

def enterRevealDiscardFromHand : Effect :=
  { targets := .player
    body := .player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject)
      (some (.exact (.binary .add (.const 1)
        (ValueExpr.count (.inZones (.graveyardOf .you) (.hasType .creature))))))) }

def stepEnchantedControllerDraws : Effect :=
  { body := Instruction.drawFixed 1 (.controllerOf .attachedHost) }

def stepDrawToTen : Effect :=
  { body := Instruction.draw (.binary .max (.const 0) (.binary .sub (.const 10) (.playerMetric .handSize .you))) }

def stepCopyAbsorbingMan : Effect :=
  { targets := (.single {
      domain := .object .battlefield (.any #[
        .hasType .artifact,
        .all #[.not (.hasSubtype (.literal .aura)), .hasType .enchantment],
        .hasType .land])
      count := .upTo 1 })
    body := .installEffect (.applyContinuous (.untilNextTurnOf .you) .this
      (.becomeCopyOf (.target 0) #[
        .setName "Absorbing Man",
        .addSupertypes #[.legendary],
        .addTypes #[.creature],
        .addSubtypes #[.human, .villain],
        .setBasePT 4 4,
        .addKeywords #[Keyword.vigilance]
      ])) }

def stepHydeChoose : Effect :=
  { body := .chooseModes {
      modes := #[
        { body := Instruction.putPlusOne .this 1 },
        { body := .bind ⟨0⟩
            (.permanent (.modifyCounters (.remove none (.exact (.const 1)))
              (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .counterCount none .ge (.const 1)]))
              (choice? := some { chooser := .controller, count := .exact (.const 1) })))
            (Instruction.ifThen (.stepSucceeded ⟨0⟩) (Instruction.drawFixed 1)) }
      ]
    } }

def stepCopyTaskmaster : Effect :=
  { targets := TargetSpec.creatureOrGyCreatureCard.asUpTo 1
    body := .installEffect (.applyContinuous (.untilNextTurnOf .you) .this
      (.becomeCopyOf (.target 0) #[
        .setName "Taskmaster, Mercenary Mimic",
        .addSupertypes #[.legendary],
        .addTypes #[.creature],
        .replaceCreatureSubtypes #[.human, .mercenary, .villain]
      ])) }

def stepHarnessedFlicker : Effect :=
  { targets := (.single {
      domain := .object .battlefield (.all #[.otherThan .this, .not (.hasType .land), .controlledBy .you])
      count := .upTo 1 })
    body := Instruction.ifThen TriggeredAbility.condSourceHarnessed
      (Instruction.exile (.target 0) { delayedReturn? := some (.immediately false .owner) }) }

def deathHellcatReturn : Effect :=
  { body := .moveZone (.inZones .anyGraveyard (.sameAs .this)) (.battlefield .owner) .put {
      enterCounters := #[(.plusOnePlusOne, .const 1)]
      enterKeywords := #[Keyword.haste]
      enterLoseAllAbilities := true
    } }

def deathVillainReturnAsHero : Effect :=
  { body := .moveZone (.filter .triggerSubject (.hasSubtype (.literal .villain))) (.battlefield .owner) .put {
      enterTypeMod? := some { mode := .add, subtypes := #[.hero] }
      enterCounters := #[(.finality, .const 1)]
    } }

def deathAttackingReturnHand : Effect :=
  { body := Instruction.bounce .triggerSubject }

def deathDeathtouchOppSac : Effect :=
  { body := .forEach (.eachPlayer .opponent) ⟨0⟩
      (.moveZone (.inZones .battlefield (.all #[
          .hasType .creature, .isToken false, .controlledBy (.ofExpr (.stepPlayers ⟨0⟩))]))
        .graveyard .sacrifice
        { choice? := some { chooser := .player (.stepPlayers ⟨0⟩), count := .exact (.const 1) } }) }

def thisAttackMayPayPlusOne : Effect :=
  { body := Instruction.may .you (some (CostSpec.ofGeneric 1))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisAttacks
        effect := {
          targets := .creature
          body := Instruction.putPlusOne (.target 0) 1
        }
      }) }

def thisAttackPayReturnAttacking : Effect :=
  { body := Instruction.may .you
      (some (CostSpec.ofMana { symbols := #[.generic 3, .colored .black] }))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisAttacks
        effect := {
          targets := .creatureCardInYourGraveyard
          body := .moveZone (.target 0) (.battlefield .controller) .put {
            tapped := true
            attacking := true
            enterCounters := #[(.finality, .const 1)]
          }
        }
      }) }

def thisAttackIfArtifactEnteredDraw : Effect :=
  { body := Instruction.drawFixed 1 }

def thisAttackBlinkNontoken : Effect :=
  { targets := (.single {
      domain := .object .battlefield (.all #[.isToken false, .any #[.hasType .artifact, .hasType .creature]])
      count := .upTo 1 })
    body := Instruction.exile (.target 0) { delayedReturn? := some (.immediately true .owner) } }

def thisAttackEquippedDrain : Effect :=
  let equipCount : ValueExpr :=
    ValueExpr.count (.inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .attachedTo .this]))
  { body := .seq #[
      Instruction.loseLife equipCount .opponents,
      Instruction.gainLife equipCount
    ] }

def thisAttackDrawIfPower4 : Effect :=
  { body := Instruction.ifThen (.cmp .ge (.objectStat .power .this) (.const 4)) (Instruction.drawFixed 1) }

def thisAttackAttacksAlonePlus2Indestructible : Effect :=
  { body := .seq #[
      Instruction.pumpFixed .this 2 0,
      Instruction.grantKeywords .this #[Keyword.indestructible]
    ] }

def enterOrAttackCopyKeywords : Effect :=
  { targets := .anotherCreature
    body := .permanent (.modifyCounters (.copyMissingKeywords (.target 0)) .this) }

def enterOrAttackCreateSquirrel : Effect :=
  { body := Instruction.createTokensFixed .squirrel11green 1 }

def watchCombatDamageExileUntilNonland : Effect :=
  let grantCast : Instruction :=
    .stack (.mayCastOrPlay (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))) {
      duration := .untilEndOfTurn, landsAllowed := false, anyManaColor := true
    })
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .revealUntil (.triggerPlayer .damagedPlayer) (.not (.hasType .land)) (.const 1)
          (exileWhileRevealing := true)
        action := .none
        rest := .leaveInPlace
      }))
      (.ifCond (.exists .this)
        (.optional .you none (Instruction.putPlusOne .this 1) grantCast)
        grantCast) }

def watchAttacksAloneDrain : Effect :=
  { targets := .opponent
    body := .seq #[Instruction.loseLifeFixed 1 (.target 0), Instruction.gainLifeFixed 1] }

def watchAttacksAloneFirstStrikeMenace : Effect :=
  { body := Instruction.grantKeywords .triggerSubject #[Keyword.firstStrike, Keyword.menace] }

def watchFirstTapUntap : Effect :=
  { body := Instruction.untap .triggerSubject }

def watchSheHulkRedirectOnce : Effect :=
  { targets := .anyTarget
    body := Instruction.may .you none (Instruction.dealDamage (.targetSlot 0) .eventAmount) }

def watchSpeedballTargeted : Effect :=
  { body := .seq #[
      Instruction.pumpFixed .this 2 2,
      .stack (.chooseNewTargets .triggerSubject true)
    ] }

def watchAnyPlayerSecondDraw : Effect :=
  { body := Instruction.drawFixed 1 }

def watchYouTargetDrawOnce : Effect :=
  { body := Instruction.drawFixed 1 }

def watchVillainOrArtifactDamage : Effect :=
  { targets := .opponent
    body := Instruction.dealDamageFixed (.players (.target 0)) 1 }

def watchVillainConniveOnce : Effect :=
  { body := Instruction.may .you none (.player (.connive .triggerSubject)) }

def watchVillainPlusOneDamageOnce : Effect :=
  { body := .seq #[Instruction.putPlusOne .this 1, Instruction.dealDamageFixed (.players .opponents) 2] }

def watchVillainAttachEquipment : Effect :=
  { targets := .upToOneEquipmentThenCreatureYouControl
    body := .permanent (.attach (.target 0) (.target 1)) }

def watchVillainPlusOneLifelink : Effect :=
  { body := .seq #[Instruction.pumpFixed .this 1 0, Instruction.grantKeywords .this #[Keyword.lifelink]] }

def watchHulklingCompare : Effect :=
  { body := Instruction.putPlusOne .this 1 }

def watchJusticeBounce : Effect :=
  { body := Instruction.putPlusOne .this 1 }

def watchNontokenHeroModal : Effect :=
  { body := .chooseModes {
      modes := #[
        { body := Instruction.createTokensFixed .soldier11white 1 },
        { body := Instruction.pumpFixed creaturesYouControlExpr 1 1 }
      ]
    } }

def watchUltronCopy : Effect :=
  { body := Instruction.may .you (some (CostSpec.ofGeneric 2))
      (.bind ⟨0⟩ (Instruction.createTokens (.copyOf .triggerSubject #[]) (.const 1))
        (.forEach (.eachObject (.filter (.stepObjects ⟨0⟩) (.not (.hasType .creature)))) ⟨1⟩
          (.installEffect (.applyContinuous .indefinite (.stepObjects ⟨1⟩)
            (.all #[
              .modifyTypes { mode := .add, types := #[.creature], subtypes := #[.robot, .villain] },
              .setBasePT (some (.const 2)) (some (.const 2))
            ]))))) }

def watchEnchantedAttachEquipment : Effect :=
  { targets := TargetSpec.equipmentYouControl.asAnyNumber
    body := .permanent (.attach .allTargets .attachedHost) }

def watchEquippedAttacksAloneUntapScry : Effect :=
  { body := .seq #[Instruction.untap .attachedHost, Instruction.scryFixed 1] }

def watchEquippedAttacksTap : Effect :=
  { targets := .defendingPlayerCreature
    body := Instruction.tap (.target 0) }

def watchEquippedTappedDamage : Effect :=
  { body := Instruction.dealDamageFixed (.players .opponents) 1 .attachedHost }

def watchHeroesDamagePlusTwo : Effect :=
  { body := Instruction.putPlusOne .this 2 }

def watchMerfolkAttackDraw : Effect :=
  { body := Instruction.drawFixed 1 }

def watchTokensEnterMayDraw : Effect :=
  { body := Instruction.may .you none (Instruction.drawFixed 1) }

/-- Individual mode effects for Hawkeye's Trick Arrows reflexive trigger (CR 603.3c / 700.2b). -/
def hawkeyeModeEffects : Array Effect :=
  #[{ targets := .creature
      body := .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.applyRule (.combat (.cantBlock .self none)))) },
    { targets := .player
      body := Instruction.dealDamageFixed (.players (.target 0)) 2 },
    { body := .seq #[Instruction.discardFixed 1, Instruction.drawFixed 1] }]

def watchHawkeyeModes : Effect :=
  { body := .optional .you (some (CostSpec.ofGeneric 1))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .thisBecomesTapped
        effect := {
          body := .chooseModes {
            minModes := .const 0
            maxModes := .eventAmount
            modes := hawkeyeModeEffects
          }
        }
      })
      .noop (maxTimes := 3) }

def watchRedHulk : Effect :=
  { body := .bind ⟨0⟩ (Instruction.putPlusOne .this 1)
      (Instruction.ifThen (.stepSucceeded ⟨0⟩)
        (.queueReflexiveTrigger {
          word := .when
          pattern := .thisDealtDamage
          effect := {
            targets := .anyOtherTarget
            body := Instruction.dealDamage (.targetSlot 0) (.counterCount (some .plusOnePlusOne) .this)
          }
        })) }

def watchHulk : Effect :=
  { body := .seq #[
      Instruction.putPlusOne .this 1,
      Instruction.ifThen (Condition.thisMatches (.combatRole .attacking))
        (.seq #[Instruction.untap .this, .turn (.extraPhase .combat true)])
    ] }

def youAttackingPay2LifeToughness : Effect :=
  { body := Instruction.may .you (some (CostSpec.ofItem (.payLife (.const 2))))
      (.installEffect (.applyRule .untilEndOfTurn
        (.combat (.assignCombatDamageByToughness
          { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] }
          (onlyIfToughnessGreater := true))))) }

def youAttackingExileTopHeroPump : Effect :=
  { body := Instruction.may .you none
      (.bind ⟨0⟩ (Instruction.exile (.topOfLibrary .you (.const 1)) {
          grantPlayPerm? := some { duration := .untilEndOfTurn, landsAllowed := true }
        })
        (Instruction.ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.hasSubtype (.literal .hero))))
          (Instruction.pumpFixed .this 2 1))) }

def youAttackingLookSixCast : Effect :=
  let maxAtkPower : ValueExpr :=
    .aggregate .max (.stat .power)
      (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .combatRole .attacking]))
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .topCards .you (.const 6) false
        action := .none
        rest := .leaveInPlace
      }))
      (.seq #[
        .stack (.mayCastOrPlay (.stepObjects ⟨0⟩) {
          freeCast := true, landsAllowed := false, castNow := true
          maxTotalManaValue? := some maxAtkPower
        }),
        .moveZone (.stepObjects ⟨0⟩) (.library .owner .bottomRandom) .put
      ]) }

def castingVillainToken : Effect :=
  { body := Instruction.createTokensFixed .villain21menace 1 }

def castingMerfolkFromBlue : Effect :=
  { body := Instruction.createTokens .merfolk (.manaSymbols (some .blue) .triggerSubject) }

def castingMayPayHasteUnblockable : Effect :=
  { body := Instruction.may .you (some (CostSpec.ofGeneric 1))
      (.queueReflexiveTrigger {
        word := .when
        pattern := .youCastNoncreature
        effect := {
          targets := (.ofDomain (.object .battlefield (.all #[.hasType .creature, .hasKeyword .haste])))
          body := .installEffect (.applyContinuous .untilEndOfTurn (.target 0)
            (.applyRule (.combat (.cantBeBlockedBy .self (.not (.hasKeyword .haste))))))
        }
      }) }

def castingPlusOneEachOther : Effect :=
  { body := Instruction.putPlusOne otherCreaturesYouControlExpr 1 }

def castingExileFlicker : Effect :=
  { targets := (.ofDomain (.object .battlefield (.all #[
      .otherThan .this, .not (.hasType .land), .isToken false])))
    body := Instruction.exile (.target 0) { delayedReturn? := some (.atNextEndStep false .owner) } }

def castingVisionModes : Effect :=
  { body := .chooseModes {
      unusedThisTurn := true
      modes := #[
        { body := Instruction.grantKeywords .this #[Keyword.doubleStrike] },
        { body := Instruction.grantKeywords .this #[Keyword.indestructible] },
        { body := Instruction.drawFixed 1 }
      ]
    } }

def castingDamageEqualMv : Effect :=
  { targets := .anyTarget
    body := Instruction.dealDamage (.targetSlot 0) (.objectStat .manaValue .triggerSubject) }

def castingDrawPowerEqualHand : Effect :=
  { body := .seq #[
      Instruction.drawFixed 1,
      .installEffect (.applyContinuous .untilEndOfTurn .this (.setBasePT (some (.playerMetric .handSize .you)) none))
    ] }

def castingPlusOneThis : Effect :=
  { body := Instruction.putPlusOne .this 1 }

def castingPlusOneScry : Effect :=
  { body := .seq #[Instruction.putPlusOne .this 1, Instruction.scryFixed 1] }

def castingIronFistTap : Effect :=
  let tapAb : ActivatedAbility := {
    cost := CostSpec.tapOnly
    effect := {
      targets := .anyOtherTarget
      body := Instruction.dealDamage (.targetSlot 0) (.objectStat .power .this)
    }
  }
  { body := .installEffect (.applyContinuous .untilEndOfTurn .this (.grantActivated #[tapAb])) }

def castingTargetsGainFlying : Effect :=
  { body := Instruction.grantKeywords (.filter (.targetsOf .triggerSubject) (.hasType .creature)) #[Keyword.flying] }

def castingCopyIfArtifactOrLand : Effect :=
  { body := .seq #[
      Instruction.putPlusOne .this 2,
      .stack (.copyStackObject .triggerSubject (.const 1) true)
    ] }

def castingTapCreatureOrLand : Effect :=
  { targets := (.ofDomain (.object .battlefield (.any #[.hasType .creature, .hasType .land])))
    body := Instruction.tap (.target 0) }

def resourceDiscardExilePlay : Effect :=
  { body := Instruction.may .you none
      (Instruction.exile .triggerSubject {
        grantPlayPerm? := some { duration := .untilEndOfNextTurnOf .you, landsAllowed := true }
      }) }

def resourceDrawIfAnotherHeroDamage : Effect :=
  { targets := .opponent
    body := Instruction.dealDamageFixed (.players (.target 0)) 1 }

def resourceSecondDrawBecome66 : Effect :=
  { body := .seq #[
      Instruction.setBasePTFixed .this 6 6,
      Instruction.grantKeywords .this #[Keyword.trample]
    ] }

def resourceSecondDrawPlusOneTarget : Effect :=
  { targets := .creature
    body := Instruction.putPlusOne (.target 0) 1 }

def resourceSecondDrawDrain : Effect :=
  { body := .seq #[Instruction.loseLifeFixed 1 .opponents, Instruction.gainLifeFixed 1] }

def resourceGainLifePlusOnes : Effect :=
  { targets := TargetSpec.creatureYouControl.asAnyNumber
    body := Instruction.putPlusOne .allTargets 1 }

def resourcePlusOneCreateInsectOnce : Effect :=
  { body := Instruction.createTokensFixed .insect11green 1 }

def resourcePlusOneOnThisOnce : Effect :=
  { body := Instruction.putPlusOne .this 1 }

def resourcePlusOneOnHeroesCreateWall : Effect :=
  { body := Instruction.may .you none (Instruction.createTokensFixed .wall04defender 1) }

/-! ### Triggers whose effect is a pure `Instruction` sequence -/

/-- Draw a card and lose 1 life. -/
def seqDrawAndLoseLife : Effect :=
  { body := .seq #[Instruction.drawFixed 1, Instruction.loseLifeFixed 1] }

/-- Draw `n` cards, then discard a card. -/
def seqDrawThenDiscard (n : Nat) : Effect :=
  { body := .seq #[Instruction.drawFixed n, Instruction.discardFixed 1] }

/-- The source gets +P/+0 and creatures you control gain trample. -/
def seqSourceGetsAndTeamTrample (power : Int) : Effect :=
  { body := .seq #[
      Instruction.pumpFixed .this power 0,
      Instruction.grantKeywords creaturesYouControlExpr #[Keyword.trample]
    ] }

/-- Put a +1/+1 counter on a target of this kind. It gains lifelink until end of turn. -/
def seqPlusOneAndLifelink (kind : TargetSpec) : Effect :=
  { targets := kind
    body := .seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.lifelink]
    ] }

/-- The source gets +1/+0 and can't be blocked this turn. -/
def seqPumpAndUnblockable : Effect :=
  { body := .seq #[Instruction.pumpFixed .this 1 0, Instruction.cantBeBlocked .this] }

/-- Put `n` +1/+1 counters on a creature you control. It gains vigilance until end of turn. -/
def seqPlusOneVigilance (n : Nat) : Effect :=
  { targets := .creatureYouControl
    body := .seq #[
      Instruction.putPlusOne (.target 0) n,
      Instruction.grantKeywords (.target 0) #[Keyword.vigilance]
    ] }

/-- Draw a card and put a +1/+1 counter on the source. -/
def seqDrawPlusOneSource : Effect :=
  { body := .seq #[Instruction.drawFixed 1, Instruction.putPlusOne .this 1] }

/-- Creatures you control get +P/+0 and gain first strike until end of turn. -/
def seqCreaturesPumpAndFirstStrike (power : Int) : Effect :=
  { body := .seq #[
      Instruction.pumpFixed creaturesYouControlExpr power 0,
      Instruction.grantKeywords creaturesYouControlExpr #[Keyword.firstStrike]
    ] }

/-- Put a +1/+1 counter on the source and draw a card. -/
def seqPlusOneOnSourceAndDraw : Effect :=
  { body := .seq #[Instruction.putPlusOne .this 1, Instruction.drawFixed 1] }

/-- The source gets +1/+1 until end of turn and deals `n` damage to each opponent. -/
def seqPumpAndDamageOpponents (n : Nat) : Effect :=
  { body := .seq #[
      Instruction.pumpFixed .this 1 1,
      Instruction.dealDamageFixed (.players .opponents) n
    ] }

/-- Untap another creature you control. If it has `subtype`, put a +1/+1 counter on it. -/
def seqUntapPlusOneIfSubtype (subtype : String) : Effect :=
  let sub := CardSubtype.ofOracleD subtype
  { targets := .anotherCreatureYouControl
    body := .seq #[
      Instruction.untap (.target 0),
      Instruction.ifThen (.exists (.filter (.target 0) (.hasSubtype (.literal sub))))
        (Instruction.putPlusOne (.target 0) 1)
    ] }

/-- You lose 1 life and create a Treasure token. -/
def seqLoseLifeCreateTreasure : Effect :=
  { body := .seq #[Instruction.loseLifeFixed 1, Instruction.createTokensFixed .treasure 1] }

/-- Exile up to one card from an opponent's graveyard. Each opponent loses `life`. -/
def seqExileOppGyCardOppsLoseLife (life : Nat) : Effect :=
  { targets := TargetSpec.oppGraveyardCard.asUpTo 1
    body := .seq #[Instruction.exile (.target 0), Instruction.loseLifeFixed life .opponents] }

end Effect

end Mtg.Engine
