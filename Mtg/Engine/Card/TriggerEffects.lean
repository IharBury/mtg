import Mtg.Engine.Card.Trigger

/-!
# Shared-trigger effect constructors

`Effect.ofTrigger`, pure `Instruction` token/sequence trigger constructors, plus
the transitional Phase-9 `Effect.enter*` / `step*` / `death*` / `watch*` /
`casting*` / `resource*` constructors that lift `SharedTrigger` payloads onto
unified effects.
-/

namespace Mtg.Engine

namespace Effect

/-- Convert a shared trigger effect to the unified `Effect`. -/
def ofTrigger (e : SharedTrigger) : Effect :=
  e.toEffect

/-- Pure Phase 8 `Instruction` trigger effect: create `n` tokens of `kind` (`tapped`). -/
def triggerCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) : Effect :=
  { body := Instruction.createTokensFixed kind n .you tapped }

/-- Pure Phase 8 `Instruction` trigger effect: create one `kind` token, then attach this source to it. -/
def triggerCreateThenAttach (kind : TokenSpec) : Effect :=
  { body := .bind ⟨0⟩ (Instruction.createTokensFixed kind 1)
      (.permanent (.attach .this (.stepObjects ⟨0⟩))) }

/-- Leftover trigger constructors as unified `Effect` factories. -/
def enterDestroy (kind : TargetSpec) : Effect :=
  ofTrigger (.enter (.destroy kind))

def enterDealDamageUpToOne (n : Nat) : Effect :=
  ofTrigger (.enter (.dealDamageUpToOne n))

def enterFightUpToOne : Effect := ofTrigger (.enter .fightUpToOne)

def enterReturnNonlandNontoken : Effect := ofTrigger (.enter .returnNonlandNontoken)

def enterCreateZabu : Effect := ofTrigger (.enter .createZabu)

def enterOppCreatesTheVoid : Effect := ofTrigger (.enter .oppCreatesTheVoid)

def enterCreateSturdyShieldAttach : Effect := ofTrigger (.enter .createSturdyShieldAttach)

def enterExileGyPlayUntilNextTurn : Effect := ofTrigger (.enter .exileGyPlayUntilNextTurn)

def enterReturnGyPermanentThisTurn : Effect := ofTrigger (.enter .returnGyPermanentThisTurn)

def enterTapOppCantUntapWhileControl : Effect := ofTrigger (.enter .tapOppCantUntapWhileControl)

def enterMaySacAnotherThenDestroyOppNonland : Effect := ofTrigger (.enter .maySacAnotherThenDestroyOppNonland)

def enterMaySacOrDiscardNonlandThenDamage : Effect := ofTrigger (.enter .maySacOrDiscardNonlandThenDamage)

def enterRevealHandExileUntilLeaves : Effect := ofTrigger (.enter .revealHandExileUntilLeaves)

def enterPlusOnesOrReturnArtEnch : Effect := ofTrigger (.enter .plusOnesOrReturnArtEnch)

def enterChooseUpToXModes : Effect := ofTrigger (.enter .chooseUpToXModes)

def enterMayTapThenGrantIndestructible : Effect := ofTrigger (.enter .mayTapThenGrantIndestructible)

def enterTapLoseAbilitiesWhileSource : Effect := ofTrigger (.enter .tapLoseAbilitiesWhileSource)

def enterRevealDiscardFromHand : Effect := ofTrigger (.enter .revealDiscardFromHand)

def enterCreateRedwing : Effect := ofTrigger (.enter .createRedwing)

def stepEnchantedControllerDraws : Effect := ofTrigger (.step .enchantedControllerDraws)

def stepDrawToTen : Effect := ofTrigger (.step .drawToTen)

def stepCopyAbsorbingMan : Effect := ofTrigger (.step .copyAbsorbingMan)

def stepHydeChoose : Effect := ofTrigger (.step .hydeChoose)

def stepCopyTaskmaster : Effect := ofTrigger (.step .copyTaskmaster)

def stepHarnessedFlicker : Effect := ofTrigger (.step .harnessedFlicker)

def deathHellcatReturn : Effect := ofTrigger (.death .hellcatReturn)

def deathVillainReturnAsHero : Effect := ofTrigger (.death .villainReturnAsHero)

def deathAttackingReturnHand : Effect := ofTrigger (.death .attackingReturnHand)

def deathDeathtouchOppSac : Effect := ofTrigger (.death .deathtouchOppSac)

def thisAttackMayPayPlusOne : Effect := ofTrigger (.thisAttack .mayPayPlusOne)

def thisAttackPayReturnAttacking : Effect := ofTrigger (.thisAttack .payReturnAttacking)

def thisAttackIfArtifactEnteredDraw : Effect := ofTrigger (.thisAttack .ifArtifactEnteredDraw)

def thisAttackBlinkNontoken : Effect := ofTrigger (.thisAttack .blinkNontoken)

def thisAttackEquippedDrain : Effect := ofTrigger (.thisAttack .equippedDrain)

def thisAttackDrawIfPower4 : Effect := ofTrigger (.thisAttack .drawIfPower4)

def thisAttackAttacksAlonePlus2Indestructible : Effect := ofTrigger (.thisAttack .attacksAlonePlus2Indestructible)

def enterOrAttackCopyKeywords : Effect := ofTrigger (.enterOrAttack .copyKeywords)

def enterOrAttackCreateSquirrel : Effect := ofTrigger (.enterOrAttack .createSquirrel)

def watchCombatDamageExileUntilNonland : Effect := ofTrigger (.watch .combatDamageExileUntilNonland)

def watchAttacksAloneDrain : Effect := ofTrigger (.watch .attacksAloneDrain)

def watchAttacksAloneFirstStrikeMenace : Effect := ofTrigger (.watch .attacksAloneFirstStrikeMenace)

def watchFirstTapUntap : Effect := ofTrigger (.watch .firstTapUntap)

def watchSheHulkRedirectOnce : Effect := ofTrigger (.watch .sheHulkRedirectOnce)

def watchSpeedballTargeted : Effect := ofTrigger (.watch .speedballTargeted)

def watchAnyPlayerSecondDraw : Effect := ofTrigger (.watch .anyPlayerSecondDraw)

def watchYouTargetDrawOnce : Effect := ofTrigger (.watch .youTargetDrawOnce)

def watchVillainOrArtifactDamage : Effect := ofTrigger (.watch .villainOrArtifactDamage)

def watchVillainConniveOnce : Effect := ofTrigger (.watch .villainConniveOnce)

def watchVillainPlusOneDamageOnce : Effect := ofTrigger (.watch .villainPlusOneDamageOnce)

def watchVillainAttachEquipment : Effect := ofTrigger (.watch .villainAttachEquipment)

def watchVillainPlusOneLifelink : Effect := ofTrigger (.watch .villainPlusOneLifelink)

def watchHulklingCompare : Effect := ofTrigger (.watch .hulklingCompare)

def watchJusticeBounce : Effect := ofTrigger (.watch .justiceBounce)

def watchNontokenHeroModal : Effect := ofTrigger (.watch .nontokenHeroModal)

def watchUltronCopy : Effect := ofTrigger (.watch .ultronCopy)

def watchEnchantedAttachEquipment : Effect := ofTrigger (.watch .enchantedAttachEquipment)

def watchEquippedAttacksAloneUntapScry : Effect := ofTrigger (.watch .equippedAttacksAloneUntapScry)

def watchEquippedAttacksTap : Effect := ofTrigger (.watch .equippedAttacksTap)

def watchEquippedTappedDamage : Effect := ofTrigger (.watch .equippedTappedDamage)

def watchHeroesDamagePlusTwo : Effect := ofTrigger (.watch .heroesDamagePlusTwo)

def watchMerfolkAttackDraw : Effect := ofTrigger (.watch .merfolkAttackDraw)

def watchTokensEnterMayDraw : Effect := ofTrigger (.watch .tokensEnterMayDraw)

def watchHawkeyeModes : Effect := ofTrigger (.watch .hawkeyeModes)

def watchRedHulk : Effect := ofTrigger (.watch .redHulk)

def watchHulk : Effect := ofTrigger (.watch .hulk)

def youAttackingPay2LifeToughness : Effect := ofTrigger (.youAttacking .pay2LifeToughness)

def youAttackingExileTopHeroPump : Effect := ofTrigger (.youAttacking .exileTopHeroPump)

def youAttackingLookSixCast : Effect := ofTrigger (.youAttacking .lookSixCast)

def castingVillainToken : Effect := ofTrigger (.casting .villainToken)

def castingMerfolkFromBlue : Effect := ofTrigger (.casting .merfolkFromBlue)

def castingMayPayHasteUnblockable : Effect := ofTrigger (.casting .mayPayHasteUnblockable)

def castingPlusOneEachOther : Effect := ofTrigger (.casting .plusOneEachOther)

def castingExileFlicker : Effect := ofTrigger (.casting .exileFlicker)

def castingVisionModes : Effect := ofTrigger (.casting .visionModes)

def castingDamageEqualMv : Effect := ofTrigger (.casting .damageEqualMv)

def castingDrawPowerEqualHand : Effect := ofTrigger (.casting .drawPowerEqualHand)

def castingPlusOneThis : Effect := ofTrigger (.casting .plusOneThis)

def castingPlusOneScry : Effect := ofTrigger (.casting .plusOneScry)

def castingIronFistTap : Effect := ofTrigger (.casting .ironFistTap)

def castingTargetsGainFlying : Effect := ofTrigger (.casting .targetsGainFlying)

def castingCopyIfArtifactOrLand : Effect := ofTrigger (.casting .copyIfArtifactOrLand)

def castingTapCreatureOrLand : Effect := ofTrigger (.casting .tapCreatureOrLand)

def resourceDiscardExilePlay : Effect := ofTrigger (.resource .discardExilePlay)

def resourceDrawIfAnotherHeroDamage : Effect := ofTrigger (.resource .drawIfAnotherHeroDamage)

def resourceSecondDrawBecome66 : Effect := ofTrigger (.resource .secondDrawBecome66)

def resourceSecondDrawPlusOneTarget : Effect := ofTrigger (.resource .secondDrawPlusOneTarget)

def resourceSecondDrawDrain : Effect := ofTrigger (.resource .secondDrawDrain)

def resourceGainLifePlusOnes : Effect := ofTrigger (.resource .gainLifePlusOnes)

def resourcePlusOneCreateInsectOnce : Effect := ofTrigger (.resource .plusOneCreateInsectOnce)

def resourcePlusOneOnThisOnce : Effect := ofTrigger (.resource .plusOneOnThisOnce)

def resourcePlusOneOnHeroesCreateWall : Effect := ofTrigger (.resource .plusOneOnHeroesCreateWall)

/-!
Triggers whose effect is a pure Phase 8 `Instruction` sequence.
`TriggeredAbility.sequenceClause` prints the exact Oracle clause from the `Instruction` shape.
-/

private def creaturesYouControlExpr : ObjectExpr :=
  .inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])

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
  { targeting := .of kind
    body := .seq #[
      Instruction.putPlusOne (.target 0) 1,
      Instruction.grantKeywords (.target 0) #[Keyword.lifelink]
    ] }

/-- The source gets +1/+0 and can't be blocked this turn. -/
def seqPumpAndUnblockable : Effect :=
  { body := .seq #[Instruction.pumpFixed .this 1 0, Instruction.cantBeBlocked .this] }

/-- Put `n` +1/+1 counters on a creature you control. It gains vigilance until end of turn. -/
def seqPlusOneVigilance (n : Nat) : Effect :=
  { targeting := .of .creatureYouControl
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
  { targeting := .of .anotherCreatureYouControl
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
  { targeting := .of .oppGraveyardCard
    allowsZeroTargets := true
    body := .seq #[Instruction.exile (.target 0), Instruction.loseLifeFixed life .opponents] }

instance : Coe SharedTrigger Effect where
  coe := ofTrigger

end Effect

end Mtg.Engine
