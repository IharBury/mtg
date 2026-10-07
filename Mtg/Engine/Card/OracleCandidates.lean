import Mtg.Engine.Card.FraEffects

/-!
Modeled abilities the Oracle parser can recognize. Each entry is a shape.
`Nat`, `Int`, `String`, and target-kind arguments are read from the card's
own Oracle text, so a prototype such as `Effect.draw 1` also matches “Draw
seven cards,” and `Effect.destroyCreature` also matches “Destroy target
artifact.” Each list keeps one prototype per shape. Another entry that
differs only by those arguments is the same ability, so it is not listed again.
A spell whose text is several of these shapes in a row is parsed as a
`Resolution.sequence` of those shapes, so the sequence itself is not listed.
“Draw N cards, then discard a card” is `draw` followed by `discardCards`,
so that sentence is not listed either.
-/

namespace Mtg.Engine.OracleCandidates

open Mtg.Engine
open Mtg.Engine.OracleActivate

def spellEffects : Thunk (Array Effect) := Thunk.mk fun _ => #[
  {
    resolution := .searchBasicLand
    phrase := Resolution.toPhrase .searchBasicLand EffectTargetKind.none.noun
  },
  {
    resolution := .onSource (.pump 1 1)
    phrase := Resolution.toPhrase (.onSource (.pump 1 1)) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.amassGoblins 1)
    phrase := SpellResolution.toPhrase (.amassGoblins 1) EffectTargetKind.none.noun
  },
  {
    resolution := .searchLandTypeToHand "Mountain"
    phrase := Resolution.toPhrase (.searchLandTypeToHand "Mountain") EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.tapScryDraw 1 1)
    phrase := SpellResolution.toPhrase (.tapScryDraw 1 1) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .player
    spellCastKind := .destroyCreature
    resolution := Resolution.ofSpell (.exileAttackersSearchBasics)
    phrase := SpellResolution.toPhrase .exileAttackersSearchBasics EffectTargetKind.player.noun
  },
  {
    targeting := .of .playerOrCreature
    spellCastKind := .burn
    resolution := Resolution.ofSpell (.onPermanent (.dealDamage 3))
    phrase := SpellResolution.toPhrase (.onPermanent (.dealDamage 3)) EffectTargetKind.playerOrCreature.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.draw 1)
    phrase := SpellResolution.toPhrase (.draw 1) EffectTargetKind.none.noun
  },
  {
    resolution := .discard 1
    phrase := s!"discard {cardPhrase 1}"
  },
  {
    resolution := .searchTwoBasicsSplit
    phrase := Resolution.toPhrase .searchTwoBasicsSplit EffectTargetKind.none.noun
  },
  {
    targeting := .of (.creaturePowerAtMost 2)
    resolution := .onPermanent .cantBeBlocked
    phrase := Resolution.toPhrase (.onPermanent .cantBeBlocked) (EffectTargetKind.creaturePowerAtMost 2).noun
  },
  {
    resolution := Resolution.ofSpell (.extraLand)
    phrase := SpellResolution.toPhrase .extraLand EffectTargetKind.none.noun
  },
  {
    resolution := .becomeSubtypeWithLandsPT "Bear"
    phrase := Resolution.toPhrase (.becomeSubtypeWithLandsPT "Bear") EffectTargetKind.none.noun
  },
  {
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.chooseTypeReturnOthers)
    phrase := SpellResolution.toPhrase .chooseTypeReturnOthers EffectTargetKind.none.noun
  },
  {
    targeting := .of (.creatureYouControlPowerAtMost 1)
    resolution := .returnFromGyAttach
    phrase := Resolution.toPhrase .returnFromGyAttach (EffectTargetKind.creatureYouControlPowerAtMost 1).noun
  },
  {
    targeting := .of .creature
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.putOnTopOrBottom)
    phrase := SpellResolution.toPhrase .putOnTopOrBottom EffectTargetKind.creature.noun
  },
  {
    resolution := .transform
    phrase := Resolution.toPhrase .transform EffectTargetKind.none.noun
  },
  {
    resolution := .harnessInfinityStone
    phrase := Resolution.toPhrase .harnessInfinityStone EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.draw 3, .discardTwoUnlessArtifact])
    phrase := SpellResolution.toPhrase (.sequence [.draw 3, .discardTwoUnlessArtifact]) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature .own
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent (.pump 3 3))
    phrase := SpellResolution.toPhrase (.onPermanent (.pump 3 3)) EffectTargetKind.creature.noun
  },
  {
    resolution := .addAnyColorSpendOnlySubtype "Hero"
    phrase := Resolution.toPhrase (.addAnyColorSpendOnlySubtype "Hero") EffectTargetKind.none.noun
  },
  {
    resolution := .returnFromGyFinalityAttach
    phrase := Resolution.toPhrase .returnFromGyFinalityAttach EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .enchantedAttachEquipment).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .enchantedAttachEquipment)
    }
  ),
  {
    resolution := .sequence [.onSource (.plusOne 1), .draw 2]
    phrase := s!"Put {plusOnePlusOneCountersPhrase 1} on this and draw {cardPhrase 2}"
  },
  {
    resolution := .draw 1
    phrase := Resolution.toPhrase (.draw 1) EffectTargetKind.none.noun
  },
  {
    resolution := .addTwoAnyColorCreatureSources
    phrase := Resolution.toPhrase .addTwoAnyColorCreatureSources EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .villainConniveOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .villainConniveOnce)
    }
  ),
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [
      .onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.cantBeBlocked)),
      .draw 1])
    phrase := SpellResolution.toPhrase (.sequence [
      .onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.cantBeBlocked)),
      .draw 1]) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [.onPermanent (.pump 3 1), .exileTopPlayUntilNext 1])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent (.pump 3 1), .exileTopPlayUntilNext 1]) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.sequence [.onPermanent (.dealDamage 5), .damageControllerIfTeamwork 2])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent (.dealDamage 5), .damageControllerIfTeamwork 2]) EffectTargetKind.creature.noun
  },
  {
    targeting := .of (.creatureMvAtMost 3)
    spellCastKind := .destroyCreature
    resolution := Resolution.ofSpell (.exileCreatureMvAtMostOrAnyIfTeamwork 3 3)
    phrase := SpellResolution.toPhrase (.exileCreatureMvAtMostOrAnyIfTeamwork 3 3) (EffectTargetKind.creatureMvAtMost 3).noun
  },
  {
    targeting := .of .attackingAloneCreatureYouControl
    resolution := .sequence [.onPermanent (.pump 1 0), .gainLife 1]
    phrase := Resolution.toPhrase (.sequence [.onPermanent (.pump 1 0), .gainLife 1]) EffectTargetKind.attackingAloneCreatureYouControl.noun
  },
  (
    let t := (SharedTrigger.step .copyAbsorbingMan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .copyAbsorbingMan)
    }
  ),
  (
    let t := (SharedTrigger.step .copyTaskmaster).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .copyTaskmaster)
    }
  ),
  {
    targeting := .of .artifactOrCreatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.becomeArtifactCreature44Flying)
    phrase := SpellResolution.toPhrase .becomeArtifactCreature44Flying EffectTargetKind.artifactOrCreatureYouControl.noun
  },
  (
    let t := (SharedTrigger.enter .tapOppCantUntapWhileControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .tapOppCantUntapWhileControl)
    }
  ),
  (
    let t := (SharedTrigger.watch .hulklingCompare).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .hulklingCompare)
    }
  ),
  {
    resolution := .sequence [.onSource (.plusOne 1), .createTigerGod]
    phrase := "Put a +1/+1 counter on this and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.doublePowerAndToughness)
    phrase := SpellResolution.toPhrase .doublePowerAndToughness EffectTargetKind.creature.noun
  },
  {
    resolution := .addBlueCantNonartifact
    phrase := Resolution.toPhrase .addBlueCantNonartifact EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .firstTapUntap).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .firstTapUntap)
    }
  ),
  (
    let t := (SharedTrigger.watch .equippedTappedDamage).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .equippedTappedDamage)
    }
  ),
  (
    let t := (SharedTrigger.enter .revealHandExileUntilLeaves).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .revealHandExileUntilLeaves)
    }
  ),
  {
    targeting := .of .twoArtifactsYouControl
    resolution := .copyArtifactYouControlNotLegendary
    phrase := Resolution.toPhrase .copyArtifactYouControlNotLegendary EffectTargetKind.twoArtifactsYouControl.noun
  },
  (
    let t := (SharedTrigger.watch .sheHulkRedirectOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .sheHulkRedirectOnce)
    }
  ),
  (
    let t := (SharedTrigger.thisAttack .drawIfPower4).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .drawIfPower4)
    }
  ),
  {
    resolution := .exileTopXPlayThisTurn
    phrase := Resolution.toPhrase .exileTopXPlayThisTurn EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.thisAttack .equippedDrain).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .equippedDrain)
    }
  ),
  (
    let t := (SharedTrigger.enter .maySacOrDiscardNonlandThenDamage).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .maySacOrDiscardNonlandThenDamage)
    }
  ),
  (
    let t := (SharedTrigger.enter .mayTapThenGrantIndestructible).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .mayTapThenGrantIndestructible)
    }
  ),
  (
    let t := (SharedTrigger.watch .hawkeyeModes).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .hawkeyeModes)
    }
  ),
  (
    let t := (SharedTrigger.thisAttack .payReturnAttacking).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .payReturnAttacking)
    }
  ),
  (
    let t := (SharedTrigger.enter .maySacAnotherThenDestroyOppNonland).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .maySacAnotherThenDestroyOppNonland)
    }
  ),
  (
    let t := (SharedTrigger.watch .redHulk).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .redHulk)
    }
  ),
  (
    let t := (SharedTrigger.casting .mayPayHasteUnblockable).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .mayPayHasteUnblockable)
    }
  ),
  (
    let t := (SharedTrigger.watch .speedballTargeted).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .speedballTargeted)
    }
  ),
  (
    let t := (SharedTrigger.youAttacking .pay2LifeToughness).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.youAttacking .pay2LifeToughness)
    }
  ),
  {
    resolution := .drawPerDiscardedThisTurn
    phrase := Resolution.toPhrase .drawPerDiscardedThisTurn EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.death .attackingReturnHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.death .attackingReturnHand)
    }
  ),
  (
    let t := (SharedTrigger.enter (.destroy .oppCreatureDealtDamageThisTurn)).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter (.destroy .oppCreatureDealtDamageThisTurn))
    }
  ),
  {
    resolution := .equipmentBecomesConstructHero
    phrase := Resolution.toPhrase .equipmentBecomesConstructHero EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.youAttacking .exileTopHeroPump).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.youAttacking .exileTopHeroPump)
    }
  ),
  (
    let t := (SharedTrigger.watch .villainPlusOneDamageOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .villainPlusOneDamageOnce)
    }
  ),
  {
    resolution := .createTokensEqualSubtype .squirrel11green "Squirrel"
    phrase := Resolution.toPhrase (.createTokensEqualSubtype .squirrel11green "Squirrel") EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.enter .tapLoseAbilitiesWhileSource).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .tapLoseAbilitiesWhileSource)
    }
  ),
  {
    targeting := .of (.upToTwoCreaturesTotalMvAtMost 6)
    allowsZeroTargets := true
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.gainControlOfUpToTwoCreaturesTotalMvAtMost 6))
    phrase := s!"Gain control of up to two target creatures with total mana value {6} or less for as long as this Saga remains on the battlefield"
  },
  {
    resolution := .nextInstantSorceryCopyIfMvAtMostSourcePower
    phrase := Resolution.toPhrase .nextInstantSorceryCopyIfMvAtMostSourcePower EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.death .villainReturnAsHero).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.death .villainReturnAsHero)
    }
  ),
  {
    targeting := .of .creature
    abilityCastKind := .creatureDamage
    resolution := .onPermanent (.dealDamage 1)
    phrase := Resolution.toPhrase (.onPermanent (.dealDamage 1)) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.casting .ironFistTap).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .ironFistTap)
    }
  ),
  {
    targeting := .of .creatureYouControlThenOppCreature
    spellCastKind := .fight
    resolution := Resolution.ofSpell (.fight)
    phrase := SpellResolution.toPhrase .fight EffectTargetKind.creatureYouControlThenOppCreature.noun
  },
  (
    let t := (SharedTrigger.enter .revealDiscardFromHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .revealDiscardFromHand)
    }
  ),
  (
    let t := (SharedTrigger.watch .ultronCopy).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .ultronCopy)
    }
  ),
  (
    let t := (SharedTrigger.casting .visionModes).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .visionModes)
    }
  ),
  (
    let t := (SharedTrigger.watch .villainAttachEquipment).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .villainAttachEquipment)
    }
  ),
  (
    let t := (SharedTrigger.step .hydeChoose).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .hydeChoose)
    }
  ),
  (
    let t := (SharedTrigger.resource .drawIfAnotherHeroDamage).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .drawIfAnotherHeroDamage)
    }
  ),
  {
    resolution := .becomeTypes #["Dinosaur", "Hero"] 3 5 (Keyword.reach.merge Keyword.vigilance)
    phrase := Resolution.toPhrase (.becomeTypes #["Dinosaur", "Hero"] 3 5 (Keyword.reach.merge Keyword.vigilance)) EffectTargetKind.none.noun
  },
  {
    resolution := .becomeTypes #["Dinosaur", "Hero"] 6 6 Keyword.trample
    phrase := Resolution.toPhrase (.becomeTypes #["Dinosaur", "Hero"] 6 6 Keyword.trample) EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.enter .chooseUpToXModes).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .chooseUpToXModes)
    }
  ),
  (
    let t := (SharedTrigger.resource .secondDrawBecome66).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .secondDrawBecome66)
    }
  ),
  {
    resolution := .createTokens .villain21menace 1 (tapped := true)
    phrase := Resolution.toPhrase (.createTokens .villain21menace 1 (tapped := true)) EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.step .drawToTen).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .drawToTen)
    }
  ),
  {
    resolution := Resolution.ofSpell (.nextFreeRGCreature)
    phrase := SpellResolution.toPhrase .nextFreeRGCreature EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.youAttacking .lookSixCast).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.youAttacking .lookSixCast)
    }
  ),
  {
    resolution := .plusOneX
    phrase := Resolution.toPhrase .plusOneX EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureYouControl
    resolution := .attach
    phrase := Resolution.toPhrase .attach EffectTargetKind.creatureYouControl.noun
  },
  {
    targeting := .of .creature .own
    resolution := .onPermanent .cantBeBlocked
    phrase := Resolution.toPhrase (.onPermanent .cantBeBlocked) EffectTargetKind.creature.noun
  },
  {
    resolution := .gainLife 3
    phrase := Resolution.toPhrase (.gainLife 3) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.onPermanent (.dealDamage 5))
    phrase := SpellResolution.toPhrase (.onPermanent (.dealDamage 5)) EffectTargetKind.creature.noun
  },
  {
    resolution := .onSource (.plusOne 1)
    phrase := Resolution.toPhrase (.onSource (.plusOne 1)) EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.enter .exileGyPlayUntilNextTurn).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .exileGyPlayUntilNextTurn)
    }
  ),
  (
    let t := (SharedTrigger.enter .fightUpToOne).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .fightUpToOne)
    }
  ),
  (
    let t := (SharedTrigger.enter .returnNonlandNontoken).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .returnNonlandNontoken)
    }
  ),
  {
    targeting := .of .creature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.onPermanent (.dealDamageLoseIndestructibleExile 3))
    phrase := SpellResolution.toPhrase (.onPermanent (.dealDamageLoseIndestructibleExile 3)) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .destroyCreature
    resolution := Resolution.ofSpell (.onPermanent .destroy)
    phrase := SpellResolution.toPhrase (.onPermanent .destroy) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .artifactOrLand
    spellCastKind := .destroyArtifactOrLand
    resolution := .sequence [.onPermanent .destroy, .creaturesWithoutFlyingCantBlock]
    phrase := "destroy target artifact or land. Creatures without flying can't block this turn"
  },
  {
    targeting := .of .creatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [
      .onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.trample.merge Keyword.hexproof))])
    phrase := "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"
  },
  {
    targeting := .of .creatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [
      .onPermanent .untap,
      .onPermanent (.pump 2 2),
      .mayAttachEquipmentIfDwarf])
    phrase := SpellResolution.toPhrase (.sequence [
      .onPermanent .untap,
      .onPermanent (.pump 2 2),
      .mayAttachEquipmentIfDwarf]) EffectTargetKind.creatureYouControl.noun
  },
  (
    let t := (SharedTrigger.casting .plusOneScry).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .plusOneScry)
    }
  ),
  (
    let t := (SharedTrigger.step .enchantedControllerDraws).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .enchantedControllerDraws)
    }
  ),
  (
    let t := (SharedTrigger.thisAttack .attacksAlonePlus2Indestructible).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .attacksAlonePlus2Indestructible)
    }
  ),
  (
    let t := (SharedTrigger.casting .plusOneThis).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .plusOneThis)
    }
  ),
  (
    let t := (SharedTrigger.watch .nontokenHeroModal).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .nontokenHeroModal)
    }
  ),
  (
    let t := (SharedTrigger.resource .secondDrawDrain).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .secondDrawDrain)
    }
  ),
  (
    let t := (SharedTrigger.death .hellcatReturn).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.death .hellcatReturn)
    }
  ),
  {
    targeting := .of .upToOneCreatureThenPlayer
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [.plusOneOnCreatureTargets, .targetPlayersGainLife 2])
    phrase := SpellResolution.toPhrase (.sequence [.plusOneOnCreatureTargets, .targetPlayersGainLife 2]) EffectTargetKind.upToOneCreatureThenPlayer.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.draw 2, .loseLife 2])
    phrase := SpellResolution.toPhrase (.sequence [.draw 2, .loseLife 2]) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.draw 1, .loseLife 1, .amassGoblins 2])
    phrase := SpellResolution.toPhrase (.sequence [.draw 1, .loseLife 1, .amassGoblins 2]) EffectTargetKind.none.noun
  },
  {
    resolution := .sequence [.shuffleSource, .draw 3]
    phrase := s!"This owner shuffles him into their library and draws {cardPhrase 3}"
  },
  {
    resolution := .sequence
      [.creaturesYouControlPump 2 0,
      .spell (.eachOpponentLosesLife 2)]
    phrase := s!"Creatures you control get {signedStat 2}/{signedStat 0} until end of turn. Each opponent loses {2} life"
  },
  {
    resolution := .sequence [.onSource (.plusOne 2), .createTokens .robotVillain22 1]
    phrase := s!"Put {plusOnePlusOneCountersPhrase 2} on this creature and {TokenKind.createPhrase .robotVillain22 1}"
  },
  {
    resolution := .subtypesGainMenace #["Goblin", "Orc"]
    phrase := Resolution.toPhrase (.subtypesGainMenace #["Goblin", "Orc"]) EffectTargetKind.none.noun
  },
  {
    resolution := .subtypesGainMenace #["Elf"]
    phrase := Resolution.toPhrase (.subtypesGainMenace #["Elf"]) EffectTargetKind.none.noun
  },
  {
    resolution := .teamGain Keyword.menace
    phrase := Resolution.toPhrase (.teamGain Keyword.menace) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.amassGoblinsOrFromGy 1 3)
    phrase := SpellResolution.toPhrase (.amassGoblinsOrFromGy 1 3) EffectTargetKind.none.noun
  },
  {
    resolution := .exileTop
    phrase := Resolution.toPhrase .exileTop EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    maxTargets := 2
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.tapTargets)
    phrase := SpellResolution.toPhrase .tapTargets EffectTargetKind.creature.noun
  },
  {
    targeting := .of .artifactOrCreatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible)))
    phrase := SpellResolution.toPhrase (.onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible))) EffectTargetKind.artifactOrCreatureYouControl.noun
  },
  {
    resolution := .creaturesYouControlPump 1 1
    phrase := Resolution.toPhrase (.creaturesYouControlPump 1 1) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.scry 2)
    phrase := SpellResolution.toPhrase (.scry 2) EffectTargetKind.none.noun
  },
  {
    resolution := .surveil 1
    phrase := Resolution.toPhrase (.surveil 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.counterUnlessPays 4)
    phrase := SpellResolution.toPhrase (.counterUnlessPays 4) EffectTargetKind.spell.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.counterExilePermanentMayCast)
    phrase := SpellResolution.toPhrase .counterExilePermanentMayCast EffectTargetKind.spell.noun
  },
  {
    targeting := .of .twoNonlandsSharingType
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.exchangeControl)
    phrase := SpellResolution.toPhrase .exchangeControl EffectTargetKind.twoNonlandsSharingType.noun
  },
  {
    resolution := .returnFromGraveyardToHand
    phrase := Resolution.toPhrase .returnFromGraveyardToHand EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    preferAsDefaultMode := true
    resolution := Resolution.ofSpell (.onPermanent (.pumpAndExileIfDies (-5) (-5)))
    phrase := SpellResolution.toPhrase (.onPermanent (.pumpAndExileIfDies (-5) (-5))) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .player
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.creaturesOfPlayerPump (-1) (-1))
    phrase := SpellResolution.toPhrase (.creaturesOfPlayerPump (-1) (-1)) EffectTargetKind.player.noun
  },
  {
    targeting := .of .player .selfPlayer
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.targetPlayerDraw 2, .targetPlayerLosesLife 2])
    phrase := SpellResolution.toPhrase (.sequence [.targetPlayerDraw 2, .targetPlayerLosesLife 2]) EffectTargetKind.player.noun
  },
  {
    targeting := .of .creature .own
    spellCastKind := .pump
    resolution := .sequence
      [.onPermanent (.pump 2 2),
      .onPermanent (.grantKeywords Keyword.lifelink)]
    phrase := s!"target creature gets {signedStat 2}/{signedStat 2} and gains lifelink until end of turn"
  },
  {
    targeting := .of .creature .own
    spellCastKind := .pump
    resolution := .sequence
      [.onPermanent (.pump 3 0), .onPermanent (.grantKeywords (Keyword.reach.merge Keyword.firstStrike))]
    phrase := s!"target creature gets {signedStat 3}/{signedStat 0} and gains {(Keyword.reach.merge Keyword.firstStrike).joinedAnd} until end of turn"
  },
  {
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.creaturesYouControlPump 2 1)
    phrase := SpellResolution.toPhrase (.creaturesYouControlPump 2 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .artifactOrEnchantment
    spellCastKind := .destroyArtifactOrLand
    resolution := Resolution.ofSpell (.sequence [.onPermanent .destroy, .gainLife 2])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent .destroy, .gainLife 2]) EffectTargetKind.artifactOrEnchantment.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent .becomeArtifactIndestructible)
    phrase := SpellResolution.toPhrase (.onPermanent .becomeArtifactIndestructible) EffectTargetKind.creature.noun
  },
  {
    resolution := .addAnyColor
    phrase := Resolution.toPhrase .addAnyColor EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureCardInYourGraveyard
    allowsZeroTargets := true
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.returnFromGyToHand, .amassGoblins 3])
    phrase := SpellResolution.toPhrase (.sequence [.returnFromGyToHand, .amassGoblins 3]) EffectTargetKind.creatureCardInYourGraveyard.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.counterThenRecruitIfMvAtMost 2)
    phrase := SpellResolution.toPhrase (.counterThenRecruitIfMvAtMost 2) EffectTargetKind.spell.noun
  },
  {
    targeting := .of .creatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.plusOneThenEachOtherIfFromGy)
    phrase := SpellResolution.toPhrase .plusOneThenEachOtherIfFromGy EffectTargetKind.creatureYouControl.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.drawIfFromGy 1 2)
    phrase := SpellResolution.toPhrase (.drawIfFromGy 1 2) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureYouControlThenOppCreature
    spellCastKind := .fight
    resolution := Resolution.ofSpell (.sequence [.plusOneOnFirstTarget 2, .fightAnnouncedCreatures])
    phrase := SpellResolution.toPhrase (.sequence [.plusOneOnFirstTarget 2, .fightAnnouncedCreatures]) EffectTargetKind.creatureYouControlThenOppCreature.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.searchLegendaryCreatureToHand)
    phrase := SpellResolution.toPhrase .searchLegendaryCreatureToHand EffectTargetKind.none.noun
  },
  {
    resolution := .addMana #[.colored .black, .colored .red]
    phrase := Resolution.toPhrase (.addMana #[.colored .black, .colored .red]) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.millThenPutInstantOrSorcery 4)
    phrase := SpellResolution.toPhrase (.millThenPutInstantOrSorcery 4) EffectTargetKind.none.noun
  },
  {
    targeting := .of .twoCreaturesOrLandsYouControl
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.exileThenReturnYouControl)
    phrase := SpellResolution.toPhrase .exileThenReturnYouControl EffectTargetKind.twoCreaturesOrLandsYouControl.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.sequence [.exileIfDiesThisTurn, .onPermanent (.dealDamage 3)])
    phrase := SpellResolution.toPhrase (.sequence [.exileIfDiesThisTurn, .onPermanent (.dealDamage 3)]) EffectTargetKind.creature.noun
  },
  {
    resolution := .createTokens .dwarf 1
    phrase := Resolution.toPhrase (.createTokens .dwarf 1) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.millThenPutLands 4 2)
    phrase := SpellResolution.toPhrase (.millThenPutLands 4 2) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.dealDamageToEachOppCreature 1)
    phrase := SpellResolution.toPhrase (.dealDamageToEachOppCreature 1) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.sequence [.dealDamageToEachNonDragon 3, .addFourManaDragonSpells])
    phrase := SpellResolution.toPhrase (.sequence [.dealDamageToEachNonDragon 3, .addFourManaDragonSpells]) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.millThenPutAllInstantsOrSorceries 6)
    phrase := SpellResolution.toPhrase (.millThenPutAllInstantsOrSorceries 6) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.exileTopPlayIfYouControlSubtype 2 "Wizard")
    phrase := SpellResolution.toPhrase (.exileTopPlayIfYouControlSubtype 2 "Wizard") EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createTokensX .dwarf)
    phrase := SpellResolution.toPhrase (.createTokensX .dwarf) EffectTargetKind.none.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.sequence [.returnTargetSpell, .playersCantCastIfGift])
    phrase := SpellResolution.toPhrase (.sequence [.returnTargetSpell, .playersCantCastIfGift]) EffectTargetKind.spell.noun
  },
  {
    targeting := .of .oppCreature
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.dealDamageToOppCreature 6))
    phrase := s!"this Saga deals {6} damage to target creature an opponent controls"
  },
  {
    targeting := .of .oppArtifact
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .destroyOppArtifact)
    phrase := "destroy target artifact an opponent controls"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.addMana (.colored .red)))
    phrase := s!"add {(ManaType.colored .red)}"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .searchBasicLandToHand)
    phrase := searchLibraryToHandPhrase "a basic land card"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .gainLandfallCreateElf)
    phrase := "this Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\""
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.elvesGetVigilance 1))
    phrase := s!"Elves you control get {signedStat 1}/+0 and gain vigilance until end of turn"
  },
  {
    targeting := .of .opponent
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .opponentDiscardsNonland)
    phrase := "target opponent reveals their hand. You choose a nonland card from it. That player discards that card"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.amassGoblins 1))
    phrase := s!"amass Goblins {1}"
  },
  {
    targeting := .of .opponent
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.opponentLosesYouGain 1))
    phrase := s!"target opponent loses {1} life and you gain {1} life"
  },
  {
    targeting := .of .twoCreaturesOrLandsYouControl
    resolution := .exileThenReturnNextEnd
    phrase := Resolution.toPhrase .exileThenReturnNextEnd EffectTargetKind.twoCreaturesOrLandsYouControl.noun
  },
  {
    resolution := .searchBasicBeholdSubtypeUntap "Elf"
    phrase := Resolution.toPhrase (.searchBasicBeholdSubtypeUntap "Elf") EffectTargetKind.none.noun
  },
  {
    targeting := .of .twoPlayers
    resolution := .twoPlayersDraw
    phrase := Resolution.toPhrase .twoPlayersDraw EffectTargetKind.twoPlayers.noun
  },
  {
    targeting := .of .opponent
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.exileTopXOppPlayForLife)
    phrase := SpellResolution.toPhrase .exileTopXOppPlayForLife EffectTargetKind.opponent.noun
  },
  {
    resolution := .discardLegendarySameNameDraw
    phrase := Resolution.toPhrase .discardLegendarySameNameDraw EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureYouControl
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .grantHexproofWhileRemains)
    phrase := "target creature you control gains hexproof for as long as this Saga remains on the battlefield"
  },
  {
    targeting := .of .creature
    allowsZeroTargets := true
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .preventDamageWhileRemains)
    phrase := "prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.draw 1))
    phrase := s!"draw {cardPhrase 1}"
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.riddlesInTheDark)
    phrase := SpellResolution.toPhrase .riddlesInTheDark EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.searchBasicPlainsExileGainLife 2 2))
    phrase := s!"search your library for up to {2} basic Plains cards, exile them, then shuffle. You gain {2} life"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .returnLinkedExileToHand)
    phrase := "put a card exiled with this Saga into its owner's hand"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .grantAttackPumpPerPlainsThisTurn)
    phrase := "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control"
  },
  {
    targeting := .of .creatureOrLandYouControl
    allowsZeroTargets := true
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .blinkUntilEndStep)
    phrase := "exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step"
  },
  {
    targeting := .of .playerOrCreature
    abilityCastKind := .creatureDamage
    resolution := .dealDamageToAny 4
    phrase := Resolution.toPhrase (.dealDamageToAny 4) EffectTargetKind.playerOrCreature.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.supperForSpiders)
    phrase := SpellResolution.toPhrase .supperForSpiders EffectTargetKind.none.noun
  },
  {
    targeting := .of (.filtered { noun := "target creature you own", types := #[.creature], ownedByYou := true })
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.eaglesAreComing)
    phrase := SpellResolution.toPhrase .eaglesAreComing (EffectTargetKind.filtered { noun := "target creature you own", types := #[.creature], ownedByYou := true }).noun
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .treasureThenDragonIfFour)
    phrase := "create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying"
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .recruit)
    phrase := "recruit"
  },
  {
    targeting := .of (.creatureCardInYourGraveyardMvAtMost 3)
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.returnCreatureFromGyMvAtMost 3))
    phrase := s!"return target creature card with mana value {3} or less from your graveyard to the battlefield"
  },
  {
    targeting := .of .creature
    allowsZeroTargets := true
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .plusOneUpToOne)
    phrase := "put a +1/+1 counter on up to one target creature"
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.lookAtTopLandsGainLife 20 8)
    phrase := SpellResolution.toPhrase (.lookAtTopLandsGainLife 20 8) EffectTargetKind.none.noun
  },
  {
    resolution := .sequence [.drawEqualToLastKnownPower, .discard 1]
    phrase := "Draw cards equal to the sacrificed creature's power, then discard a card"
  },
  {
    targeting := .of .player
    resolution := .mill 3
    phrase := Resolution.toPhrase (.mill 3) EffectTargetKind.player.noun
  },
  {
    targeting := .of (.creatureSpellPTAtMost 2)
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.counter)
    phrase := SpellResolution.toPhrase .counter (EffectTargetKind.creatureSpellPTAtMost 2).noun
  },
  {
    resolution := .returnFromGraveyardTapped
    phrase := Resolution.toPhrase .returnFromGraveyardTapped EffectTargetKind.none.noun
  },
  {
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.allCreaturesPump (-4) (-4))
    phrase := SpellResolution.toPhrase (.allCreaturesPump (-4) (-4)) EffectTargetKind.none.noun
  },
  {
    targeting := .of .player
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.exileGraveyardCreaturesGrantCast)
    phrase := SpellResolution.toPhrase .exileGraveyardCreaturesGrantCast EffectTargetKind.player.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .destroyCreature
    preferAsDefaultMode := true
    resolution := Resolution.ofSpell (.sequence [.onPermanent .destroy, .controllerOfTargetLosesLife 2])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent .destroy, .controllerOfTargetLosesLife 2]) EffectTargetKind.creature.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.sequence [.returnTargetSpell, .draw 1])
    phrase := SpellResolution.toPhrase (.sequence [.returnTargetSpell, .draw 1]) EffectTargetKind.spell.noun
  },
  {
    resolution := .scry 2
    phrase := Resolution.toPhrase (.scry 2) EffectTargetKind.none.noun
  },
  {
    targeting := .of .player .selfPlayer
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.targetPlayerDraw 2)
    phrase := SpellResolution.toPhrase (.targetPlayerDraw 2) EffectTargetKind.player.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.drawEqualToughnessThenPutCreatures)
    phrase := SpellResolution.toPhrase .drawEqualToughnessThenPutCreatures EffectTargetKind.none.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.addRedPerOppArtifacts)
    phrase := SpellResolution.toPhrase .addRedPerOppArtifacts EffectTargetKind.none.noun
  },
  {
    resolution := .createTokensX .treasure
    phrase := Resolution.toPhrase (.createTokensX .treasure) EffectTargetKind.none.noun
  },
  {
    resolution := .createTokens .food 1
    phrase := Resolution.toPhrase (.createTokens .food 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .anotherCreature
    resolution := .arwenShare
    phrase := Resolution.toPhrase .arwenShare EffectTargetKind.anotherCreature.noun
  },
  {
    targeting := .of .artifact
    allowsZeroTargets := true
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.gainControlOppArtifacts)
    phrase := SpellResolution.toPhrase .gainControlOppArtifacts EffectTargetKind.artifact.noun
  },
  {
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.damageOppCreaturesEqualOtherSpellsMv)
    phrase := SpellResolution.toPhrase .damageOppCreaturesEqualOtherSpellsMv EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    resolution := .grantCombatDamageCreateTreasure
    phrase := Resolution.toPhrase .grantCombatDamageCreateTreasure EffectTargetKind.creature.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.phaseOutKicker)
    phrase := SpellResolution.toPhrase .phaseOutKicker EffectTargetKind.creature.noun
  },
  {
    targeting := .of .creature
    resolution := .putShadowCounter
    phrase := Resolution.toPhrase .putShadowCounter EffectTargetKind.creature.noun
  },
  {
    resolution := .damageEachOpponent 1
    phrase := Resolution.toPhrase (.damageEachOpponent 1) EffectTargetKind.none.noun
  },
  {
    resolution := .chooseTwoDestroyRest
    phrase := Resolution.toPhrase .chooseTwoDestroyRest EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    resolution := .blackGateUnblockable
    phrase := Resolution.toPhrase .blackGateUnblockable EffectTargetKind.creature.noun
  },
  {
    resolution := .sequence [.onSource .burdenCounter, .drawEqualToBurdenCounters]
    phrase := "Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring"
  },
  {
    resolution := .teamGain Keyword.doubleStrike
    phrase := Resolution.toPhrase (.teamGain Keyword.doubleStrike) EffectTargetKind.none.noun
  },
  {
    resolution := .sequence [.onSource (.grantKeywords Keyword.indestructible), .onSource .tap]
    phrase := "Witch-king of Angmar gains indestructible until end of turn. Tap him"
  },
  (
    let t := (SharedTrigger.casting .plusOneEachOther).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .plusOneEachOther)
    }
  ),
  (
    let t := (SharedTrigger.watch .hulk).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .hulk)
    }
  ),
  {
    resolution := .plusOneOnEachOtherSubtype "Hero" 1
    phrase := Resolution.toPhrase (.plusOneOnEachOtherSubtype "Hero" 1) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createTokens .hero32vigilance 2)
    phrase := SpellResolution.toPhrase (.createTokens .hero32vigilance 2) EffectTargetKind.none.noun
  },
  {
    resolution := .sequence [.onSource (.plusOne 1), .onSource .indestructibleCounter]
    phrase := "Put a +1/+1 counter and an indestructible counter on this"
  },
  {
    targeting := .of .attackingOrBlockingCreature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.dealDamageTeamwork 2 4)
    phrase := SpellResolution.toPhrase (.dealDamageTeamwork 2 4) EffectTargetKind.attackingOrBlockingCreature.noun
  },
  (
    let t := (SharedTrigger.resource .plusOneOnHeroesCreateWall).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .plusOneOnHeroesCreateWall)
    }
  ),
  (
    let t := (SharedTrigger.step .harnessedFlicker).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.step .harnessedFlicker)
    }
  ),
  {
    targeting := .of (.creatureToughnessAtLeast 4)
    spellCastKind := .destroyCreature
    resolution := Resolution.ofSpell (.exileTarget)
    phrase := SpellResolution.toPhrase .exileTarget (EffectTargetKind.creatureToughnessAtLeast 4).noun
  },
  {
    targeting := .of (.enchantmentMvAtLeast 4)
    spellCastKind := .destroyArtifactOrLand
    resolution := Resolution.ofSpell (.exileTarget)
    phrase := SpellResolution.toPhrase .exileTarget (EffectTargetKind.enchantmentMvAtLeast 4).noun
  },
  (
    let listed := orJoin (#["Hero", "Equipment", "Vehicle"]).toList
    let art := indefinite ((#["Hero", "Equipment", "Vehicle"])[0]?.getD "")
    {
      resolution := .sequence [.onSource (.plusOne 2), .lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]]
      phrase := s!"Put two +1/+1 counters on this, then look at the top {7} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
    }
  ),
  (
    let t := (SharedTrigger.enter .returnGyPermanentThisTurn).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .returnGyPermanentThisTurn)
    }
  ),
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.mayPutHeroMvOrDraw 3)
    phrase := SpellResolution.toPhrase (.mayPutHeroMvOrDraw 3) EffectTargetKind.none.noun
  },
  {
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.plusOneOnEachYouControl)
    phrase := SpellResolution.toPhrase .plusOneOnEachYouControl EffectTargetKind.none.noun
  },
  {
    targeting := .of .playerThenCreature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [
      .targetPlayerInvestigates,
      .onCreatureAmongTargets (.grantKeywords Keyword.flying),
      .onCreatureAmongTargets .untap,
      .onCreatureAmongTargets (.pump 1 0)])
    phrase := SpellResolution.toPhrase (.sequence [
      .targetPlayerInvestigates,
      .onCreatureAmongTargets (.grantKeywords Keyword.flying),
      .onCreatureAmongTargets .untap,
      .onCreatureAmongTargets (.pump 1 0)]) EffectTargetKind.playerThenCreature.noun
  },
  {
    targeting := .of .anotherCreatureYouControl
    resolution := .sequence [.onPermanent (.pump 2 0), .onPermanent (.grantKeywords Keyword.hexproof)]
    phrase := s!"Another target creature you control gets {signedStat 2}/{signedStat 0} and gains {(Keyword.hexproof).joinedAnd} until end of turn"
  },
  (
    let t := (SharedTrigger.casting .tapCreatureOrLand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .tapCreatureOrLand)
    }
  ),
  {
    targeting := .of .creature
    resolution := .onPermanent .tap
    phrase := Resolution.toPhrase (.onPermanent .tap) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.enter .oppCreatesTheVoid).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .oppCreatesTheVoid)
    }
  ),
  (
    let t := (SharedTrigger.watch .equippedAttacksAloneUntapScry).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .equippedAttacksAloneUntapScry)
    }
  ),
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [.onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.lifelink.merge Keyword.indestructible))])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.lifelink.merge Keyword.indestructible))]) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.enter .plusOnesOrReturnArtEnch).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .plusOnesOrReturnArtEnch)
    }
  ),
  {
    targeting := .of .player
    resolution := Resolution.ofSpell (.targetPlayerCreatesTokens .leviathan65hexproof 1)
    phrase := SpellResolution.toPhrase (.targetPlayerCreatesTokens .leviathan65hexproof 1) EffectTargetKind.player.noun
  },
  {
    targeting := .of .nonland
    maxTargets := 2
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.returnOneOrTwoNonlands)
    phrase := SpellResolution.toPhrase .returnOneOrTwoNonlands EffectTargetKind.nonland.noun
  },
  (
    let t := (SharedTrigger.watch .merfolkAttackDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .merfolkAttackDraw)
    }
  ),
  {
    resolution := .drawX
    phrase := Resolution.toPhrase .drawX EffectTargetKind.none.noun
  },
  {
    targeting := .of (.stackAbilityFromCreatureSource)
    resolution := .copyControlledAbility true
    phrase := Resolution.toPhrase (.copyControlledAbility true) EffectTargetKind.stackAbilityFromCreatureSource.noun
  },
  (
    let t := (SharedTrigger.enter .createRedwing).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .createRedwing)
    }
  ),
  {
    resolution := .revealTopDrawIfArtifact
    phrase := Resolution.toPhrase .revealTopDrawIfArtifact EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .justiceBounce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .justiceBounce)
    }
  ),
  {
    resolution := .sequence [.onSource (.plusOne 1), .extraTurn]
    phrase := "Put a +1/+1 counter on this. Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  },
  (
    let t := (SharedTrigger.watch .youTargetDrawOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .youTargetDrawOnce)
    }
  ),
  (
    let t := (SharedTrigger.watch .tokensEnterMayDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .tokensEnterMayDraw)
    }
  ),
  (
    let t := (SharedTrigger.casting .drawPowerEqualHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .drawPowerEqualHand)
    }
  ),
  {
    resolution := Resolution.ofSpell (.copyNontokenCreaturesYouControl)
    phrase := SpellResolution.toPhrase .copyNontokenCreaturesYouControl EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.casting .merfolkFromBlue).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .merfolkFromBlue)
    }
  ),
  {
    resolution := .lookAtTopRevealArtifact 4
    phrase := Resolution.toPhrase (.lookAtTopRevealArtifact 4) EffectTargetKind.none.noun
  },
  {
    targeting := .of .oppCreatureThenUpToOneCreatureYouControl
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.ownerPutsLibraryThenConnive)
    phrase := SpellResolution.toPhrase .ownerPutsLibraryThenConnive EffectTargetKind.oppCreatureThenUpToOneCreatureYouControl.noun
  },
  {
    targeting := .of .spell
    spellCastKind := .counter
    resolution := Resolution.ofSpell (.counterUnlessPaysTeamwork 2 4)
    phrase := SpellResolution.toPhrase (.counterUnlessPaysTeamwork 2 4) EffectTargetKind.spell.noun
  },
  (
    let t := (SharedTrigger.casting .exileFlicker).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .exileFlicker)
    }
  ),
  (
    let t := (SharedTrigger.watch .combatDamageExileUntilNonland).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .combatDamageExileUntilNonland)
    }
  ),
  {
    targeting := .of .creature .own
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent (.pump (-4) (-4)))
    phrase := SpellResolution.toPhrase (.onPermanent (.pump (-4) (-4))) EffectTargetKind.creature.noun
  },
  {
    targeting := .of (.filtered { noun := s!"target {("Villain")} card in your graveyard", zone := .yourGraveyard, controller := .you, subtypes := #["Villain"] })
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.returnGySubtypeToHand "Villain")
    phrase := SpellResolution.toPhrase (.returnGySubtypeToHand "Villain") (EffectTargetKind.filtered { noun := s!"target {("Villain")} card in your graveyard", zone := .yourGraveyard, controller := .you, subtypes := #["Villain"] }).noun
  },
  {
    targeting := .of (.filtered { noun := s!"target {("Hero")} card in your graveyard", zone := .yourGraveyard, controller := .you, subtypes := #["Hero"] })
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.returnGySubtypeToHand "Hero")
    phrase := SpellResolution.toPhrase (.returnGySubtypeToHand "Hero") (EffectTargetKind.filtered { noun := s!"target {("Hero")} card in your graveyard", zone := .yourGraveyard, controller := .you, subtypes := #["Hero"] }).noun
  },
  (
    let t := (SharedTrigger.watch .attacksAloneDrain).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .attacksAloneDrain)
    }
  ),
  {
    resolution := .connive
    phrase := Resolution.toPhrase .connive EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.resource .discardExilePlay).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .discardExilePlay)
    }
  ),
  {
    resolution := .eachOppDiscardThenPlusOne
    phrase := Resolution.toPhrase .eachOppDiscardThenPlusOne EffectTargetKind.none.noun
  },
  {
    resolution := .addTwoAnyColorEquipment
    phrase := Resolution.toPhrase .addTwoAnyColorEquipment EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    resolution := .onPermanent (.pump (-4) (-4))
    phrase := Resolution.toPhrase (.onPermanent (.pump (-4) (-4))) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.resource .secondDrawPlusOneTarget).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .secondDrawPlusOneTarget)
    }
  ),
  {
    resolution := .createTokens .wall04defender 1
    phrase := Resolution.toPhrase (.createTokens .wall04defender 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .player
    resolution := .targetPlayerDraw 4
    phrase := Resolution.toPhrase (.targetPlayerDraw 4) EffectTargetKind.player.noun
  },
  {
    targeting := .of (.creatureCardInYourGraveyardMvAtMost 4)
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.returnGyCreatureMvAtMostOrAny 4)
    phrase := SpellResolution.toPhrase (.returnGyCreatureMvAtMostOrAny 4) (EffectTargetKind.creatureCardInYourGraveyardMvAtMost 4).noun
  },
  {
    targeting := .of .creatureCardInYourGraveyard
    allowsZeroTargets := true
    resolution := .sequence [.fra .returnFromGyToHand, .onSource (.plusOne 2)]
    phrase := s!"Return up to one target creature card from your graveyard to your hand. Put {plusOnePlusOneCountersPhrase 2} on this creature"
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent (.grantKeywords Keyword.deathtouch))
    phrase := SpellResolution.toPhrase (.onPermanent (.grantKeywords Keyword.deathtouch)) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.watch .villainPlusOneLifelink).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .villainPlusOneLifelink)
    }
  ),
  {
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.dealDamageToEachCreature 3)
    phrase := SpellResolution.toPhrase (.dealDamageToEachCreature 3) EffectTargetKind.none.noun
  },
  {
    targeting := .of .artifactOrLand
    spellCastKind := .destroyArtifactOrLand
    resolution := Resolution.ofSpell (.sequence [.onPermanent .destroy, .ownerMaySearchBasic])
    phrase := SpellResolution.toPhrase (.sequence [.onPermanent .destroy, .ownerMaySearchBasic]) EffectTargetKind.artifactOrLand.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.gainControlUntilEotOrNextIfVillain)
    phrase := SpellResolution.toPhrase .gainControlUntilEotOrNextIfVillain EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.casting .copyIfArtifactOrLand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .copyIfArtifactOrLand)
    }
  ),
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.exileHandDrawPlayUntilNext)
    phrase := SpellResolution.toPhrase .exileHandDrawPlayUntilNext EffectTargetKind.none.noun
  },
  {
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [.createTokens .villain21menace 1, .creaturesYouControlPump 1 0])
    phrase := SpellResolution.toPhrase (.sequence [.createTokens .villain21menace 1, .creaturesYouControlPump 1 0]) EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .villainOrArtifactDamage).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .villainOrArtifactDamage)
    }
  ),
  (
    let t := (SharedTrigger.enter (.dealDamageUpToOne 4)).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter (.dealDamageUpToOne 4))
    }
  ),
  {
    abilityCastKind := .creatureDamage
    resolution := .dealDamageToEachCreature 2
    phrase := Resolution.toPhrase (.dealDamageToEachCreature 2) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .creatureDamage
    resolution := Resolution.ofSpell (.copyThisSpellXTimesThenDamage 1)
    phrase := SpellResolution.toPhrase (.copyThisSpellXTimesThenDamage 1) EffectTargetKind.creature.noun
  },
  {
    resolution := .sequence [.onSource (.plusOne 1), .onSource .doubleStrikeCounter]
    phrase := "Put a +1/+1 counter and a double strike counter on this"
  },
  {
    resolution := .createTokens .treasure 1
    phrase := Resolution.toPhrase (.createTokens .treasure 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [
      .onPermanent (.grantKeywords Keyword.doubleStrike),
      .grantTrampleIfTeamwork])
    phrase := SpellResolution.toPhrase (.sequence [
      .onPermanent (.grantKeywords Keyword.doubleStrike),
      .grantTrampleIfTeamwork]) EffectTargetKind.creature.noun
  },
  (
    let t := (SharedTrigger.casting .damageEqualMv).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .damageEqualMv)
    }
  ),
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.maySacArtifactOrDiscardDraw 2)
    phrase := SpellResolution.toPhrase (.maySacArtifactOrDiscardDraw 2) EffectTargetKind.none.noun
  },
  {
    targeting := .of (.filtered { noun := "up to two target artifact, creature, enchantment, and/or land cards in your graveyard", zone := .yourGraveyard, types := #[.artifact, .creature, .enchantment, .land], controller := .you })
    allowsZeroTargets := true
    maxTargets := 2
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.returnUpToTwoGyModal)
    phrase := SpellResolution.toPhrase .returnUpToTwoGyModal (EffectTargetKind.filtered {
      noun := "up to two target artifact, creature, enchantment, and/or land cards in your graveyard"
      zone := .yourGraveyard
      types := #[.artifact, .creature, .enchantment, .land]
      controller := .you }).noun
  },
  {
    resolution := .addAnyColorEqualToSourcePower
    phrase := Resolution.toPhrase .addAnyColorEqualToSourcePower EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.revealTopPutCreatures 8)
    phrase := SpellResolution.toPhrase (.revealTopPutCreatures 8) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureYouControlThenOppCreature
    spellCastKind := .fight
    resolution := Resolution.ofSpell (.mutualFight)
    phrase := SpellResolution.toPhrase .mutualFight EffectTargetKind.creatureYouControlThenOppCreature.noun
  },
  {
    targeting := .of .creature
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.onPermanent (.plusOne 1))
    phrase := SpellResolution.toPhrase (.onPermanent (.plusOne 1)) EffectTargetKind.creature.noun
  },
  (
    let joined := if ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste).vigilance && ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste).indestructible && ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste).haste then "vigilance, indestructible, and haste" else ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste).joinedAnd
    {
      resolution := .sequence [.onSource (.plusOne 1), .onSource (.grantKeywords ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste))]
      phrase := s!"Put a +1/+1 counter on this. He gains {joined} until end of turn"
    }
  ),
  (
    let t := (SharedTrigger.resource .gainLifePlusOnes).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .gainLifePlusOnes)
    }
  ),
  (
    let t := (SharedTrigger.enter .createZabu).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .createZabu)
    }
  ),
  (
    let t := (SharedTrigger.resource .plusOneOnThisOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .plusOneOnThisOnce)
    }
  ),
  {
    resolution := .sequence [.onSource (.plusOne 1), .createTokens .hero32vigilance 1]
    phrase := s!"Put {plusOnePlusOneCountersPhrase 1} on this creature and {TokenKind.createPhrase .hero32vigilance 1}"
  },
  {
    targeting := .of .permanentOrPlayer
    resolution := .proliferateEachKind
    phrase := Resolution.toPhrase .proliferateEachKind EffectTargetKind.permanentOrPlayer.noun
  },
  {
    targeting := .of .creatureYouControlThenOppCreature
    spellCastKind := .fight
    resolution := Resolution.ofSpell (.creatureYouControlDealsTwicePower)
    phrase := SpellResolution.toPhrase .creatureYouControlDealsTwicePower EffectTargetKind.creatureYouControlThenOppCreature.noun
  },
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.millThenPutPermanentGainLife 2 2)
    phrase := SpellResolution.toPhrase (.millThenPutPermanentGainLife 2 2) EffectTargetKind.none.noun
  },
  {
    targeting := .of .upToOneCreatureThenPlayer
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.gainLifeSearchBasicPlusOne 2)
    phrase := SpellResolution.toPhrase (.gainLifeSearchBasicPlusOne 2) EffectTargetKind.upToOneCreatureThenPlayer.noun
  },
  {
    resolution := .millThenPutSubtypeOrEnchantment 4 "Hero"
    phrase := Resolution.toPhrase (.millThenPutSubtypeOrEnchantment 4 "Hero") EffectTargetKind.none.noun
  },
  {
    targeting := .of .artifactOrEnchantment
    allowsZeroTargets := true
    abilityCastKind := .destroyColorless
    resolution := .sequence [.onPermanent .destroy, .onSource (.plusOne 1)]
    phrase := "Destroy up to one target artifact or enchantment. Put a +1/+1 counter on this"
  },
  (
    let t := (SharedTrigger.watch .heroesDamagePlusTwo).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .heroesDamagePlusTwo)
    }
  ),
  (
    let t := (SharedTrigger.enterOrAttack .createSquirrel).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enterOrAttack .createSquirrel)
    }
  ),
  {
    targeting := .of .creatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.plusOneOnCreatureN 3)
    phrase := SpellResolution.toPhrase (.plusOneOnCreatureN 3) EffectTargetKind.creatureYouControl.noun
  },
  {
    targeting := .of .creatureYouControl
    spellCastKind := .pump
    resolution := Resolution.ofSpell (.sequence [.doublePowerAndToughness, .onPermanent (.grantKeywords Keyword.trample)])
    phrase := SpellResolution.toPhrase (.sequence [.doublePowerAndToughness, .onPermanent (.grantKeywords Keyword.trample)]) EffectTargetKind.creatureYouControl.noun
  },
  {
    targeting := .of .oppCreature
    allowsZeroTargets := true
    resolution := .sequence [.onSource (.plusOne 1), .fra .sourceFightsTarget]
    phrase := "Put a +1/+1 counter on this. This fights up to one target creature an opponent controls"
  },
  (
    let t := (SharedTrigger.thisAttack .mayPayPlusOne).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .mayPayPlusOne)
    }
  ),
  (
    let t := (SharedTrigger.resource .plusOneCreateInsectOnce).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.resource .plusOneCreateInsectOnce)
    }
  ),
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.mayDrawPerArtifactOppsDraw)
    phrase := SpellResolution.toPhrase .mayDrawPerArtifactOppsDraw EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.artifactSpellsCostLessThisTurn .artifact 1)
    phrase := SpellResolution.toPhrase (.artifactSpellsCostLessThisTurn .artifact 1) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.supertypeSpellsCostLessThisTurn .legendary 1)
    phrase := SpellResolution.toPhrase (.supertypeSpellsCostLessThisTurn .legendary 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .opponent
    resolution := Resolution.trigger (SharedTrigger.chapter 0 .dealXDamageToTargetOpponentGreatestArtifactMv)
    phrase := "This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control"
  },
  {
    resolution := .createTokensEqualRemovedPlusOnes .insect11green
    phrase := Resolution.toPhrase (.createTokensEqualRemovedPlusOnes .insect11green) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createTokens .villain21menace 2)
    phrase := SpellResolution.toPhrase (.createTokens .villain21menace 2) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.trigger (SharedTrigger.chapter 0 (.dealDamageToEachNonSubtypeAndOpponents 2 "Villain"))
    phrase := s!"This Saga deals {2} damage to each non-{("Villain")} creature and each opponent"
  },
  {
    resolution := Resolution.ofSpell (.createTokensPerSubtype .treasure "Villain")
    phrase := SpellResolution.toPhrase (.createTokensPerSubtype .treasure "Villain") EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .attacksAloneFirstStrikeMenace).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .attacksAloneFirstStrikeMenace)
    }
  ),
  {
    targeting := .of .nonland
    allowsZeroTargets := true
    spellCastKind := .destroyArtifactOrLand
    resolution := Resolution.ofSpell (.destroyUpToOneNonland)
    phrase := SpellResolution.toPhrase .destroyUpToOneNonland EffectTargetKind.nonland.noun
  },
  {
    spellCastKind := .burn
    resolution := Resolution.ofSpell (.eachOpponentLosesLife 2)
    phrase := SpellResolution.toPhrase (.eachOpponentLosesLife 2) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createGalactus)
    phrase := SpellResolution.toPhrase .createGalactus EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.thisAttack .ifArtifactEnteredDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .ifArtifactEnteredDraw)
    }
  ),
  (
    let t := (SharedTrigger.watch .anyPlayerSecondDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .anyPlayerSecondDraw)
    }
  ),
  (
    let t := (SharedTrigger.casting .villainToken).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .villainToken)
    }
  ),
  (
    let t := (SharedTrigger.thisAttack .blinkNontoken).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.thisAttack .blinkNontoken)
    }
  ),
  {
    targeting := .of (.stackAbilityFromArtifactSource)
    resolution := .copyControlledAbility false
    phrase := Resolution.toPhrase (.copyControlledAbility false) EffectTargetKind.stackAbilityFromArtifactSource.noun
  },
  (
    let t := (SharedTrigger.death .deathtouchOppSac).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.death .deathtouchOppSac)
    }
  ),
  (
    let t := (SharedTrigger.casting .targetsGainFlying).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.casting .targetsGainFlying)
    }
  ),
  {
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.sequence [.creaturesYouControlPump 1 1, .teamGain Keyword.vigilance])
    phrase := SpellResolution.toPhrase (.sequence [.creaturesYouControlPump 1 1, .teamGain Keyword.vigilance]) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creatureYouControlThenOppCreature
    allowsZeroTargets := true
    spellCastKind := .fight
    resolution := Resolution.ofSpell (.fightUpToOne)
    phrase := SpellResolution.toPhrase .fightUpToOne EffectTargetKind.creatureYouControlThenOppCreature.noun
  },
  {
    resolution := .sequence [.onSource (.plusOne 2), .chooseOddOrEvenDestroy]
    phrase := "Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  },
  (
    let t := (SharedTrigger.enter .createSturdyShieldAttach).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enter .createSturdyShieldAttach)
    }
  ),
  {
    resolution := Resolution.ofSpell (.searchLibraryOrGyArtifactCreatureX)
    phrase := SpellResolution.toPhrase .searchLibraryOrGyArtifactCreatureX EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.worldsWithinWorlds)
    phrase := SpellResolution.toPhrase .worldsWithinWorlds EffectTargetKind.none.noun
  },
  {
    resolution := .addMana #[.colorless, .colorless, .colorless]
    phrase := Resolution.toPhrase (.addMana #[.colorless, .colorless, .colorless]) EffectTargetKind.none.noun
  },
  (
    let t := (SharedTrigger.watch .equippedAttacksTap).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.watch .equippedAttacksTap)
    }
  ),
  (
    let t := (SharedTrigger.enterOrAttack .copyKeywords).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.enterOrAttack .copyKeywords)
    }
  ),
  {
    resolution := .lookAtTopRevealSubtype 3 "Hero"
    phrase := Resolution.toPhrase (.lookAtTopRevealSubtype 3 "Hero") EffectTargetKind.none.noun
  },
  {
    resolution := .addFourAnyCombination
    phrase := Resolution.toPhrase .addFourAnyCombination EffectTargetKind.none.noun
  },
  {
    resolution := .addAnyColorSpendOnlyArtifactSpell
    phrase := Resolution.toPhrase .addAnyColorSpendOnlyArtifactSpell EffectTargetKind.none.noun
  },
  {
    resolution := .createTokens .doombot 1
    phrase := Resolution.toPhrase (.createTokens .doombot 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of (.creatureYouControlSubtype "Villain")
    resolution := .targetSubtypeConnives "Villain"
    phrase := Resolution.toPhrase (.targetSubtypeConnives "Villain") (EffectTargetKind.creatureYouControlSubtype "Villain").noun
  },
  (
    let t := (SharedTrigger.scry 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.scry 2)
    }
  ),
  {
    spellCastKind := .draw
    resolution := Resolution.ofSpell (.sequence [.draw 1, .loseLife 0])
    phrase := SpellResolution.toPhrase (.sequence [.draw 1, .loseLife 0]) EffectTargetKind.none.noun
  },
  {
    resolution := .becomeSubtypeWithLandsPT "Elf"
    phrase := Resolution.toPhrase (.becomeSubtypeWithLandsPT "Elf") EffectTargetKind.none.noun
  },
  {
    targeting := .of (.creatureYouControl)
    resolution := .onPermanent (.plusOne 2)
    phrase := Resolution.toPhrase (.onPermanent (.plusOne 2)) EffectTargetKind.creatureYouControl.noun
  },
  (
    let t := (SharedTrigger.draw 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.draw 1)
    }
  ),
  (
    let t := (SharedTrigger.createTokens .treasure 1 true).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createTokens .treasure 1 true)
    }
  ),
  (
    let t := (SharedTrigger.dividedDamage 3 3).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.dividedDamage 3 3)
    }
  ),
  (
    let t := (SharedTrigger.opponentSacrificesCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.opponentSacrificesCreature)
    }
  ),
  (
    let t := (SharedTrigger.attachTo .legendaryCreatureYouControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.attachTo .legendaryCreatureYouControl)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOn .creatureYouControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOn .creatureYouControl)
    }
  ),
  (
    let t := (SharedTrigger.createTokens .wall 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createTokens .wall 1)
    }
  ),
  (
    let t := (SharedTrigger.connive).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.connive)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOnSource).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOnSource)
    }
  ),
  (
    let t := (SharedTrigger.drawAndLoseLife).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawAndLoseLife)
    }
  ),
  (
    let t := (SharedTrigger.gainLife 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.gainLife 2)
    }
  ),
  (
    let t := (SharedTrigger.pumpTarget .creature 4 4).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpTarget .creature 4 4)
    }
  ),
  (
    let t := (SharedTrigger.exileUntilLeaves .oppTappedCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileUntilLeaves .oppTappedCreature)
    }
  ),
  (
    let t := (SharedTrigger.youRecruit).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.youRecruit)
    }
  ),
  (
    let t := (SharedTrigger.damageEachOpponent 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageEachOpponent 2)
    }
  ),
  (
    let t := (SharedTrigger.exileTop).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileTop)
    }
  ),
  (
    let t := (SharedTrigger.mayDiscardDraw 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mayDiscardDraw 2)
    }
  ),
  (
    let t := (SharedTrigger.eachOpponentDiscards).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.eachOpponentDiscards)
    }
  ),
  (
    let t := (SharedTrigger.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0)).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.onPermanent .anotherCreatureYouControl (.pumpAndTrample 2 0))
    }
  ),
  (
    let t := (SharedTrigger.investigate).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.investigate)
    }
  ),
  (
    let t := (SharedTrigger.amassOrcs 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.amassOrcs 1)
    }
  ),
  (
    let t := (SharedTrigger.searchForest).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.searchForest)
    }
  ),
  (
    let t := (SharedTrigger.eachPlayerSacrificesCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.eachPlayerSacrificesCreature)
    }
  ),
  (
    let t := (SharedTrigger.loot).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.loot)
    }
  ),
  (
    let t := (SharedTrigger.plusOneEachYouControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneEachYouControl)
    }
  ),
  (
    let t := (SharedTrigger.pumpByLookedAt).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpByLookedAt)
    }
  ),
  (
    let t := (SharedTrigger.pumpAndUnblockable).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpAndUnblockable)
    }
  ),
  (
    let t := (SharedTrigger.mayDiscardHandDraw 4).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mayDiscardHandDraw 4)
    }
  ),
  (
    let t := (SharedTrigger.plusOneAndLifelink .creature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneAndLifelink .creature)
    }
  ),
  (
    let t := (SharedTrigger.pumpGreatestPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpGreatestPower)
    }
  ),
  (
    let t := (SharedTrigger.damageBlockers 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageBlockers 1)
    }
  ),
  (
    let t := (SharedTrigger.createThenAttach .treasure).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createThenAttach .treasure)
    }
  ),
  (
    let t := (SharedTrigger.drawPlusOneSource).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawPlusOneSource)
    }
  ),
  (
    let t := (SharedTrigger.ringTempts).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.ringTempts)
    }
  ),
  (
    let t := (SharedTrigger.setOtherBasePT).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.setOtherBasePT)
    }
  ),
  (
    let t := (SharedTrigger.returnElfGainLife).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.returnElfGainLife)
    }
  ),
  (
    let t := (SharedTrigger.damageFromLastKnownPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageFromLastKnownPower)
    }
  ),
  (
    let t := (SharedTrigger.exileOppGyCardOppsLoseLife 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileOppGyCardOppsLoseLife 2)
    }
  ),
  (
    let t := (SharedTrigger.creaturesYouControlPumpAndFirstStrike 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.creaturesYouControlPumpAndFirstStrike 1)
    }
  ),
  (
    let t := (SharedTrigger.mayPayGenericDraw 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mayPayGenericDraw 1)
    }
  ),
  (
    let t := (SharedTrigger.drawThenBottomIfNoLegendary).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawThenBottomIfNoLegendary)
    }
  ),
  (
    let t := (SharedTrigger.removeHopeDrawSac).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.removeHopeDrawSac)
    }
  ),
  (
    let t := (SharedTrigger.tapHumansDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.tapHumansDraw)
    }
  ),
  (
    let t := (SharedTrigger.untapPlusOneIfSubtype "Bear").timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.untapPlusOneIfSubtype "Bear")
    }
  ),
  (
    let t := (SharedTrigger.destroyOppArtifactsEnchantmentsGainLife).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.destroyOppArtifactsEnchantmentsGainLife)
    }
  ),
  (
    let t := (SharedTrigger.damageEqualSubtypeToEachOpponent "Dwarf").timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageEqualSubtypeToEachOpponent "Dwarf")
    }
  ),
  (
    let t := (SharedTrigger.damageEqualTreasures).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageEqualTreasures)
    }
  ),
  (
    let t := (SharedTrigger.loseLifeCreateTreasure).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.loseLifeCreateTreasure)
    }
  ),
  (
    let t := (SharedTrigger.dealDamageDestroyIfSubtype 1 "Dragon").timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.dealDamageDestroyIfSubtype 1 "Dragon")
    }
  ),
  (
    let t := (SharedTrigger.attachEquipmentToCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.attachEquipmentToCreature)
    }
  ),
  (
    let t := (SharedTrigger.defenderSacsLeastPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.defenderSacsLeastPower)
    }
  ),
  (
    let t := (SharedTrigger.returnOtherPlusOne).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.returnOtherPlusOne)
    }
  ),
  (
    let t := (SharedTrigger.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"]).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.lookAtTopRevealTypes 4 #["Dwarf", "Equipment"])
    }
  ),
  (
    let t := (SharedTrigger.createTappedTreasuresEqualOppArtifacts).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createTappedTreasuresEqualOppArtifacts)
    }
  ),
  (
    let t := (SharedTrigger.putNonlandMvAtMostFromGy 3).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.putNonlandMvAtMostFromGy 3)
    }
  ),
  (
    let t := (SharedTrigger.othersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1)).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.othersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1))
    }
  ),
  (
    let t := (SharedTrigger.wolfPlusOneOrTreasure).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.wolfPlusOneOrTreasure)
    }
  ),
  (
    let t := (SharedTrigger.trampleCounterBecomeBear).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.trampleCounterBecomeBear)
    }
  ),
  (
    let t := (SharedTrigger.millThenSubtypeToHand 4 "Elf").timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.millThenSubtypeToHand 4 "Elf")
    }
  ),
  (
    let t := (SharedTrigger.exileOppNonlandEachUntilLeaves).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileOppNonlandEachUntilLeaves)
    }
  ),
  (
    let t := (SharedTrigger.plusOneEqualLastKnownMv).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneEqualLastKnownMv)
    }
  ),
  (
    let t := (SharedTrigger.mountainQuestDragon).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mountainQuestDragon)
    }
  ),
  (
    let t := (SharedTrigger.treasuresPerChosenType).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.treasuresPerChosenType)
    }
  ),
  (
    let t := (SharedTrigger.revealUntilCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.revealUntilCreature)
    }
  ),
  (
    let t := (SharedTrigger.attackSacPlusOneEqualPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.attackSacPlusOneEqualPower)
    }
  ),
  (
    let t := (SharedTrigger.lootLandEntersTapped).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.lootLandEntersTapped)
    }
  ),
  (
    let t := (SharedTrigger.millThatManyLost).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.millThatManyLost)
    }
  ),
  (
    let t := (SharedTrigger.drawPerFatGraveyard).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawPerFatGraveyard)
    }
  ),
  (
    let t := (SharedTrigger.maySacDrawTreasure).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.maySacDrawTreasure)
    }
  ),
  (
    let t := (SharedTrigger.plusOneEachIfCityBlessing).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneEachIfCityBlessing)
    }
  ),
  (
    let t := (SharedTrigger.castInstantSorceryFromHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.castInstantSorceryFromHand)
    }
  ),
  (
    let t := (SharedTrigger.castInstantSorceryMvAtMost).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.castInstantSorceryMvAtMost)
    }
  ),
  (
    let t := (SharedTrigger.millThenCopy).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.millThenCopy)
    }
  ),
  (
    let t := (SharedTrigger.pumpTargetBySourcePower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpTargetBySourcePower)
    }
  ),
  (
    let t := (SharedTrigger.createAlienPerInvasion).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createAlienPerInvasion)
    }
  ),
  (
    let t := (SharedTrigger.mayPutArtifactAttachEquipment).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mayPutArtifactAttachEquipment)
    }
  ),
  (
    let t := (SharedTrigger.cascade).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.cascade)
    }
  ),
  (
    let t := (SharedTrigger.bolgMaySacrifice).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.bolgMaySacrifice)
    }
  ),
  (
    let t := (SharedTrigger.surveil 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.surveil 2)
    }
  ),
  (
    let t := (SharedTrigger.targetOpponentLosesLife 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.targetOpponentLosesLife 1)
    }
  ),
  (
    let t := (SharedTrigger.amassGoblinsEqualPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.amassGoblinsEqualPower)
    }
  ),
  (
    let t := (SharedTrigger.recruit).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.recruit)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOn .creature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOn .creature)
    }
  ),
  (
    let t := (SharedTrigger.attachTo .creatureYouControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.attachTo .creatureYouControl)
    }
  ),
  (
    let t := (SharedTrigger.conniveTarget .creatureYouControl).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.conniveTarget .creatureYouControl)
    }
  ),
  (
    let t := (SharedTrigger.exileUntilLeaves .oppNonland).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileUntilLeaves .oppNonland)
    }
  ),
  (
    let t := (SharedTrigger.exileUntilLeaves .defendingPlayerCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileUntilLeaves .defendingPlayerCreature)
    }
  ),
  (
    let t := (SharedTrigger.sourceGets 1 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.sourceGets 1 1)
    }
  ),
  (
    let t := (SharedTrigger.createTokens .treasure 1).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createTokens .treasure 1)
    }
  ),
  (
    let t := (SharedTrigger.searchBasicToHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.searchBasicToHand)
    }
  ),
  (
    let t := (SharedTrigger.exileTarget .anotherCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileTarget .anotherCreature)
    }
  ),
  (
    let t := (SharedTrigger.returnCreatureFromGyToHand).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.returnCreatureFromGyToHand)
    }
  ),
  (
    let t := (SharedTrigger.honeEachEquipment).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.honeEachEquipment)
    }
  ),
  (
    let t := (SharedTrigger.plusOneEachOtherGainLife).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneEachOtherGainLife)
    }
  ),
  (
    let t := (SharedTrigger.pumpTargetPerPlains).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpTargetPerPlains)
    }
  ),
  (
    let t := (SharedTrigger.drawThenDiscard 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawThenDiscard 2)
    }
  ),
  (
    let t := (SharedTrigger.pumpForEachOtherCreature).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.pumpForEachOtherCreature)
    }
  ),
  (
    let t := (SharedTrigger.grantFlying .attackingCreatureWithoutFlying).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.grantFlying .attackingCreatureWithoutFlying)
    }
  ),
  (
    let t := (SharedTrigger.returnLinkedExile).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.returnLinkedExile)
    }
  ),
  (
    let t := (SharedTrigger.createAxe).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createAxe)
    }
  ),
  (
    let t := (SharedTrigger.tapOppOrUntapYours).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.tapOppOrUntapYours)
    }
  ),
  (
    let t := (SharedTrigger.gainControlOppUntilEot).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.gainControlOppUntilEot)
    }
  ),
  (
    let t := (SharedTrigger.createAxeAttach).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createAxeAttach)
    }
  ),
  (
    let t := (SharedTrigger.payReturnFromGy).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.payReturnFromGy)
    }
  ),
  (
    let t := (SharedTrigger.plusOneVigilance 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneVigilance 2)
    }
  ),
  (
    let t := (SharedTrigger.mayDrawXDiscard2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.mayDrawXDiscard2)
    }
  ),
  (
    let t := (SharedTrigger.belladonnaTokenReward).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.belladonnaTokenReward)
    }
  ),
  (
    let t := (SharedTrigger.bolgDealSacrificedPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.bolgDealSacrificedPower)
    }
  ),
  (
    let t := (SharedTrigger.createSpiritsForEquipped).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createSpiritsForEquipped)
    }
  ),
  (
    let t := (SharedTrigger.createTreasuresEqualDamagedPlayerArtifacts).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createTreasuresEqualDamagedPlayerArtifacts)
    }
  ),
  (
    let t := (SharedTrigger.deal1ThenAmassOrcs).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.deal1ThenAmassOrcs)
    }
  ),
  (
    let t := (SharedTrigger.allianceMode).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.allianceMode)
    }
  ),
  (
    let t := (SharedTrigger.destroyOtherAmassControllerPower).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.destroyOtherAmassControllerPower)
    }
  ),
  (
    let t := (SharedTrigger.gollumMode).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.gollumMode)
    }
  ),
  (
    let t := (SharedTrigger.discardHandDrawDamageIfStory).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.discardHandDrawDamageIfStory)
    }
  ),
  (
    let t := (SharedTrigger.castFromGyArtifactInstantSorcery).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.castFromGyArtifactInstantSorcery)
    }
  ),
  (
    let t := (SharedTrigger.equippedAttackersGainDoubleStrike).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.equippedAttackersGainDoubleStrike)
    }
  ),
  (
    let t := (SharedTrigger.tapEnchantedRemoveCounters).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.tapEnchantedRemoveCounters)
    }
  ),
  (
    let t := (SharedTrigger.beginCombatIfDrawnTwoPump).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.beginCombatIfDrawnTwoPump)
    }
  ),
  (
    let t := (SharedTrigger.honePerOppAttach).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.honePerOppAttach)
    }
  ),
  (
    let t := (SharedTrigger.damageTargetOpponent 2).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.damageTargetOpponent 2)
    }
  ),
  (
    let t := (SharedTrigger.copySelfNonlegendary).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.copySelfNonlegendary)
    }
  ),
  (
    let t := (SharedTrigger.attachEquipmentThenFight).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.attachEquipmentThenFight)
    }
  ),
  (
    let t := (SharedTrigger.returnAsArtifact).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.returnAsArtifact)
    }
  ),
  (
    let t := (SharedTrigger.exileLandsThenReturnTapped).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileLandsThenReturnTapped)
    }
  ),
  (
    let t := (SharedTrigger.grimaImpulse).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.grimaImpulse)
    }
  ),
  (
    let t := (SharedTrigger.palantir).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.palantir)
    }
  ),
  (
    let t := (SharedTrigger.treasuresEqualLastKnown).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.treasuresEqualLastKnown)
    }
  ),
  (
    let t := (SharedTrigger.protectionEverything).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.protectionEverything)
    }
  ),
  (
    let t := (SharedTrigger.loseLifePerBurden).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.loseLifePerBurden)
    }
  ),
  (
    let t := (SharedTrigger.revealSaga).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.revealSaga)
    }
  ),
  (
    let t := (SharedTrigger.sacDamagersRingTempts).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.sacDamagersRingTempts)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOnSourceAndDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOnSourceAndDraw)
    }
  ),
  (
    let t := (SharedTrigger.lootAndPlan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.lootAndPlan)
    }
  ),
  (
    let t := (SharedTrigger.createVillainAndPlan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createVillainAndPlan)
    }
  ),
  (
    let t := (SharedTrigger.drawLoseLifeAndPlan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawLoseLifeAndPlan)
    }
  ),
  (
    let t := (SharedTrigger.treasureTappedAndPlan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.treasureTappedAndPlan)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOnTargetAndPlan).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOnTargetAndPlan)
    }
  ),
  (
    let t := (SharedTrigger.planFinishDrawPlusOneEach).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishDrawPlusOneEach)
    }
  ),
  (
    let t := (SharedTrigger.planFinishReturnInstants).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishReturnInstants)
    }
  ),
  (
    let t := (SharedTrigger.planFinishControlOpponent).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishControlOpponent)
    }
  ),
  (
    let t := (SharedTrigger.planFinishExileTopCast).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishExileTopCast)
    }
  ),
  (
    let t := (SharedTrigger.planFinishCreateRobots 3).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishCreateRobots 3)
    }
  ),
  (
    let t := (SharedTrigger.planFinishDividedDamage 7).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishDividedDamage 7)
    }
  ),
  (
    let t := (SharedTrigger.planFinishIndestructibleOnTarget).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.planFinishIndestructibleOnTarget)
    }
  ),
  (
    let t := (SharedTrigger.exileOtherCopyEnchanted).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileOtherCopyEnchanted)
    }
  ),
  (
    let t := (SharedTrigger.exileUntilNextEndStep).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.exileUntilNextEndStep)
    }
  ),
  (
    let t := (SharedTrigger.tapOrUntapNonland).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.tapOrUntapNonland)
    }
  ),
  (
    let t := (SharedTrigger.createFoodOrTreasure).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.createFoodOrTreasure)
    }
  ),
  (
    let t := (SharedTrigger.villainIfGyElseMill).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.villainIfGyElseMill)
    }
  ),
  (
    let t := (SharedTrigger.drawMayPutLandTapped).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawMayPutLandTapped)
    }
  ),
  (
    let t := (SharedTrigger.drawGainLifeIfAnotherHero).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.drawGainLifeIfAnotherHero)
    }
  ),
  (
    let t := (SharedTrigger.plusOneOrTwoIfAnotherHero).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.plusOneOrTwoIfAnotherHero)
    }
  ),
  (
    let t := (SharedTrigger.maySacArtifactOrDiscardDraw).timing
    {
      targeting := t.targeting
      allowsZeroTargets := t.allowsZeroTargets
      maxTargets := t.maxTargets
      dividedDamage := t.dividedDamage
      resolution := Resolution.ofSharedTrigger (.maySacArtifactOrDiscardDraw)
    }
  ),
  {
    targeting := .of .creature .own
    spellCastKind := .pump
    resolution := .sequence
      [.onPermanent (.pump 2 2), .onPermanent (.grantKeywords Keyword.flying)]
    phrase := s!"target creature gets {signedStat 2}/{signedStat 2} and gains {(Keyword.flying).joinedAnd} until end of turn"
  },
  {
    targeting := .of .creature
    resolution := .sequence [.onPermanent (.plusOne 1), .gainLife 1]
    phrase := Resolution.toPhrase (.sequence [.onPermanent (.plusOne 1), .gainLife 1]) EffectTargetKind.creature.noun
    spellCastKind := .pump
  },
  {
    targeting := .of .opponent
    resolution := .onPermanent (.dealDamage 1)
    phrase := s!"This deals {1} damage to target opponent"
    spellCastKind := .burn
  },
  {
    resolution := .millSelf 3
    phrase := Resolution.toPhrase (.millSelf 3) EffectTargetKind.none.noun
  },
  {
    resolution := .mayDiscardDraw 1
    phrase := Resolution.toPhrase (.mayDiscardDraw 1) EffectTargetKind.none.noun
    spellCastKind := .draw
  },
  {
    resolution := Resolution.ofSpell (.createTokens .heartwood 1)
    phrase := SpellResolution.toPhrase (.createTokens .heartwood 1) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createTokens .beast44trample 1)
    phrase := SpellResolution.toPhrase (.createTokens .beast44trample 1) EffectTargetKind.none.noun
  },
  {
    resolution := .sequence [.createTokens .cadet 1, .surveil 1]
    phrase := Resolution.toPhrase (.sequence [.createTokens .cadet 1, .surveil 1]) EffectTargetKind.none.noun
  },
  {
    resolution := .createTokensLifeGained .cadet
    phrase := Resolution.toPhrase (.createTokensLifeGained .cadet) EffectTargetKind.none.noun
  },
  {
    targeting := .of .creature
    resolution := .onPermanent (.setBasePT 0 0)
    phrase := Resolution.toPhrase (.onPermanent (.setBasePT 0 0)) EffectTargetKind.creature.noun
    spellCastKind := .creatureDamage
  },
  {
    targeting := .of .opponent
    resolution := .sequence [.oppSacrificesGreatestMv, .gainLife 2]
    phrase := s!"Target opponent sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control. You gain {2} life"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of .creatureOrPlaneswalker
    resolution := .damageThenEmpowerExcess 6
    phrase := Resolution.toPhrase (.damageThenEmpowerExcess 6) EffectTargetKind.creatureOrPlaneswalker.noun
    spellCastKind := .creatureDamage
  },
  {
    resolution := .jaceLoyaltyAtInstantSpeed
    phrase := Resolution.toPhrase .jaceLoyaltyAtInstantSpeed EffectTargetKind.none.noun
  },
  {
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.sequence [.creaturesYouControlPump 1 0, .teamGain Keyword.haste])
    phrase := SpellResolution.toPhrase (.sequence [.creaturesYouControlPump 1 0, .teamGain Keyword.haste]) EffectTargetKind.none.noun
  },
  {
    resolution := Resolution.ofSpell (.createTokens .pridemate 1)
    phrase := SpellResolution.toPhrase (.createTokens .pridemate 1) EffectTargetKind.none.noun
  },
  {
    targeting := .of .player
    resolution := .copyEachCreatureOfTargetPlayer
    phrase := Resolution.toPhrase .copyEachCreatureOfTargetPlayer EffectTargetKind.player.noun
    spellCastKind := .extraLand
  },
  {
    resolution := .copyNextInstantSorceryThisTurn
    phrase := Resolution.toPhrase .copyNextInstantSorceryThisTurn EffectTargetKind.none.noun
  },
  {
    resolution := .addMana #[.colored .red]
    phrase := Resolution.toPhrase (.addMana #[.colored .red]) EffectTargetKind.none.noun
  },
  {
    resolution := .exileTopMayCastElseDamageOpponents 2
    phrase := Resolution.toPhrase (.exileTopMayCastElseDamageOpponents 2) EffectTargetKind.none.noun
  },
  {
    resolution := .emblemCastSpellDamage 5
    phrase := Resolution.toPhrase (.emblemCastSpellDamage 5) EffectTargetKind.none.noun
  },
  {
    resolution := .addMana #[.colored .red, .colored .red]
    phrase := Resolution.toPhrase (.addMana #[.colored .red, .colored .red]) EffectTargetKind.none.noun
  },
  {
    targeting := .of (.creatureYouControlThenOppCreatureOrPlaneswalker)
    resolution := .firstDealsStatDamageToSecond false
    phrase := Resolution.toPhrase (.firstDealsStatDamageToSecond false) EffectTargetKind.creatureYouControlThenOppCreatureOrPlaneswalker.noun
    spellCastKind := .fight
  },
  {
    targeting := .of (.planeswalkerYouControlThenOppCreatureOrPlaneswalker)
    resolution := .firstDealsStatDamageToSecond true
    phrase := Resolution.toPhrase (.firstDealsStatDamageToSecond true) EffectTargetKind.planeswalkerYouControlThenOppCreatureOrPlaneswalker.noun
    spellCastKind := .fight
  },
  {
    targeting := .of (.filtered { noun := "target creature card with mana value 3 or less from your graveyard", zone := .yourGraveyard, types := #[.creature], mvAtMost := some 3 })
    resolution := .fra (.returnFromGyToBattlefield 1)
    phrase := "Return target creature card with mana value 3 or less from your graveyard to the battlefield with an additional +1/+1 counter on it"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .createTokens .cadet 3
    phrase := "Create three 2/2 colorless Wizard Soldier creature tokens named Cadet"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra .destroyAllNotChosenType
    phrase := "Choose a creature type. Destroy all creatures that aren't of the chosen type"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .fra .searchPlaneswalkerToTop
    phrase := "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .fra (.plusOneOnEachTarget 1)
    phrase := "Put a +1/+1 counter on each of one or two target creatures"
    spellCastKind := .pump
    maxTargets := 2
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .fra .destroyDrawIfNotAttacking
    phrase := "Destroy target creature. If it wasn't attacking, its controller draws a card"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's green or blue"
      colors := #[.green, .blue] })
    resolution := .sequence [.fra .exile, .surveil 1]
    phrase := "Exile target creature or planeswalker that's green or blue. Surveil 1"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .fra .returnAllNonlandPermanentsFromGy
    phrase := "Return all nonland permanent cards from your graveyard to the battlefield"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { TargetFilter.creature with
      noun := "target creature with toughness 4 or greater", toughnessAtLeast := some 4 })
    resolution := .sequence [.fra .destroy, .gainLife 1]
    phrase := "Destroy target creature with toughness 4 or greater. You gain 1 life"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.draw 1, .gainLife 2]
    phrase := s!"You draw {cardPhrase 1} and gain {2} life"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker with mana value 3 or greater"
      mvAtLeast := some 3 })
    resolution := .sequence [.fra .destroy, .surveil 1]
    phrase := "Destroy target creature or planeswalker with mana value 3 or greater. Surveil 1"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered TargetFilter.spell)
    resolution := .fra .counter
    phrase := "Counter target spell"
    spellCastKind := .counter
  },
  {
    targeting := .of (.player)
    resolution := .fra .drawMilledThisTurn
    phrase := "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { noun := "target creature or legendary spell", zone := .stack, types := #[.creature], orLegendary := true })
    resolution := .fra (.counterUnlessPays 3)
    phrase := "Counter target creature or legendary spell unless its controller pays {3}"
    spellCastKind := .counter
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .onPermanent (.pump (-5) 0)
    phrase := s!"Target creature gets {signedStat (-5)}/{signedStat 0} until end of turn"
    spellCastKind := .pump
  },
  {
    targeting := .of (.filtered { noun := "target white or black spell", zone := .stack, colors := #[.white, .black] })
    resolution := .fra .counter
    phrase := "Counter target white or black spell"
    spellCastKind := .counter
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.draw 2, .fra .sphinxsApproach]
    phrase := "Draw two cards. Then you may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .fra .bounce
    phrase := "Return target creature to its owner's hand"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered { TargetFilter.creature with
      noun := "target creature an opponent controls with mana value 3 or less"
      controller := .opponent, mvAtMost := some 3 })
    resolution := .sequence [.fra .bounce, .surveil 1]
    phrase := "Return target creature an opponent controls with mana value 3 or less to its owner's hand. Surveil 1"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .fra (.eachPlayerMayWheel 7)
    phrase := "Each player may discard their hand and draw seven cards"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.draw 2, .fra (.damageEachPlayer 2)]
    phrase := "Draw two cards. This spell deals 2 damage to each player"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .sequence [.fra .exile, .fra (.damageEachOpponent 1), .gainLife 1]
    phrase := "Exile target creature or planeswalker. This spell deals 1 damage to each opponent and you gain 1 life"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .fra .extrapolate
    phrase := "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra .exileAllCreaturesEmpower
    phrase := "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered { noun := "target creature or planeswalker card with mana value 6 or less from your graveyard", zone := .yourGraveyard, types := #[.creature, .planeswalker], mvAtMost := some 6 })
    resolution := .fra (.returnFromGyToBattlefield 0)
    phrase := "Return target creature or planeswalker card with mana value 6 or less from your graveyard to the battlefield"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra .drawGreatestPowerLoseLife
    phrase := "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"
    spellCastKind := .draw
  },
  {
    spellCastKind := .massPump
    resolution := Resolution.ofSpell (.allCreaturesPump (-3) (-3))
    phrase := SpellResolution.toPhrase (.allCreaturesPump (-3) (-3)) EffectTargetKind.none.noun
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .fra .destroy
    phrase := "Destroy target creature or planeswalker"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.opponent)
    resolution := .fra (.revealHandDiscardNonland true)
    phrase := "Target opponent reveals their hand. You choose a nonland permanent card from it. That player discards that card"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { TargetFilter.creatureOrPlaneswalker with
      noun := "target creature or planeswalker that's blue or red"
      colors := #[.blue, .red] })
    resolution := .sequence [.fra .destroy, .gainLife 1]
    phrase := "Destroy target creature or planeswalker that's blue or red. You gain 1 life"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .sequence [.fra (.loseLife 2), .fra .destroy]
    phrase := "You lose 2 life. Destroy target creature or planeswalker"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.fra (.loseLife 2), .empowerJace 6]
    phrase := "You lose 2 life. Empower Jace 6"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.teamGain Keyword.firstStrike, .draw 1]
    phrase := "Creatures you control gain first strike until end of turn.\nDraw a card"
    spellCastKind := .pump
  },
  {
    targeting := .of (.multi #[TargetFilter.oppCreatureOrPlaneswalker,
      { TargetFilter.creatureYouControl with noun := "up to one target creature you control" }] #[1])
    resolution := .sequence [.fra (.damageSourceAt 0 6), .fra (.plusOneAt 1 1)]
    phrase := "This spell deals 6 damage to target creature or planeswalker an opponent controls. Put a +1/+1 counter on up to one target creature you control"
    spellCastKind := .creatureDamage
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.createTokens .cadet 1, .fra .plusOneOnWizardTokensExceptRecent]
    phrase := "Create a 2/2 colorless Wizard Soldier creature token named Cadet, then put a +1/+1 counter on each other Wizard token you control"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { TargetFilter.creatureOrPlaneswalker with noun := "target black or green creature or planeswalker", colors := #[.black, .green] })
    resolution := .fra (.damageExileIfDies 5)
    phrase := "This spell deals 5 damage to target black or green creature or planeswalker. If that permanent would die this turn, exile it instead"
    spellCastKind := .creatureDamage
  },
  {
    targeting := .of (.none)
    resolution := .fra (.damageEachOppCreatureAndPlaneswalker 1)
    phrase := "This spell deals 1 damage to each creature and planeswalker your opponents control"
    spellCastKind := .creatureDamage
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .onPermanent (.dealDamage 5)
    phrase := s!"This spell deals {5} damage to target creature or planeswalker"
    spellCastKind := .creatureDamage
  },
  {
    targeting := .of (.none)
    resolution := .fra .mountainsAddExtraRed
    phrase := "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra .searchLandToGraveyard
    phrase := "Search your library for a land card, put it into your graveyard, then shuffle"
    spellCastKind := .draw
  },
  {
    targeting := .of (.multi #[{ TargetFilter.oppCreatureOrPlaneswalker with
      noun := "target creature or planeswalker an opponent controls that's red or white"
      colors := #[.red, .white] }, TargetFilter.creatureYouControl] #[])
    resolution := .sequence [.fra (.loseAbilitiesAt 0), .fra (.powerDamageFromTo 1 0)]
    phrase := "Target creature or planeswalker an opponent controls that's red or white loses all abilities until end of turn. Target creature you control deals damage equal to its power to that permanent"
    spellCastKind := .fight
  },
  {
    targeting := .of (.filtered { noun := "target permanent card from your graveyard", zone := .yourGraveyard, permanentCard := true })
    resolution := .sequence [.fra .returnFromGyToHand, .gainLife 4]
    phrase := "Return target permanent card from your graveyard to your hand. You gain 4 life"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra (.millMayPutPermanentGainLife 4 1)
    phrase := "Mill four cards. You may put a permanent card from among them into your hand. You gain 1 life"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .sequence [.onPermanent (.pump 2 2), .onPermanent (.grantKeywords Keyword.reach),
      .onPermanent .untap]
    phrase := "Target creature gets +2/+2 and gains reach until end of turn. Untap it"
    spellCastKind := .pump
  },
  {
    targeting := .of (.none)
    resolution := .creaturesYouControlPump 2 0
    phrase := s!"Creatures you control get {signedStat 2}/{signedStat 0} until end of turn"
    spellCastKind := .pump
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .sequence [.onPermanent (.pump 2 0), .onPermanent (.grantKeywords Keyword.firstStrike),
      .onPermanent (.plusOne 1)]
    phrase := "Target creature gets +2/+0 and gains first strike until end of turn. Put a +1/+1 counter on it"
    spellCastKind := .pump
  },
  {
    targeting := .of (.filtered { noun := "target nonland permanent", nonland := true })
    resolution := .fra .clashOfElements
    phrase := "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this spell deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.none)
    resolution := .fra .entrustTheSpark
    phrase := "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.draw 1, .empowerJace 2]
    phrase := s!"Draw {cardPhrase 1}. Empower Jace {2}"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered { noun := "target spell or creature", zone := .spellOrCreature })
    resolution := .fra .bounce
    phrase := "Return target spell or creature to its owner's hand"
    spellCastKind := .counter
  },
  {
    targeting := .of (.filtered { TargetFilter.creature with noun := "target creature with flying", withFlying := true })
    resolution := .onPermanent (.dealDamage 6)
    phrase := s!"This spell deals {6} damage to target creature with flying"
    spellCastKind := .destroyFlying
  },
  (
    let noun := "target creature"
    {
      targeting := .of (.filtered { TargetFilter.creature with noun })
      resolution := .sequence [.onPermanent (.plusOne 2), .onPermanent (.grantKeywords Keyword.trample)]
      phrase := s!"Put {plusOnePlusOneCountersPhrase 2} on {noun}. It gains {(Keyword.trample).joinedAnd} until end of turn"
      spellCastKind := .pump
    }
  ),
  {
    targeting := .of (.none)
    resolution := .addMana (Array.replicate 3 .colorless)
    phrase := s!"Add {String.join (List.replicate 3 "{C}")}"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.createTokens .cadet 2, .fra .plusOnePerThreeGraveyardOnRecentIfFromGy]
    phrase := "Create two 2/2 colorless Wizard Soldier creature tokens named Cadet. If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .onPermanent (.grantKeywords (Keyword.firstStrike.merge Keyword.deathtouch))
    phrase := s!"Target creature gains {("first strike and deathtouch")} until end of turn"
    spellCastKind := .pump
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.createTokens .cadet 1, .fra .grantHasteToRecentTokens]
    phrase := "Create a 2/2 colorless Wizard Soldier creature token named Cadet. It gains haste until end of turn"
    spellCastKind := .draw
  },
  {
    targeting := .of (.opponent)
    resolution := .sequence [.fra (.damageAny 2), .fra (.revealHandDiscardNonland false)]
    phrase := "This spell deals 2 damage to target opponent. That player reveals their hand. You choose a nonland card from it. They discard that card"
    spellCastKind := .burn
  },
  {
    targeting := .of (.filtered { noun := "target noncreature spell", zone := .stack, noncreature := true })
    resolution := .fra (.counterUnlessPays 2)
    phrase := "Counter target noncreature spell unless its controller pays {2}"
    spellCastKind := .counter
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.millSelf 3, .draw 1]
    phrase := s!"Mill {englishNumber 3} cards, then draw {cardPhrase 1}"
    spellCastKind := .draw
  },
  {
    targeting := .of (.none)
    resolution := .fra .drawOneOrTwoIfNotFromHand
    phrase := "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
    spellCastKind := .draw
  },
  {
    targeting := .of (.multi #[{ noun := "target nonland permanent", nonland := true },
      { noun := "target player", zone := .player }] #[])
    resolution := .sequence [.fra (.destroyAt 0), .fra (.plusOneOnCreaturesOfPlayerAt 1)]
    phrase := "Destroy target nonland permanent. Put a +1/+1 counter on each creature target player controls"
    spellCastKind := .destroyCreature
  },
  {
    targeting := .of (.filtered { noun := "target permanent you control", controller := .you })
    resolution := .onPermanent (.grantKeywords (Keyword.hexproof.merge Keyword.indestructible))
    phrase := s!"Target permanent you control gains {(Keyword.hexproof.merge Keyword.indestructible).joinedAnd} until end of turn"
    spellCastKind := .pump
  },
  {
    targeting := .of (.none)
    resolution := .sequence [.draw 1, .gainLife 3]
    phrase := s!"You draw {cardPhrase 1} and gain {3} life"
    spellCastKind := .draw
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .fra (.exileReturnBrieflyIfMvAtMost 3)
    phrase := "Exile target creature or planeswalker. If that permanent's mana value was 3 or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"
    spellCastKind := .destroyCreature
  },
  (
    let noun := "up to one target creature"
    {
      targeting := .of (.filtered { TargetFilter.creature with noun })
      resolution := .sequence [.onPermanent (.plusOne 1), .onPermanent (.grantKeywords Keyword.vigilance)]
      phrase := s!"Put {plusOnePlusOneCountersPhrase 1} on {noun}. It gains {(Keyword.vigilance).joinedAnd} until end of turn"
      spellCastKind := .pump
      allowsZeroTargets := true
    }
  ),
  {
    targeting := .of (.filtered { noun := "target legendary card from your graveyard", zone := .yourGraveyard, legendary := true })
    resolution := .fra .returnFromGyToHand
    phrase := "Return target legendary card from your graveyard to your hand"
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .sequence [.onPermanent (.plusOne 1),
      .onPermanent (.grantKeywords (Keyword.vigilance.merge Keyword.indestructible))]
    phrase := "Put a +1/+1 counter on target creature. It gains vigilance and indestructible until end of turn"
    spellCastKind := .pump
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .onPermanent .tap
    phrase := "Tap target creature"
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .onPermanent .untap
    phrase := "Untap target creature"
  },
  {
    targeting := .of (.filtered { noun := "target noncreature, nonland permanent", noncreature := true, nonland := true })
    resolution := .fra .destroy
    phrase := "Destroy target noncreature, nonland permanent"
  },
  {
    targeting := .of (.none)
    resolution := .gainLife 4
    phrase := s!"You gain {4} life"
  },
  {
    targeting := .of (.filtered TargetFilter.creature)
    resolution := .fra .minusPowerPerGraveyard
    phrase := "Target creature gets -X/-0 until end of turn, where X is the number of cards in your graveyard"
  },
  {
    targeting := .of (.none)
    resolution := .surveil 2
    phrase := s!"Surveil {2}"
  },
  {
    targeting := .of (.filtered TargetFilter.creatureOrPlaneswalker)
    resolution := .onPermanent (.dealDamage 4)
    phrase := s!"This creature deals {4} damage to target creature or planeswalker"
  },
  {
    targeting := .of (.none)
    resolution := .createTokens .cadet 1
    phrase := "Create a 2/2 colorless Wizard Soldier creature token named Cadet"
  },
  {
    targeting := .of (.none)
    resolution := .draw 1
    phrase := "Draw a card"
  },
  FraCandidates.ab (.createTokens .illusion11blue 1) "Create a 1/1 blue Illusion creature token",
  FraCandidates.ab (.fra .bounceEachTarget)
      "For each opponent, return up to one target artifact or creature that player controls to its owner's hand"
      (.filtered { noun := "up to one target artifact or creature that player controls",
                   types := #[.artifact, .creature], controller := .eachOpponent })
      (allowsZeroTargets := true),
  FraCandidates.ab (.sequence [.draw 3, .fra .plusOnesEqualToHandOnEachCreature])
      "Draw three cards. Then put X +1/+1 counters on each creature you control, where X is the number of cards in your hand",
  FraCandidates.ab (.fra .surveilReturnNoncreatureNonland)
      "Surveil 1. If you put a noncreature, nonland card into your graveyard this way, put that card into your hand",
  FraCandidates.ab (.fra .addBlueNoncreatureOnly) "Add {U}. Spend this mana only to cast a noncreature spell",
  FraCandidates.ab (.fra .tapAndStunX) "Tap target artifact or creature. Put X stun counters on it"
      (.filtered { noun := "target artifact or creature", types := #[.artifact, .creature] }),
  FraCandidates.ab (.fra .emblemDrawOnCast) "You get an emblem with \"Whenever you cast a spell, draw a card.\"",
  FraCandidates.ab (.fra .empowerJacePerIsland) "Empower Jace X, where X is the number of Islands you control",
  FraCandidates.ab (.fra .attackersGetMinusFiveUntilYourTurn)
      "Until your next turn, whenever a creature attacks you or a planeswalker you control, it gets -5/-0 until end of turn",
  FraCandidates.ab (.fra .exileOpponentLibrariesButBottom) "Exile all but the bottom card of each opponent's library",
  FraCandidates.ab (.fra .minusFourMinusOneUntilYourTurn) "Up to one target creature gets -4/-1 until your next turn"
      (.filtered { TargetFilter.creature with noun := "up to one target creature" }) (allowsZeroTargets := true),
  FraCandidates.ab (.fra .eachPlayerSacrificesThenBeast)
      "Each player sacrifices a creature of their choice. If you sacrificed a creature this way, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab (.fra .eachOpponentDiscardsTwoDrawPerShort)
      "Each opponent discards two cards. For each opponent who didn't discard two nonland cards this way, you draw a card",
  FraCandidates.ab (.sequence [.fra .discardHand, .fra .drawPerCreatureYouControl]) "Discard your hand, then draw a card for each creature you control",
  FraCandidates.ab (.fra (.damageEachCreatureExceptYourTokens 4)) "This deals 4 damage to each creature except for tokens you control",
  FraCandidates.ab (.fra .emblemCreaturesGetTwoTwo) "You get an emblem with \"Creatures you control get +2/+2.\"",
  FraCandidates.ab (.fra .untapTargets) "Untap up to two target lands"
      (.filtered { noun := "up to two target lands", types := #[.land] }) (allowsZeroTargets := true) (maxTargets := 2),
  FraCandidates.ab (.fra .attackersGetTwoTwoTrampleUntilYourTurn)
      "Until your next turn, whenever one or more creatures attack one of your opponents, those creatures get +2/+2 and gain trample until end of turn",
  FraCandidates.ab (.sequence [.fra (.damageEachOpponent 1), .gainLife 1])
      "This planeswalker deals 1 damage to each opponent and you gain 1 life",
  FraCandidates.ab (.fra .plusOnePerLand) "Put a +1/+1 counter on target creature for each land you control"
      (.filtered TargetFilter.creature),
  FraCandidates.ab (.fra .maySacrificeCreatureForBeast)
      "You may sacrifice a creature. If you do, create a 4/4 green Beast creature token with trample",
  FraCandidates.ab (.fra (.damageUpToOneAndPlayer 2))
      "This planeswalker deals 2 damage to up to one target creature or planeswalker and 2 damage to target player"
      (.multi #[{ TargetFilter.creatureOrPlaneswalker with noun := "up to one target creature or planeswalker" },
        { noun := "target player", zone := .player }] #[0]),
  FraCandidates.ab (.createTokens .leviathan88hexproof 1) "Create an 8/8 blue Leviathan creature token with hexproof"
]

def staticAbilities : Thunk (Array StaticAbility) := Thunk.mk fun _ => #[
  .otherCreaturesHaveTrample #["Orc", "Goblin"],
  .enchantedCreatureGets 3 3,
  .otherCreaturesGet #["Elf"] 1 1,
  .equippedCreatureGets 2 0,
  .powerToughnessEqualLandsYouControl,
  .cantBlockUnlessYouControl #["Goblin", "Orc"],
  .cantBlockUnlessYouControl #[],
  .cantBeBlockedByTokens,
  .powerEqualCreaturesYouControl,
  .otherCreaturesGet #[] 1 1,
  .cantAttackUnlessYouControlNOther 2 "Wolf",
  .equippedCreatureGetsAndHas 1 0 Keyword.menace,
  .enchantedCreatureGetsAndHas 2 2 Keyword.flying,
  .equippedCreatureGetsAndWard 2 2 1,
  .creaturesYouControlWithPlusOneHaveMenace,
  .creaturesYouControlGet 1 1,
  .hasteIfYouControlOtherSubtype "Goblin",
  .equippedCreatureGetsAndHas 1 1 Keyword.reach,
  .getsAndHasIfEnduringStory 1 0 Keyword.vigilance,
  .getsAndHasIfEnduringStory 1 0 Keyword.haste,
  .doesntUntapUnlessEnduringStory,
  .creaturesYouControlGetIfEnduringStory 1 1,
  .artifactsAndCreaturesHaveWardIfEnduringStory 1,
  .creaturesCantAttackYouUnlessPayIfEnduringStory 1,
  .thresholdGets 1 1,
  .cantBeBlockedByPowerAtMost 2,
  .equipAbilitiesTargetingThisCostLess 2,
  .equippedCreatureHasKeywordsAndCantBeBlocked Keyword.hexproof,
  .firstEquipFreeIfEnduringStory,
  .lifelinkIfYouControlOtherSubtype "Dwarf",
  .instantSorceryCostReductionEqualEquippedPower,
  .chosenTypeCreaturesGet 2 2,
  .extraTriggerIfEnduringStorySubtype "Dwarf",
  .enchantedLosesAbilitiesDoesntUntap,
  .exileOppDeathCreateWolf,
  .powerPerFatGraveyard 2,
  .equippedCreatureGetsAndHas 2 2 Keyword.trample,
  .copyActivatedFromGySubtype "Elf",
  .equippedTriggersAgain,
  .equippedCreatureHasKeywords Keyword.prowess,
  .enchantedIsOnlySubtypeCantAttackOrBlock "Spirit",
  .powerEqualCardsInHand,
  .cantBeBlockedExceptBy 3,
  .armiesYouControlHaveTrample,
  .legendaryCreaturesGetAndWard 2 1 1,
  .nonlegendaryCreaturesGet 1 1,
  .equippedCreatureHasKeywords Keyword.indestructible,
  .equippedCreaturesHaveKeywordsDuringYourTurn (Keyword.firstStrike.merge Keyword.vigilance),
  .otherSubtypeHaveTapAddOneOf #["Elf"] #[.colored .green, .colored .blue],
  .otherSubtypeGetPowerPerArtifactToken "Dwarf",
  .cantBeBlockedByPowerAtLeast 3,
  .equippedHexproofUnblockableDuringYourTurn,
  .extraTriggerAnotherYouControl #["Wolf"] true,
  .equippedFirstStrikePlusPerInstantSorcery,
  .wardDiscardEnchantmentInstantOrSorcery,
  .wardSacrificeLegendary,
  .equippedGetsTrampleAndCombatTreasures 1 1,
  StaticAbility.opponentsCantCastOnYourTurn,
  StaticAbility.preventAllDamageToThis,
  StaticAbility.creaturesYouControlOfSubtypeGet "Hero" 2 2,
  StaticAbility.youAndOtherSubtypeHaveHexproofIfShield "Hero",
  StaticAbility.flashIfOpponentCastThisTurn,
  StaticAbility.attackingTokensHave Keyword.firstStrike,
  StaticAbility.enchantedCreatureGetsHasAndTypes 2 2
        (Keyword.firstStrike.merge Keyword.vigilance) #["legendary", "Soldier"],
  StaticAbility.otherCreaturesGet #["Merfolk"] 1 1,
  StaticAbility.equippedCreatureGetsHasAndWard 1 1 Keyword.flying 1,
  StaticAbility.enchantedLosesAbilitiesCantUntap,
  .improvise,
  .noncreatureSpellsHaveImprovise,
  StaticAbility.hexproofIfPlusOneThisTurn,
  StaticAbility.extraDrawOnConnive,
  .noMaximumHandSize,
  .powerEqualSubtypeYouControl "Merfolk",
  StaticAbility.enchantedCreatureHasWard 2,
  .typeSpellsCostLess .artifact 1,
  .supertypeSpellsCostLess .legendary 1,
  StaticAbility.cantBeBlockedIfPowerAtMost 1,
  StaticAbility.boast,
  StaticAbility.subtypeSpellsCostLess "Villain" 1,
  StaticAbility.indestructibleIfArtifactCreatureOrPlan,
  StaticAbility.sneak (ManaCost.ofGenericAndColors 1 [.black, .black]),
  StaticAbility.opponentsCreaturesGet (-1) (-1),
  StaticAbility.noncombatDamagePlusSourcePower,
  StaticAbility.equippedDealsDoubleDamage,
  StaticAbility.mayBeginOnBattlefield,
  StaticAbility.instantSorceryCostLessEqualPower,
  StaticAbility.enchantedCreatureGetsAndHas 1 0 Keyword.haste,
  StaticAbility.extraPowerUpActivation,
  StaticAbility.extraCounterOnPermanents,
  StaticAbility.mayPlayLandsFromGraveyard,
  StaticAbility.activateCreaturesAsThoughHaste,
  StaticAbility.enchantedCreatureGetsHasAndWard 4 4
        Keyword.trample 1,
  StaticAbility.creaturesWithPlusOneHave Keyword.trample,
  StaticAbility.getsAndAllTypesIfGyCreatureCards 2 2 2,
  StaticAbility.attacksEachCombatIfAble,
  StaticAbility.flyingIfPlusOneThisTurn,
  StaticAbility.otherPowerUpCostsLess 3,
  StaticAbility.getsPowerPerOtherArtifact 1,
  StaticAbility.getsIfGyCreatureCards 2 2 1,
  .extort,
  StaticAbility.entersWithXPlusOne,
  StaticAbility.wardPoisonCounters 5,
  StaticAbility.flyingCantAttackYouOrBlockYours,
  StaticAbility.wardDiscardOrPay 2,
  StaticAbility.getsPowerPerAttachedEquipment 2,
  StaticAbility.healOtherDamageWhenDealt,
  StaticAbility.equippedCreatureGetsAndHas 0 8 Keyword.vigilance,
  StaticAbility.equippedCreatureGetsAndHas 2 1 Keyword.flying,
  .powerEqualLegendaryCreaturesYouControl,
  .maximumHandSize 10,
  .planeswalkersSurviveZeroLoyalty,
  .enteringArtifactsCreaturesDontTrigger,
  .instantSorcerySplitSecond,
  .ptEqualGraveyardCardTypes,
  .artifactTokensBecomeDragons,
  .smallCreaturesYouControlUnblockable,
  .toughnessAssignsCombatDamage,
  .negativePowerAssignsAsPositive,
  .castFromHandFreeUpToCreatures,
  .fra .attackDespiteDefenderIfScried,
  .fra .powerPerSevenInGraveyard,
  .fra .creaturesYouControlHaveTrample,
  .fra .firstStrikeDuringYourTurn,
  .fra .equippedHuntersAxe,
  .fra .enchantArtifactOrNonAuraEnchantment,
  .fra .enchantedIsConstruct55,
  .fra .enchantedGetsOneAndDeathtouch,
  .fra .vigilanceIfJace,
  .fra .powerAndFlyingIfSevenInGraveyard,
  .fra .plusOneCreaturesHaveVigilance,
  .fra .flyingHasteIfOpponentDealtNoncombat,
  .fra .equippedMedicsKitesail,
  .fra .entersTappedChooseColor,
  .fra .tapAddChosenColor,
  .fra .creaturesAttackDespiteDefender,
  .fra .creatureTokensGetOneAndVigilance,
  .fra .tapAddColorlessNotFromHand,
  .fra .tapAddAnyColorPlaneswalkerOnly,
  .fra .opponentsNoncreatureSpellsCostMore,
  .fra .planeswalkersAttackedByOneAtMost,
  .fra .extraPlusOneCounter,
  .fra .noSpellsOrAbilitiesDuringCombat,
  .fra .noncreatureSpellsCostLess,
  .fra .costsLessIfCastNoncreature,
  .fra .exileOpponentsDyingCreatures,
  .fra .wardDiscardCard,
  .fra .wardSacrificeThreePermanents,
  .fra .powerPerCreatureAndPlaneswalkerCard,
  .fra .otherPlusOneCreaturesHaveHaste,
  .fra .creaturesYouControlHaveHaste,
  .fra .noncombatDamagePlusOne,
  .fra .powerEqualsBasicLandTypes,
  .fra .otherCreaturesHaveTrample,
  .fra .landsHaveHexproof,
  .fra .hexproofUntilCombatDamage,
  .fra .thoptersHaveHaste,
  .fra .artifactCreaturesHaveVigilance,
  .fra .doesntUntap,
  .fra .entersChooseNonlandCardName,
  .fra .chosenNameSpellsCantBeCast,
]

def triggeredAbilities : Thunk (Array TriggeredAbility) := Thunk.mk fun _ => #[
  .onAttackPumpByGreatestPower,
  .onTheRingTemptsYouDraw 1,
  .onChooseRingBearerDraw,
  .onEnterDraw 1,
  .onEnterGainLife 1,
  .onDiesDealDamageEqualToPowerToOppCreature,
  .onBecomesBlockedDeal1ToBlockers,
  .onEnterScry 2,
  .onEnterSearchForest,
  .onAnotherElfYouControlEntersGets1,
  .onEnterMayDiscardDraw 2,
  .onEnterTargetOpponentSacrificesCreature,
  .onLandYouControlEntersPlusOnePlusOne,
  (.onLandYouControlEntersGets 1 1),
  .onEnterDealDividedDamage 3 3,
  .onEnterOrAttackDealDividedDamage 3 3,
  .onEnterOrAttackReturnElfGainLife,
  .onAttackWithElvesScry 1,
  .onScryPumpSelfForEachLookedAt,
  .onCastInstantOrSorceryDealDamageToEachOpponent 2,
  .onAttackSetOtherBasePT,
  .onAttackScry 1,
  .onAttackFerociousGainLife 2,
  .onAttackOtherGets2AndTrample,
  .onAttackPumpForEachOtherCreature,
  .onDrawSecondPlusOne,
  .onDrawPlusOne,
  .onCombatDamageToPlayerLoot,
  .onDiesOppCreatureGets (-1) (-1),
  .onOneOrMoreOtherCreaturesDieScry 1,
  .onEnterExileOppGyCardOppsLoseLife 2,
  .onEnterEachOpponentDiscards,
  .onEnterUntapOtherPlusOneIfSubtype "Bear",
  .onAttackFerociousSourceGets 2 2,
  .onAttackFerociousSourceGetsAndTeamTrample 1,
  .onAttackFerociousPlusOneEach,
  .onYourBeginCombatFerociousPlusOne,
  .onYouAttackFerociousDrawLoseLife,
  .onEnterPlusOneOnCreature,
  .onEnterRecruit,
  .onDiesRecruit,
  .onEnterCreateTokens .treasure 1 true,
  .onEnterCreateTokens .treasure 1,
  .onEnterExileTop,
  .onCastNoncreatureAmassGoblins 1,
  .onDiesAmassGoblins 4,
  .onEnterAmassGoblins 1,
  .onYouAttackAmassGoblins 2,
  .onEnterOrAttackRecruit,
  .onArtifactYouControlEntersDraw,
  .onYourUpkeepCreateTokens .wolf 1,
  .onEnterCreateThenAttach .dwarf,
  .onEnterAmassThenAttach 1,
  .onEnterAttachToSubtype "Dwarf",
  .onYourEndStepDraw,
  .onAttackTargetGainsKeywords Keyword.firstStrike,
  .onEnterSearchBasicToHand,
  .onEnterDealDamageDestroyIfSubtype 1 "Dragon",
  .onAttackDamageEqualTreasures,
  .onYourUpkeepCreateTokens .treasure 1,
  .onOpponentCastsFirstNoncreatureRecruit,
  .onThisOrNontokenSubtypeEntersCreateTokens "Dwarf" .dwarf 1,
  .onEnterGainLifeSearchBasicOnTop 2,
  .onLandYouControlEntersCreateTokens .elf 1,
  .onYourFirstMainAddMana #[.colored .red, .colored .red],
  .onEnterAttachTargetEquipment,
  .onBecomesTargetDraw,
  .onYouAttackRecruit,
  .onLandYouControlEntersTapOrUntap,
  .onLandYouControlEntersBecomePT 4 2,
  .onEnterReturnOtherPlusOne,
  .onAnotherSubtypeOrEquipmentEntersDrawOnce "Dwarf",
  .onEnterLookAtTopRevealTypes 4 #["Dwarf", "Equipment"],
  .onEnterCreateTappedTreasuresEqualOppArtifacts,
  .onCastWithTreasureDrawLoseLife,
  .onEnterCreateAxe,
  .onCastNoncreaturePumpAndDamageOpponents 1,
  .onEnterReturnCreatureFromGyToHand,
  .onCreatureCardLeavesYourGyAmassGoblins 1,
  .onEnterDestroyOtherAmassControllerPower,
  .onThisOrAnotherSubtypeEntersDiscardHand "Dwarf",
  .onDrawSecondPlusOneLifelink,
  .onCombatDamageWolfPlusOneOrTreasure,
  .onTokenYouControlEntersBelladonna,
  .onYourBeginCombatTrampleCounterBecomeBear,
  .onEnterOrAttackPlusOneOnCreature,
  .onAttackCastFromGyArtifactInstantSorcery,
  .onEnterBolgMaySacrifice,
  .onEnterLookAtTopRevealTypes 4 #["permanent"],
  .onEnterMillThenSubtypeToHand 4 "Elf",
  .onEnterExileOppNonlandEachUntilLeaves,
  .onLandYouControlEntersCreateTokens .bear 1,
  .onCastCreaturePlusOneEqualMv,
  .onAttackWithTotalPowerUntapExtraCombat 12,
  .onEnterOrAttackHoneEachEquipment,
  .onEnterCreateAxeAttach,
  .onAttackEquippedGainDoubleStrike,
  .onActivateCreatureAbilityDrawOnce,
  .onEnterTapEnchantedRemoveCounters,
  .onDiesRevealTopPutRandomCreature 13,
  .onOpponentDrawsSecondCreateTreasure,
  .onOpponentCastsChosenParityModes,
  .onYourBeginCombatIfDrawnTwoPumpFirstStrike,
  .onMountainEntersQuestThenDragon,
  .onDrawSecondMillPlayer 3,
  .onEquippedCombatDamageTreasuresPerChosenType,
  .onNontokenYouControlDiesRevealCreature,
  .onAttackMaySacAnotherPlusOneEqualPower,
  .onDiesAmassGoblinsEqualPower,
  .onEnterLootLandEntersTapped,
  .onLandYouControlEntersPayReturnFromGy,
  .onEnterHonePerOppCreaturesAttach,
  .onEnterOrAttackCreateWall,
  .onPutCountersOnGoblinOrcArmyDamageOpp,
  .onAnotherGoblinOrcArmyDiesExileTop,
  .onPlayerLosesLifeMillThatMany,
  .onDiesDrawPerFatGraveyard,
  .onEnterIfNotTokenCopySelf,
  .onEnterMaySacDrawTreasure,
  .onYouSacrificeTokenOppLosesLife,
  .onEnterAttachEquipmentThenFight,
  .onLandYouControlEntersPlusOneVigilance,
  .onAnotherLegendarySubtypeEntersLoot "Elf",
  .onDiesReturnAsArtifact,
  .onCastNoncreatureMayDrawXDiscard2,
  .onAnotherCreatureYouControlPowerAtMostEntersMayPayDraw 2 1,
  .onEnterMayExileAnotherCreature,
  .onLeaveReturnExiled,
  .onEnterDrawThenBottomIfNoLegendary,
  .onAttackWithTwoOrMoreGrantFlying,
  .onEnterTargetGets 2 0,
  .onEnterCreaturesYouControlGetAndFirstStrike 1,
  .onEnterExileOppNonlandUntilLeaves,
  .onYourEndStepRemoveHopeDrawSac,
  .onDiesDraw 1,
  .onAttackTapHumansDraw,
  .onAttackMayExileDefenderUntilLeaves,
  .onScryPumpAndUnblockableOnce,
  .onEnterEachPlayerSacrificesCreature,
  .onYouAttackDraw,
  .onEnterOrAttackAmassGoblins 3,
  .onEnterCreateTokens .food 3,
  .onEnterAttachToLegendary,
  .onPlayerCastsSecondSpellLoseLifeCreateTreasure,
  .onEnterDestroyOppArtifactsEnchantmentsGainLife,
  .onAttackDamageEqualSubtypeToEachOpponent "Dwarf",
  .onEnterOrAttackPlusOneEachOtherGainLife,
  .onEachEndStepDrawIfGainedLife 3,
  .onAttackDefenderSacsLeastPower,
  .onCastGreenOrForestEntersPlusOne,
  .onEnterGainControlOppUntilEot,
  .onEachCombatOthersGetAndOppsGet #["Goblin", "Orc"] 2 2 (-1) (-1),
  .onThisOrAnotherSubtypeEntersCreateTokens "Dwarf" .treasure 1,
  .onCombatDamagePutNonlandMvAtMost 3,
  .onEquippedAttacksCreateSpirits,
  .onEquippedAttacksPlusOneEachIfCityBlessing,
  .onCastColorCreateTokens .white .humanSoldier 1,
  .onCastColorScry .blue 2,
  .onCastColorDamageOpponent .red 3,
  .onCastColorPump .green 4 4,
  .onEquippedAttacksAloneDrawLoseLife,
  .onCombatDamageCreateTreasuresEqualPlayerArtifacts,
  .onAnotherSubtypeEntersPlusOneOnSource "Wolf" 2,
  .onAnotherCreatureYouControlEntersAlliance,
  .onYourBeginCombatCastInstantSorceryFromHand,
  .onEnterExileLandsThenReturnTapped,
  .onLandYouControlEntersDrawPlusOneSource,
  .onEquippedCombatDamageCastInstantSorcery,
  .onCombatDamageImpulseInstantSorcery,
  .onEnterOrOpponentDrawsDeal1AmassOrcs,
  .onYourEndStepPalantir,
  .onCastSecondSpellMillThenCopy,
  .onOpponentCastsAmassOrcs 1,
  .onArmyCombatDamageRingTempts,
  .onRingTemptsMayDiscardDraw 4,
  .onDealtNoncombatDamageCreateTreasures,
  .onEnterIfCastProtectionEverything,
  .onYourUpkeepLoseLifePerBurden,
  .onSubtypeYouControlCombatDamageCreateTokens "Dwarf" .treasure 2,
  .onFinalSagaChapterRevealSaga,
  .onCombatDamageToYouSacRingTempts,
  .onWatch Effect.watchSheHulkRedirectOnce,
  .onCasting Effect.castingPlusOneEachOther,
  .onWatch Effect.watchHulk,
  .onCombatMayPutArtifactAttachEquipment,
  .onCombatDamageDraw 1,
  .onCreatureYouControlAttacksAloneInvestigate,
  .onTappedForTeamworkPlusOneAndDraw,
  .onCreatureYouControlAttacksAlonePump 1 1,
  .onEachEndStepDrawIfAttackedOrEnteredSubtype "Hero",
  .onAttackOthersOfSubtypeGetEqualToughness "Hero",
  .onCasting Effect.castingPlusOneScry,
  .onEnterDrawGainLifeIfAnotherHero,
  .onResource Effect.resourcePlusOneOnHeroesCreateWall,
  .onThisAttack Effect.thisAttackAttacksAlonePlus2Indestructible,
  .onStep Effect.stepHarnessedFlicker,
  .onCasting Effect.castingPlusOneThis,
  .onEnter Effect.enterReturnGyPermanentThisTurn,
  .onEnterCreateTokens .soldier11white 2,
  .onCreatureYouControlEntersScryAndPlan 1,
  .onFourthPlanDrawPlusOneEach,
  .onCasting Effect.castingTapCreatureOrLand,
  .onEnter (Effect.enterDestroy .oppCreatureDealtDamageThisTurn),
  .onEnter Effect.enterOppCreatesTheVoid,
  .onWatch Effect.watchEquippedAttacksAloneUntapScry,
  .onEnterExileOppTappedUntilLeaves,
  .onWatch Effect.watchEnchantedAttachEquipment,
  .onEnter Effect.enterPlusOnesOrReturnArtEnch,
  .onEnterConnive,
  .onWatch Effect.watchMerfolkAttackDraw,
  .onEnter Effect.enterCreateRedwing,
  .onEnterAttachToCreatureYouControl,
  .onEnterEnchanted .tap,
  .onEnterTapOrUntapNonland,
  .onEnter Effect.enterReturnNonlandNontoken,
  .onWatch Effect.watchJusticeBounce,
  .onCombatTargetYouControlConnives,
  .onWatch Effect.watchYouTargetDrawOnce,
  .onWatch Effect.watchTokensEnterMayDraw,
  .onCasting Effect.castingDrawPowerEqualHand,
  .onCasting Effect.castingMerfolkFromBlue,
  .onCreaturesYouControlBecomeTappedLootAndPlan,
  .onFourthPlanReturnInstants,
  .onEnterExileOtherCopyEnchanted,
  .onEnterCreateTokens .soldier11white 1,
  .onEnterExileCreatureReturnEndStep,
  .onStep Effect.stepEnchantedControllerDraws,
  .onEnterAttachThen .untap,
  .onCasting Effect.castingExileFlicker,
  .onEnter Effect.enterTapLoseAbilitiesWhileSource,
  .onDiesCreateTokens .villain21menace 1,
  .onYouCastColorFromHandConnive .black,
  .onWatch Effect.watchVillainConniveOnce,
  .onWatch Effect.watchCombatDamageExileUntilNonland,
  .onYouDrawSecondCreateVillainAndPlan,
  .onSeventhPlanControlOpponent,
  .onWatch Effect.watchVillainPlusOneDamageOnce,
  .onEnterCreateTokens .doombot 2,
  .onYourEndStepDrawLoseLife,
  .onVillainYouControlEntersDrainAndPlan 1,
  .onFifthPlanExileTopCast,
  .onThisAttack Effect.thisAttackPayReturnAttacking,
  .onEnterTargetOpponentDiscards 2,
  .onWatch Effect.watchAttacksAloneDrain,
  .onEnterVillainIfGyElseMill,
  .onEnter Effect.enterRevealDiscardFromHand,
  .onYouDrawSecondCreateTokens .villain21menace,
  .onResource Effect.resourceDiscardExilePlay,
  .onCreatureCardsToGyDrawLoseLifeAndPlan,
  .onThirdPlanCreateRobots,
  .onResource Effect.resourceSecondDrawPlusOneTarget,
  .onEnterAttachThen (.grantKeywords Keyword.indestructible),
  .onWatch Effect.watchVillainAttachEquipment,
  .onEquippedCreatureYouControlAttacksConnive,
  .onDeath Effect.deathVillainReturnAsHero,
  .onThisAttack Effect.thisAttackEquippedDrain,
  .onWatch Effect.watchVillainPlusOneLifelink,
  .onCastNoncreatureTreasureAndPlan,
  .onFourthPlanDividedDamage,
  .onCasting Effect.castingCopyIfArtifactOrLand,
  .onWatch Effect.watchHawkeyeModes,
  .onWatch Effect.watchEquippedTappedDamage,
  .onResource Effect.resourceDrawIfAnotherHeroDamage,
  .onWatch Effect.watchVillainOrArtifactDamage,
  .onCasting Effect.castingIronFistTap,
  .onEnterMaySacArtifactOrDiscardDraw,
  .onAnotherArtifactEntersPlusOne,
  .onEnter (Effect.enterDealDamageUpToOne 4),
  .onWatch Effect.watchRedHulk,
  .onCasting Effect.castingMayPayHasteUnblockable,
  .onEnterEnchanted (.grantKeywords Keyword.firstStrike),
  .onEnter Effect.enterExileGyPlayUntilNextTurn,
  .onCasting Effect.castingDamageEqualMv,
  .onEnterCreateFoodOrTreasure,
  .onLandYouControlEntersPlusOneAndPlan,
  .onFourthPlanIndestructible,
  .onDeath Effect.deathHellcatReturn,
  .onEnterCreateTokens .food 1,
  .onResource Effect.resourceGainLifePlusOnes,
  .onWatch Effect.watchHulklingCompare,
  .onEnter Effect.enterCreateZabu,
  .onResource Effect.resourcePlusOneOnThisOnce,
  .onStep Effect.stepHydeChoose,
  .onLandYouControlEntersCreateTokens .moloid 1,
  .onWatch Effect.watchHeroesDamagePlusTwo,
  .onGainLifePlusOne,
  .onCombatPlusOneOnCreatureYouControl,
  .onEnterOrAttack Effect.enterOrAttackCreateSquirrel,
  .onEnterPlusOneOrTwoIfAnotherHero,
  .onStep Effect.stepCopyAbsorbingMan,
  .onCombatCreateAlienPerInvasion,
  .onThisAttack Effect.thisAttackMayPayPlusOne,
  .onResource Effect.resourcePlusOneCreateInsectOnce,
  .onDeath Effect.deathAttackingReturnHand,
  .onWatch Effect.watchNontokenHeroModal,
  .onWatch Effect.watchAttacksAloneFirstStrikeMenace,
  .onEnter Effect.enterMaySacOrDiscardNonlandThenDamage,
  .onWatch Effect.watchFirstTapUntap,
  .onEnter Effect.enterRevealHandExileUntilLeaves,
  .onYouAttacking Effect.youAttackingExileTopHeroPump,
  .onThisAttack Effect.thisAttackIfArtifactEnteredDraw,
  .onAttackConnive,
  .onResource Effect.resourceSecondDrawDrain,
  .onEnter Effect.enterMaySacAnotherThenDestroyOppNonland,
  .onWatch Effect.watchAnyPlayerSecondDraw,
  .onYouAttacking Effect.youAttackingPay2LifeToughness,
  .onCasting Effect.castingVillainToken,
  .onThisAttack Effect.thisAttackBlinkNontoken,
  .onEquipmentYouControlEntersDraw,
  .onResource Effect.resourceSecondDrawBecome66,
  .onArtifactYouControlEntersDrawOnce,
  .onEnter Effect.enterChooseUpToXModes,
  .onDeath Effect.deathDeathtouchOppSac,
  .onWatch Effect.watchSpeedballTargeted,
  .onEnter Effect.enterMayTapThenGrantIndestructible,
  .onEnter Effect.enterTapOppCantUntapWhileControl,
  .onCasting Effect.castingTargetsGainFlying,
  .onStep Effect.stepCopyTaskmaster,
  .onEnter Effect.enterCreateSturdyShieldAttach,
  .onCombatAnotherGetsSourcePower,
  .onEnter Effect.enterFightUpToOne,
  .onEnterSurveil 2,
  .onWatch Effect.watchEquippedAttacksTap,
  .onYouAttacking Effect.youAttackingLookSixCast,
  .onEnterDrawMayPutLandTapped,
  .onEnterOrAttack Effect.enterOrAttackCopyKeywords,
  .onStep Effect.stepDrawToTen,
  .onWatch Effect.watchUltronCopy,
  .onCasting Effect.castingVisionModes,
  .onThisAttack Effect.thisAttackDrawIfPower4,
  .triggered .enter (Effect.ofTrigger (.empowerJace 1)),
  .triggered .youGainLife (Effect.ofTrigger (.onSource (.plusOne 2))),
  .triggered .landYouControlEnters (Effect.ofTrigger (.empowerJace 2)),
  .onStep (Effect.ofTrigger .prepareSourceIfNot),
  .onStep (Effect.ofTrigger .prepareSourceIfThreeDied),
  .triggered .youActivateLoyaltyAbility (Effect.ofTrigger .drawIfRemovedTwoLoyalty),
  .triggered .youActivateLoyaltyAbility (Effect.ofTrigger (.createTokens .cadet 1)),
  .triggered .youCastFirstNoncreature (Effect.ofTrigger (.empowerJace 1)),
  .triggered .youCastNoncreature (Effect.ofTrigger (.createTokens .sculpture 1)),
  .triggered .youGainLife (Effect.ofTrigger (.plusOneOnEachSubtypeYouControl "Angel")),
  .triggered .youCastTargetingOpponentOrTheirCreature (Effect.ofTrigger .plusOneOnSource),
  .triggered .landYouControlEnters (Effect.ofTrigger (.gainLife 1)),
  .triggered (.subtypeYouControlEnters "Plains") (Effect.ofTrigger (.plusOneOn .creature)),
  .triggered .youGainLife (Effect.ofTrigger .loyaltyOnSource),
  .triggered .enter (Effect.ofTrigger (.grantThenCounterByType Keyword.hexproof)),
  .triggered .enter (Effect.ofTrigger (.grantThenCounterByType Keyword.deathtouch)),
  .triggered .enter (Effect.ofTrigger .destroyOppPermanentIfSixLands),
  .onStep (Effect.ofTrigger .pumpOrCounterIfScried),
  .triggered .eachUpkeep (Effect.ofTrigger (.createTokens .forestTentacle 1)),
  .triggered .eachOpponentDrawStep (Effect.ofTrigger (.draw 1)),
  .triggered .youCastNoncreature (Effect.ofTrigger (.creaturesYouControlGet 1 0)),
  .triggered .dies (Effect.ofTrigger .putSourceCountersOnTarget),
  .triggered .creatureYouControlDies (Effect.ofTrigger .chargeCounterOnSource),
  .onStep (Effect.ofTrigger .addGreenPerChargeCounter),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.mayPayPlusOneAndDraw 2)),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.sourceGets 1 1)),
  .triggered .youScryOrSurveil (Effect.ofTrigger (.creaturesYouControlGet 1 0)) .once,
  .triggered .opponentsDealtCombatDamageYourTurn (Effect.ofTrigger .drawTwoWinIfEmptyShuffleSource),
  .triggered .forestYouControlEnters (Effect.ofTrigger .pumpIfFiveOtherForests),
  .onStep (Effect.ofTrigger .surveilReturnIfGainedLife),
  TriggeredAbility.fra (.fra .castThis) "When you cast this spell, untap all lands you control."
    (.fra .untapAllLandsYouControl),
  TriggeredAbility.fra .youCastCreature
    "Whenever you cast a creature spell, exile up to one other target creature you control, then return that card to the battlefield under its owner's control."
    (.fra .blink)
    (.filtered { noun := "up to one other target creature you control", types := #[.creature], controller := .you, another := true })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .yourBeginCombat
    "At the beginning of combat on your turn, you may remove a +1/+1 counter from this creature. If you do, put a +1/+1 counter on each other creature you control."
    (.fra .mayMovePlusOneToEachOther),
  TriggeredAbility.fra .attack
    "Whenever this creature attacks, empower Jace X, where X is the number of creatures you control."
    (.fra .empowerJacePerCreature),
  TriggeredAbility.fra .enter "When this Aura enters, tap enchanted creature. It becomes unprepared."
    (.fra .tapEnchantedUnprepare),
  TriggeredAbility.fra .enter
    "When this enchantment enters, the owner of up to one other target nonland permanent puts it on their choice of the top or bottom of their library."
    (.fra .ownerPutsOnTopOrBottom)
    (.filtered { noun := "up to one other target nonland permanent", nonland := true, another := true })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter
    "When this creature enters, draw two cards, then discard two cards. When you discard one or more nonland cards this way, tap up to that many target creatures and put a stun counter on each of them."
    (.fra .drawTwoDiscardTwoStun),
  TriggeredAbility.fra .attack "Whenever this creature attacks, draw a card, then discard a card."
    (.sequence [.draw 1, .discard 1]),
  TriggeredAbility.fra .dies "When this creature dies, if it isn't a token, create a token that's a copy of it."
    (.fra .copyTokenOfSourceIfNotToken) (cond := .sourceNotToken),
  TriggeredAbility.fra (.or .enter .dies) "When this creature enters or dies, you gain 2 life." (.gainLife 2),
  TriggeredAbility.fra .enter "When this creature enters, mill three cards." (.millSelf 3),
  TriggeredAbility.fra (.fra .yourBeginCombatFromGraveyard)
    "At the beginning of combat on your turn, if two or more creatures died this turn, return this card from your graveyard to the battlefield."
    (.fra (.returnSourceFromGy false false 0)) (cond := .twoCreaturesDiedThisTurn),
  TriggeredAbility.fra .enter
    "When this Equipment enters, you may pay {2}. When you do, for each opponent, destroy up to one target creature or planeswalker that player controls."
    (.fra (.mayPayThenDestroyPerOpponent 2)),
  TriggeredAbility.fra .enter "When this creature enters, target creature gets +2/+2 and gains deathtouch until end of turn."
    (.sequence [.onPermanent (.pump 2 2), .onPermanent (.grantKeywords Keyword.deathtouch)])
    (.filtered TargetFilter.creature),
  TriggeredAbility.fra .attack "Whenever this creature attacks, it deals 1 damage to each opponent and you gain 1 life."
    (.sequence [.fra (.damageEachOpponent 1), .gainLife 1]),
  TriggeredAbility.fra .enter "When this enchantment enters, it deals X damage to any target." (.fra .damageX) .playerOrCreature,
  TriggeredAbility.fra .youCastNoncreature "Whenever you cast a noncreature spell, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra (.fra .eachUpkeepFromGraveyard)
    "At the beginning of each upkeep, if an opponent was dealt noncombat damage last turn, return this card from your graveyard to your hand."
    (.fra (.returnSourceFromGy true false 0)) (cond := .opponentDealtNoncombatDamageLastTurn),
  TriggeredAbility.fra .enter
    "When this creature enters, creatures you control gain trample and get +X/+0 until end of turn, where X is the number of artifacts you control."
    (.sequence [.fra .creaturesGetPowerPerArtifact, .teamGain Keyword.trample]),
  TriggeredAbility.fra .enter
    "When this creature enters, search your library for a card, put it into your hand, shuffle, then discard a card at random."
    (.fra .searchCardThenDiscardRandom),
  TriggeredAbility.fra .enter "When this creature enters, create a 2/2 colorless Wizard Soldier creature token named Cadet."
    (.createTokens .cadet 1),
  TriggeredAbility.fra (.fra .opponentsDealtNoncombatDamage)
    "Whenever one or more opponents are dealt noncombat damage, creatures you control get +1/+0 until end of turn."
    (.creaturesYouControlPump 1 0),
  TriggeredAbility.fra .enter
    "When this creature enters, target instant or sorcery card in your graveyard gains flashback until end of turn. The flashback cost is equal to its mana cost."
    (.fra .grantFlashbackUntilEot)
    (.filtered { noun := "target instant or sorcery card in your graveyard", zone := .yourGraveyard, types := #[.instant, .sorcery] }),
  TriggeredAbility.fra .enter "When this creature enters, you may discard a card. When you do, this creature deals 2 damage to any target."
    (.fra (.mayDiscardThenDamage 2)),
  TriggeredAbility.fra .combatDamageToPlayer
    "Whenever this creature deals combat damage to a player, return target land card from your graveyard to your hand."
    (.fra .returnFromGyToHand)
    (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }),
  TriggeredAbility.fra .anotherCreatureYouControlEnters "Whenever another creature you control enters, you gain 1 life."
    (.gainLife 1),
  TriggeredAbility.fra .sourceDealtDamage
    "Whenever this creature is dealt damage, you may search your library for up to that many land cards, put them onto the battlefield tapped, then shuffle."
    (.fra .maySearchLandsEqualDamage),
  TriggeredAbility.fra .enter "When this creature enters, create a Heartwood token." (.createTokens .heartwood 1),
  TriggeredAbility.fra (.fra .youPutLoyaltyCounters)
    "Whenever you put one or more loyalty counters on a planeswalker, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra .enter
    "When this creature enters, you may search your library for a basic land card, put that card onto the battlefield tapped, then shuffle."
    (.fra .maySearchBasicLandTapped),
  TriggeredAbility.fra .enter "When this creature enters, put three +1/+1 counters on target creature."
    (.onPermanent (.plusOne 3)) (.filtered TargetFilter.creature),
  TriggeredAbility.fra (.or .enter .dies) "When this creature enters or dies, create a Heartwood token."
    (.createTokens .heartwood 1),
  TriggeredAbility.fra .youGainLife "Whenever you gain life, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  TriggeredAbility.fra .youScryOrSurveil "Whenever you scry or surveil, put a +1/+1 counter on each creature you control."
    (.fra .plusOneOnEachCreatureYouControl),
  TriggeredAbility.fra (.fra .enchantedDies)
    "When enchanted creature dies, return that card to the battlefield tapped under its owner's control."
    (.fra .returnCauseTapped),
  TriggeredAbility.fra .eachEndStep "At the beginning of the end step, sacrifice this creature." (.fra .sacrificeSource),
  TriggeredAbility.fra (.fra .creatureYouControlAttacks)
    "Whenever a creature you control attacks, that creature deals 1 damage to each opponent."
    (.fra (.causeDealsDamageToEachOpponent 1)),
  TriggeredAbility.fra .youGainLife
    "Whenever you gain life, create a colorless artifact token named Lotus with \"{T}, Sacrifice this token: Add three mana of any one color.\" This ability triggers only once each turn."
    (.createTokens .lotus 1) (once := true),
  TriggeredAbility.fra .enter "When this creature enters, it fights up to one target creature an opponent controls."
    (.fra .sourceFightsTarget)
    (.filtered { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter
    "When this creature enters, if you cast it, target opponent reveals their hand. You choose a nonland card from it. Exile that card."
    (.fra .exileFromHandUntilLeaves) .opponent (cond := .sourceWasCast),
  TriggeredAbility.fra .enter
    "When this creature enters, mill four cards. When you do, return target land card from your graveyard to the battlefield tapped."
    (.fra (.millThenReturnLandTapped 4)),
  TriggeredAbility.fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, surveil 1." (.surveil 1),
  TriggeredAbility.fra (.fra (.opponentCastsSpellMvAtMost 2))
    "Whenever an opponent casts a spell with mana value 2 or less, you gain 2 life." (.gainLife 2),
  TriggeredAbility.fra .enter
    "When this artifact enters, exile target nonland permanent an opponent controls with mana value 3 or less until this artifact leaves the battlefield."
    (.fra .exileUntilSourceLeaves)
    (.filtered { noun := "target nonland permanent an opponent controls with mana value 3 or less", nonland := true, controller := .opponent, mvAtMost := some 3 }),
  TriggeredAbility.fra .enter
    "When this creature enters, you may sacrifice a land. If you do, create two tapped Heartwood tokens."
    (.fra .maySacrificeLandForHeartwoods),
  TriggeredAbility.fra .enter
    "When this creature enters, if you cast him, exile up to one target nonland card of each card type from your graveyard. Copy those cards. You may cast any number of spells with total mana value 6 or less from among the copies without paying their mana costs."
    (.fra .uldarosCopies)
    (.filtered { noun := "up to one target nonland card of each card type from your graveyard"
                 zone := .yourGraveyard, nonland := true })
    (allowsZeroTargets := true) (maxTargets := 8) (cond := .sourceWasCast),
  TriggeredAbility.fra .enter "When this Equipment enters, it deals 3 damage to any target and you gain 3 life."
    (.sequence [.fra (.damageAny 3), .gainLife 3]) .playerOrCreature,
  TriggeredAbility.fra .attack "Whenever this creature attacks, exile up to one target card from a graveyard."
    (.fra .exileCardFromGraveyard)
    (.filtered { noun := "up to one target card from a graveyard", zone := .anyGraveyard })
    (allowsZeroTargets := true),
  TriggeredAbility.fra (.fra .youCastPreparedSpell)
    "Whenever you cast a prepared spell, copy it. You may choose new targets for the copy."
    (.fra .copyCauseSpell),
  TriggeredAbility.fra .enter "When this artifact enters, draw a card, then discard a card." (.sequence [.draw 1, .discard 1]),
  TriggeredAbility.fra .yourUpkeep
    "At the beginning of your upkeep, surveil 1. Then if there are seven or more cards in your graveyard, sacrifice this artifact, it deals 2 damage to each opponent, and you gain 2 life."
    (.fra .eyeOfJace),
  TriggeredAbility.fra (.fra .youCastEquipmentOrTargetingCreatureYouControl)
    "Whenever you cast an Equipment spell or a spell that targets a creature you control, draw a card. This ability triggers only once each turn."
    (.draw 1) (once := true),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, you gain 1 life." (.gainLife 1),
  TriggeredAbility.fra .youScryOrSurveil
    "Whenever you scry or surveil, create a 1/1 colorless Thopter artifact creature token with flying. This ability triggers only once each turn."
    (.createTokens .thopter 1) (once := true),
  TriggeredAbility.fra .youGainLife "Whenever you gain life, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  TriggeredAbility.fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, it gains double strike until end of turn."
    (.fra (.causeGains Keyword.doubleStrike)),
  TriggeredAbility.fra (.fra .anotherNontokenCreatureYouControlEnters)
    "Whenever another nontoken creature you control enters, untap this creature." (.fra .untapSource),
  TriggeredAbility.fra .enter
    "When this creature enters, for each opponent, tap up to one target creature that player controls. Put a stun counter on each of those creatures."
    (.fra .tapAndStunPerOpponent) (.filtered { noun := "up to one target creature that player controls", types := #[.creature], controller := .eachOpponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .eachEndStep
    "At the beginning of each end step, if you've drawn three or more cards this turn, create a 3/3 blue Angel creature token with flying."
    (.createTokens .angel33blue 1) (cond := .drewThreeThisTurn),
  TriggeredAbility.fra (.fra .creatureOpponentControlsEnters)
    "Whenever a creature an opponent controls enters, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra (.fra .opponentActivatesLoyaltyAbility)
    "Whenever an opponent activates a loyalty ability, this creature deals 1 damage to that player."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlEnters)
    "Whenever another creature or planeswalker you control enters, mill two cards." (.millSelf 2),
  TriggeredAbility.fra .enter "When this creature enters, remove up to three counters from another target creature or planeswalker."
    (.fra (.removeUpToCounters 3))
    (.filtered { TargetFilter.creatureOrPlaneswalker with noun := "another target creature or planeswalker", another := true }),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, this creature deals 1 damage to target opponent and you gain 1 life."
    (.sequence [.fra (.damageAny 1), .gainLife 1]) .opponent,
  TriggeredAbility.fra (.fra .opponentDealtNoncombatDamage)
    "Whenever an opponent is dealt noncombat damage, put a +1/+1 counter on this creature."
    (.fra (.plusOneOnSource 1)),
  TriggeredAbility.fra (.fra .playerDiscards)
    "Whenever a player discards one or more cards, this creature deals 1 damage to each opponent."
    (.fra (.damageEachOpponent 1)),
  TriggeredAbility.fra .creatureYouControlDies
    "Whenever a creature you control dies, put a loyalty counter on each planeswalker you control."
    (.fra .loyaltyOnEachPlaneswalkerYouControl),
  TriggeredAbility.fra .enter
    "When this creature enters, you may sacrifice a creature or planeswalker. When you do, each opponent sacrifices a creature of their choice."
    (.fra .maySacrificeThenEdict),
  TriggeredAbility.fra .anotherCreatureYouControlEnters
    "Whenever another creature you control enters, this creature gets +X/+0 until end of turn, where X is that creature's power."
    (.fra .sourceGetsCausePower),
  TriggeredAbility.fra (.fra .creatureYouControlAttacksPlayerAlone)
    "Whenever a creature you control attacks a player alone, discard a card, then draw a card. Then put a +1/+1 counter on that creature for each card you've discarded this turn."
    (.fra .jiangYangguAlone),
  TriggeredAbility.fra .enter "When this creature enters, create a 5/5 red Dragon creature token with flying."
    (.createTokens .dragon55flying 1),
  TriggeredAbility.fra .landYouControlEnters
    "Whenever a land you control enters, this creature deals 1 damage to each opponent. If that land is a Mountain, add {R}."
    (.fra .kothGeomancer),
  TriggeredAbility.fra .enter "When this creature enters, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  TriggeredAbility.fra (.fra .opponentSmallCreatureBlocks)
    "Whenever a creature an opponent controls with power or toughness 1 or less blocks, this creature deals 1 damage to that creature's controller."
    (.fra (.damageCauseController 1)),
  TriggeredAbility.fra .yourEndStep
    "At the beginning of your end step, if you didn't cast a spell this turn, put two +1/+1 counters on this creature."
    (.fra (.plusOneOnSource 2)) (cond := .castNoSpellThisTurn),
  TriggeredAbility.fra .enter
    "When this creature enters, search your library for up to X basic land cards with different names, reveal them, put them into your hand, then shuffle."
    (.fra .fblthpSearch),
  TriggeredAbility.fra (.fra (.creatureYouControlPowerAtLeastEnters 4))
    "Whenever a creature you control with power 4 or greater enters, draw a card." (.draw 1),
  TriggeredAbility.fra .enter "When this creature enters, create Mowu, a legendary 3/3 green Dog creature token."
    (.createTokens .mowu 1),
  TriggeredAbility.fra .yourEndStep "At the beginning of your end step, untap all tokens you control."
    (.fra .untapAllTokensYouControl),
  TriggeredAbility.fra .enter
    "When this creature enters, you may discard a card. If you do, search your library for an enchantment card, reveal it, put it into your hand, then shuffle."
    (.fra .mayDiscardThenSearchEnchantment),
  TriggeredAbility.fra (.fra .youDiscardThis) "When you discard this card, you gain 3 life." (.gainLife 3),
  TriggeredAbility.fra .youActivateLoyaltyAbility
    "Whenever you activate a loyalty ability, you gain 1 life. You may play an additional land this turn."
    (.sequence [.gainLife 1, .spell .extraLand]),
  TriggeredAbility.fra .enter
    "When this creature enters, another target creature you control fights up to one target creature an opponent controls."
    (.fra .firstFightsSecond)
    (.multi #[{ noun := "another target creature you control", types := #[.creature], controller := .you, another := true },
      { noun := "up to one target creature an opponent controls", types := #[.creature], controller := .opponent }] #[1]),
  TriggeredAbility.fra (.fra .anotherCreatureOrPlaneswalkerYouControlDies)
    "Whenever another creature or planeswalker you control dies, you gain 1 life." (.gainLife 1),
  TriggeredAbility.fra .enter
    "When this creature enters, for each opponent, put X -1/-1 counters on up to one target creature that player controls, where X is the greatest mana value among cards in your graveyard."
    (.fra .minusOnesPerOpponent) (.filtered { noun := "up to one target creature that player controls", types := #[.creature], controller := .eachOpponent })
    (allowsZeroTargets := true),
  TriggeredAbility.fra .enter "When this creature enters, draw a card for each color among other artifacts you control."
    (.fra .drawPerColorAmongOtherArtifacts),
  TriggeredAbility.fra .youAttack
    "Whenever you attack, if you've activated a loyalty ability this turn, untap target attacking creature. It can't be blocked this turn."
    (.fra .untapUnblockable)
    (.filtered { noun := "target attacking creature", types := #[.creature], attacking := true })
    (cond := .activatedLoyaltyThisTurn),
  TriggeredAbility.fra (.fra .thisOrAnotherCreatureYouControlEnters)
    "Whenever this creature or another creature you control enters, put a +1/+1 counter on target creature that entered this turn."
    (.onPermanent (.plusOne 1))
    (.filtered { noun := "target creature that entered this turn", types := #[.creature], enteredThisTurn := true }),
  TriggeredAbility.fra .youCastNoncreature
    "Whenever you cast a noncreature spell, create a 1/1 colorless Thopter artifact creature token with flying."
    (.createTokens .thopter 1),
  TriggeredAbility.fra (.fra .youCastArtifactOrCreature) "Whenever you cast an artifact or creature spell, untap this creature."
    (.fra .untapSource),
  TriggeredAbility.fra (.fra .creatureYouControlLeaves)
    "Whenever a creature you control leaves the battlefield, if it had counters on it, put those counters on this artifact."
    (.fra .putCauseCountersOnSource) (cond := .causeHadCounters),
  TriggeredAbility.fra .yourBeginCombat
    "At the beginning of combat on your turn, if this artifact has counters on it, you may move all counters from this artifact onto target creature."
    (.fra .mayMoveSourceCountersToTarget) (.filtered TargetFilter.creature) (cond := .sourceHasCounters),
  TriggeredAbility.fra .enter "When this creature enters, you may pay {3}. If you do, proliferate twice."
    (.fra (.mayPayThenProliferate 3 2)),
  TriggeredAbility.fra (.fra .youProliferate) "Whenever you proliferate, draw a card." (.draw 1),
]

def activatedAbilities : Thunk (Array ActivatedAbility) := Thunk.mk fun _ => #[
  activated (Effect.sourceGets 1 1) (ManaCost.ofGeneric 2)
          (costReductionIfYouControlLegendary := 2),
  {
        cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true },
        effect := Effect.gainLife 3
      },
  equipAbility (ManaCost.ofGeneric 3),
  activated (Effect.becomeBearCreatureWithLandsPT)
          (ManaCost.ofGenericAndColors 5 [.green, .green]),
  activated (Effect.sourceGets 1 0) (ManaCost.ofGenericAndColor 1 .red),
  activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.sourceGets 1 0) (ManaCost.ofColor .red),
  activated (Effect.putPlusOnePlusOneOnSource 3)
          (ManaCost.ofGenericAndColors 5 [.green, .green]),
  activated (Effect.abilityCreaturesYouControlGet 1 1) (ManaCost.ofGenericAndColor 3 .white),
  activated (Effect.sourceGets 2 2) (payLife := 2) (onceEachTurn := true),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGeneric 2)
          (sacrificeAnotherCreatureOrArtifact := true)
          (onlyAsSorcery := true) (activateFromGraveyard := true),
  activated (Effect.exileTopPlayUntilEndOfNextTurn)
          (sacrificeAnotherCreatureOrArtifact := true)
          (onlyDuringYourTurn := true) (onceEachTurn := true),
  activated (Effect.targetCantBeBlockedThisTurn) (ManaCost.ofGenericAndColor 4 .blue),
  activated (Effect.searchBasicLandTapped) (tap := true) (sacrificeSource := true),
  typecyclingAbility "Halfling" (ManaCost.ofGeneric 4),
  activated (Effect.addAnyColor) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.destroyTargetPermanent) (ManaCost.ofGeneric 7) (tap := true)
          (sacrificeSource := true),
  activated (Effect.returnFromGyAttachPowerAtMost 1)
          (ManaCost.ofGenericAndHybrids 2 .white .blue 2)
          (activateFromGraveyard := true) (onlyAsSorcery := true),
  activated (Effect.ownerShuffleSourceDraw 3) (ManaCost.ofGeneric 6),
  activated (Effect.addMana #[.colored .black, .colored .red]) (tap := true)
          (sacrificeAnotherSubtype := some "Goblin"),
  activated (Effect.abilityDrawThenDiscard 1) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 1) (tap := true)
          (discardACard := true),
  activated (Effect.abilityCreateTokens .dwarf 1) (ManaCost.ofGenericAndColor 4 .red)
          (tap := true) (onlyAsSorcery := true) (costReductionPerEquipment := 1),
  activated (Effect.attachToTargetCreatureYouControl) (ManaCost.ofGeneric 2)
          (onlyAsSorcery := true) (payLife := 2),
  activated (Effect.searchTwoBasicsSplit) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true),
  activated (Effect.subtypesGainMenace #["Goblin", "Orc"]) (ManaCost.ofGenericAndColor 1 .black),
  activated (Effect.exileThenReturnNextEnd) (ManaCost.ofGenericAndColors 5 [.blue, .blue]),
  activated (Effect.searchBasicBeholdSubtypeUntap "Elf") (tap := true) (payLife := 1)
          (sacrificeSource := true),
  activated (Effect.twoPlayersDraw) (ManaCost.ofGenericAndColor 2 .white),
  activated (Effect.discardLegendarySameNameDraw) (ManaCost.ofGeneric 1) (tap := true)
          (discardLegendarySameName := true),
  activated (Effect.dealDamageToAny 4) (ManaCost.ofGenericAndColor 2 .red)
          (sacrificeArtifact := true),
  activated (Effect.drawEqualSacrificedPowerThenDiscard) (ManaCost.ofGeneric 1)
          (sacrificeAnotherSubtype := some "creature"),
  typecyclingAbility "Plains",
  equipAbility (ManaCost.ofGeneric 1) (some "Human"),
  activated (Effect.destroyTargetArtifactOrEnchantment) (sacrificeSource := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityCreaturesYouControlGet 1 1)
          (ManaCost.ofGenericAndColor 4 .white) (tap := true)
          (costReductionIfYouControlLegendary := 2),
  activated (Effect.millPlayer 3) (ManaCost.ofGenericAndColor 5 .blue) (tap := true),
  activated (Effect.returnFromGraveyardTapped) (ManaCost.ofGenericAndColor 2 .black)
          (activateFromGraveyard := true) (onlyIfYouControlLegendary := true),
  activated (Effect.searchBasicLandTapped) (ManaCost.ofGeneric 2)
          (tap := true) (sacrificeSource := true),
  activated (Effect.dealDamageToTargetCreature 2) (ManaCost.ofGeneric 1)
          (sacrificeSource := true)
          (otherModes := #[Effect.destroyTargetColorlessNonland]),
  activated (Effect.targetCantBeBlockedPowerAtMost 2) (tap := true),
  activated (Effect.abilityScry 2) (ManaCost.ofGenericAndColor 1 .blue) (tap := true)
          (onlyIfYouControlLegendary := true),
  activated (Effect.abilityDrawThenDiscard 2) (ManaCost.ofGeneric 3) (tap := true),
  activated (Effect.abilityCreateTokensX .treasure) { symbols := #[.x, .x] }
          (tap := true) (sacrificeSource := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 1 .white) (tap := true)
          (onlyIfYouAttackedWithTwoOrMore := true),
  activated (Effect.abilityCreateTokens .food 1) (ManaCost.ofGenericAndColor 1 .green)
          (tap := true) (tapAnUntappedCreatureYouControl := true),
  activated (Effect.creaturesYouControlGetOppsLoseLife 2 0 2)
          (ManaCost.ofGenericAndColors 1 [.black, .red]),
  activated (Effect.arwenShare) (ManaCost.ofGeneric 1) (removeIndestructibleCounter := true),
  activated (Effect.grantCombatDamageCreateTreasure) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.putShadowCounter) (ManaCost.ofGenericAndColor 3 .black) (tap := true),
  activated (Effect.damageEachOpponent 1) (ManaCost.ofGenericAndColors 1 [.black, .red]) (tap := true),
  activated (Effect.chooseTwoDestroyRest) (ManaCost.ofGenericAndColors 5 [.black, .red])
          (tap := true) (sacrificeSource := true) (sacrificeLegendaryArtifact := true)
          (onlyAsSorcery := true),
  activated (Effect.blackGateUnblockable) (ManaCost.ofGenericAndColor 1 .black) (tap := true),
  activated (Effect.burdenThenDraw) (tap := true),
  activated (Effect.teamGain Keyword.doubleStrike) (ManaCost.ofGeneric 10),
  activated (Effect.sourceGainsIndestructibleTap) (discardACard := true),
  activated (Effect.plusOneOnEachOtherSubtype "Hero" 1) (ManaCost.empty) (tap := true),
  typecyclingAbility "Basic land" (ManaCost.ofGeneric 2),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .white),
  activated (Effect.plusOneAndIndestructibleCounter) (ManaCost.ofGenericAndColors 5 [.white, .white]) (powerUp := true),
  activated (Effect.pumpAttackingAloneGainLife) (ManaCost.empty) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 3 [.green, .white, .white]) (onlyAsSorcery := true),
  activated (Effect.harnessInfinityStone) (ManaCost.ofGenericAndColor 5 .white) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .white, .white]) (onlyAsSorcery := true),
  activated (Effect.lookAtTopPutTypes 7 #["Hero", "Equipment", "Vehicle"]) (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (powerUp := true),
  activated (Effect.anotherYouControlGetsAndGrant 2 0 Keyword.hexproof) (ManaCost.ofGeneric 2) (tap := true),
  activated (Effect.tapTargetCreature) (ManaCost.ofGeneric 2) (tap := true)
        (costReductionIfTargetPowerAtMost := some (1, 3)),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.plusOneAndDraw 1 2) (ManaCost.ofGenericAndColor 5 .blue) (powerUp := true),
  activated (Effect.drawX) ({ symbols := #[.x, .x] }) (tap := true) (onlyAsSorcery := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 2 [.red, .red, .green, .green]) (onlyAsSorcery := true),
  activated (Effect.copyControlledAbility true) (ManaCost.ofGeneric 1) (tap := true),
  equipAbility (ManaCost.ofGenericAndColor 2 .blue),
  activated (Effect.abilityDraw 2) (ManaCost.ofGenericAndColor 3 .blue) (sacrificeSource := true),
  activated (Effect.addBlueCantNonartifact) (ManaCost.empty) (tap := true),
  activated (Effect.revealTopDrawIfArtifact) (ManaCost.empty) (tap := true),
  activated (Effect.plusOneAndExtraTurn) (ManaCost.ofGenericAndColors 5 [.blue, .blue, .blue]) (powerUp := true),
  activated (Effect.copyArtifactYouControlNotLegendary) (ManaCost.ofGeneric 1) (tap := true) (onlyAsSorcery := true),
  activated (Effect.plusOneX) ({ symbols := #[.x, .colored .blue, .colored .blue] }) (powerUp := true),
  activated (Effect.lookAtTopRevealArtifact 4) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.blue, .red]) (onlyAsSorcery := true),
  activated (Effect.createTappedTokens .villain21menace 1) (ManaCost.ofGeneric 3) (tap := true)
        (onlyIfGyCreaturesAtLeast := 2),
  activated (Effect.abilityDraw 1) (ManaCost.ofGenericAndColor 2 .black)
        (sacrificeArtifactOrCreature := true),
  activated (Effect.searchLandTypeToHand "Plan") (ManaCost.ofGenericAndColor 1 .black)
        (discardSource := true) (activateFromHand := true),
  activated (Effect.connive) (payLife := 3) (onlyDuringYourTurn := true),
  activated (Effect.eachOppDiscardThenPlusOne) (ManaCost.ofGenericAndColor 4 .black) (powerUp := true),
  activated (Effect.returnFromGraveyardToHand) (ManaCost.ofGenericAndColor 2 .black),
  activated (Effect.addTwoAnyColorEquipment) (payLife := 2) (onceEachTurn := true),
  activated (Effect.targetGets (-4) (-4)) (tap := true) (sacrificeEquipmentAttachedToSource := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityCreateTokens .wall04defender 1) (ManaCost.ofGenericAndColor 2 .white),
  activated (Effect.sourceGets 4 4) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.dealDamageToTargetCreature 4) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.abilityTargetPlayerDraw 4) (ManaCost.ofGenericAndColor 5 .blue),
  activated (Effect.returnGyCreatureThenPlusOne 2) (ManaCost.ofGenericAndColors 5 [.black, .black]) (powerUp := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 3) (ManaCost.ofGenericAndColor 6 .red),
  activated (Effect.exileTopXPlayThisTurn) (tap := true) (putStunCounterOnSource := true),
  activated (Effect.nextInstantSorceryCopyIfMvAtMostSourcePower) (ManaCost.ofGeneric 1) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 4 .red),
  activated (Effect.drawPerDiscardedThisTurn)
        (ManaCost.ofGeneric 2) (tap := true) (discardACard := true),
  equipWorthyAbility (ManaCost.ofGeneric 1),
  activated (Effect.abilityDealDamageToEachCreature 2) (ManaCost.ofGenericAndColor 2 .red)
          (discardSource := true) (activateFromHand := true),
  activated (Effect.plusOneAndDoubleStrikeCounter) (ManaCost.ofGenericAndColor 4 .red) (powerUp := true),
  activated (Effect.abilityCreateTokens .treasure 1) (ManaCost.ofGeneric 2) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 5 .red),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColors 5 [.red, .red]),
  activated (Effect.addAnyColorEqualToSourcePower) (ManaCost.empty) (tap := true),
  activated (Effect.destroyTargetNoncreatureArtOrEnch)
        (sacrificeSource := true) (onlyAsSorcery := true),
  activated (Effect.plusOneAndGrant ((Keyword.vigilance.merge Keyword.indestructible).merge Keyword.haste)) (ManaCost.ofGenericAndColor 4 .green) (powerUp := true),
  activated (Effect.plusOneAndCreateTokens 1 .hero32vigilance) (ManaCost.ofGenericAndColor 6 .green) (powerUp := true),
  activated (Effect.proliferateEachKind) (ManaCost.empty) (tap := true) (onlyAsSorcery := true),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 3 5 (Keyword.reach.merge Keyword.vigilance)) (ManaCost.ofGeneric 3),
  activated (Effect.becomeTypes #["Dinosaur", "Hero"] 6 6 Keyword.trample) (ManaCost.ofGeneric 6),
  activated (Effect.millThenPutSubtypeOrEnchantment 4 "Hero") (ManaCost.ofGeneric 3) (tap := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGenericAndColor 3 .green),
  activated (Effect.addTwoAnyColorCreatureSources) (ManaCost.empty) (tap := true),
  activated (Effect.destroyUpToOneThenPlusOne) (ManaCost.ofGenericAndColors 4 [.green, .green]) (powerUp := true),
  activated (Effect.createTokensEqualSubtype .squirrel11green "Squirrel") (ManaCost.ofGenericAndColors 1 [.green, .green, .green]),
  activated (Effect.addAnyColor) (ManaCost.empty) (tap := true),
  activated (Effect.plusOneAndCreateTigerGod) (ManaCost.ofGenericAndColor 5 .green) (powerUp := true),
  activated (Effect.plusOneThenFightUpToOne) (ManaCost.ofGenericAndHybrids 5 .red .green 2) (powerUp := true),
  activated (Effect.createTokensEqualRemovedPlusOnes .insect11green)
        (ManaCost.ofGenericAndColor 2 .green) (tap := true) (removeAnyNumberPlusOne := true),
  activated (Effect.dealDamageToAny 2) (ManaCost.ofGeneric 3)
        (tap := true) (sacrificeArtifactOrDiscardNonland := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 5) (ManaCost.ofGenericAndColors 6 [.red, .green]),
  activated (Effect.transform) (ManaCost.ofGenericAndColors 4 [.white, .blue]) (onlyAsSorcery := true),
  activated (Effect.copyControlledAbility false)
        (payLife := 2) (onlyDuringYourTurn := true) (onceEachTurn := true),
  activated (Effect.plusTwoThenOddEvenDestroy) ({ symbols := #[.colorless, .colored .white, .colored .blue, .colored .black, .colored .red, .colored .green] }) (powerUp := true),
  activated (Effect.returnFromGyFinalityAttach) (ManaCost.ofGenericAndColors 3 [.white, .black])
        (activateFromGraveyard := true),
  activated (Effect.addMana #[.colorless, .colorless, .colorless]) (ManaCost.empty) (tap := true),
  activated (Effect.equipmentBecomesConstructHero) (ManaCost.ofGeneric 2),
  activated (Effect.plusOneAndCreateTokens 2 .robotVillain22) (ManaCost.ofGeneric 6) (powerUp := true),
  powerUpAbility (Effect.putPlusOnePlusOneOnSource 2) (ManaCost.ofGeneric 7),
  activated (Effect.addAnyColorSpendOnlySubtype "Hero") (ManaCost.empty) (tap := true),
  activated (Effect.lookAtTopRevealSubtype 3 "Hero") (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.addFourAnyCombination) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.abilityDraw 1) (ManaCost.ofGeneric 4) (tap := true)
          (onlyIfYouControlCreatureToughnessAtLeast := 4),
  activated (Effect.addAnyColorSpendOnlyArtifactSpell) (ManaCost.empty) (tap := true),
  activated (Effect.abilityCreateTokens .doombot 1) (ManaCost.ofGeneric 3) (tap := true)
          (sacrificeArtifact := true) (onlyAsSorcery := true),
  activated (Effect.targetSubtypeConnives "Villain") (ManaCost.ofGeneric 3) (tap := true) (onlyAsSorcery := true),
  {
      cost := { mana := ManaCost.ofGeneric 2, sacrificeSource := true },
      effect := Effect.abilityDraw 1
    },
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 6),
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGenericAndColor 2 .blue) (tap := true),
  activated (Effect.targetCreatureBecomesPrepared) (ManaCost.ofGeneric 4) (tap := true),
  activated (Effect.eachCreatureYouControlBecomesPrepared)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true),
  activated (Effect.becomeCopyLegendRuleOff) (ManaCost.ofGeneric 5),
  activated (Effect.cantBeBlockedAnotherPowerAtMost 2) (ManaCost.ofGeneric 1) (tap := true),
  activated (Effect.proliferatePlaneswalkerTypesTimes)
          (ManaCost.ofColors [.white, .blue, .black, .red, .green]) (tap := true),
  activated (Effect.returnFromGyWithFinality) (ManaCost.ofColors [.black, .red])
          (activateFromGraveyard := true) (onlyIfOpponentDealtNoncombatDamage := true),
  activated (Effect.tapAndStunTargetCreature) (ManaCost.ofGenericAndColor 3 .blue)
          (activateFromGraveyard := true) (exileSourceFromGraveyard := true)
          (onlyAsSorcery := true),
  activated (Effect.abilityEmpowerJace 2) (ManaCost.ofGeneric 1)
          (activateFromGraveyard := true) (exileSourceFromGraveyard := true),
  ActivatedAbility.fra
    "{3}, Exile this card from your hand: Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled."
    (FraCandidates.ab (.fra .emrakulGrantMana) "Target land gains \"{T}: Add {C}{C}\" until this card is cast from exile. You may cast this card for as long as it remains exiled"
      (.filtered { noun := "target land", types := #[.land] }))
    { mana := ManaCost.ofGeneric 3, fra := .exileSourceFromHand } (activateFromHand := true),
  ActivatedAbility.fra "{4}{W}: Creatures you control get +1/+1 until end of turn."
    (FraCandidates.ab (.creaturesYouControlPump 1 1) "Creatures you control get +1/+1 until end of turn")
    { mana := ⟨#[.generic 4, .colored .white]⟩ },
  ActivatedAbility.fra "{3}{U}{U}, Exile this card from your graveyard: Draw two cards."
    (FraCandidates.ab (.draw 2) "Draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{U}: Surveil 1." (FraCandidates.ab (.surveil 1) "Surveil 1")
    { mana := ⟨#[.generic 3, .colored .blue]⟩ },
  ActivatedAbility.fra "{U}, Sacrifice this creature: The next spell you cast this turn can't be countered."
    (FraCandidates.ab (.fra .nextSpellCantBeCountered) "The next spell you cast this turn can't be countered")
    { mana := ⟨#[.colored .blue]⟩, sacrificeSource := true },
  ActivatedAbility.fra "{2}: This creature gets +1/-1 until end of turn."
    (FraCandidates.ab (.onSource (.pump 1 (-1))) "This creature gets +1/-1 until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{3}{B}, Exile this card from your graveyard: Return another target creature card from your graveyard to your hand."
    (FraCandidates.ab (.fra .returnFromGyToHand) "Return another target creature card from your graveyard to your hand"
      (.filtered { noun := "another target creature card from your graveyard", zone := .yourGraveyard
                   types := #[.creature], another := true }))
    { mana := ⟨#[.generic 3, .colored .black]⟩, exileSourceFromGraveyard := true }
    (activateFromGraveyard := true),
  ActivatedAbility.fra "{T}, Discard a card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { tap := true, discardACard := true },
  ActivatedAbility.fra
    "{3}{R}: Exile target creature or planeswalker you control. Reveal cards from the top of your library until you reveal a creature or planeswalker card. Put that card onto the battlefield and the rest on the bottom of your library in a random order. Activate only as a sorcery."
    (FraCandidates.ab (.fra .identityEcho) "Exile target creature or planeswalker you control"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "target creature or planeswalker you control", controller := .you }))
    { mana := ⟨#[.generic 3, .colored .red]⟩ } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "Sacrifice this creature: Destroy target artifact or enchantment. If that permanent was a legendary enchantment, draw a card. Activate only as a sorcery."
    (FraCandidates.ab (.fra .destroyDrawIfLegendaryEnchantment) "Destroy target artifact or enchantment"
      (.filtered { noun := "target artifact or enchantment", types := #[.artifact, .enchantment] }))
    { sacrificeSource := true } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{1}, Sacrifice another artifact: Put a +1/+1 counter on this creature. It gains your choice of trample, hexproof, or haste until end of turn."
    (FraCandidates.ab (.sequence [.fra (.plusOneOnSource 1), .fra (.chooseKeyword [0, 1, 2])]) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 1, fra := .sacrificeAnotherArtifact },
  ActivatedAbility.fra "{4}{G}: Return this card from your graveyard to your hand."
    (FraCandidates.ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 4, .colored .green]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{3}{G}, Discard this card: Destroy target creature with flying."
    (FraCandidates.ab (.fra .destroy) "Destroy target creature with flying"
      (.filtered { TargetFilter.creature with noun := "target creature with flying", withFlying := true }))
    { mana := ⟨#[.generic 3, .colored .green]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{6}{G}{G}: This creature gets +4/+4 and gains trample until end of turn."
    (FraCandidates.ab (.onSource (.pumpAndTrample 4 4)) "This creature gets +4/+4 and gains trample until end of turn")
    { mana := ⟨#[.generic 6, .colored .green, .colored .green]⟩ },
  ActivatedAbility.fra
    "{6}: Create a Heartwood token. Then this creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab (.sequence [.createTokens .heartwood 1, .fra .sourceGetsPowerPerArtifact])
      "Create a Heartwood token")
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{2}{W/B}: Return this card from your graveyard to your hand."
    (FraCandidates.ab .returnFromGraveyardToHand "Return this card from your graveyard to your hand")
    { mana := ⟨#[.generic 2, .hybrid .white .black]⟩ } (activateFromGraveyard := true),
  ActivatedAbility.fra "{4}{G}{W}: Target creature gains trample and lifelink until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords (Keyword.trample.merge Keyword.lifelink)))
      "Target creature gains trample and lifelink until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 4, .colored .green, .colored .white]⟩ },
  ActivatedAbility.fra
    "{4}: Create a 2/2 colorless Wizard Soldier creature token named Cadet. Then creatures you control gain haste until end of turn."
    (FraCandidates.ab (.sequence [.createTokens .cadet 1, .teamGain Keyword.haste]) "Create a Cadet")
    { mana := ManaCost.ofGeneric 4 },
  ActivatedAbility.fra "{2}: Put target card from your graveyard on the bottom of your library."
    (FraCandidates.ab (.fra .graveyardCardToLibraryBottom) "Put target card from your graveyard on the bottom of your library"
      (.filtered { noun := "target card from your graveyard", zone := .yourGraveyard }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{W}{U}: Return this card from your graveyard to the battlefield with a finality counter on it. Activate only if you've scried or surveilled this turn."
    (FraCandidates.ab .returnFromGyWithFinality "Return this card from your graveyard to the battlefield with a finality counter on it")
    { mana := ⟨#[.colored .white, .colored .blue]⟩ } (activateFromGraveyard := true)
    (cond := .scriedOrSurveilledThisTurn),
  ActivatedAbility.fra "{1}, {T}, Discard a legendary card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 1, tap := true, fra := .discardLegendaryCard },
  ActivatedAbility.fra "Tap two untapped artifacts you control: Put two +1/+1 counters on this creature."
    (FraCandidates.ab (.onSource (.plusOne 2)) "Put two +1/+1 counters on this creature")
    { fra := .tapTwoUntappedArtifacts },
  { ActivatedAbility.fra
      "Equip {3}. This ability costs {1} less to activate for each +1/+1 counter on the creature it targets."
      Effect.attachToTargetCreatureYouControl { mana := ManaCost.ofGeneric 3 } (onlyAsSorcery := true)
    with costLessPerPlusOneOnTarget := true },
  ActivatedAbility.fra "{2}: This creature gains flying until end of turn."
    (FraCandidates.ab (.onSource (.grantKeywords Keyword.flying)) "This creature gains flying until end of turn")
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra "{5}, {T}, Exile this artifact: Destroy all creatures. Activate only as a sorcery."
    (FraCandidates.ab (.fra .destroyAllCreatures) "Destroy all creatures")
    { mana := ManaCost.ofGeneric 5, tap := true, fra := .exileSource } (onlyAsSorcery := true),
  ActivatedAbility.fra
    "{6}, Sacrifice this creature: Choose target creature or planeswalker an opponent controls. Its owner shuffles it into their library."
    (FraCandidates.ab (.fra .ownerShufflesIntoLibrary) "Its owner shuffles it into their library"
      (.filtered TargetFilter.oppCreatureOrPlaneswalker))
    { mana := ManaCost.ofGeneric 6, sacrificeSource := true },
  ActivatedAbility.fra "{2}, {T}, Discard a card: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, discardACard := true },
  ActivatedAbility.fra
    "{2}, {T}: Target creature that attacked this turn becomes prepared. Activate only as a sorcery."
    (FraCandidates.ab (.onPermanent .becomePrepared) "Target creature that attacked this turn becomes prepared"
      (.filtered { TargetFilter.creature with noun := "target creature that attacked this turn", attackedThisTurn := true }))
    { mana := ManaCost.ofGeneric 2, tap := true } (onlyAsSorcery := true),
  ActivatedAbility.fra "{1}{W}, Discard this card: It deals 4 damage to target attacking or blocking creature."
    (FraCandidates.ab (.onPermanent (.dealDamage 4)) "It deals 4 damage to target attacking or blocking creature"
      (.filtered { TargetFilter.creature with noun := "target attacking or blocking creature", attackingOrBlocking := true }))
    { mana := ⟨#[.generic 1, .colored .white]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra
    "{1}, {T}, Discard a card: Another target creature or planeswalker you control gains hexproof until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords Keyword.hexproof)) "Another target creature or planeswalker you control gains hexproof until end of turn"
      (.filtered { TargetFilter.creatureOrPlaneswalker with
        noun := "another target creature or planeswalker you control", controller := .you, another := true }))
    { mana := ManaCost.ofGeneric 1, tap := true, discardACard := true },
  ActivatedAbility.fra "{T}: Return another target permanent you control to its owner's hand. Activate only during your turn."
    (FraCandidates.ab (.fra .bounce) "Return another target permanent you control to its owner's hand"
      (.filtered { noun := "another target permanent you control", controller := .you, another := true }))
    { tap := true } (onlyDuringYourTurn := true),
  ActivatedAbility.fra "{T}: Target creature with a +1/+1 counter on it gains flying until end of turn."
    (FraCandidates.ab (.onPermanent (.grantKeywords Keyword.flying)) "Target creature with a +1/+1 counter on it gains flying until end of turn"
      (.filtered { TargetFilter.creature with noun := "target creature with a +1/+1 counter on it", withPlusOneCounter := true }))
    { tap := true },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target legendary creature."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target legendary creature"
      (.filtered { TargetFilter.creature with noun := "target legendary creature", legendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{6}: Put a +1/+1 counter on target nonlegendary creature."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target nonlegendary creature"
      (.filtered { TargetFilter.creature with noun := "target nonlegendary creature", nonlegendary := true }))
    { mana := ManaCost.ofGeneric 6 },
  ActivatedAbility.fra "{T}: Draw a card, then discard a card."
    (FraCandidates.ab (.sequence [.draw 1, .discard 1]) "Draw a card, then discard a card") { tap := true },
  ActivatedAbility.fra "{2}{U}: Untap target creature."
    (FraCandidates.ab (.onPermanent .untap) "Untap target creature" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 2, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{3}{U}{U}: Until end of turn, whenever this creature deals combat damage to a player, draw two cards."
    (FraCandidates.ab (.fra .grantCombatDamageDrawTwo) "Until end of turn, whenever this creature deals combat damage to a player, draw two cards")
    { mana := ⟨#[.generic 3, .colored .blue, .colored .blue]⟩ },
  ActivatedAbility.fra
    "{4}{B}, Exile another creature card from your graveyard: Return this card from your graveyard to the battlefield tapped with a +1/+1 counter on her."
    (FraCandidates.ab (.fra (.returnSourceFromGy false true 1)) "Return this card from your graveyard to the battlefield tapped")
    { mana := ⟨#[.generic 4, .colored .black]⟩, fra := .exileAnotherCreatureCardFromGraveyard }
    (activateFromGraveyard := true),
  ActivatedAbility.fra
    "{5}{B}: Return target creature or planeswalker card from your graveyard to the battlefield. Put a +1/+1 counter on this creature. Activate only as a sorcery."
    (FraCandidates.ab
      (.sequence [.fra (.returnFromGyToBattlefield 0), .onSource (.plusOne 1)])
      "Return target creature or planeswalker card from your graveyard to the battlefield"
      (.filtered { noun := "target creature or planeswalker card from your graveyard", zone := .yourGraveyard
                   types := #[.creature, .planeswalker] }))
    { mana := ⟨#[.generic 5, .colored .black]⟩ } (onlyAsSorcery := true) (exhaust := true),
  ActivatedAbility.fra
    "Sacrifice another creature or planeswalker: This creature gets -2/-0 until end of turn. Activate only if there are seven or more cards in your graveyard."
    (FraCandidates.ab (.onSource (.pump (-2) 0)) "This creature gets -2/-0 until end of turn")
    { fra := .sacrificeAnotherCreatureOrPlaneswalker } (cond := .graveyardAtLeast 7),
  ActivatedAbility.fra "{B}, Discard this card: Target creature gets -3/-1 until end of turn."
    (FraCandidates.ab (.onPermanent (.pump (-3) (-1))) "Target creature gets -3/-1 until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.colored .black]⟩, discardSource := true } (activateFromHand := true),
  ActivatedAbility.fra "{1}{R}, {T}: Put a +1/+1 counter on target creature that entered this turn."
    (FraCandidates.ab (.onPermanent (.plusOne 1)) "Put a +1/+1 counter on target creature that entered this turn"
      (.filtered { TargetFilter.creature with noun := "target creature that entered this turn", enteredThisTurn := true }))
    { mana := ⟨#[.generic 1, .colored .red]⟩, tap := true },
  ActivatedAbility.fra "{8}: Create a 5/5 red Dragon creature token with flying."
    (FraCandidates.ab (.createTokens .dragon55flying 1) "Create a 5/5 red Dragon creature token with flying")
    { mana := ManaCost.ofGeneric 8 },
  ActivatedAbility.fra "{2}, {T}, Sacrifice an artifact or land: Draw a card." (FraCandidates.ab (.draw 1) "Draw a card")
    { mana := ManaCost.ofGeneric 2, tap := true, fra := .sacrificeArtifactOrLand },
  ActivatedAbility.fra
    "{5}{R}: Target creature gets +X/+0 until end of turn, where X is the number of artifacts you control."
    (FraCandidates.ab (.fra .pumpPerArtifact) "Target creature gets +X/+0 until end of turn" (.filtered TargetFilter.creature))
    { mana := ⟨#[.generic 5, .colored .red]⟩ },
  ActivatedAbility.fra "{4}{G}: Put a +1/+1 counter on each creature you control with a +1/+1 counter on it."
    (FraCandidates.ab (.fra .plusOneOnEachWithPlusOne) "Put a +1/+1 counter on each creature you control with a +1/+1 counter on it")
    { mana := ⟨#[.generic 4, .colored .green]⟩ },
  ActivatedAbility.fra "{2}: Return target land card from your graveyard to your hand."
    (FraCandidates.ab (.fra .returnFromGyToHand) "Return target land card from your graveyard to your hand"
      (.filtered { noun := "target land card from your graveyard", zone := .yourGraveyard, types := #[.land] }))
    { mana := ManaCost.ofGeneric 2 },
  ActivatedAbility.fra
    "{2}, Sacrifice another creature or planeswalker: Put a +1/+1 counter on this creature. He gains menace until end of turn."
    (FraCandidates.ab (.sequence [.onSource (.plusOne 1), .onSource (.grantKeywords Keyword.menace)]) "Put a +1/+1 counter on this creature")
    { mana := ManaCost.ofGeneric 2, fra := .sacrificeAnotherCreatureOrPlaneswalker },
]

def chapterEffects : Thunk (Array (String × Effect)) := Thunk.mk fun _ => #[
  ("This Saga deals 6 damage to target creature an opponent controls.", Effect.chapterDealDamageToOppCreature 6),
  ("Destroy target artifact an opponent controls.", Effect.chapterDestroyOppArtifact),
  ("Add {R}.", Effect.chapterAddMana (.colored .red)),
  ("Search your library for a basic land card, reveal it, put it into your hand, then shuffle.", Effect.chapterSearchBasicLandToHand),
  ("This Saga gains \"Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.\"", Effect.chapterGainLandfallCreateElf),
  ("Elves you control get +1/+0 and gain vigilance until end of turn.", Effect.chapterElvesGetVigilance 1),
  ("Target opponent reveals their hand. You choose a nonland card from it. That player discards that card.", Effect.chapterOpponentDiscardsNonland),
  ("Amass Goblins 1. (Put a +1/+1 counter on an Army you control. It's also a Goblin. If you don't control an Army, create a 0/0 black Goblin Army creature token first.)", Effect.chapterAmassGoblins 1),
  ("Target opponent loses 1 life and you gain 1 life.", Effect.chapterOpponentLosesYouGain 1),
  ("Target creature you control gains hexproof for as long as this Saga remains on the battlefield.", Effect.chapterGrantHexproofWhileRemains),
  ("Prevent all damage that would be dealt by up to one target creature for as long as this Saga remains on the battlefield.", Effect.chapterPreventDamageWhileRemains),
  ("Draw a card.", Effect.chapterDraw 1),
  ("Search your library for up to two basic Plains cards, exile them, then shuffle. You gain 2 life.", Effect.chapterSearchBasicPlainsExileGainLife 2 2),
  ("Put a card exiled with this Saga into its owner's hand.", Effect.chapterReturnLinkedExileToHand),
  ("Whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each Plains you control.", Effect.chapterGrantAttackPumpPerPlainsThisTurn),
  ("Exile up to one target creature or land you control. If you do, return it to the battlefield under its owner's control at the beginning of the next end step.", Effect.chapterBlinkUntilEndStep),
  ("Create a Treasure token. Then if you control four or more Treasures, sacrifice this Saga. If you do, create a 6/6 red Dragon creature token with flying. (A Treasure token is an artifact with \"{T}, Sacrifice this token: Add one mana of any color.\")", Effect.chapterTreasureThenDragonIfFour),
  ("Recruit. (Draw a card, then discard a card. If you discarded a nonland card, create a 1/1 white Human Soldier creature token.)", Effect.chapterRecruit),
  ("Return target creature card with mana value 3 or less from your graveyard to the battlefield.", Effect.chapterReturnCreatureFromGyMvAtMost 3),
  ("Put a +1/+1 counter on up to one target creature.", Effect.chapterPlusOneUpToOne),
  ("Scry 2.", Effect.scry 2),
  ("You may put a Hero creature card with mana value 3 or less from your hand onto the battlefield. If you don't, draw a card.", Effect.mayPutHeroMvOrDraw 3),
  ("Put a +1/+1 counter on each creature you control.", Effect.plusOneOnEachYouControl),
  ("The next red or green creature spell you cast this turn can be cast without paying its mana cost.", Effect.nextFreeRGCreature),
  ("Put three +1/+1 counters on target creature you control.", Effect.plusOneOnCreatureN 3),
  ("Choose target creature you control. Until end of turn, double its power and toughness and it gains trample.", Effect.chooseTargetDoubleAndTrample),
  ("You may draw a card for each artifact you control. If you do, each opponent draws a card.", Effect.mayDrawPerArtifactOppsDraw),
  ("Artifact spells you cast this turn cost {1} less to cast.", Effect.artifactSpellsCostLessThisTurn 1),
  ("This Saga deals X damage to target opponent, where X is the greatest mana value among artifacts you control.", Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv),
  ("Create two 2/1 black Villain creature tokens with menace.", Effect.createTokens .villain21menace 2),
  ("This Saga deals 2 damage to each non-Villain creature and each opponent.", Effect.chapterDealDamageToEachNonSubtypeAndOpponents 2 "Villain"),
  ("Create a Treasure token for each Villain you control.", Effect.createTokensPerSubtype .treasure "Villain"),
  ("Destroy up to one target nonland permanent.", Effect.destroyUpToOneNonland),
  ("Each opponent loses 2 life.", Effect.eachOpponentLosesLife 2),
  ("Create Galactus, a legendary 16/16 black Elder Alien creature token with flying, trample, and \"Whenever Galactus attacks, destroy target land.\".", Effect.createGalactus),
  ("Gain control of up to two target creatures with total mana value 6 or less for as long as this Saga remains on the battlefield.", Effect.chapterGainControlOfUpToTwoCreaturesTotalMvAtMost 6),
  ("Creatures you control get +1/+1 and gain vigilance until end of turn.", Effect.creaturesYouControlGetAndGrant 1 1 Keyword.vigilance),
  ("Target creature you control fights up to one other target creature.", Effect.fightUpToOne),
]

end Mtg.Engine.OracleCandidates
