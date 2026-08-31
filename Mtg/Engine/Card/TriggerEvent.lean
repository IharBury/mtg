import Mtg.Engine.Color
import Mtg.Engine.Card.Text

/-!
# Trigger events (CR 603)

When a triggered ability fires, with per-event clause wording and metadata.
-/

namespace Mtg.Engine

/-- When a triggered ability fires (CR 603). Several printed abilities share
an event (`scry` on attack, enter, or attack-with-Elves); “enters or attacks”
is two events. -/
inductive TriggerEvent where
  /-- This creature is declared as an attacker (CR 508.2). -/
  | attacking
  /-- This creature becomes blocked (CR 509.5c). -/
  | becomesBlocked
  /-- This permanent enters the battlefield (CR 603.6a). -/
  | entering
  /-- A land the controller controls enters (landfall). -/
  | landYouControlEnters
  /-- This creature dies (CR 700.4 / 603.6c). -/
  | dying
  /-- You cast an instant or sorcery (CR 601.2i). -/
  | youCastInstantOrSorcery
  /-- You attack with one or more Elves (CR 508.2 / 603.2a). -/
  | youAttackWithElves
  /-- You scry (CR 701.20 / 603.2). -/
  | youScry
  /-- Another Elf you control enters (CR 603.6a). -/
  | anotherElfYouControlEnters
  /-- One or more other creatures die (CR 700.4 / 603.2a). -/
  | oneOrMoreOtherCreaturesDie
  /-- This permanent leaves the battlefield (CR 603.6c). -/
  | leaving
  /-- You draw a card (CR 121 / 603.2). -/
  | youDraw
  /-- You draw your second card this turn. -/
  | youDrawSecondCard
  /-- Two or more creatures you control attack a player. -/
  | youAttackWithTwoOrMore
  /-- This creature deals combat damage to a player (CR 510.2 / 603.2). -/
  | dealsCombatDamageToPlayer
  /-- The beginning of your end step (CR 513.1 / 603.1). -/
  | yourEndStep
  /-- Another creature you control enters (CR 603.6a). -/
  | anotherCreatureYouControlEnters
  /-- The beginning of combat on your turn (CR 507.1 / 603.1). -/
  | yourBeginCombat
  /-- You attack with one or more creatures (CR 508.2). -/
  | youAttack
  /-- You cast a noncreature spell (CR 601.2i / 603.3). -/
  | youCastNoncreature
  /-- The beginning of your upkeep (CR 503.1 / 603.1). -/
  | yourUpkeep
  /-- An artifact you control enters (CR 603.6a). -/
  | artifactYouControlEnters
  /-- An opponent casts their first noncreature spell this turn. -/
  | opponentCastsFirstNoncreature
  /-- A player casts their second spell this turn. -/
  | anyPlayerCastsSecondSpell
  /-- The beginning of your first main phase. -/
  | yourFirstMain
  /-- This or another nontoken permanent of a listed subtype you control
  enters. The subtype is stored on the triggered ability. -/
  | thisOrNontokenSubtypeYouControlEnters
  /-- This becomes the target of a spell or ability an opponent controls. -/
  | becomesTarget
  /-- The beginning of each end step. -/
  | eachEndStep
  /-- The beginning of each combat. -/
  | eachBeginCombat
  /-- You cast a green spell. -/
  | youCastGreen
  /-- A Forest you control enters. -/
  | forestYouControlEnters
  /-- Another permanent of a listed subtype or an Equipment you control enters. -/
  | anotherSubtypeOrEquipmentYouControlEnters
  /-- You cast a spell that had Treasure mana spent. -/
  | youCastWithTreasure
  /-- This or another permanent of a listed subtype you control enters. -/
  | thisOrAnotherSubtypeYouControlEnters
  /-- This deals combat damage to a player or battle. -/
  | dealsCombatDamageToPlayerOrBattle
  /-- The Ring tempts you. -/
  | theRingTemptsYou
  /-- You choose a creature as your Ring-bearer. -/
  | youChooseRingBearer
  /-- Equipped creature is the only attacker declared this combat. -/
  | equippedAttacksAlone
  /-- A token you control enters (CR 603.6a). -/
  | tokenYouControlEnters
  /-- You activate an ability of a creature, including a mana ability
  (CR 605.3b / 603.2). -/
  | youActivateCreatureAbility
  /-- Equipped creature attacks (CR 508.2). -/
  | equippedAttacks
  /-- An opponent draws a card that is not the first card of their draw step. -/
  | opponentDrawsExceptFirstDrawStep
  /-- An opponent draws their second card this turn. -/
  | opponentDrawsSecondCard
  /-- You attack with creatures whose total power meets a threshold. -/
  | youAttackWithTotalPower
  /-- Delayed trigger: create Bird Soldiers at the next upkeep. -/
  | eaglesCreateBirds
  /-- You sacrificed a creature to Bolg's enters instruction. -/
  | bolgSacrificedForReflexive
  /-- You cast a spell of this color. -/
  | youCastColor (color : Color)
  /-- An opponent casts a spell whose mana value matches a chosen odd/even. -/
  | opponentCastsMatchingParity
  /-- A creature card leaves your graveyard. -/
  | creatureCardLeavesYourGy
  /-- You cast a creature spell. -/
  | youCastCreature
  /-- A Mountain you control enters. -/
  | mountainYouControlEnters
  /-- This was dealt noncombat damage. -/
  | sourceDealtNoncombatDamage
  /-- An opponent casts a spell. -/
  | opponentCastsSpell
  /-- An Army you control deals combat damage to a player. -/
  | armyYouControlCombatDamage
  /-- A lore counter was put on this Saga (CR 714.3). -/
  | sagaChapter
  /-- The final chapter of a Saga you control resolves. -/
  | finalSagaChapterResolves
  /-- One or more creatures deal combat damage to you. -/
  | combatDamageToYou
  /-- You cast your second spell this turn. -/
  | youCastSecondSpell
  /-- You sacrifice a token. -/
  | youSacrificeToken
  /-- A player loses life. -/
  | playerLosesLife
  /-- You put one or more counters on a Goblin, Orc, or Army you control. -/
  | youPutCountersOnGoblinOrcArmy
  /-- Another Goblin, Orc, or Army you control dies. -/
  | anotherGoblinOrcArmyDies
  /-- A nontoken creature you control dies. -/
  | nontokenYouControlDies
  /-- Equipped creature deals combat damage to a player. -/
  | equippedDealsCombatDamageToPlayer
  /-- A creature you control is the only attacker declared this combat. -/
  | creatureYouControlAttacksAlone
  /-- This permanent became tapped to pay a teamwork cost. -/
  | tappedForTeamwork
  /-- A creature you control enters. -/
  | creatureYouControlEnters
  /-- A permanent you control of this subtype enters. -/
  | subtypeYouControlEnters (subtype : String)
  /-- One or more creatures you control become tapped. -/
  | creaturesYouControlBecomeTapped
  /-- One or more creature cards are put into your graveyard from anywhere. -/
  | creatureCardsPutIntoYourGy
  /-- You cast a spell of this color from your hand. -/
  | youCastColorFromHand (color : Color)
  /-- This permanent was dealt damage. -/
  | sourceDealtDamage
  /-- The `n`th plan counter was put on this enchantment. -/
  | nthPlanCounter (n : Nat)
  /-- You cast a Villain spell. -/
  | youCastVillain
  /-- You cast a spell that targets a creature you control. -/
  | youCastTargetingCreatureYouControl
  /-- You cast a spell. -/
  | youCastSpell
  /-- You discard a card. -/
  | youDiscard
  /-- You put a +1/+1 counter on a creature. -/
  | youPutPlusOne
  /-- You gain life. -/
  | youGainLife
  /-- A player draws their second card this turn. -/
  | anyPlayerDrawsSecond
  /-- A spell targets this permanent. -/
  | spellTargetsSource
  /-- A player or permanent becomes the target of an ability you control. -/
  | youTargetSomething
  /-- An Equipment you control enters. -/
  | equipmentYouControlEnters
  /-- Another Villain or artifact you control enters. -/
  | anotherVillainOrArtifactEnters
  /-- Another Villain you control enters. -/
  | anotherVillainEnters
  /-- Another artifact you control enters. -/
  | anotherArtifactEnters
  /-- Another nontoken Hero you control enters. -/
  | anotherNontokenHeroEnters
  /-- Another nontoken artifact you control enters. -/
  | anotherNontokenArtifactEnters
  /-- Another nonland permanent you control is returned to hand. -/
  | anotherNonlandReturned
  /-- A Villain you control dies. -/
  | villainYouControlDies
  /-- An attacking creature you control dies. -/
  | attackingCreatureYouControlDies
  /-- An equipped creature you control attacks. -/
  | equippedCreatureYouControlAttacks
  /-- Enchanted creature attacks or blocks. -/
  | enchantedAttacksOrBlocks
  /-- A creature you control becomes tapped during your turn. -/
  | creatureYouControlTapped
  /-- A creature you control is dealt damage. -/
  | creatureYouControlDealtDamage
  /-- One or more Heroes you control deal damage to a player. -/
  | heroesDealDamageToPlayer
  /-- One or more Merfolk you control attack a player. -/
  | merfolkAttackPlayer
  /-- The upkeep of the enchanted creature's controller. -/
  | enchantedControllerUpkeep
  /-- This permanent becomes tapped. -/
  | sourceBecomesTapped
  /-- Equipped creature becomes tapped. -/
  | equippedBecomesTapped
deriving Repr, Inhabited, BEq, DecidableEq

namespace TriggerEvent

/-- Oracle wording plus how Game queues this event. Exhaustive so a new event
is a compile error here rather than silently matching `When this occurs` with
`Whenever`, or restating the stack label and CR 603.3d check at every queue
site. -/
structure Spec where
  clause : String
  isWhenever : Bool := true
  /-- Log label when this event is put on the stack. -/
  label : String
  /-- Remove the ability when it requires a target and has none (CR 603.3d). -/
  checkTargets : Bool := true
  /-- Trigger condition is another ability triggering (CR 603.3b part 2). -/
  isAnotherAbilityTriggering : Bool := false
deriving Repr, Inhabited, BEq

/-- Classification of this event. `clause`, `isWhenever`, `label`, and
`checkTargets` read this table. -/
def spec : TriggerEvent → Spec
  | .attacking =>
    { clause := "this creature attacks", label := "attack trigger" }
  | .becomesBlocked =>
    { clause := "this creature becomes blocked", label := "becomes-blocked trigger",
      checkTargets := false }
  | .entering =>
    { clause := "this permanent enters", isWhenever := false, label := "enters trigger" }
  | .landYouControlEnters =>
    { clause := "a land you control enters", label := "landfall trigger" }
  | .dying =>
    { clause := "this creature dies", isWhenever := false, label := "dies trigger" }
  | .youCastInstantOrSorcery =>
    { clause := "you cast an instant or sorcery spell", label := "cast trigger",
      checkTargets := false }
  | .youAttackWithElves =>
    { clause := "you attack with one or more Elves", label := "attack trigger",
      checkTargets := false }
  | .youScry =>
    { clause := "you scry", label := "scry trigger", checkTargets := false }
  | .anotherElfYouControlEnters =>
    { clause := "another Elf you control enters", label := "Elf-enters trigger",
      checkTargets := false }
  | .oneOrMoreOtherCreaturesDie =>
    { clause := "one or more other creatures die", label := "other-creatures-die trigger",
      checkTargets := false }
  | .leaving =>
    { clause := "this creature leaves the battlefield", isWhenever := false,
      label := "leaves trigger", checkTargets := false }
  | .youDraw =>
    { clause := "you draw a card", label := "draw trigger", checkTargets := false }
  | .youDrawSecondCard =>
    { clause := "you draw your second card each turn", label := "second-card trigger",
      checkTargets := false }
  | .youAttackWithTwoOrMore =>
    { clause := "two or more creatures you control attack a player",
      label := "attack trigger" }
  | .dealsCombatDamageToPlayer =>
    { clause := "this deals combat damage to a player", label := "combat-damage trigger",
      checkTargets := false }
  | .yourEndStep =>
    { clause := "the beginning of your end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .anotherCreatureYouControlEnters =>
    { clause := "another creature you control enters", label := "creature-enters trigger",
      checkTargets := false }
  | .yourBeginCombat =>
    { clause := "the beginning of combat on your turn", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youAttack =>
    { clause := "you attack", label := "attack trigger", checkTargets := false }
  | .youCastNoncreature =>
    { clause := "you cast a noncreature spell", label := "cast trigger",
      checkTargets := false }
  | .yourUpkeep =>
    { clause := "the beginning of your upkeep", isWhenever := false,
      label := "upkeep trigger", checkTargets := false }
  | .artifactYouControlEnters =>
    { clause := "an artifact you control enters", label := "artifact-enters trigger",
      checkTargets := false }
  | .opponentCastsFirstNoncreature =>
    { clause := "an opponent casts their first noncreature spell each turn",
      label := "opponent-cast trigger", checkTargets := false }
  | .anyPlayerCastsSecondSpell =>
    { clause := "a player casts their second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .yourFirstMain =>
    { clause := "the beginning of your first main phase", isWhenever := false,
      label := "main-phase trigger", checkTargets := false }
  | .thisOrNontokenSubtypeYouControlEnters =>
    { clause := "this or another nontoken creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .becomesTarget =>
    { clause := "this creature becomes the target of a spell or ability an opponent controls",
      label := "becomes-target trigger", checkTargets := false }
  | .eachEndStep =>
    { clause := "the beginning of each end step", isWhenever := false,
      label := "end-step trigger", checkTargets := false }
  | .eachBeginCombat =>
    { clause := "the beginning of each combat", isWhenever := false,
      label := "begin-combat trigger", checkTargets := false }
  | .youCastGreen =>
    { clause := "you cast a green spell", label := "cast trigger" }
  | .forestYouControlEnters =>
    { clause := "a Forest you control enters", label := "forest-enters trigger" }
  | .anotherSubtypeOrEquipmentYouControlEnters =>
    { clause := "another Dwarf or Equipment you control enters",
      label := "dwarf-or-equipment trigger", checkTargets := false }
  | .youCastWithTreasure =>
    { clause := "you cast a spell, if mana from a Treasure was spent to cast it",
      label := "treasure-cast trigger", checkTargets := false }
  | .thisOrAnotherSubtypeYouControlEnters =>
    { clause := "this or another creature you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .dealsCombatDamageToPlayerOrBattle =>
    { clause := "this deals combat damage to a player or battle",
      label := "combat-damage trigger" }
  | .theRingTemptsYou =>
    { clause := "the Ring tempts you", label := "Ring-tempts trigger",
      checkTargets := false }
  | .youChooseRingBearer =>
    { clause := "you choose a creature as your Ring-bearer",
      label := "Ring-bearer trigger", checkTargets := false }
  | .equippedAttacksAlone =>
    { clause := "equipped creature attacks alone",
      label := "attacks-alone trigger", checkTargets := false }
  | .tokenYouControlEnters =>
    { clause := "a token you control enters", label := "token-enters trigger",
      checkTargets := false }
  | .youActivateCreatureAbility =>
    { clause := "you activate an ability of a creature",
      label := "activate-creature trigger", checkTargets := false }
  | .equippedAttacks =>
    { clause := "equipped creature attacks",
      label := "equipped-attacks trigger", checkTargets := false }
  | .opponentDrawsExceptFirstDrawStep =>
    { clause := "an opponent draws a card except the first one they draw in each of their draw steps",
      label := "opponent-draw trigger" }
  | .opponentDrawsSecondCard =>
    { clause := "an opponent draws their second card each turn",
      label := "opponent-second-card trigger", checkTargets := false }
  | .youAttackWithTotalPower =>
    { clause := "you attack with creatures with total power 12 or greater",
      label := "total-power-attack trigger", checkTargets := false }
  | .eaglesCreateBirds =>
    { clause := "the beginning of the next upkeep", isWhenever := false,
      label := "delayed Bird Soldier trigger", checkTargets := false }
  | .bolgSacrificedForReflexive =>
    { clause := "you sacrifice a creature this way", isWhenever := false,
      label := "reflexive trigger" }
  | .youCastColor c =>
    { clause := s!"you cast a {c} spell", label := "cast-color trigger",
      checkTargets := false }
  | .opponentCastsMatchingParity =>
    { clause := "an opponent casts a spell with mana value of the chosen quality",
      label := "parity-cast trigger", checkTargets := false }
  | .creatureCardLeavesYourGy =>
    { clause := "a creature card leaves your graveyard",
      label := "leaves-graveyard trigger", checkTargets := false }
  | .youCastCreature =>
    { clause := "you cast a creature spell", label := "cast-creature trigger" }
  | .mountainYouControlEnters =>
    { clause := "a Mountain you control enters", label := "mountain-enters trigger" }
  | .sourceDealtNoncombatDamage =>
    { clause := "this is dealt noncombat damage",
      label := "noncombat-damage trigger", checkTargets := false }
  | .opponentCastsSpell =>
    { clause := "an opponent casts a spell", label := "opponent-cast trigger",
      checkTargets := false }
  | .armyYouControlCombatDamage =>
    { clause := "an Army you control deals combat damage to a player",
      label := "army-combat-damage trigger", checkTargets := false }
  | .sagaChapter =>
    { clause := "a lore counter is put on this Saga", isWhenever := false,
      label := "saga chapter", checkTargets := true }
  | .finalSagaChapterResolves =>
    { clause := "the final chapter ability of a Saga you control resolves",
      label := "saga-chapter trigger", checkTargets := false }
  | .combatDamageToYou =>
    { clause := "one or more creatures deal combat damage to you",
      label := "combat-damage-to-you trigger", checkTargets := false }
  | .youCastSecondSpell =>
    { clause := "you cast your second spell each turn",
      label := "second-spell trigger", checkTargets := false }
  | .youSacrificeToken =>
    { clause := "you sacrifice a token", label := "sacrifice-token trigger" }
  | .playerLosesLife =>
    { clause := "a player loses life", label := "lose-life trigger",
      checkTargets := false }
  | .youPutCountersOnGoblinOrcArmy =>
    { clause := "you put one or more counters on a Goblin, Orc, or Army you control",
      label := "put-counters trigger" }
  | .anotherGoblinOrcArmyDies =>
    { clause := "another Goblin, Orc, or Army you control dies",
      label := "army-dies trigger", checkTargets := false }
  | .nontokenYouControlDies =>
    { clause := "a nontoken creature you control dies",
      label := "nontoken-dies trigger", checkTargets := false }
  | .equippedDealsCombatDamageToPlayer =>
    { clause := "equipped creature deals combat damage to a player",
      label := "equipped-combat-damage trigger", checkTargets := false }
  | .creatureYouControlAttacksAlone =>
    { clause := "a creature you control attacks alone",
      label := "attacks-alone trigger" }
  | .tappedForTeamwork =>
    { clause := "this becomes tapped to pay a teamwork cost",
      label := "teamwork-tap trigger", checkTargets := false }
  | .creatureYouControlEnters =>
    { clause := "a creature you control enters",
      label := "creature-enters trigger", checkTargets := false }
  | .subtypeYouControlEnters subtype =>
    { clause := s!"a {subtype} you control enters",
      label := "subtype-enters trigger", checkTargets := false }
  | .creaturesYouControlBecomeTapped =>
    { clause := "one or more creatures you control become tapped",
      label := "tap trigger", checkTargets := false }
  | .creatureCardsPutIntoYourGy =>
    { clause := "one or more creature cards are put into your graveyard from anywhere",
      label := "graveyard trigger", checkTargets := false }
  | .youCastColorFromHand color =>
    { clause := s!"you cast a {color.englishName} spell from your hand",
      label := "cast trigger", checkTargets := false }
  | .sourceDealtDamage =>
    { clause := "this is dealt damage",
      label := "dealt-damage trigger", checkTargets := false }
  | .nthPlanCounter n =>
    let ord :=
      match n with
      | 1 => "first" | 2 => "second" | 3 => "third" | 4 => "fourth"
      | 5 => "fifth" | 6 => "sixth" | 7 => "seventh" | 8 => "eighth"
      | _ => s!"{n}th"
    { clause := s!"the {ord} plan counter is put on this enchantment",
      isWhenever := false, label := "plan trigger" }
  | .youCastVillain =>
    { clause := "you cast a Villain spell", label := "cast trigger",
      checkTargets := false }
  | .youCastTargetingCreatureYouControl =>
    { clause := "you cast a spell that targets a creature you control",
      label := "cast trigger", checkTargets := false }
  | .youCastSpell =>
    { clause := "you cast a spell", label := "cast trigger", checkTargets := false }
  | .youDiscard =>
    { clause := "you discard a card", label := "discard trigger", checkTargets := false }
  | .youPutPlusOne =>
    { clause := "you put a +1/+1 counter on a creature",
      label := "counter trigger", checkTargets := false }
  | .youGainLife =>
    { clause := "you gain life", label := "gain-life trigger", checkTargets := false }
  | .anyPlayerDrawsSecond =>
    { clause := "a player draws their second card each turn",
      label := "second-card trigger", checkTargets := false }
  | .spellTargetsSource =>
    { clause := "a player casts a spell that targets this",
      label := "becomes-target trigger", checkTargets := false }
  | .youTargetSomething =>
    { clause := "a player or permanent becomes the target of an ability you control",
      label := "you-target trigger", checkTargets := false }
  | .equipmentYouControlEnters =>
    { clause := "an Equipment you control enters",
      label := "equipment-enters trigger", checkTargets := false }
  | .anotherVillainOrArtifactEnters =>
    { clause := "another Villain and/or artifact you control enters",
      label := "villain-or-artifact trigger", checkTargets := false }
  | .anotherVillainEnters =>
    { clause := "another Villain you control enters",
      label := "villain-enters trigger", checkTargets := false }
  | .anotherArtifactEnters =>
    { clause := "another artifact you control enters",
      label := "artifact-enters trigger", checkTargets := false }
  | .anotherNontokenHeroEnters =>
    { clause := "another nontoken Hero you control enters",
      label := "hero-enters trigger", checkTargets := false }
  | .anotherNontokenArtifactEnters =>
    { clause := "another nontoken artifact you control enters",
      label := "artifact-enters trigger", checkTargets := false }
  | .anotherNonlandReturned =>
    { clause := "another nonland permanent you control is returned to its owner's hand",
      label := "return trigger", checkTargets := false }
  | .villainYouControlDies =>
    { clause := "a Villain you control dies",
      label := "villain-dies trigger", checkTargets := false }
  | .attackingCreatureYouControlDies =>
    { clause := "an attacking creature you control dies",
      label := "attacker-dies trigger", checkTargets := false }
  | .equippedCreatureYouControlAttacks =>
    { clause := "an equipped creature you control attacks",
      label := "equipped-attacks trigger", checkTargets := false }
  | .enchantedAttacksOrBlocks =>
    { clause := "enchanted creature attacks or blocks",
      label := "enchanted-combat trigger", checkTargets := false }
  | .creatureYouControlTapped =>
    { clause := "a creature you control becomes tapped during your turn",
      label := "tap trigger", checkTargets := false }
  | .creatureYouControlDealtDamage =>
    { clause := "a creature you control is dealt damage",
      label := "dealt-damage trigger", checkTargets := false }
  | .heroesDealDamageToPlayer =>
    { clause := "one or more Heroes you control deal damage to a player",
      label := "hero-damage trigger", checkTargets := false }
  | .merfolkAttackPlayer =>
    { clause := "one or more Merfolk you control attack a player",
      label := "merfolk-attack trigger", checkTargets := false }
  | .enchantedControllerUpkeep =>
    { clause := "the beginning of the upkeep of enchanted creature's controller",
      isWhenever := false, label := "enchanted-upkeep trigger", checkTargets := false }
  | .sourceBecomesTapped =>
    { clause := "this becomes tapped", label := "becomes-tapped trigger",
      checkTargets := false }
  | .equippedBecomesTapped =>
    { clause := "equipped creature becomes tapped", label := "equipped-tapped trigger",
      checkTargets := false }

/-- Oracle “when/whenever” clause after the leading word. -/
def clause (e : TriggerEvent) : String :=
  e.spec.clause

/-- `Whenever` rather than one-shot `When` (enters / dies). -/
def isWhenever (e : TriggerEvent) : Bool :=
  e.spec.isWhenever

/-- Log label when this event is put on the stack. -/
def label (e : TriggerEvent) : String :=
  e.spec.label

/-- True when Game removes this trigger for lack of a legal target (CR 603.3d). -/
def checkTargets (e : TriggerEvent) : Bool :=
  e.spec.checkTargets

/-- True when this event is “another ability triggering” (CR 603.3b part 2). -/
def isAnotherAbilityTriggering (e : TriggerEvent) : Bool :=
  e.spec.isAnotherAbilityTriggering

end TriggerEvent

end Mtg.Engine
