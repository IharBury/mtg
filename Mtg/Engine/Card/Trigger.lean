import Mtg.Engine.Card.Counter
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.TriggerEvent

/-!
# Triggered-ability core (CR 603)

The unified `TriggeredAbility` carrier plus its stack/resolution metadata
(`TriggerTiming`) and the reusable `SharedTrigger` (`Effect`) constructors.
`TriggerResolution` names `Resolution`.
-/

namespace Mtg.Engine

/-- Who `SharedTrigger.connive` makes connive. -/
inductive ConniveSubject where
  /-- The trigger's source. -/
  | source
  /-- The announced target of this kind. -/
  | target (kind : EffectTargetKind)
  /-- The Villain that caused this trigger. You may have it connive.
  Already chosen this turn does nothing. A Villain that will not connive
  is reported. -/
  | enteringVillain
deriving Repr, Inhabited, BEq

/-- An intervening “if” or trigger condition (CR 603.2 / 603.4). -/
inductive InterveningCondition where
  /-- “while you control a creature with power ≥ n” (e.g. Ferocious). -/
  | youControlCreatureWithPower (n : Int)
  /-- “if you gained `n` or more life this turn”. -/
  | gainedLifeAtLeast (n : Nat)
  /-- “another creature you control with power ≤ n”. -/
  | anotherCreaturePowerAtMost (n : Int)
  | none
  /-- “if it isn't a token” (the source, as it last existed). -/
  | sourceNotToken
  /-- “if two or more creatures died this turn”. -/
  | twoCreaturesDiedThisTurn
  /-- “if an opponent was dealt noncombat damage last turn”. -/
  | opponentDealtNoncombatDamageLastTurn
  /-- “if you've drawn three or more cards this turn”. -/
  | drewThreeThisTurn
  /-- “if you didn't cast a spell this turn”. -/
  | castNoSpellThisTurn
  /-- “if you've activated a loyalty ability this turn”. -/
  | activatedLoyaltyThisTurn
  /-- “if you cast it”. -/
  | sourceWasCast
  /-- “if it had counters on it” (the object that caused the trigger). -/
  | causeHadCounters
  /-- “if this has counters on it”. -/
  | sourceHasCounters
deriving Repr, Inhabited, BEq, DecidableEq

/-- Backward-compatible alias for `InterveningCondition` (CR 603.4). -/
abbrev FraCondition := InterveningCondition

/-- Optional intervening conditions and wording filters for `triggered` (CR 603). -/
structure SharedTriggerOpts where
  onceEachTurn : Bool := false
  /-- Intervening or event-threshold condition (CR 603.2 / 603.4). -/
  condition : InterveningCondition := .none
  /-- Subtype filter watched by the trigger event. -/
  subtype : Option String := none
  allowsZeroTargets : Bool := false
  /-- Drop targeting from the shared effect (e.g. Guttersnipe). -/
  untargeted : Bool := false
  /-- The ability's printed sentence, when its wording isn't built from the
  event and resolution (Reality Fracture). -/
  printed : String := ""
  /-- The other permanent must be legendary (“another legendary Elf”). -/
  anotherLegendary : Bool := false
deriving Repr, Inhabited, BEq

namespace SharedTriggerOpts

def youControlCreatureWithPower (o : SharedTriggerOpts) : Option Int :=
  match o.condition with
  | .youControlCreatureWithPower n => some n
  | _ => none

def gainedLifeAtLeast (o : SharedTriggerOpts) : Option Nat :=
  match o.condition with
  | .gainedLifeAtLeast n => some n
  | _ => none

def anotherCreaturePowerAtMost (o : SharedTriggerOpts) : Option Int :=
  match o.condition with
  | .anotherCreaturePowerAtMost n => some n
  | _ => none

def fraCondition (o : SharedTriggerOpts) : InterveningCondition :=
  match o.condition with
  | .youControlCreatureWithPower _ | .gainedLifeAtLeast _ | .anotherCreaturePowerAtMost _ => .none
  | c => c

def thisOrNontokenSubtype (o : SharedTriggerOpts) : Option String := o.subtype
def thisOrAnotherSubtype (o : SharedTriggerOpts) : Option String := o.subtype
def anotherSubtypeOrEquipment (o : SharedTriggerOpts) : Option String := o.subtype
def watchedSubtype (o : SharedTriggerOpts) : Option String := o.subtype

/-- Ferocious intervening condition (power 4 or greater). -/
def ferocious : SharedTriggerOpts :=
  { condition := .youControlCreatureWithPower 4 }

/-- “This ability triggers only once each turn.” -/
def once : SharedTriggerOpts :=
  { onceEachTurn := true }

/-- Shared effect has targeting; this printed ability does not. -/
def noTarget : SharedTriggerOpts :=
  { untargeted := true }

end SharedTriggerOpts

/-- A triggered ability the engine currently understands (CR 603).
One constructor keeps the C runtime tag under the limit; leftover printed
names are aliases of `triggered`. -/
inductive TriggeredAbility where
  /-- Reusable trigger: when it fires, a unified `Effect`, and optional
  intervening conditions / wording filters. -/
  | triggered (when : TriggerEvent) (effect : Effect)
      (opts : SharedTriggerOpts := {})
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

/-- How a triggered ability selects targets when it is put on the stack
(CR 603.3d / 601.2c). Spell and activated-ability targeting use the same
`EffectTargetKind` constructors. -/
abbrev TriggerTargetKind := EffectTargetKind

/-- When a triggered ability fires, how it targets, optional divided-damage
parameters, and how it resolves (CR 603 / 601.2d / 608). -/
structure TriggerTiming where
  events : Array TriggerEvent := #[]
  targeting : EffectTargeting := .of .none
  /-- Zero targets is a legal announcement (CR 115.1c / 601.2c), e.g. “up to one”. -/
  allowsZeroTargets : Bool := false
  /-- Most targets one instance of “target” may take (“any number of target
  …”); 0 means the targeting's own count. -/
  maxTargets : Nat := 0
  /-- Damage amount and maximum number of targets when this ability divides
  damage as the controller chooses (CR 601.2d). -/
  dividedDamage : Option (Nat × Nat) := none
  /-- What happens when this ability resolves. -/
  resolution : TriggerResolution := .pump .greatestPower (.fixed 0) .source
  /-- This trigger fires only once each turn. -/
  onceEachTurn : Bool := false
  /-- “Do this only once each turn”: the ability keeps triggering until the
  controller chooses to do the optional action (MSH 69). -/
  optionalOnceEachTurn : Bool := false
  /-- Intervening or event-threshold condition (CR 603.2 / 603.4). -/
  condition : InterveningCondition := .none
  /-- Subtype filter watched by the trigger event. -/
  subtype : Option String := none
deriving Repr, Inhabited, BEq

namespace TriggerTiming

def youControlCreatureWithPower (t : TriggerTiming) : Option Int :=
  match t.condition with
  | .youControlCreatureWithPower n => some n
  | _ => none

def gainedLifeAtLeast (t : TriggerTiming) : Option Nat :=
  match t.condition with
  | .gainedLifeAtLeast n => some n
  | _ => none

def anotherCreaturePowerAtMost (t : TriggerTiming) : Option Int :=
  match t.condition with
  | .anotherCreaturePowerAtMost n => some n
  | _ => none

def thisOrNontokenSubtype (t : TriggerTiming) : Option String := t.subtype
def thisOrAnotherSubtype (t : TriggerTiming) : Option String := t.subtype
def anotherSubtypeOrEquipment (t : TriggerTiming) : Option String := t.subtype

end TriggerTiming

end TriggeredAbility

/-- Backward-compatible alias: shared trigger payloads are unified `Effect`s. -/
def SharedTrigger : Type := Effect

namespace SharedTrigger

/-- Targeting, divided-damage parameters, and resolution for this shared effect. -/
def timing (e : SharedTrigger) : TriggeredAbility.TriggerTiming :=
  let e : Effect := e
  { events := e.events
    targeting := e.targeting
    allowsZeroTargets := e.allowsZeroTargets
    maxTargets := e.maxTargets
    dividedDamage := e.dividedDamage
    resolution := e.resolution
    onceEachTurn := e.onceEachTurn
    optionalOnceEachTurn := e.optionalOnceEachTurn }

-- Library triggers (CR 121 / CR 701.13 / CR 701.18 / CR 701.20 / CR 701.25 / CR 701.48)
def scry (n : Nat) : Effect := { resolution := .scry (.fixed n) }
def draw (n : Nat) : Effect := { resolution := .draw (.fixed n) }
def connive (who : ConniveSubject := .source) : Effect :=
  match who with
  | .source => { resolution := .connive .source }
  | .target kind => { targeting := .of kind, resolution := .connive .target }
  | .enteringVillain => { resolution := .connive .enteringVillain }
def millPlayer (n : Nat) : Effect :=
  { targeting := .of .player, resolution := .mill (.fixed n) (.target .player) }
def searchLibrary : Effect := { resolution := .searchLibrary (.put .forest) }
def searchBasicLandToHand : Effect :=
  { resolution := .searchLibrary (.returnToHand .basicLand) }
def mayDiscardHandDraw (n : Nat) : Effect :=
  { resolution := .may (.discard .hand) (.draw (.fixed n)) .ifYouDo }
def drawXDiscard (n : Nat) : Effect :=
  { resolution := .sequence
      [.draw .equalToManaSpent, .«if» .manaSpent (.discard (.cards n))] }
def mayPayGenericDraw (n : Nat) (plusOneOnSource : Bool := false) : Effect :=
  { resolution :=
      if plusOneOnSource then
        .may (.pay (.mana #[.generic n]))
          (.sequence [.putCounters (.ofKind .plusOnePlusOne) .source, .draw (.fixed 1)]) .ifYouDo
      else
        .may (.pay (.mana #[.generic n])) (.draw (.fixed 1)) .ifYouDo }
def drawThenBottomIfNoLegendary : Effect :=
  { resolution := .sequence
      [.draw (.fixed 1), .«if» (.not (.atLeast (.count .legendaryCreaturesYouControl) (.fixed 1))) (.putOnLibrary .bottom .cardFromHand)] }
def tapHumansDraw : Effect :=
  { resolution := .sequence
      [.may (.tap .humans) (.sequence []), .draw .forEachTappedHuman] }
def lookAtTopRevealTypes (n : Nat) (types : Array String) : Effect :=
  { resolution := .revealLibrary (.topNumber (.fixed n)) (.returnToHand (.lookedTypes types)) }
def millThenSubtypeToHand (n : Nat) (subtype : String) : Effect :=
  { resolution := .sequence
      [.mill (.fixed n) (note := .milledCards), .returnToHand (.milledSubtype subtype)] }
def revealUntilCreature : Effect :=
  { resolution := .revealLibrary .untilCreature
      (.ifElse .revealedManaValueAtMostLands (.put .revealed) (.returnToHand .revealed)) }
def lootLandEntersTapped : Effect :=
  { resolution := .sequence
      [.draw (.fixed 1), .discard (.cards 1), .put .discardedLand (how := .tapped)] }
def millThatManyLost : Effect :=
  { resolution := .mill .thatManyLost .thatPlayer }
def drawPerFatGraveyard : Effect :=
  { resolution := .draw .perFatGraveyard }
def millThenCopy : Effect :=
  { resolution := .sequence
      [.mill (.fixed 2) .eachOpponent (note := .opponentsMilled),
       .«if» .opponentsMilled (.queueReflexive (.mayCast .milledSpell .causingSpell .withoutPaying))] }
def cascade : Effect := { resolution := .cascade }
def discardHandDrawDamageIfStory : Effect :=
  { resolution := .sequence
      [.may (.discard .hand) (.sequence []), .draw .discardedHand,
       .«if» .enduringStoryNoted (.dealDamage .discardedHand (.player .eachOpponent))] }
def revealTopPutRandomCreature (n : Nat) : Effect :=
  { resolution := .revealLibrary (.top n) (.put .randomCreature) }
def grimaImpulse : Effect :=
  { resolution := .sequence
      [.revealLibrary .untilInstantOrSorcery (.exile .top .forLater .impulse) .damagedPlayer,
       .mayCast .impulse .unlimited .withoutPaying] }
def palantir : Effect :=
  { targeting := .of .opponent,
    resolution := .sequence
      [.putCounters (.ofKind .influence) .source, .scry (.fixed 2),
       .may (.draw (.fixed 1) (who := .opponentHasYou)) (.sequence [])] }
def revealSaga : Effect :=
  { resolution := .revealLibrary .untilSaga (.put .revealed) }
def drawIfAttackedOrEnteredSubtype (subtype : String) : Effect :=
  { resolution := .«if»
      (.or [.attackedWithSubtype subtype, .subtypeEntered subtype])
      (.draw (.fixed 1)) }
def surveil (n : Nat) : Effect := { resolution := .surveil (.fixed n) }
def drawIfRemovedTwoLoyalty : Effect :=
  { resolution := .«if» (.atLeast .lastKnownPower (.fixed 2)) (.draw (.fixed 1)) }
def drawTwoWinIfEmptyShuffleSource : Effect :=
  { resolution := .sequence
      [.draw (.fixed 2), .«if» (.not (.atLeast .libraryCards (.fixed 1))) .winTheGame, .«if» (.atLeast .libraryCards (.fixed 1)) (.putOnLibrary .shuffled .source)] }
def surveilReturnIfGainedLife : Effect :=
  { events := #[.yourEndStep],
    resolution := .sequence [.surveil (.fixed 0) .armReturnLifeGained, .surveil (.fixed 1)] }
def drawMayPutLandTapped : Effect :=
  { resolution := .sequence
      [.draw (.fixed 1), .may (.put .landFromHand (how := .tapped)) (.sequence [])] }
def drawGainLifeIfAnotherHero : Effect :=
  { resolution := .sequence [.draw (.fixed 1), .«if» (.atLeast (.count (.othersOfSubtype "Hero")) (.fixed 1)) (.gainLife (.fixed 2))] }
def maySacArtifactOrDiscardDraw : Effect :=
  { resolution := .may (.pay (.or [.sacrifice (.fixed 1) .artifact, .discard (.fixed 1) .card])) (.draw (.fixed 1)) .ifYouDo }

-- Token & counter triggers (CR 111 / CR 122 / CR 701.36 / CR 701.47)
def createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false) : Effect :=
  { resolution := .createTokens kind (.fixed n) tapped }
def amass (n : Nat) (subtype : String := "Goblin")
    (amount : TriggeredAbility.NumberSelector := .fixed n) (attachSource : Bool := false) : Effect :=
  { resolution := .amass amount subtype attachSource }
def recruit (who : RecruitSubject := .recruit) : Effect := { resolution := .recruit who }
def investigate : Effect := { resolution := .investigate }
def plusOneEachYouControl (which : YouControlPlusOne := .eachCreature) : Effect :=
  { resolution := .putCounters (.ofKind .plusOnePlusOne) (.youControl which) }
def honeEachEquipment : Effect :=
  { resolution := .putCounters (.ofKind .hone 1) (.youControl (.subtype "Equipment")) }
def plusOneEachOtherGainLife : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plusOnePlusOne) .eachOther,
       .gainLife .perOtherCreature] }
def createThenAttach (kind : TokenKind) : Effect :=
  { resolution := .sequence [.createTokens kind (.fixed 1) false, .attach .source .createdToken] }
def createAxe (attach : Bool := false) : Effect :=
  { resolution :=
      .createTokens .axe (.fixed 1) false
        (note := if attach then .attachReflexive else .none) }
def ringTempts : Effect := { resolution := .ringTempts }
def removeHopeDrawSac : Effect :=
  { resolution := .sequence
      [.removeCounters .hope .source, .«if» .removedHope (.draw (.fixed 1)), .«if» (.not .hopeOnSource) (.sequence [.sacrifice .source, .gainLife (.fixed 4)])] }
def createTappedTreasuresEqualOppArtifacts : Effect :=
  { resolution := .createTokens .treasure .oppArtifacts true }
def wolfPlusOneOrTreasure : Effect :=
  { resolution := .or
      [.putCounters (.ofKind .plusOnePlusOne) .permanent,
       .createTokens .treasure (.fixed 1) false] }
def trampleCounterBecomeBear : Effect :=
  { targeting := .of .creatureYouControl, allowsZeroTargets := true,
    resolution := .sequence
      [.putCounters (.ofKind .trample) .permanent, .grant .bearType .target, .«if» ((.atLeast (.count (.youControl (.subtype "Bear"))) (.fixed 3))) (.draw (.fixed 2))] }
def plusOneEqualLastKnownMv : Effect :=
  { targeting := .of .creatureYouControl,
    resolution := .putCounters .plusOneLastKnownMv .permanent }
def mountainQuestDragon : Effect :=
  { resolution := .sequence [.putCounters (.ofKind .quest) .source, .«if» ((.atLeast (.count .questCounters) (.fixed 6))) (.sequence [.sacrifice (.sacrificedSource .movedAsSacrificed), .searchLibrary (.put .dragon)])] }
def treasuresPerChosenType : Effect :=
  { resolution := .createTokens .treasure .chosenCreatureType false }
def attackSacPlusOneEqualPower : Effect :=
  { resolution := .may (.pay (.sacrifice (.fixed 1) .another))
      (.putCounters .plusOneSacrificedPower .source) .ifYouDo }
def maySacDrawTreasure : Effect :=
  { resolution := .may (.pay (.sacrifice (.fixed 1) .anotherCreatureOrArtifact))
      (.sequence [.draw (.fixed 1), .createTokens .treasure (.fixed 1) false]) .ifYouDo }
def createAlienPerInvasion : Effect :=
  { resolution := .sequence
      [.createTokens .alien (.fixed 1) false (note := .invasion),
       .putCounters .plusOneNoted .createdToken,
       .putCounters (.ofKind .invasion) .source] }
def belladonnaTokenReward : Effect :=
  { resolution := .sequence [
      .noteResolveThisTurn 3,
      .«if» (.nthResolve 1) (.gainLife (.fixed 1)),
      .«if» (.nthResolve 2) (.draw (.fixed 1)),
      .«if» (.nthResolve 3) (.putCounters (.ofKind .plusOnePlusOne) .youControl)] }
def createSpiritsForEquipped : Effect :=
  { resolution := .sequence
      [.createTokens .spirit (.fixed 2) true, .«if» (.atLeast (.count (.intersection [.equipped, .legendaryCreaturesYouControl])) (.fixed 1)) (.grant .attacking .createdToken)] }
def createTreasuresEqualDamagedPlayerArtifacts : Effect :=
  { resolution := .createTokens .treasure .damagedPlayerArtifacts false }
def eaglesCreateBirds : Effect :=
  { resolution := .createTokens .birdSoldier .lastKnownPower false }
def honePerOppAttach : Effect :=
  { targeting := .of (.multi #[
      { noun := "target opponent", zone := .player, controller := .opponent },
      { noun := "target creature you control", controller := .you, types := #[.creature] }
    ] #[1])
    resolution := .sequence
      [.putCounters .honePerOpponent .source, .attach .source (.target .laterCreature)] }
def treasuresEqualLastKnown : Effect :=
  { resolution := .createTokens .treasure .lastKnownPower false }
def scryAndPlan (n : Nat) : Effect :=
  { resolution := .sequence [.putCounters (.ofKind .plan) .source, .scry (.fixed n)] }
def lootAndPlan : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .discard (.cards 1)] }
def createVillainAndPlan : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plan) .source, .createTokens .villain21menace (.fixed 1) false] }
def drainAndPlan (n : Nat) : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plan) .source, .loseLife (.fixed n) .eachOpponent, .gainLife (.fixed n)] }
def drawLoseLifeAndPlan : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plan) .source, .draw (.fixed 1), .loseLife (.fixed 1)] }
def treasureTappedAndPlan : Effect :=
  { resolution := .sequence
      [.putCounters (.ofKind .plan) .source, .createTokens .treasure (.fixed 1) true] }
def plusOneOnTargetAndPlan : Effect :=
  { targeting := .of .creatureYouControl,
    resolution := .sequence
      [.putCounters (.ofKind .plan) .source,
       .putCounters (.ofKind .plusOnePlusOne) (.permanent true)] }
def planFinishDrawPlusOneEach : Effect :=
  { resolution := .sequence
      [.sacrifice .plan, .draw (.fixed 1), .putCounters (.ofKind .plusOnePlusOne) .youControl] }
def planFinishReturnInstants : Effect :=
  { resolution := .sequence
      [.sacrifice .plan .forReflexive,
       .«if» .planWasSacrificed (.queueReflexive (.returnToHand (.graveyardInstants 2)))] }
def planFinishControlOpponent : Effect :=
  { resolution := .sequence
      [.sacrifice .plan .forReflexive,
       .«if» .planWasSacrificed (.queueReflexive (.gainControl .duringNextTurn))] }
def planFinishExileTopCast : Effect :=
  { resolution := .sequence
      [.sacrifice .plan .forReflexive,
       .«if» .planWasSacrificed (.queueReflexive (.exile (.opponentTop 5) (.mayCastUpTo 2)))] }
def planFinishCreateRobots (n : Nat) : Effect :=
  { resolution := .sequence
      [.sacrifice .plan, .createTokens .robotVillain22 (.fixed n) false] }
def planFinishDividedDamage (n : Nat) : Effect :=
  { resolution := .sequence
      [.sacrifice .plan .forReflexive,
       .«if» .planWasSacrificed (.queueReflexive (.dealDamage (.fixed n) .target .divided))] }
def planFinishIndestructibleOnTarget : Effect :=
  { resolution := .sequence
      [.sacrifice .plan .forReflexive,
       .«if» .planWasSacrificed (.queueReflexive (.putCounters (.ofKind .indestructible) .permanent))] }
def empowerJace (n : Nat) : Effect := { resolution := .empowerJace (.fixed n) }
def loyaltyOnSource : Effect :=
  { resolution := .putCounters (.ofKind .loyalty) .source }
def grantThenCounterByType (k : Keywords) : Effect :=
  { targeting := .of .permanentYouControl,
    resolution := .sequence
      [.grant (.keywords k) .target,
       .«if» (.atLeast (.count (.target .creature)) (.fixed 1)) (.putCounters (.ofKind .plusOnePlusOne) .permanent),
       .«if» (.atLeast (.count (.target .planeswalker)) (.fixed 1)) (.putCounters (.ofKind .loyalty) .permanent)] }
def pumpOrCounterIfScried : Effect :=
  { events := #[.yourBeginCombat], targeting := .of .anotherCreatureYouControl,
    resolution := .ifElse (.or [.scriedThisTurn, .surveilledThisTurn])
      (.putCounters (.ofKind .plusOnePlusOne) .permanent)
      (.pump (.fixed 1) (.fixed 1) .target) }
def putSourceCountersOnTarget : Effect :=
  { targeting := .of .creatureYouControl, allowsZeroTargets := true,
    resolution := .putCounters .sourceCounters .permanent }
def chargeCounterOnSource : Effect :=
  { resolution := .putCounters (.ofKind .charge) .source }
def createFoodOrTreasure : Effect :=
  { resolution := .or
      [.createTokens .food (.fixed 1) false, .createTokens .treasure (.fixed 1) false] }
def villainIfGyElseMill : Effect :=
  { resolution := .ifElse ((.atLeast (.count .creatureCardsInGraveyard) (.fixed 2)))
      (.createTokens .villain21menace (.fixed 1) true) (.mill (.fixed 2)) }
def plusOneOrTwoIfAnotherHero : Effect :=
  { targeting := .of .creature,
    resolution := .ifElse ((.atLeast (.count (.target (.anotherSubtype "Hero"))) (.fixed 1)))
      (.putCounters (.ofKind .plusOnePlusOne 2) .permanent)
      (.putCounters (.ofKind .plusOnePlusOne) .permanent) }

-- Combat & damage triggers (CR 119 / CR 120 / CR 508 / CR 701.3 / CR 701.14)
def dividedDamage (amount maxTargets : Nat) : Effect :=
  { targeting := .of .playerOrCreature,
    dividedDamage := some (amount, maxTargets), resolution := .dealDamage (.fixed 0) .target .preallocated }
def gainLife (n : Nat) : Effect := { resolution := .gainLife (.fixed n) }
def damageEachOpponent (n : Nat) : Effect :=
  { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player .eachOpponent) }
def attachTo (kind : EffectTargetKind) : Effect :=
  { targeting := .of kind, resolution := .attach .source .target }
def pumpCause (p t : Int) : Effect := { resolution := .pump (.fixed p) (.fixed t) .cause }
def becomePT (p t : Int) : Effect := { resolution := .may (.setBasePT (.fixed p) (.fixed t) .source) (.sequence []) }
def pumpTargetPerPlains : Effect :=
  { targeting := .of .creatureYouControl, resolution := .pump .perPlains .perPlains .target }
def pumpByLookedAt : Effect := { resolution := .pump .perLookedAt .perLookedAt .source }
def pumpGreatestPower : Effect := { resolution := .pump .greatestPower (.fixed 0) .source }
def pumpForEachOtherCreature : Effect :=
  { resolution := .pump .perOtherCreature .perOtherCreature .source }
def damageBlockers (n : Nat) : Effect := { resolution := .dealDamage (.fixed n) .blockers }
def gainLifeSearchBasicOnTop (n : Nat) : Effect :=
  { resolution := .sequence [.gainLife (.fixed n), .searchLibrary (.put .basicLandOnTop)] }
def targetOpponentLosesLife (n : Nat) : Effect :=
  { targeting := .of .opponent, resolution := .loseLife (.fixed n) (.target .opponent) }
def setOtherBasePT : Effect :=
  { targeting := .of .anotherCreatureYouControl, allowsZeroTargets := true,
    resolution := .setBasePT .equalSourcePower .equalSourceToughness }
def damageFromLastKnownPower : Effect :=
  { targeting := .of .oppCreature,
    resolution := .dealDamage .lastKnownPower .permanent }
def damageEqualSubtypeToEachOpponent (subtype : String) : Effect :=
  { resolution := .dealDamage (.subtypeCount subtype) (.player .eachOpponent) }
def damageEqualTreasures : Effect :=
  { targeting := .of .playerOrCreature,
    resolution := .dealDamage (.subtypeCount "Treasure") .target }
def dealDamageDestroyIfSubtype (n : Nat) (subtype : String) : Effect :=
  { targeting := .of .playerOrCreature,
    resolution := .sequence
      [.dealDamage (.fixed n) .target .markedPermanent,
       .«if» (.dealtDamageToSubtype subtype) (.destroy .permanentDealtDamage)] }
def attachEquipmentToCreature : Effect :=
  { targeting := .of .equipmentYouControlThenCreatureYouControl,
    allowsZeroTargets := true, resolution := .attach .target .optionalCreature }
def othersGetAndOppsGet (subtypes : Array String) (p t oppP oppT : Int) : Effect :=
  { resolution := .sequence
      [.pump (.fixed p) (.fixed t) (.intersection [.creaturesYouControl, .union (subtypes.toList.map .othersOfSubtype)]),
       .pump (.fixed oppP) (.fixed oppT) .opponentsCreatures] }
def pumpTargetBySourcePower : Effect :=
  { targeting := .of .anotherCreatureYouControl,
    resolution := .pump .equalSourcePower (.fixed 0) .target }
def bolgDealSacrificedPower : Effect :=
  { targeting := .of .anotherCreature,
    resolution := .sequence
      [.dealDamage .lastKnownPower .permanent .excess,
       .amass .notedExcess] }
def deal1ThenAmassOrcs : Effect :=
  { targeting := .of .playerOrCreature,
    resolution := .sequence
      [.dealDamage (.fixed 1) .target .markedPermanent, .amass (.fixed 1) "Orc"] }
def untapAttackersExtraCombat (_n : Int := 12) : Effect :=
  { resolution := .sequence [.untap .attackingCreatures, .additionalCombatPhase] }
def beginCombatIfDrawnTwoPump : Effect :=
  { targeting := .of .anotherCreatureYouControl,
    resolution := .«if» (.atLeast .cardsDrawnThisTurn (.fixed 2)) (.sequence [
      .pump (.fixed 3) (.fixed 0) .target,
      .grant (.keywords Keyword.firstStrike) .target]) }
def damageTargetOpponent (n : Nat) : Effect :=
  { targeting := .of .opponent, resolution := .dealDamage (.fixed n) (.player (.target .opponent)) }
def attachEquipmentThenFight : Effect :=
  { targeting := .of .creatureYouControl,
    resolution := .sequence [.attach .anyYouControl .target,
      .«if» .equipmentAttached (.fight .equipmentHost .reflexive)] }
def loseLifePerBurden : Effect := { resolution := .loseLife .perBurden }
def othersOfSubtypeGetEqualSourceToughness (subtype : String) : Effect :=
  { resolution := .pump .equalSourceToughness .equalSourceToughness
      (.othersOfSubtype subtype) }
def creaturesYouControlGet (p t : Int) : Effect :=
  { resolution := .pump (.fixed p) (.fixed t) .creaturesYouControl }
def pumpIfFiveOtherForests : Effect :=
  { targeting := .of .creatureYouControl,
    resolution := .«if» ((.atLeast (.count .forestsExceptCause) (.fixed 5))) (.pump (.fixed 3) (.fixed 3) .target) }

-- Zone-change triggers (CR 400 / CR 701.8 / CR 701.9 / CR 701.13 / CR 701.21)
def exileUntilLeaves (kind : EffectTargetKind) : Effect :=
  { targeting := .of kind, resolution := .exile .target .untilSourceLeaves }
def opponentSacrificesCreature : Effect :=
  { targeting := .of .opponent,
    resolution := .sacrifice .opponentChosenCreature }
def exileTop : Effect := { resolution := .exile .top .playUntilNextTurn }
def discard (n : Nat := 1) : Effect := { resolution := .discard (.cards n) }
def opponentDiscards (n : Nat := 1) (who : TriggeredAbility.PlayerSelector := .eachOpponent) : Effect :=
  { targeting := if who == .target .opponent then .of .opponent else .of .none
    resolution := .discard (.cards n who) }
def eachPlayerSacrificesCreature : Effect :=
  { resolution := .sacrifice .eachPlayersCreature }
def exileTarget (kind : EffectTargetKind) : Effect :=
  { targeting := .of kind, resolution := .exile .target .leaveTrigger }
def returnCreatureFromGyToHand : Effect :=
  { targeting := .of .creatureCardInYourGraveyard,
    resolution := .returnToHand .graveyardCard }
def returnLinkedExile : Effect := { resolution := .put .linkedExile }
def payReturnFromGy : Effect :=
  { resolution := .may
      (.pay (.mana #[.generic 1, .colored .green, .colored .blue])) (.returnToHand .source) .ifYouDo }
def returnElfGainLife : Effect :=
  { targeting := .of .elfInYourGraveyard
    resolution := .sequence
      [.returnToHand .graveyardCard, .gainLife .equalToTargetPower] }
def destroyOppArtifactsEnchantmentsGainLife : Effect :=
  { resolution := .sequence
      [.destroy .oppArtifactsEnchantments (note := .countDestroyed),
       .gainLife .forEachDestroyedThisWay] }
def defenderSacsLeastPower : Effect :=
  { resolution := .sacrifice .leastPower }
def returnOtherPlusOne : Effect :=
  { targeting := .of (.filtered { noun := "up to one other target permanent you control"
                                  controller := .you, another := true })
    allowsZeroTargets := true
    resolution := .sequence
      [.returnToHand .permanent .returnedPermanent,
       .«if» .returnedPermanent (.putCounters (.ofKind .plusOnePlusOne) .source)] }
def putNonlandMvAtMostFromGy (mv : Nat) : Effect :=
  { targeting := .of (.filtered
      { noun := s!"up to one target nonland permanent card with mana value {mv} or less from a graveyard"
        zone := .anyGraveyard, permanentCard := true, nonland := true, mvAtMost := some mv })
    allowsZeroTargets := true, resolution := .put (.nonlandMvAtMost mv) }
def exileOppNonlandEachUntilLeaves : Effect :=
  { targeting := .of (.filtered
      { noun := "for each opponent, up to one target nonland permanent that player controls"
        nonland := true, controller := .eachOpponent })
    allowsZeroTargets := true
    resolution := .exile (.target .eachPermanent) .untilSourceLeaves }
def mayPutArtifactAttachEquipment : Effect :=
  { resolution := .sequence
      [.may (.put .artifactFromHand (note := .forAttach)) (.sequence []),
       .«if» (.atLeast (.count .putEquipment) (.fixed 1)) (.attach .putArtifact .notedHost)] }
def bolgMaySacrifice : Effect := { resolution := .may (.sacrifice .another) (.sequence []) }
def destroyOtherAmassControllerPower : Effect :=
  { targeting := .of .anotherCreature, allowsZeroTargets := true,
    resolution := .sequence
      [.destroy .target (note := .forAmass),
       .amass .notedPower (who := .controller .target),
       .«if» .youControlledDestroyed (.draw (.fixed 1))] }
def returnAsArtifact : Effect := { resolution := .put .source (how := .asArtifact) }
def exileLandsThenReturnTapped : Effect :=
  { targeting := .of (.filtered {
      noun := "up to three target lands you control"
      types := #[.land], controller := .you })
    allowsZeroTargets := true, maxTargets := 3
    resolution := .sequence
      [.exile .landsYouControl .forLater .lands,
       .put .notedLands (how := .tapped)] }
def sacDamagersRingTempts : Effect :=
  { resolution := .sequence [.sacrifice .combatDamager, .ringTempts] }
def destroyOppPermanentIfSixLands : Effect :=
  { targeting := .of .oppPermanent,
    resolution := .«if» ((.atLeast (.count .landsYouControl) (.fixed 6))) (.sequence [
      .destroy .target,
      .createTokens .treasure (.fixed 1) false (who := .controller .target)]) }
def sacrificeSourceIfNoPlaneswalker : Effect :=
  { events := #[.eachEndStep],
    resolution := .«if» (.not (.atLeast (.count .planeswalkersYouControl) (.fixed 1))) (.sacrifice (.sacrificedSource .controllerSacrifices)) }
def exileOtherCopyEnchanted : Effect :=
  { targeting := .of .creature, allowsZeroTargets := true,
    resolution := .sequence
      [.exile .target .untilSourceLeaves .copyAndHost, .becomeCopy .noted] }
def exileUntilNextEndStep : Effect :=
  { targeting := .of .creatureYouControl, allowsZeroTargets := true,
    resolution := .exile .target .nextEndStep }

-- Continuous & modal triggers (CR 106 / CR 601 / CR 611 / CR 700.2 / CR 707)
def addMana (types : Array ManaType) : Effect := { resolution := .addMana types }
def tapOppOrUntapYours : Effect :=
  { resolution := .or [.tap .target, .untap] }
def gainControlOppUntilEot : Effect :=
  { targeting := .of .oppCreature, resolution := .gainControl .untilEndOfTurn }
def castInstantSorceryFromHand : Effect :=
  { resolution := .mayCast .hand .twiceLegendaryWizards .withoutPaying }
def castInstantSorceryMvAtMost : Effect :=
  { resolution := .mayCast .hand .lastKnown .withoutPaying }
def allianceMode : Effect :=
  { resolution := .chooseModes TriggeredAbility.TriggerResolution.allianceModes
      .oneUnusedThisTurn }
def gollumMode : Effect :=
  { resolution := .chooseModes TriggeredAbility.TriggerResolution.gollumModes
      .oneUnused }
def castFromGyArtifactInstantSorcery : Effect :=
  { resolution := .mayCast .graveyard .unlimited .pay .exileInstead }
def equippedAttackersGainDoubleStrike : Effect :=
  { resolution := .grant .doubleStrike .equippedAttackers }
def tapEnchantedRemoveCounters : Effect :=
  { resolution := .sequence [.tap .enchanted, .removeCounters .all .enchanted] }
def copySelfNonlegendary : Effect := { resolution := .becomeCopy .sourceTwoNonlegendaryTokens }
def protectionEverything : Effect :=
  { resolution := .grant .protectionEverything .youIfCast }
def prepareSource (when : PrepareWhen := .ifNotPrepared) : SharedTrigger :=
  match when with
  | .ifNotPrepared =>
    { events := #[.yourUpkeep], resolution := .«if» (.not .preparedSource) (.becomePrepared .source) }
  | .ifThreeCreaturesDied =>
    { events := #[.eachEndStep], resolution := .«if» (.atLeast .creaturesDiedThisTurn (.fixed 3)) (.becomePrepared .source) }
def addGreenPerChargeCounter : Effect :=
  { events := #[.yourFirstMain],
    resolution := .addMana #[.colored .green] .perChargeCounter }
def tapOrUntapNonland : Effect :=
  { targeting := .of .nonland,
    resolution := .or [.tap .target, .untap] }

-- Permanent-action triggers (CR 122 / CR 611 / CR 701.21)
def onPermanent (kind : EffectTargetKind) (action : PermanentAction) : Effect :=
  { targeting := .of kind
    resolution := TriggeredAbility.TriggerResolution.ofPermanent action }
def onSource (action : PermanentAction) : Effect :=
  { resolution := TriggeredAbility.TriggerResolution.ofSource action }
def onEnchanted (action : PermanentAction) : Effect :=
  { resolution := TriggeredAbility.TriggerResolution.ofEnchanted action }
def attachThen (followup : PermanentAction) : Effect :=
  { targeting := .of .creatureYouControl,
    resolution := .sequence
      ([.attach .source .target] ++
        (TriggeredAbility.TriggerResolution.ofTargetWhileSource followup).flatten) }

-- Optional combinators
def mayTo (can thenDo : SharedTrigger) : SharedTrigger :=
  let can : Effect := can
  let thenDo : Effect := thenDo
  { targeting :=
      if can.targeting.kind == .none then thenDo.targeting else can.targeting
    allowsZeroTargets := can.allowsZeroTargets || thenDo.allowsZeroTargets
    maxTargets :=
      if can.targeting.kind == .none then thenDo.maxTargets else can.maxTargets
    dividedDamage :=
      match Effect.dividedDamage can with
      | some d => some d
      | none => Effect.dividedDamage thenDo
    resolution := .may can.resolution thenDo.resolution .ifYouDo }

def may (action : SharedTrigger) : SharedTrigger :=
  let action : Effect := action
  { action with resolution := .may action.resolution (.sequence []) }

end SharedTrigger

#guard TriggeredAbility.TriggerResolution.ofPermanent .loseIndestructible ==
  .lose .indestructible
#guard TriggeredAbility.TriggerResolution.ofSource .loseIndestructible ==
  .lose .indestructible .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .loseIndestructible ==
  .lose .indestructible .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .loseIndestructible ==
  .lose .indestructible (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .cantBeBlocked ==
  .cant .beBlocked
#guard TriggeredAbility.TriggerResolution.ofPermanent .indestructibleCounter ==
  .putCounters (.ofKind .indestructible) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .doubleStrikeCounter ==
  .putCounters (.ofKind .doubleStrike) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .burdenCounter ==
  .putCounters (.ofKind .burden) .permanent
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomeArtifactIndestructible ==
  .sequence [.becomeArtifact, .grant (.keywords Keyword.indestructible) .target]
#guard TriggeredAbility.TriggerResolution.ofPermanent .becomePrepared == .becomePrepared
#guard TriggeredAbility.TriggerResolution.ofPermanent (.setBasePT 2 2) ==
  .setBasePT (.fixed 2) (.fixed 2)
#guard TriggeredAbility.TriggerResolution.ofPermanent .tapAndStun ==
  .sequence [.tap .target, .putCounters (.ofKind .stun) .permanent]
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnTopOfLibrary ==
  .putOnLibrary .top
#guard TriggeredAbility.TriggerResolution.ofPermanent .putOnBottomOfLibrary ==
  .putOnLibrary .bottom
#guard TriggeredAbility.TriggerResolution.ofSource .putOnTopOfLibrary ==
  .putOnLibrary .top .source
#guard TriggeredAbility.TriggerResolution.ofSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnTopOfLibrary ==
  .putOnLibrary .top .enchanted
#guard TriggeredAbility.TriggerResolution.ofEnchanted .putOnBottomOfLibrary ==
  .putOnLibrary .bottom .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnTopOfLibrary ==
  .putOnLibrary .top (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .putOnBottomOfLibrary ==
  .putOnLibrary .bottom (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofPermanent .exile == .exile .target .forLater
#guard TriggeredAbility.TriggerResolution.ofSource .exile == .exile .source .forLater
#guard TriggeredAbility.TriggerResolution.ofEnchanted .exile ==
  .exile .enchanted .forLater
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .exile ==
  .exile (.target .whileSource) .forLater
#guard TriggeredAbility.TriggerResolution.ofPermanent .doublePowerAndToughness ==
  .pump .double .double .target
#guard TriggeredAbility.TriggerResolution.ofPermanent (.pumpAndTrample 2 0) ==
  .sequence [.pump (.fixed 2) (.fixed 0) .target, .grant (.keywords Keyword.trample) .target]
#guard TriggeredAbility.TriggerResolution.ofSource (.plusOne 1) ==
  .putCounters (.ofKind .plusOnePlusOne) .source
#guard TriggeredAbility.TriggerResolution.ofSource (.pump 1 1) ==
  .pump (.fixed 1) (.fixed 1) .source
#guard TriggeredAbility.TriggerResolution.ofSource .tap == .tap .source
#guard TriggeredAbility.TriggerResolution.ofEnchanted .tap == .tap .enchantedWhileSource
#guard TriggeredAbility.TriggerResolution.ofEnchanted (.grantKeywords Keyword.firstStrike) ==
  .grant (.keywords Keyword.firstStrike) .enchanted
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource .untap ==
  .untap (.target .whileSource)
#guard TriggeredAbility.TriggerResolution.ofTargetWhileSource
    (.grantKeywords Keyword.indestructible) ==
  .grant (.keywords Keyword.indestructible) (.target .whileSource)

end Mtg.Engine
