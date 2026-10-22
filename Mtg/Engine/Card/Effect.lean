import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggerEvent

/-!
# Unified one-shot effects (CR 608)

The `Effect` structure shared by spells, activated abilities, Saga
chapters, and triggered abilities. They resolve through `Resolution`
(`SpellResolution` and `TriggeredAbility.TriggerResolution` name that
inductive).
-/

namespace Mtg.Engine



/-- Target announcement metadata for a one-shot effect (CR 115.1 / 601.2c / 601.2d). -/
structure EffectTargetingMeta where
  targeting : EffectTargeting := .of .none
  allowsZeroTargets : Bool := false
  maxTargets : Nat := 0
  dividedDamage : Option (Nat × Nat) := none
deriving Repr, Inhabited, BEq

/-- Shared trigger condition, frequency, and subtype filter metadata (CR 603.2 / 603.4). -/
structure TriggerConditionMeta where
  onceEachTurn : Bool := false
  /-- “Do this only once each turn”: the ability keeps triggering until the
  controller chooses to do the optional action (MSH 69). -/
  optionalOnceEachTurn : Bool := false
  /-- Intervening or event-threshold condition (CR 603.2 / 603.4). -/
  condition : ConditionSelector := .none
  /-- Subtype filter watched by the trigger event. -/
  subtype : Option String := none
deriving Repr, Inhabited, BEq

namespace TriggerConditionMeta

def youControlCreatureWithPower (t : TriggerConditionMeta) : Option Int :=
  match t.condition with
  | .youControlCreatureWithPower n => some n
  | _ => none

def gainedLifeAtLeast (t : TriggerConditionMeta) : Option Nat :=
  match t.condition with
  | .gainedLifeAtLeast n => some n
  | _ => none

def anotherCreaturePowerAtMost (t : TriggerConditionMeta) : Option Int :=
  match t.condition with
  | .anotherCreaturePowerAtMost n => some n
  | _ => none

def thisOrNontokenSubtype (t : TriggerConditionMeta) : Option String := t.subtype
def thisOrAnotherSubtype (t : TriggerConditionMeta) : Option String := t.subtype
def anotherSubtypeOrEquipment (t : TriggerConditionMeta) : Option String := t.subtype

end TriggerConditionMeta

/-- Unified one-shot effect for spells, activated abilities, Saga chapters,
and triggered abilities. Targeting, printed wording, and resolution live
here so Game has one apply path. -/
structure Effect extends EffectTargetingMeta, TriggerConditionMeta where
  events : Array TriggerEvent := #[]
  spellCastKind : SpellCastKind := .extraLand
  abilityCastKind : AbilityCastKind := .other
  preferAsDefaultMode : Bool := false
  resolution : Resolution := .draw 0
  phrase : String := ""
deriving Repr, Inhabited, BEq

namespace Effect

/-- Whom this effect may target (CR 115.1 / 601.2c). -/
def targetKind (e : Effect) : EffectTargetKind :=
  e.targeting.kind

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (e : Effect) : Nat :=
  e.targeting.targetCount

/-- True when announcing this effect requires choosing a target. -/
def requiresTarget (e : Effect) : Bool :=
  e.targeting.requiresTarget

/-- Upper bound on announced targets. `0` on `maxTargets` means `targetCount`. -/
def maxTargetCount (e : Effect) : Nat :=
  if e.maxTargets == 0 then e.targetCount else e.maxTargets

/-- Demonstration-agent category for a spell mode. -/
def castKind (e : Effect) : SpellCastKind :=
  e.spellCastKind

/-- Demonstration-agent category for an activated-ability mode. -/
def abilityKind (e : Effect) : AbilityCastKind :=
  e.abilityCastKind

/-- Oracle-style reminder text. -/
def toNotation (e : Effect) : String :=
  e.phrase

instance : HasTargeting Effect where
  targeting e := e.targeting

instance : ToString Effect where
  toString := toNotation

end Effect

namespace Resolution

private def phraseGrant (r : Resolution) (noun : String) : Option String :=
  match r with
  | .recruit _ =>
    some "Recruit"
  | .attach .source .target =>
    some s!"Attach this Equipment to {noun}"
  | .grant (.subtypeWithLandsPT subtype) .source =>
    some s!"This enchantment becomes {indefinite subtype} {subtype} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .grant (.keywords _) (.intersection [.creaturesYouControl, .union what]) =>
    let subtypes := (what.filterMap fun | .youControl (.subtype s) => some s | _ => none).toArray
    some s!"{StaticAbility.joinedSubtypes subtypes StaticAbility.pluralSubtype} you control gain menace until end of turn"
  | .grant .arwenShare .target =>
    some "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"
  | .grant .combatDamageCreateTreasure .target =>
    some "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
  | .cant (.beBlockedByMostLifePlayer .target) =>
    some "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"
  | .grant (.keywords k) .creaturesYouControl =>
    some s!"Creatures you control gain {k.joinedAnd} until end of turn"
  | .grant .extraTurn .youIfCast =>
    some "Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  | .grant .transformed .source =>
    some "Transform this"
  | .connive .source =>
    some "This creature connives"
  | .becomeCopy (.stackAbility fromCreature) =>
    let src := if fromCreature then "a creature" else "an artifact"
    some s!"Copy target activated or triggered ability you control from {src} source. You may choose new targets for the copy"
  | .grant .constructHero .source =>
    some "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .becomeCopy .secondArtifactTargetNotLegendary =>
    some "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .grant (.typesPTAndKeywords types p t k) .source =>
    let joined :=
      if k.reach && k.vigilance then "reach and vigilance"
      else k.joinedAnd
    let typeWords := String.intercalate " " types.toList
    let art := indefinite (types[0]?.getD "")
    some s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {p}/{t} and gains {joined}"
  | .grant (.nextSpellCopy true) .source =>
    some "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"
  | .grant .harnessed .source =>
    some "Harness this"
  | .connive (.target (.youControl (.subtype subtype))) =>
    some s!"Target {subtype} you control connives"
  | .empowerJace (.fixed n) =>
    some s!"Empower Jace {n}"
  | .cant (.block .creaturesWithoutFlying) =>
    some "Creatures without flying can't block this turn"
  | .becomePrepared .creaturesYouControl true =>
    some "Each creature you control becomes prepared"
  | .grant .jaceLoyaltyAtInstantSpeed .youIfCast =>
    some "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant"
  | .grant (.emblemCastSpellDamage n) .youIfCast =>
    some s!"You get an emblem with \"Whenever you cast a spell, this emblem deals {n} damage to any target.\""
  | .grant (.nextSpellCopy false) .source =>
    some "When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy"
  | .becomeCopy (.creaturesControlledBy (.target .player)) =>
    some s!"For each creature {noun} controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""
  | .becomeCopy .targetLegendRuleOff =>
    some s!"This land becomes a copy of {noun} until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn"
  | .lose .allAbilities (.targetAt _) =>
    some s!"{capitalizeAscii noun} loses all abilities until end of turn"
  | .grant (.keywords _) .createdToken =>
    some "It gains haste until end of turn"
  | .grant .mountainsAddExtraRed .landsYouControl =>
    some "Until end of turn, whenever you tap a Mountain for mana, add an additional {R}"
  | .counter =>
    some s!"Counter {noun}"
  | _ => none

private def phrasePlayerAndCardsPart2 (r : @& Resolution) (noun : @& String) : Option String :=
  match r with
  | .draw (.fixed 1) .targetPlayers =>
    some "Two target players each draw a card"
  | .draw .lastKnownPower _ =>
    some "Draw cards equal to the sacrificed creature's power"
  | .draw .perBurden _ =>
    some "Draw a card for each burden counter on this"
  | .draw .chosenX _ =>
    some "Draw X cards"
  | .draw .cardsDiscardedThisTurn _ =>
    some "Draw a card for each card you've discarded this turn"
  | .draw (.fixed n) .player =>
    some s!"{noun} draws {cardPhrase n.toNat}"
  | .surveil (.fixed n) .none =>
    some s!"Surveil {n}"
  | .loseLife (.fixed n) .player =>
    some s!"{noun} loses {n} life"
  | .loseLife (.fixed n) (.controller .target) =>
    some s!"Its controller loses {n} life"
  | .returnToHand .targetSpell _ =>
    some s!"Return {noun} to its owner's hand"
  | .returnToHand (.target .graveyardCard) _ =>
    some s!"Return {noun} to your hand"
  | .returnToHand .target .none =>
    some s!"Return {noun} to its owner's hand"
  | .draw .milledByTargetPlayerThisTurn _ =>
    some "Draw X cards, where X is the number of cards that were put into target player's graveyard from their library this turn"
  | .draw .greatestPowerAndLoseLife _ =>
    some "Draw cards equal to the greatest power among creatures you control. You lose life equal to the number of cards drawn this way"
  | .discard .chosenNonlandPermanent =>
    some s!"{capitalizeAscii noun} reveals their hand. You choose a nonland permanent card from it. That player discards that card"
  | .discard .chosenNonland =>
    some s!"{capitalizeAscii noun} reveals their hand. You choose a nonland card from it. That player discards that card"
  | .discard .hand =>
    some "Discard your hand"
  | .draw (.perControlled .creature) _ =>
    some "Draw a card for each creature you control"
  | .returnToHand .outsideGameOpponentChoice _ =>
    some "You may reveal exactly two cards you own with different names from outside the game. An opponent chooses one of them. You put that card into your hand"
  | .putOnLibrary .topOrBottomDamage2 .target =>
    some "Choose target nonland permanent. Its owner may put it on top of their library. If they do, this deals 2 damage to them. If they didn't put the card on top of their library, they put it on the bottom"
  | .discard (.mayWheel n _) =>
    some s!"Each player may discard their hand and draw {englishNumber n} cards"
  | .mill (.fixed n) .you (.permanentAndGainLife l) =>
    some s!"Mill {englishNumber n.toNat} cards. You may put a permanent card from among them into your hand. You gain {l} life"
  | _ => none

private def phrasePlayerAndCardsPart1b (r : @& Resolution) (noun : @& String) : Option String :=
  match r with
  | .addMana #[] (.fixed 2) .creatureSources =>
    some "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addMana #[.colored .blue] (.fixed 1) .cantNonartifact =>
    some "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addMana #[] .equalSourcePower .anyColor =>
    some "Add X mana of any one color, where X is this creature's power"
  | .addMana #[] (.fixed 4) .anyCombination =>
    some "Add four mana in any combination of colors"
  | .addMana #[] (.fixed 2) .equipment =>
    some "Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities"
  | .discard (.cards n) =>
    some s!"Discard {cardPhrase n}"
  | .putOnLibrary .shuffled .source =>
    some "Shuffle this into its owner's library"
  | .returnToHand .source _ =>
    some "Return this card from your graveyard to your hand"
  | .mill (.fixed n) .you .none =>
    some s!"Mill {cardPhrase n.toNat}"
  | .mill (.fixed n) .you (.subtypeOrEnchantmentToHand subtype) =>
    some s!"Mill {n} cards. You may put {indefinite subtype} {subtype} or enchantment card from among those cards into your hand"
  | .mill (.fixed n) .player .none =>
    some s!"{noun} mills {n} cards"
  | r => phrasePlayerAndCardsPart2 r noun

private def phrasePlayerAndCards (r : @& Resolution) (noun : @& String) : Option String :=
  match r with
  | .draw (.fixed n) .you =>
    some s!"Draw {cardPhrase n.toNat}"
  | .scry (.fixed n) =>
    some s!"Scry {n}"
  | .gainLife (.fixed n) .you =>
    some s!"You gain {n} life"
  | .amass (.fixed n) "Goblin" _ _ =>
    some s!"Amass Goblins {n.toNat}"
  | .createTokens .tigerGod (.fixed 1) false _ _ =>
    some "Create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .createTokens kind (.fixed n) tapped _ _ =>
    some (capitalizeAscii (TokenKind.createPhrase kind n.toNat (tapped := tapped)))
  | .createTokens kind .chosenX _ _ _ =>
    some s!"Create X {kind.pluralNoun}"
  | .createTokens kind (.perSubtype subtype) _ _ _ =>
    some s!"Create X {kind.pluralNoun}, where X is the number of {subtype}s you control"
  | .createTokens kind .removedPlusOnes _ _ _ =>
    some s!"Create that many {kind.pluralNoun}"
  | .createTokens kind .lifeGainedThisTurn _ _ _ =>
    some s!"Create X {kind.pluralNoun}, where X is the amount of life you gained this turn"
  | .addMana types (.fixed 1) .none =>
    some s!"Add {manaSymbolsText types}"
  | .addMana #[] (.fixed 1) .anyColor =>
    some "Add one mana of any color"
  | .addMana #[] (.fixed 1) (.subtypeSpellsOrAbilities subtype) =>
    some s!"Add one mana of any color. Spend this mana only to cast {indefinite subtype} {subtype} spell or to activate an ability of {indefinite subtype} {subtype} source"
  | .addMana #[] (.fixed 1) .artifactSpell =>
    some "Add one mana of any color. Spend this mana only to cast an artifact spell"
  | r => phrasePlayerAndCardsPart1b r noun

private def phraseZoneAndReveal (r : Resolution) (noun : String) : Option String :=
  match r with
  | .searchLibrary (.put .basicLand .tapped _) =>
    some (capitalizeAscii (searchBasicLandTappedPhrase "your"))
  | .searchLibrary (.returnToHand (.landSubtype t) _) =>
    some (capitalizeAscii (searchLibraryToHandPhrase s!"a {t} card"))
  | .exile .top .playUntilNextTurn =>
    some "Exile the top card of your library. You may play it until the end of your next turn"
  | .put .source .tapped .none =>
    some "Return this card from your graveyard to the battlefield tapped"
  | .put .source .asPrinted .forAttach =>
    some s!"Return this card from your graveyard to the battlefield attached to {noun}"
  | .searchLibrary (.returnToHand .basicLand _) =>
    some (capitalizeAscii (searchLibraryToHandPhrase "a basic land card"))
  | .searchLibrary (.sequence [.put .basicLand .tapped _, .returnToHand .basicLand _]) =>
    some "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"
  | .exile (.target .eachPermanent) .nextEndStep _ =>
    some "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"
  | .searchLibrary (.put (.basicBeholdUntap subtype) .tapped _) =>
    some s!"{capitalizeAscii (searchBasicLandTappedPhrase "your")}. You may behold {indefinite subtype} {subtype}. If you do, untap that land"
  | .destroy .allCreaturesExceptTwoChosen _ =>
    some "Choose up to two creatures, then destroy the rest"
  | .revealLibrary (.top n) (.put (.lookedTypes types) _ _) _ =>
    let listed := orJoin types.toList
    let art := indefinite (types[0]?.getD "")
    some s!"Look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
  | .revealLibrary (.top n) (.returnToHand .artifact _) _ =>
    some s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .exile .topPower .playThisTurn _ =>
    some "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"
  | .revealLibrary (.top n) (.returnToHand (.milledSubtype subtype) _) _ =>
    some s!"Look at the top {n} cards of your library. You may reveal a {subtype} card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .destroy .otherCreaturesOddOrEvenMv _ =>
    some "Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .put .source .asPrinted (.entering [.counter .finality 1 true]) =>
    some "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .revealLibrary (.top 1) (.draw (.fixed 1) _) _ =>
    some "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .sacrifice .oppGreatestMvCreatureOrPlaneswalker _ =>
    some s!"{capitalizeAscii noun} sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control"
  | .exile .top (.mayCastElseDamageOpponents n) _ =>
    some s!"Exile the top card of your library. You may cast that card. If you don't, this deals {n} damage to each opponent"
  | .put .source .asPrinted (.entering [.counter .finality 1 false]) =>
    some "Return this card from your graveyard to the battlefield with a finality counter on it"
  | .destroy .target .drawIfNotAttacking =>
    some s!"Destroy {noun}. If it wasn't attacking, its controller draws a card"
  | .put .graveyardCard .asPrinted .none =>
    some s!"Return {noun} to the battlefield"
  | .put .graveyardCard .asPrinted (.entering [.counter .plusOnePlusOne _ true]) =>
    some s!"Return {noun} to the battlefield with an additional +1/+1 counter on it"
  | .destroy .creaturesNotChosenType _ =>
    some "Choose a creature type. Destroy all creatures that aren't of the chosen type"
  | .searchLibrary (.putOnLibrary .top .planeswalkerCard) =>
    some "Search your library for a planeswalker card, reveal it, then shuffle and put that card on top"
  | .put .allNonlandPermanentsInGraveyard .asPrinted .none =>
    some "Return all nonland permanent cards from your graveyard to the battlefield"
  | .exile .allCreatures .forLater .empowerJace =>
    some "Exile all creatures. Empower Jace X, where X is the number of creatures exiled this way"
  | .exile .sphinxsApproach .forLater _ =>
    some "You may exile this spell and four cards named Sphinx's Approach from your graveyard. If you do, search your library for a Sphinx creature card, put it onto the battlefield, then shuffle"
  | .destroy (.targetAt _) .none =>
    some s!"Destroy {noun}"
  | .exile .target (.returnBrieflyIfMvAtMost n) _ =>
    some s!"Exile {noun}. If that permanent's mana value was {n} or less, return it to the battlefield tapped under your control. Exile it at the beginning of the next end step"
  | .searchLibrary (.mill (.fixed 1) _ _) =>
    some "Search your library for a land card, put it into your graveyard, then shuffle"
  | _ => none

private def phraseCombatCountersAndFlowPart3 (r : @& Resolution) (noun : @& String)
    (sequence : List Resolution → String) : Option String :=
  match r with
  | .putCounters .plusOnePerThreeGraveyardIfFromGy .createdToken =>
    some "If this spell was cast from a graveyard, put a +1/+1 counter on each of them for every three cards in your graveyard"
  | .ifElse .notFromHand (.draw (.fixed 2) _) (.draw (.fixed 1) _) =>
    some "Draw a card. If this spell wasn't cast from your hand, draw two cards instead"
  | .putCounters (.ofKind .plusOnePlusOne 1) (.creaturesControlledBy (.targetAt _)) =>
    some "Put a +1/+1 counter on each creature target player controls"
  | .unlessPays .counter n =>
    some s!"Counter {noun} unless its controller pays \{{n}}"
  | .chooseModes _ (.fraTrigger n) =>
    some (if n == 2 then "choose two" else "choose one")
  | .pump .minusGraveyardCards (.fixed 0) .target =>
    some s!"{capitalizeAscii noun} gets -X/-0 until end of turn, where X is the number of cards in your graveyard"
  | .sequence rs =>
    some (match r.onPermanent? with
    | some action => PermanentAction.toNotation action noun (sentence := true)
    | none =>
      match r.onSource? with
      | some action => PermanentAction.toNotation action "this creature" (sentence := true)
      | none => sequence rs)
  | _ => none

private def phraseCombatCountersAndFlowPart2 (r : @& Resolution) (noun : @& String)
    (sequence : List Resolution → String) : Option String :=
  match r with
  | .dealDamage (.fixed n) (.player .eachPlayer) _ =>
    some s!"This deals {n} damage to each player"
  | .dealDamage (.fixed n) (.targetAt _) .none =>
    some s!"This deals {n} damage to {noun}"
  | .putCounters (.ofKind .plusOnePlusOne n) (.targetAt _) =>
    some s!"Put {plusOnePlusOneCountersPhrase n} on {noun}"
  | .putCounters (.ofKind .plusOnePlusOne n) (.target .eachPermanent) =>
    some s!"Put {plusOnePlusOneCountersPhrase n} on each of {noun}"
  | .putCounters (.ofKind .plusOnePlusOne _) .wizardTokensExceptRecent =>
    some "Put a +1/+1 counter on each other Wizard token you control"
  | .dealDamage (.fixed n) .oppCreaturesAndPlaneswalkers _ =>
    some s!"This deals {n} damage to each creature and planeswalker your opponents control"
  | .may (.sacrifice .planeswalker _) (.searchLibrary (.put .planeswalkerCard _ _)) .ifYouDo =>
    some "You may sacrifice a planeswalker. If you do, search your library for a planeswalker card, put it onto the battlefield, then shuffle"
  | r => phraseCombatCountersAndFlowPart3 r noun sequence

private def phraseCombatCountersAndFlowPart1 (r : @& Resolution) (noun : @& String)
    (sequence : List Resolution → String) : Option String :=
  match r with
  | .may (.discard (.cards 1 .you)) (.draw (.fixed n) .you) .ifYouDo =>
    some s!"You may discard a card. If you do, draw {cardPhrase n.toNat}"
  | .sequence [.dealDamage (.fixed n) .target .excess, .empowerJace .notedExcess] =>
    some s!"This deals {n} damage to {noun}. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage"
  | .sequence [.replace, .dealDamage (.fixed n) .target .none] =>
    some s!"This deals {n} damage to {noun}. If that permanent would die this turn, exile it instead"
  | .dealDamage (.loyalty (.targetAt 0)) (.targetAt 1) _ =>
    some "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls"
  | .dealDamage (.power (.targetAt 0)) (.targetAt 1) _ =>
    some "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls"
  | .dealDamage (.power (.targetAt 1)) (.targetAt 0) .none =>
    some "Target creature you control deals damage equal to its power to that permanent"
  | .proliferate .planeswalkerTypes .youControl =>
    some "Proliferate X times, where X is the number of planeswalker types among planeswalkers you control"
  | r => phraseCombatCountersAndFlowPart2 r noun sequence

private def phraseCombatCountersAndFlowPart1b (r : @& Resolution) (noun : @& String)
    (sequence : List Resolution → String) : Option String :=
  match r with
  | .putCounters .plusOneChosenX .source =>
    some "Put X +1/+1 counters on this"
  | .sequence [.discard (.cards 1 .eachOpponent), .putCounters (.ofKind .plusOnePlusOne 1) .source] =>
    some "Each opponent discards a card. Put a +1/+1 counter on this"
  | .dealDamage (.fixed n) .allCreatures _ =>
    some s!"This deals {n} damage to each creature"
  | .proliferate (.fixed 1) .target =>
    some "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | r => phraseCombatCountersAndFlowPart1 r noun sequence

private def phraseCombatCountersAndFlow (r : @& Resolution) (noun : @& String)
    (sequence : List Resolution → String) : Option String :=
  match r with
  | .pump (.fixed p) (.fixed t) .creaturesYouControl =>
    some s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .dealDamage (.fixed n) .target .none =>
    some s!"This creature deals {n} damage to {noun}"
  | .putCounters (.ofKind .shadow 1) .target =>
    some "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"
  | .dealDamage (.fixed n) (.player .eachOpponent) _ =>
    some s!"This deals {n} damage to each opponent"
  | .putCounters (.ofKind .plusOnePlusOne n) (.othersOfSubtype subtype) =>
    some s!"Put {plusOnePlusOneCountersPhrase n} on each other {subtype} you control"
  | r => phraseCombatCountersAndFlowPart1b r noun sequence

/-- `toPhrase` of one activated-ability resolution. Spell and trigger steps
phrase through `SpellResolution.toPhrase`.

Keep this non-recursive: recursion through `List.map` makes a definition
well-founded, and Lean then compiles a match splitter over every constructor,
which clang takes many seconds to optimize. -/
private def phraseWith (r : Resolution) (noun : String)
    (sequence : List Resolution → String) : String :=
  let opt :=
    match r with
    | .combatCountersOrTokens (some _) .. => phraseGrant r noun
    | .playerResource .. | .zoneOrTap true ..
    | .combatCountersOrTokens none none none (some _) ..
    | .combatCountersOrTokens none none none none (some _) .. =>
      phrasePlayerAndCards r noun
    | .zoneOrTap false .. | .flowOrReveal true .. | .flowOrReveal false none (some _) .. =>
      phraseZoneAndReveal r noun
    | .combatCountersOrTokens .. | .flowOrReveal .. =>
      phraseCombatCountersAndFlow r noun sequence
  match opt with
  | some s => s
  | none =>
    match r.onPermanent? with
    | some action => PermanentAction.toNotation action noun (sentence := true)
    | none =>
      match r.onSource? with
      | some action => PermanentAction.toNotation action "this creature" (sentence := true)
      | none =>
        SpellResolution.toPhrase r noun

/-- Oracle-style reminder from targeting and resolution. Source-deals-damage
uses the creature as the subject rather than the generic `PermanentAction`
wording. -/
def toPhrase (r : Resolution) (noun : String) : String :=
  phraseWith r noun fun rs => String.intercalate ". " (rs.map (fun step => phraseWith step noun fun _ => ""))

/-- True when resolving `r` as a spell or Saga chapter would do nothing. -/
partial def doesNothingAsSpell (r : Resolution) : Bool :=
  match r with
  | .unrecognized => true
  | .sequence rs => rs.any doesNothingAsSpell
  | _ => false

/-- True when resolving `r` as an activated ability would do nothing. -/
partial def doesNothingAsActivated (r : Resolution) : Bool :=
  match r with
  | .unrecognized => true
  | .sequence rs => rs.any doesNothingAsActivated
  | _ => false

end Resolution

end Mtg.Engine
