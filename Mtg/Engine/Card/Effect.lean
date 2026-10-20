import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.SharedTrigger
import Mtg.Engine.Card.StaticAbility

/-!
# Unified one-shot effects (CR 608)

The `Effect` structure shared by spells, activated abilities, Saga
chapters, and triggered abilities. They resolve through `Resolution`
(`SpellResolution` and `TriggeredAbility.TriggerResolution` name that
inductive).
-/

namespace Mtg.Engine



/-- Unified one-shot effect for spells, activated abilities, Saga chapters,
and triggered abilities. Targeting, printed wording, and resolution live
here so Game has one apply path. -/
structure Effect where
  targeting : EffectTargeting := .of .none
  allowsZeroTargets : Bool := false
  maxTargets : Nat := 0
  dividedDamage : Option (Nat × Nat) := none
  spellCastKind : SpellCastKind := .extraLand
  abilityCastKind : AbilityCastKind := .other
  preferAsDefaultMode : Bool := false
  resolution : Resolution := .draw 0
  /-- Shared trigger this effect was built from, when any.
  `asTrigger?` and `asChapter?` read it. The steps themselves are `resolution`. -/
  sharedTrigger : Option SharedTrigger := none
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

/-- Recover a Saga chapter stored on this effect, if any. -/
def asChapter? (e : Effect) : Option ChapterResolution :=
  match e.sharedTrigger with
  | some (.chapter _ ce) => some ce
  | _ => none

/-- Recover the leftover shared trigger stored on this effect, if any. -/
def asTrigger? (e : Effect) : Option SharedTrigger :=
  e.sharedTrigger

/-- Oracle-style reminder text. -/
def toNotation (e : Effect) : String :=
  e.phrase

instance : HasTargeting Effect where
  targeting e := e.targeting

instance : ToString Effect where
  toString := toNotation

end Effect

namespace Resolution

/-- Nested `sequence` constructors, left to right. -/
def flatten : Resolution → List Resolution
  | .sequence rs => rs.flatMap flatten
  | r => [r]

/-- `toPhrase` of one activated-ability resolution. Spell and trigger steps
phrase through `SpellResolution.toPhrase`.

Keep this non-recursive: recursion through `List.map` makes a definition
well-founded, and Lean then compiles a match splitter over every constructor,
which clang takes many seconds to optimize. -/
private def phraseWith (r : Resolution) (noun : String)
    (sequence : List Resolution → String) : String :=
  match r with
  | .draw (.fixed n) .you =>
    s!"Draw {cardPhrase n.toNat}"
  | .scry (.fixed n) =>
    s!"Scry {n}"
  | .onPermanent (.dealDamage n) =>
    s!"This creature deals {n} damage to {noun}"
  | .onPermanent action =>
    PermanentAction.toNotation action noun (sentence := true)
  | .onSource action =>
    PermanentAction.toNotation action "this creature" (sentence := true)
  | .gainLife (.fixed n) .you =>
    s!"You gain {n} life"
  | .recruit _ =>
    "Recruit"
  | .amass (.fixed n) "Goblin" _ _ =>
    s!"Amass Goblins {n.toNat}"
  | .createTokens .tigerGod (.fixed 1) false _ _ =>
    "Create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .createTokens kind (.fixed n) tapped _ _ =>
    capitalizeAscii (TokenKind.createPhrase kind n.toNat (tapped := tapped))
  | .createTokens kind .chosenX _ _ _ =>
    s!"Create X {kind.pluralNoun}"
  | .createTokens kind (.perSubtype subtype) _ _ _ =>
    s!"Create X {kind.pluralNoun}, where X is the number of {subtype}s you control"
  | .addMana types (.fixed 1) .none =>
    s!"Add {manaSymbolsText types}"
  | .addMana #[] (.fixed 1) .anyColor =>
    "Add one mana of any color"
  | .addMana #[] (.fixed 1) (.subtypeSpellsOrAbilities subtype) =>
    s!"Add one mana of any color. Spend this mana only to cast {indefinite subtype} {subtype} spell or to activate an ability of {indefinite subtype} {subtype} source"
  | .addMana #[] (.fixed 1) .artifactSpell =>
    "Add one mana of any color. Spend this mana only to cast an artifact spell"
  | .addMana #[] (.fixed 2) .creatureSources =>
    "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addMana #[.colored .blue] (.fixed 1) .cantNonartifact =>
    "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addMana #[] .equalSourcePower .anyColor =>
    "Add X mana of any one color, where X is this creature's power"
  | .addMana #[] (.fixed 4) .anyCombination =>
    "Add four mana in any combination of colors"
  | .addMana #[] (.fixed 2) .equipment =>
    "Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities"
  | .discard (.cards n) =>
    s!"Discard {cardPhrase n}"
  | .putOnLibrary .shuffled .source =>
    "Shuffle this into its owner's library"
  | .searchLibrary (.put .basicLand .tapped _) =>
    capitalizeAscii (searchBasicLandTappedPhrase "your")
  | .searchLibrary (.returnToHand (.landSubtype t) _) =>
    capitalizeAscii (searchLibraryToHandPhrase s!"a {t} card")
  | .exile .top .playUntilNextTurn =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .attach .source .target =>
    s!"Attach this Equipment to {noun}"
  | .grant (.subtypeWithLandsPT subtype) .source =>
    s!"This enchantment becomes {indefinite subtype} {subtype} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .put .source .tapped .none =>
    "Return this card from your graveyard to the battlefield tapped"
  | .returnToHand .source _ =>
    "Return this card from your graveyard to your hand"
  | .pump (.fixed p) (.fixed t) .creaturesYouControl =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .mill (.fixed n) .you .none =>
    s!"Mill {cardPhrase n.toNat}"
  | .mill (.fixed n) .you (.subtypeOrEnchantmentToHand subtype) =>
    s!"Mill {n} cards. You may put {indefinite subtype} {subtype} or enchantment card from among those cards into your hand"
  | .mill (.fixed n) .player .none =>
    s!"{noun} mills {n} cards"
  | .put .source .asPrinted .forAttach =>
    s!"Return this card from your graveyard to the battlefield attached to {noun}"
  | .searchLibrary (.returnToHand .basicLand _) =>
    capitalizeAscii (searchLibraryToHandPhrase "a basic land card")
  | .searchLibrary (.sequence [.put .basicLand .tapped _, .returnToHand .basicLand _]) =>
    "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"
  | .grant (.keywords _) (.intersection [.creaturesYouControl, .union what]) =>
    let subtypes := (what.filterMap fun | .youControl (.subtype s) => some s | _ => none).toArray
    s!"{StaticAbility.joinedSubtypes subtypes StaticAbility.pluralSubtype} you control gain menace until end of turn"
  | .exile (.target .eachPermanent) .nextEndStep _ =>
    "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"
  | .searchLibrary (.put (.basicBeholdUntap subtype) .tapped _) =>
    s!"{capitalizeAscii (searchBasicLandTappedPhrase "your")}. You may behold {indefinite subtype} {subtype}. If you do, untap that land"
  | .draw (.fixed 1) .targetPlayers =>
    "Two target players each draw a card"
  | .dealDamage (.fixed n) .target .none =>
    s!"This creature deals {n} damage to any target"
  | .draw .lastKnownPower _ =>
    "Draw cards equal to the sacrificed creature's power"
  | .grant .arwenShare .target =>
    "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"
  | .grant .combatDamageCreateTreasure .target =>
    "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
  | .putCounters (.ofKind .shadow 1) .target =>
    "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"
  | .dealDamage (.fixed n) (.player .eachOpponent) _ =>
    s!"This deals {n} damage to each opponent"
  | .destroy .allCreaturesExceptTwoChosen _ =>
    "Choose up to two creatures, then destroy the rest"
  | .cant (.beBlockedByMostLifePlayer .target) =>
    "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"
  | .draw .perBurden _ =>
    "Draw a card for each burden counter on this"
  | .grant (.keywords k) .creaturesYouControl =>
    s!"Creatures you control gain {k.joinedAnd} until end of turn"
  | .putCounters (.ofKind .plusOnePlusOne n) (.othersOfSubtype subtype) =>
    s!"Put {plusOnePlusOneCountersPhrase n} on each other {subtype} you control"
  | .grant .extraTurn .youIfCast =>
    "Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  | .putCounters .plusOneChosenX .source =>
    "Put X +1/+1 counters on this"
  | .sequence [.discard (.cards 1 .eachOpponent), .putCounters (.ofKind .plusOnePlusOne 1) .source] =>
    "Each opponent discards a card. Put a +1/+1 counter on this"
  | .revealLibrary (.top n) (.put (.lookedTypes types) _ _) _ =>
    let listed := orJoin types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
  | .grant .transformed .source =>
    "Transform this"
  | .draw .chosenX _ =>
    "Draw X cards"
  | .revealLibrary (.top n) (.returnToHand .artifact _) _ =>
    s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .connive .source =>
    "This creature connives"
  | .draw .cardsDiscardedThisTurn _ =>
    "Draw a card for each card you've discarded this turn"
  | .dealDamage (.fixed n) .allCreatures _ =>
    s!"This deals {n} damage to each creature"
  | .createTokens kind .removedPlusOnes _ _ _ =>
    s!"Create that many {kind.pluralNoun}"
  | .exile .topPower .playThisTurn _ =>
    "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"
  | .draw (.fixed n) .player =>
    s!"{noun} draws {cardPhrase n.toNat}"
  | .becomeCopy (.stackAbility fromCreature) =>
    let src := if fromCreature then "a creature" else "an artifact"
    s!"Copy target activated or triggered ability you control from {src} source. You may choose new targets for the copy"
  | .proliferate (.fixed 1) .target =>
    "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | .grant .constructHero .source =>
    "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .revealLibrary (.top n) (.returnToHand (.milledSubtype subtype) _) _ =>
    s!"Look at the top {n} cards of your library. You may reveal a {subtype} card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .destroy .otherCreaturesOddOrEvenMv _ =>
    "Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .put .source .asPrinted (.entering [.counter .finality 1 true]) =>
    "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .revealLibrary (.top 1) (.draw (.fixed 1) _) _ =>
    "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .becomeCopy .secondArtifactTargetNotLegendary =>
    "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .grant (.typesPTAndKeywords types p t k) .source =>
    let joined :=
      if k.reach && k.vigilance then "reach and vigilance"
      else k.joinedAnd
    let typeWords := String.intercalate " " types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {p}/{t} and gains {joined}"
  | .grant (.nextSpellCopy true) .source =>
    "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"
  | .grant .harnessed .source =>
    "Harness this"
  | .connive (.target (.youControl (.subtype subtype))) =>
    s!"Target {subtype} you control connives"
  | .empowerJace (.fixed n) =>
    s!"Empower Jace {n}"
  | .surveil (.fixed n) .none =>
    s!"Surveil {n}"
  | .may (.discard (.cards 1 .you)) (.draw (.fixed n) .you) .ifYouDo =>
    s!"You may discard a card. If you do, draw {cardPhrase n.toNat}"
  | .createTokens kind .lifeGainedThisTurn _ _ _ =>
    s!"Create X {kind.pluralNoun}, where X is the amount of life you gained this turn"
  | .sacrifice .oppGreatestMvCreatureOrPlaneswalker _ =>
    s!"{capitalizeAscii noun} sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control"
  | .cant (.block .creaturesWithoutFlying) =>
    "Creatures without flying can't block this turn"
  | .loseLife (.fixed n) .player =>
    s!"{noun} loses {n} life"
  | .loseLife (.fixed n) (.controller .target) =>
    s!"Its controller loses {n} life"
  | .returnToHand .targetSpell _ =>
    s!"Return {noun} to its owner's hand"
  | .returnToHand (.target .graveyardCard) _ =>
    s!"Return {noun} to your hand"
  | .becomePrepared .creaturesYouControl true =>
    "Each creature you control becomes prepared"
  | .sequence [.dealDamage (.fixed n) .target .excess, .empowerJace .notedExcess] =>
    s!"This deals {n} damage to {noun}. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage"
  | .sequence [.replace .diesThisTurn .exile, .onPermanent (.dealDamage n)] =>
    s!"This deals {n} damage to {noun}. If that permanent would die this turn, exile it instead"
  | .grant .jaceLoyaltyAtInstantSpeed .youIfCast =>
    "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant"
  | .exile .top (.mayCastElseDamageOpponents n) _ =>
    s!"Exile the top card of your library. You may cast that card. If you don't, this deals {n} damage to each opponent"
  | .grant (.emblemCastSpellDamage n) .youIfCast =>
    s!"You get an emblem with \"Whenever you cast a spell, this emblem deals {n} damage to any target.\""
  | .dealDamage (.loyalty (.targetAt 0)) (.targetAt 1) _ =>
    "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls"
  | .dealDamage (.power (.targetAt 0)) (.targetAt 1) _ =>
    "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls"
  | .put .source .asPrinted (.entering [.counter .finality 1 false]) =>
    "Return this card from your graveyard to the battlefield with a finality counter on it"
  | .grant (.nextSpellCopy false) .source =>
    "When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy"
  | .proliferate .planeswalkerTypes .youControl =>
    "Proliferate X times, where X is the number of planeswalker types among planeswalkers you control"
  | .becomeCopy (.creaturesControlledBy (.target .player)) =>
    s!"For each creature {noun} controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""
  | .becomeCopy .targetLegendRuleOff =>
    s!"This land becomes a copy of {noun} until end of turn. The \"legend rule\" doesn't apply to permanents you control this turn"
  | .sequence rs =>
    sequence rs
  | r =>
    match r.fraPhrase? noun with
    | some phrase => phrase
    | none => SpellResolution.toPhrase r noun

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
