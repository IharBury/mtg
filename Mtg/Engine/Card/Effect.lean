import Mtg.Engine.Card.AbilityResolution
import Mtg.Engine.Card.SharedTrigger
import Mtg.Engine.Card.StaticAbility

/-!
# Unified one-shot effects (CR 608)

The `Effect` structure shared by spells, activated abilities, Saga
chapters, and triggered abilities, plus the shared `Resolution` vocabulary
they resolve through.
-/

namespace Mtg.Engine

/-- How an `Effect` resolves (CR 608). Shared shapes (`draw`, `scry`,
`onPermanent`, …) are used by spells, activated abilities, chapters, and
triggers. Spell-only and trigger leftovers stay nested so the C runtime
tag stays under the limit. Activated-ability leftovers live here so
`Resolution.toPhrase` and `Effect.mkAbility` cover every resolution. -/
inductive Resolution where
  /-- Draw `n` cards. -/
  | draw (n : Nat)
  /-- Scry `n`. -/
  | scry (n : Nat)
  /-- Affect a still-legal permanent target. -/
  | onPermanent (action : PermanentAction)
  /-- Affect the source if it is still on the battlefield. -/
  | onSource (action : PermanentAction)
  /-- You gain `n` life. -/
  | gainLife (n : Nat)
  /-- Recruit. -/
  | recruit
  /-- Amass Goblins `n`. -/
  | amassGoblins (n : Nat)
  /-- Create `n` tokens of this kind. -/
  | createTokens (kind : TokenKind) (n : Nat) (tapped : Bool := false)
  /-- Add these mana types. -/
  | addMana (types : Array ManaType)
  /-- Discard `n` cards. -/
  | discard (n : Nat)
  /-- Owner shuffles the source into their library. -/
  | shuffleSource
  /-- Search for a basic land, put it onto the battlefield tapped, then shuffle. -/
  | searchBasicLand
  /-- Search for a card with this land type, put it into your hand, then shuffle. -/
  | searchLandTypeToHand (landType : String)
  /-- Exile the top card and grant permission to play it. -/
  | exileTop
  /-- Attach this Equipment to the announced creature. -/
  | attach
  /-- Become this subtype with lands-you-control P/T. -/
  | becomeSubtypeWithLandsPT (subtype : String)
  /-- Return the source from the graveyard to the battlefield tapped. -/
  | returnFromGraveyardTapped
  /-- Return the source from the graveyard to its owner's hand. -/
  | returnFromGraveyardToHand
  /-- Creatures you control get +P/+T until end of turn. -/
  | creaturesYouControlPump (power toughness : Int)
  /-- Target player mills `n` cards. -/
  | mill (n : Nat)
  /-- Add one mana of any color. -/
  | addAnyColor
  /-- Return from the graveyard attached to the targeted creature. -/
  | returnFromGyAttach
  /-- Search for a basic land and put it into hand. -/
  | searchBasicLandToHand
  /-- Create X tokens of this kind. -/
  | createTokensX (kind : TokenKind)
  /-- Search two basics; one tapped, one to hand. -/
  | searchTwoBasicsSplit
  /-- These subtypes you control gain menace. -/
  | subtypesGainMenace (subtypes : Array String)
  /-- Exile then return at the next end step. -/
  | exileThenReturnNextEnd
  /-- Search a basic tapped, then behold this subtype to untap it. -/
  | searchBasicBeholdSubtypeUntap (subtype : String)
  /-- Two players each draw. -/
  | twoPlayersDraw
  /-- Discard a same-name legendary; draw two. -/
  | discardLegendarySameNameDraw
  /-- Deal `n` to any target. -/
  | dealDamageToAny (n : Nat)
  /-- Draw equal to sacrificed power, then discard. -/
  | drawEqualSacrificedPowerThenDiscard
  /-- Arwen share. -/
  | arwenShare
  /-- Grant a combat-damage Treasure trigger. -/
  | grantCombatDamageCreateTreasure
  /-- Put a shadow counter. -/
  | putShadowCounter
  /-- Damage each opponent. -/
  | damageEachOpponent (n : Nat)
  /-- Choose two, destroy the rest. -/
  | chooseTwoDestroyRest
  /-- Black Gate unblockable. -/
  | blackGateUnblockable
  /-- Burden then draw. -/
  | burdenThenDraw
  /-- Creatures you control gain this keyword. -/
  | teamGain (k : Keywords)
  /-- Source gains indestructible and taps. -/
  | sourceGainsIndestructibleTap
  /-- +1/+1 on each other permanent of this subtype. -/
  | plusOneOnEachOtherSubtype (subtype : String) (n : Nat)
  /-- +1/+1 and an indestructible counter on the source. -/
  | plusOneAndIndestructibleCounter
  /-- +1/+1 on the source and an extra turn. -/
  | plusOneAndExtraTurn
  /-- X +1/+1 counters on the source. -/
  | plusOneX
  /-- Each opponent discards; +1/+1 on the source. -/
  | eachOppDiscardThenPlusOne
  /-- Look at the top `n`; put a card of one of these types onto the battlefield. -/
  | lookAtTopPutTypes (n : Nat) (types : Array String)
  /-- Transform the source. -/
  | transform
  /-- Draw X cards. -/
  | drawX
  /-- Look at the top `n`; reveal an artifact to hand. -/
  | lookAtTopRevealArtifact (n : Nat)
  /-- The source connives. -/
  | connive
  /-- Add one mana of any color, spendable only on this subtype's spells or sources. -/
  | addAnyColorSpendOnlySubtype (subtype : String)
  /-- Add one mana of any color, spendable only to cast an artifact spell. -/
  | addAnyColorSpendOnlyArtifactSpell
  /-- Add two mana of any one color, spendable only on creature-source abilities. -/
  | addTwoAnyColorCreatureSources
  /-- Add {U} that can't be spent to cast a nonartifact spell. -/
  | addBlueCantNonartifact
  /-- Add X mana of any one color, where X is this creature's power. -/
  | addAnyColorEqualToSourcePower
  /-- Add four mana in any combination of colors. -/
  | addFourAnyCombination
  /-- Add two mana of any one color, spendable only on Equipment spells or equip. -/
  | addTwoAnyColorEquipment
  /-- Draw a card for each card you've discarded this turn. -/
  | drawPerDiscardedThisTurn
  /-- This deals `n` damage to each creature. -/
  | dealDamageToEachCreature (n : Nat)
  /-- Create that many tokens of this kind (X = removed +1/+1 counters). -/
  | createTokensEqualRemovedPlusOnes (kind : TokenKind)
  /-- Exile the top X cards; you may play them this turn. -/
  | exileTopXPlayThisTurn
  /-- Target player draws `n` cards. -/
  | targetPlayerDraw (n : Nat)
  /-- Copy target activated or triggered ability you control from this source type. -/
  | copyControlledAbility (fromCreature : Bool)
  /-- Create tokens equal to the number of permanents you control of this subtype. -/
  | createTokensEqualSubtype (kind : TokenKind) (subtype : String)
  /-- For each kind of counter on target permanent or player, give another of that kind. -/
  | proliferateEachKind
  /-- If this Equipment isn't a creature, it becomes a 0/0 Construct Hero with flying. -/
  | equipmentBecomesConstructHero
  /-- Look at the top `n`; you may reveal a card of this subtype and put it into your hand. -/
  | lookAtTopRevealSubtype (n : Nat) (subtype : String)
  /-- Mill `n`. You may put a card of this subtype or an enchantment into your hand. -/
  | millThenPutSubtypeOrEnchantment (n : Nat) (subtype : String)
  /-- Put a +1/+1 counter and a double strike counter on this. -/
  | plusOneAndDoubleStrikeCounter
  /-- Put a +1/+1 counter on this. It fights up to one target creature an opponent controls. -/
  | plusOneThenFightUpToOne
  /-- Put a +1/+1 counter on this and create The Tiger God. -/
  | plusOneAndCreateTigerGod
  /-- Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with that MV. -/
  | plusTwoThenOddEvenDestroy
  /-- Return this from your graveyard with a finality counter. Then you may attach an Equipment. -/
  | returnFromGyFinalityAttach
  /-- Return up to one target creature card from your graveyard to your hand. Put `n` +1/+1 counters on this. -/
  | returnGyCreatureThenPlusOne (n : Nat)
  /-- Reveal the top card. If it's an artifact, draw a card. -/
  | revealTopDrawIfArtifact
  /-- Target artifact you control becomes a copy of a second until EOT, except it isn't legendary. -/
  | copyArtifactYouControlNotLegendary
  /-- Target creature you control that's attacking alone gets +1/+0. You gain 1 life. -/
  | pumpAttackingAloneGainLife
  /-- Until end of turn, this becomes these types with base P/T and these keywords. -/
  | becomeTypes (types : Array String) (power toughness : Int) (k : Keywords)
  /-- When you next cast an instant or sorcery with MV ≤ this's power this turn, copy it. -/
  | nextInstantSorceryCopyIfMvAtMostSourcePower
  /-- Harness this Infinity Stone. -/
  | harnessInfinityStone
  /-- Destroy target noncreature artifact or noncreature enchantment. -/
  | destroyTargetNoncreatureArtOrEnch
  /-- Target permanent you control of this subtype connives. -/
  | targetSubtypeConnives (subtype : String)
  /-- Apply each resolution in the given list, in order. -/
  | sequence (rs : List Resolution)
  /-- Spell-only resolution leftover. -/
  | spell (r : SpellResolution)
  /-- Trigger leftover (timing stays on the shared trigger effect). -/
  | trigger (e : SharedTrigger)
deriving Repr, Inhabited, BEq

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

/-- Recover the leftover spell resolution (common shapes lift back). -/
def spellResolution (e : Effect) : SpellResolution :=
  match e.resolution with
  | .spell r => r
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .amassGoblins n => .amassGoblins n
  | .createTokens kind n _ => .createTokens kind n
  | .onSource a => .onPermanent a
  | .creaturesYouControlPump p t => .creaturesYouControlPump p t
  | .createTokensX kind => .createTokensX kind
  | .dealDamageToEachCreature n => .dealDamageToEachCreature n
  | .targetPlayerDraw n => .targetPlayerDraw n
  | .sequence rs =>
    match rs with
    | [.draw n, .discard 1] => .drawThenDiscard n
    | [.spell (.drawAndLoseLife 1 1), .amassGoblins n] => .drawLoseLifeThenAmass n
    | [.createTokens kind n _, .creaturesYouControlPump p t] =>
      .createTokensThenTeamPump kind n p t
    | [.createTokens kind n _, .spell (.creaturesYouControlPump p t)] =>
      .createTokensThenTeamPump kind n p t
    | [.onPermanent .destroy, .gainLife n] => .destroyArtifactOrEnchantmentGainLife n
    | _ => .extraLand
  | _ => .extraLand

/-- Recover a Saga chapter stored on this effect, if any. -/
def asChapter? (e : Effect) : Option ChapterResolution :=
  match e.resolution with
  | .trigger (.chapter _ ce) => some ce
  | _ => none

/-- Recover the leftover shared trigger stored on this effect, if any. -/
def asTrigger? (e : Effect) : Option SharedTrigger :=
  match e.resolution with
  | .trigger te => some te
  | _ => none

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

/-- Oracle-style reminder from targeting and resolution. Source-deals-damage
uses the creature as the subject rather than the generic `PermanentAction`
wording. Adding a constructor is a compile error here rather than silently
skipping the new effect. -/
def toPhrase (r : Resolution) (noun : String) : String :=
  match r with
  | .draw n =>
    s!"Draw {cardPhrase n}"
  | .scry n =>
    s!"Scry {n}"
  | .onPermanent (.dealDamage n) =>
    s!"This creature deals {n} damage to {noun}"
  | .onPermanent action =>
    PermanentAction.toNotation action noun (sentence := true)
  | .onSource action =>
    PermanentAction.toNotation action "this creature" (sentence := true)
  | .gainLife n =>
    s!"You gain {n} life"
  | .recruit =>
    "Recruit"
  | .amassGoblins n =>
    s!"Amass Goblins {n}"
  | .createTokens kind n tapped =>
    capitalizeAscii (TokenKind.createPhrase kind n (tapped := tapped))
  | .addMana types =>
    s!"Add {manaSymbolsText types}"
  | .discard n =>
    s!"Discard {cardPhrase n}"
  | .shuffleSource =>
    "Shuffle this into its owner's library"
  | .searchBasicLand =>
    capitalizeAscii (searchBasicLandTappedPhrase "your")
  | .searchLandTypeToHand t =>
    capitalizeAscii (searchLibraryToHandPhrase s!"a {t} card")
  | .exileTop =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .attach =>
    s!"Attach this Equipment to {noun}"
  | .becomeSubtypeWithLandsPT subtype =>
    s!"This enchantment becomes {indefinite subtype} {subtype} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .returnFromGraveyardTapped =>
    "Return this card from your graveyard to the battlefield tapped"
  | .returnFromGraveyardToHand =>
    "Return this card from your graveyard to your hand"
  | .creaturesYouControlPump p t =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .mill n =>
    s!"{noun} mills {n} cards"
  | .addAnyColor =>
    "Add one mana of any color"
  | .returnFromGyAttach =>
    s!"Return this card from your graveyard to the battlefield attached to {noun}"
  | .searchBasicLandToHand =>
    capitalizeAscii (searchLibraryToHandPhrase "a basic land card")
  | .createTokensX kind =>
    s!"Create X {kind.pluralNoun}"
  | .searchTwoBasicsSplit =>
    "Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle"
  | .subtypesGainMenace subtypes =>
    s!"{StaticAbility.joinedSubtypes subtypes StaticAbility.pluralSubtype} you control gain menace until end of turn"
  | .exileThenReturnNextEnd =>
    "Exile up to two other target nonland permanents you control. Return those cards to the battlefield under their owner's control at the beginning of the next end step"
  | .searchBasicBeholdSubtypeUntap subtype =>
    s!"{capitalizeAscii (searchBasicLandTappedPhrase "your")}. You may behold {indefinite subtype} {subtype}. If you do, untap that land"
  | .twoPlayersDraw =>
    "Two target players each draw a card"
  | .discardLegendarySameNameDraw =>
    "Draw two cards"
  | .dealDamageToAny n =>
    s!"This creature deals {n} damage to any target"
  | .drawEqualSacrificedPowerThenDiscard =>
    "Draw cards equal to the sacrificed creature's power, then discard a card"
  | .arwenShare =>
    "Another target creature gains indestructible until end of turn. Put a +1/+1 counter and a lifelink counter on that creature and a +1/+1 counter and a lifelink counter on Arwen"
  | .grantCombatDamageCreateTreasure =>
    "Until end of turn, target creature gains \"Whenever this creature deals combat damage to a player, create a Treasure token.\""
  | .putShadowCounter =>
    "Put a shadow counter on target creature. For as long as that creature has a shadow counter on it, it's a Wraith in addition to its other types"
  | .damageEachOpponent n =>
    s!"This deals {n} damage to each opponent"
  | .chooseTwoDestroyRest =>
    "Choose up to two creatures, then destroy the rest"
  | .blackGateUnblockable =>
    "Choose a player with the most life or tied for most life. Target creature can't be blocked by creatures that player controls this turn"
  | .burdenThenDraw =>
    "Put a burden counter on The One Ring, then draw a card for each burden counter on The One Ring"
  | .teamGain k =>
    s!"Creatures you control gain {k.joinedAnd} until end of turn"
  | .sourceGainsIndestructibleTap =>
    "Witch-king of Angmar gains indestructible until end of turn. Tap him"
  | .plusOneOnEachOtherSubtype subtype n =>
    s!"Put {plusOnePlusOneCountersPhrase n} on each other {subtype} you control"
  | .plusOneAndIndestructibleCounter =>
    "Put a +1/+1 counter and an indestructible counter on this"
  | .plusOneAndExtraTurn =>
    "Put a +1/+1 counter on this. Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  | .plusOneX =>
    "Put X +1/+1 counters on this"
  | .eachOppDiscardThenPlusOne =>
    "Each opponent discards a card. Put a +1/+1 counter on this"
  | .lookAtTopPutTypes n types =>
    let listed := orJoin types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Put two +1/+1 counters on this, then look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
  | .transform =>
    "Transform this"
  | .drawX =>
    "Draw X cards"
  | .lookAtTopRevealArtifact n =>
    s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .connive =>
    "This creature connives"
  | .addAnyColorSpendOnlySubtype subtype =>
    s!"Add one mana of any color. Spend this mana only to cast {indefinite subtype} {subtype} spell or to activate an ability of {indefinite subtype} {subtype} source"
  | .addAnyColorSpendOnlyArtifactSpell =>
    "Add one mana of any color. Spend this mana only to cast an artifact spell"
  | .addTwoAnyColorCreatureSources =>
    "Add two mana of any one color. Spend this mana only to activate abilities of creature sources"
  | .addBlueCantNonartifact =>
    "Add {U}. This mana can't be spent to cast a nonartifact spell"
  | .addAnyColorEqualToSourcePower =>
    "Add X mana of any one color, where X is this creature's power"
  | .addFourAnyCombination =>
    "Add four mana in any combination of colors"
  | .addTwoAnyColorEquipment =>
    "Add two mana of any one color. Spend this mana only to cast Equipment spells or activate equip abilities"
  | .drawPerDiscardedThisTurn =>
    "Draw a card for each card you've discarded this turn"
  | .dealDamageToEachCreature n =>
    s!"This deals {n} damage to each creature"
  | .createTokensEqualRemovedPlusOnes kind =>
    s!"Create that many {kind.pluralNoun}"
  | .exileTopXPlayThisTurn =>
    "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"
  | .targetPlayerDraw n =>
    s!"{noun} draws {cardPhrase n}"
  | .copyControlledAbility fromCreature =>
    let src := if fromCreature then "a creature" else "an artifact"
    s!"Copy target activated or triggered ability you control from {src} source. You may choose new targets for the copy"
  | .createTokensEqualSubtype kind subtype =>
    s!"Create X {kind.pluralNoun}, where X is the number of {subtype}s you control"
  | .proliferateEachKind =>
    "For each kind of counter on target permanent or player, give that permanent or player another counter of that kind"
  | .equipmentBecomesConstructHero =>
    "If this Equipment isn't a creature, it becomes a 0/0 Construct Hero artifact creature with flying and \"This creature gets +1/+1 for each artifact you control\" until end of turn"
  | .lookAtTopRevealSubtype n subtype =>
    s!"Look at the top {n} cards of your library. You may reveal a {subtype} card from among them and put it into your hand. Put the rest on the bottom of your library in any order"
  | .millThenPutSubtypeOrEnchantment n subtype =>
    s!"Mill {n} cards. You may put {indefinite subtype} {subtype} or enchantment card from among those cards into your hand"
  | .plusOneAndDoubleStrikeCounter =>
    "Put a +1/+1 counter and a double strike counter on this"
  | .plusOneThenFightUpToOne =>
    "Put a +1/+1 counter on this. This fights up to one target creature an opponent controls"
  | .plusOneAndCreateTigerGod =>
    "Put a +1/+1 counter on this and create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .plusTwoThenOddEvenDestroy =>
    "Put two +1/+1 counters on this. Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .returnFromGyFinalityAttach =>
    "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .returnGyCreatureThenPlusOne n =>
    s!"Return up to one target creature card from your graveyard to your hand. Put {plusOnePlusOneCountersPhrase n} on this creature"
  | .revealTopDrawIfArtifact =>
    "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .copyArtifactYouControlNotLegendary =>
    "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .pumpAttackingAloneGainLife =>
    "Target creature you control that's attacking alone gets +1/+0 until end of turn. You gain 1 life"
  | .becomeTypes types p t k =>
    let joined :=
      if k.reach && k.vigilance then "reach and vigilance"
      else k.joinedAnd
    let typeWords := String.intercalate " " types.toList
    let art := indefinite (types[0]?.getD "")
    s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {p}/{t} and gains {joined}"
  | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
    "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"
  | .harnessInfinityStone =>
    "Harness this"
  | .destroyTargetNoncreatureArtOrEnch =>
    "Destroy target noncreature artifact or noncreature enchantment"
  | .targetSubtypeConnives subtype =>
    s!"Target {subtype} you control connives"
  | .sequence rs =>
    String.intercalate ". " (rs.map (fun step => toPhrase step noun))
  | .spell r =>
    SpellResolution.toPhrase r noun
  | .trigger _ =>
    ""

/-- Lift a spell resolution onto the shared `Resolution` vocabulary. -/
def ofSpell : SpellResolution → Resolution
  | .draw n => .draw n
  | .scry n => .scry n
  | .onPermanent a => .onPermanent a
  | .drawThenDiscard n => .sequence [.draw n, .discard 1]
  | .amassGoblins n => .amassGoblins n
  | .createTokens kind n => .createTokens kind n
  | .drawLoseLifeThenAmass n =>
    .sequence [.spell (.drawAndLoseLife 1 1), .amassGoblins n]
  | .createTokensThenTeamPump kind n p t =>
    .sequence [.createTokens kind n, .creaturesYouControlPump p t]
  | .destroyArtifactOrEnchantmentGainLife n =>
    .sequence [.onPermanent .destroy, .gainLife n]
  | .creaturesYouControlPump p t => .creaturesYouControlPump p t
  | .createTokensX kind => .createTokensX kind
  | .dealDamageToEachCreature n => .dealDamageToEachCreature n
  | .targetPlayerDraw n => .targetPlayerDraw n
  | r => .spell r

/-- Store a shared trigger on `Resolution`. Timing stays on the nested
effect so leftover family events remain recoverable. -/
def ofSharedTrigger (e : SharedTrigger) : Resolution :=
  .trigger e

end Resolution

end Mtg.Engine
