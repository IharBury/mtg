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
  | .gainLife (.fixed n) =>
    s!"You gain {n} life"
  | .recruit _ =>
    "Recruit"
  | .amass (.fixed n) .goblin _ _ =>
    s!"Amass Goblins {n.toNat}"
  | .createTokens kind (.fixed n) tapped _ _ _ =>
    capitalizeAscii (TokenKind.createPhrase kind n.toNat (tapped := tapped))
  | .addMana types (.fixed 1) =>
    s!"Add {manaSymbolsText types}"
  | .discard (.cards n) =>
    s!"Discard {cardPhrase n}"
  | .shuffleSource =>
    "Shuffle this into its owner's library"
  | .searchBasicLand =>
    capitalizeAscii (searchBasicLandTappedPhrase "your")
  | .searchLandTypeToHand t =>
    capitalizeAscii (searchLibraryToHandPhrase s!"a {t} card")
  | .exileTop =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .attach .source .target =>
    s!"Attach this Equipment to {noun}"
  | .becomeSubtypeWithLandsPT subtype =>
    s!"This enchantment becomes {indefinite subtype} {subtype} creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .returnFromGraveyardTapped =>
    "Return this card from your graveyard to the battlefield tapped"
  | .returnFromGraveyardToHand =>
    "Return this card from your graveyard to your hand"
  | .creaturesYouControlPump p t =>
    s!"Creatures you control get {signedStat p}/{signedStat t} until end of turn"
  | .mill (.fixed n) _ _ =>
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
    s!"{StaticAbility.joinedSubtypes subtypes CardSubtype.pluralName} you control gain menace until end of turn"
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
  | .drawEqualToLastKnownPower =>
    "Draw cards equal to the sacrificed creature's power"
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
  | .drawEqualToBurdenCounters =>
    "Draw a card for each burden counter on this"
  | .teamGain k =>
    s!"Creatures you control gain {k.joinedAnd} until end of turn"
  | .plusOneOnEachOtherSubtype subtype n =>
    s!"Put {plusOnePlusOneCountersPhrase n} on each other {subtype} you control"
  | .extraTurn =>
    "Take an extra turn after this one. During that turn, power-up abilities can't be activated"
  | .plusOneX =>
    "Put X +1/+1 counters on this"
  | .eachOppDiscardThenPlusOne =>
    "Each opponent discards a card. Put a +1/+1 counter on this"
  | .lookAtTopPutTypes n types =>
    let names := (types.map CardSubtype.englishName).toList
    let listed := orJoin names
    let art := indefinite (names[0]?.getD "")
    s!"Look at the top {n} cards of your library. You may put {art} {listed} card from among them onto the battlefield. If it's a double-faced card, you may transform it. {restOnBottomRandomPhrase}"
  | .transform =>
    "Transform this"
  | .drawX =>
    "Draw X cards"
  | .lookAtTopRevealArtifact n =>
    s!"Look at the top {n} cards of your library. You may reveal an artifact card from among them and put it into your hand. {restOnBottomRandomPhrase}"
  | .connive .source =>
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
  | .dealDamageToEachCreature n .each .fixed =>
    s!"This deals {n} damage to each creature"
  | .createTokensEqualRemovedPlusOnes kind =>
    s!"Create that many {kind.pluralNoun}"
  | .exileTopXPlayThisTurn =>
    "Exile the top X cards of your library, where X is this creature's power. You may play those cards this turn"
  | .targetPlayerDraw n =>
    s!"{noun} draws {cardPhrase n}"
  | .copyControlledAbility ty =>
    let w := ty.oracleWord
    s!"Copy target activated or triggered ability you control from {indefinite w} {w} source. You may choose new targets for the copy"
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
  | .createTigerGod =>
    "Create The Tiger God, a legendary 4/4 green Cat God creature token with \"The Tiger God can't be blocked by more than one creature.\""
  | .chooseOddOrEvenDestroy =>
    "Choose odd or even. Destroy each other creature with mana value of the chosen quality"
  | .returnFromGyFinalityAttach =>
    "Return this card from your graveyard to the battlefield with a finality counter on him. Then you may attach an Equipment you control to him"
  | .revealTopDrawIfArtifact =>
    "Reveal the top card of your library. If it's an artifact card, draw a card"
  | .copyArtifactYouControlNotLegendary =>
    "Target artifact you control becomes a copy of a second target artifact you control until end of turn, except it isn't legendary"
  | .becomeTypes types p t k =>
    let joined :=
      if k.reach && k.vigilance then "reach and vigilance"
      else k.joinedAnd
    let names := (types.map CardSubtype.englishName).toList
    let typeWords := String.intercalate " " names
    let art := indefinite (names[0]?.getD "")
    s!"Until end of turn, this becomes {art} {typeWords} with base power and toughness {p}/{t} and gains {joined}"
  | .nextInstantSorceryCopyIfMvAtMostSourcePower =>
    "When you next cast an instant or sorcery spell with mana value less than or equal to this creature's power this turn, copy that spell. You may choose new targets for the copy"
  | .harnessInfinityStone =>
    "Harness this"
  | .targetSubtypeConnives subtype =>
    s!"Target {subtype} you control connives"
  | .empowerJace (.fixed n) =>
    s!"Empower Jace {n}"
  | .surveil (.fixed n) =>
    s!"Surveil {n}"
  | .millSelf n =>
    s!"Mill {cardPhrase n}"
  | .mayDiscardDraw n =>
    s!"You may discard a card. If you do, draw {cardPhrase n}"
  | .createTokensLifeGained kind =>
    s!"Create X {kind.pluralNoun}, where X is the amount of life you gained this turn"
  | .oppSacrificesGreatestMv =>
    s!"{capitalizeAscii noun} sacrifices a creature or planeswalker with the greatest mana value among creatures and planeswalkers they control"
  | .creaturesWithoutFlyingCantBlock =>
    "Creatures without flying can't block this turn"
  | .targetPlayerLoseLife n =>
    s!"{noun} loses {n} life"
  | .controllerOfTargetLosesLife n =>
    s!"Its controller loses {n} life"
  | .returnTargetSpell =>
    s!"Return {noun} to its owner's hand"
  | .eachCreatureYouControlBecomesPrepared =>
    "Each creature you control becomes prepared"
  | .damageThenEmpowerExcess n =>
    s!"This deals {n} damage to {noun}. If excess damage was dealt to that permanent this way, empower Jace X, where X is that excess damage"
  | .jaceLoyaltyAtInstantSpeed =>
    "Until end of turn, you may activate loyalty abilities of Jace planeswalkers you control on any player's turn any time you could cast an instant"
  | .exileTopMayCastElseDamageOpponents n =>
    s!"Exile the top card of your library. You may cast that card. If you don't, this deals {n} damage to each opponent"
  | .emblemCastSpellDamage n =>
    s!"You get an emblem with \"Whenever you cast a spell, this emblem deals {n} damage to any target.\""
  | .firstDealsStatDamageToSecond useLoyalty =>
    if useLoyalty then
      "Target planeswalker you control deals damage equal to its loyalty to target creature or planeswalker an opponent controls"
    else
      "Target creature you control deals damage equal to its power to target creature or planeswalker an opponent controls"
  | .returnFromGyWithFinality =>
    "Return this card from your graveyard to the battlefield with a finality counter on it"
  | .copyNextInstantSorceryThisTurn =>
    "When you next cast an instant or sorcery spell this turn, copy that spell. You may choose new targets for the copy"
  | .proliferatePlaneswalkerTypesTimes =>
    "Proliferate X times, where X is the number of planeswalker types among planeswalkers you control"
  | .copyEachCreatureOfTargetPlayer =>
    s!"For each creature {noun} controls, create a token that's a copy of that creature, except it has haste and \"At the beginning of the end step, if you don't control a planeswalker, sacrifice this creature.\""
  | .becomeCopyLegendRuleOff =>
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
  match r with
  | .sequence rs => String.intercalate ". " (rs.map (fun step => toPhrase step noun))
  | r => phraseWith r noun fun _ => ""

/-- One spell step on the shared vocabulary. Names that already exist stay
themselves. A few spell shapes land on the activated-ability constructor
that means the same thing. `sequence` is flattened by `ofSpell`. -/
def ofSpellStep : SpellResolution → Resolution
  | .draw (.fixed n) .player => .targetPlayerDraw n.toNat
  | .loseLife (.fixed n) .player => .targetPlayerLoseLife n.toNat
  | .loseLife (.fixed n) (.controller .target) => .controllerOfTargetLosesLife n.toNat
  | .returnTargetToHand .spell => .returnTargetSpell
  | .returnTargetToHand .graveyard => .returnFromGyToHand
  | .creaturesPump p t .youControl => .creaturesYouControlPump p t
  | .createTokens kind .chosenX false .kind .you .none => .createTokensX kind
  | .sequence rs => .sequence (rs.map ofSpellStep)
  | r => r

/-- Lift a spell resolution onto the shared `Resolution` vocabulary. -/
def ofSpell (r : SpellResolution) : Resolution :=
  match r with
  | .sequence rs => .sequence ((rs.map ofSpell).flatMap flatten)
  | r => ofSpellStep r

/-- A shared resolution as a spell step, when every part of it is one.
Activated-ability constructors stay `none`, so `spellResolution` is
`.unrecognized` for them. -/
def toSpellStep : Resolution → Option SpellResolution
  | .returnFromGyToHand => some (.returnTargetToHand .graveyard)
  | .targetPlayerLoseLife n => some (.loseLife n .player)
  | .controllerOfTargetLosesLife n => some (.loseLife n (.controller .target))
  | .returnTargetSpell => some .returnTargetToHand
  | .creaturesYouControlPump p t => some (.creaturesPump p t)
  | .createTokensX kind => some (.createTokens kind .chosenX)
  | .targetPlayerDraw n => some (.draw n .player)
  | .unrecognized | .sequence _ => none
  | .onSource _ | .searchBasicLand | .searchLandTypeToHand _
  | .exileTop | .becomeSubtypeWithLandsPT _
  | .returnFromGraveyardTapped | .returnFromGraveyardToHand
  | .addAnyColor | .returnFromGyAttach | .searchBasicLandToHand
  | .searchTwoBasicsSplit | .subtypesGainMenace _
  | .exileThenReturnNextEnd | .searchBasicBeholdSubtypeUntap _
  | .twoPlayersDraw | .discardLegendarySameNameDraw
  | .dealDamageToAny _ | .drawEqualToLastKnownPower
  | .drawEqualToBurdenCounters | .arwenShare
  | .grantCombatDamageCreateTreasure | .putShadowCounter
  | .damageEachOpponent _ | .chooseTwoDestroyRest
  | .blackGateUnblockable | .plusOneOnEachOtherSubtype _ _
  | .extraTurn | .plusOneX | .eachOppDiscardThenPlusOne
  | .lookAtTopPutTypes _ _ | .transform | .drawX
  | .lookAtTopRevealArtifact _
  | .addAnyColorSpendOnlySubtype _ | .addAnyColorSpendOnlyArtifactSpell
  | .addTwoAnyColorCreatureSources | .addBlueCantNonartifact
  | .addAnyColorEqualToSourcePower | .addFourAnyCombination
  | .addTwoAnyColorEquipment | .drawPerDiscardedThisTurn
  | .createTokensEqualRemovedPlusOnes _ | .exileTopXPlayThisTurn
  | .copyControlledAbility _ | .createTokensEqualSubtype _ _
  | .proliferateEachKind | .equipmentBecomesConstructHero
  | .lookAtTopRevealSubtype _ _ | .millThenPutSubtypeOrEnchantment _ _
  | .createTigerGod | .chooseOddOrEvenDestroy
  | .returnFromGyFinalityAttach | .revealTopDrawIfArtifact
  | .copyArtifactYouControlNotLegendary
  | .becomeTypes _ _ _ _ | .nextInstantSorceryCopyIfMvAtMostSourcePower
  | .harnessInfinityStone | .targetSubtypeConnives _
  | .millSelf _ | .mayDiscardDraw _ | .createTokensLifeGained _
  | .oppSacrificesGreatestMv | .creaturesWithoutFlyingCantBlock
  | .eachCreatureYouControlBecomesPrepared
  | .damageThenEmpowerExcess _ | .jaceLoyaltyAtInstantSpeed
  | .becomeCopyLegendRuleOff | .copyEachCreatureOfTargetPlayer
  | .proliferatePlaneswalkerTypesTimes | .copyNextInstantSorceryThisTurn
  | .returnFromGyWithFinality | .firstDealsStatDamageToSecond _
  | .exileTopMayCastElseDamageOpponents _ | .emblemCastSpellDamage _ => none
  | r => if r.isFra then none else some r

/-- The spell view of `r`. A sequence is a spell sequence only when every
step lifts; otherwise it stays unrecognized, as before. -/
def toSpell (r : Resolution) : Option SpellResolution :=
  match r with
  | .sequence rs =>
    match rs.flatMap flatten |>.mapM toSpellStep with
    | some steps => some (.sequence steps)
    | none => none
  | r => toSpellStep r

/-- Recover the spell view. `onSource` is the spell `onPermanent` of the
same action. Anything that does not lift is `.unrecognized`. -/
def _root_.Mtg.Engine.Effect.spellResolution (e : Effect) : SpellResolution :=
  match e.resolution with
  | .onSource a => .onPermanent a
  | r => r.toSpell.getD .unrecognized

/-- True when resolving `r` as a spell or Saga chapter would do nothing. -/
partial def doesNothingAsSpell (r : Resolution) : Bool :=
  match r with
  | .sequence rs => rs.any doesNothingAsSpell
  | .shuffleSource | .gainLife _ | .damageEachOpponent _ | .recruit _ | .addMana _ _ | .discard _ | .onSource _ => false
  | .empowerJace _ | .surveil _ | .millSelf _ | .mayDiscardDraw _
  | .createTokensLifeGained _ | .oppSacrificesGreatestMv
  | .createTigerGod | .extraTurn | .drawEqualToBurdenCounters
  | .creaturesWithoutFlyingCantBlock | .targetPlayerLoseLife _
  | .controllerOfTargetLosesLife _ | .returnTargetSpell | .chooseOddOrEvenDestroy
  | .eachCreatureYouControlBecomesPrepared | .damageThenEmpowerExcess _
  | .exileTopMayCastElseDamageOpponents _ | .emblemCastSpellDamage _
  | .firstDealsStatDamageToSecond _ | .returnFromGyWithFinality
  | .copyNextInstantSorceryThisTurn | .proliferatePlaneswalkerTypesTimes
  | .copyEachCreatureOfTargetPlayer | .becomeCopyLegendRuleOff
  | .teamGain _ | .jaceLoyaltyAtInstantSpeed | .drawEqualToLastKnownPower => false
  | .searchBasicLand | .searchLandTypeToHand _ | .searchBasicLandToHand | .exileTop => false
  | .unrecognized => true
  | r =>
    if r.isFra then false
    else ({ resolution := r } : Effect).spellResolution == .unrecognized

/-- True when resolving `r` as an activated ability would do nothing. -/
partial def doesNothingAsActivated (r : Resolution) : Bool :=
  match r with
  | .unrecognized => true
  | .sequence rs => rs.any doesNothingAsActivated
  | _ => false

end Resolution

end Mtg.Engine
