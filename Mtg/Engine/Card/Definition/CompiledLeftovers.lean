import Mtg.Engine.Card.Definition.TokenLeftovers

/-!
# Compiled leftovers

Leftovers that already name an `Effect` or a `TriggeredAbility`: mill,
Saga chapters, continuous actions, and enters-the-battlefield searches.
-/

namespace Mtg.Engine

namespace CardAction

/-- Mill-then-put sequences that compile to a named `Effect`. -/
def leftoverMillThenPutCompiled? (action : CardAction) : Option Effect :=
  match leftoverMillThenPutPermanentGainLife? action with
  | some (n, life) => some (Effect.millThenPutPermanentGainLife n life)
  | none =>
    match leftoverMillThenPutSubtypeOrEnchantment? action with
    | some (n, st) => some (Effect.millThenPutSubtypeOrEnchantment n st)
    | none =>
      match leftoverMillThenPutLands? action with
      | some (n, max) => some (Effect.millThenPutLands n max)
      | none =>
        match leftoverMillThenPutInstantOrSorcery? action with
        | some n => some (Effect.millThenPutInstantOrSorcery n)
        | none =>
          leftoverMillThenPutAllInstantsOrSorceries? action |>.map
            Effect.millThenPutAllInstantsOrSorceries

/-- Mill n, then put all cards of a subtype from among them into hand. -/
def leftoverMillThenSubtypeToHand? : CardAction → Option (Nat × String)
  | .sequence [.actionId id (.mill who (.nat n)), .returnToHand among] =>
    if leftoverYou who then
      leftoverMilledSubtype? id among |>.map (fun st => (n, st))
    else none
  | _ => none

/-- Combat-damage destination is a player, or a player or battle. -/
def leftoverPlayerOrBattle : Selector → Bool
  | .player => true
  | .union fs =>
    fs.any (fun s => s == .player) &&
      fs.any (fun s => s == .cardType .battle)
  | _ => false

/-- Another nontoken Hero you control enters: create a Soldier or team pump. -/
def leftoverNontokenHeroModal? (among : Selector) : List CardAction → Bool
  | [a, b] =>
    let soldier (x : CardAction) : Bool :=
      leftoverCreateTokensKindN? x == some (.soldier11white, 1)
    let pump (x : CardAction) : Bool :=
      match x with
      | .continuous effects _ =>
        ContinuousEffect.addedPT? effects == some (1, 1) &&
          match ContinuousEffect.massSelector? effects with
          | some s => s.shape.sameController && s.shape.types.eqTypes [.creature]
          | none => false
      | _ => false
    among.shape.other && among.shape.nontoken && among.shape.sameController &&
      among.shape.subtype == some "Hero" &&
      ((soldier a && pump b) || (soldier b && pump a))
  | _ => false

/-- Lose 1 life and create a Treasure (second spell each turn). -/
def leftoverLoseLifeCreateTreasure? : CardAction → Bool
  | .sequence [.loseLife who 1, .createTokens c 1 parts []] =>
    leftoverYou who && leftoverYou c && leftoverTokenKind? parts == some .treasure
  | .sequence [.createTokens c 1 parts [], .loseLife who 1] =>
    leftoverYou who && leftoverYou c && leftoverTokenKind? parts == some .treasure
  | _ => false

/-- You may draw a card for each artifact you control. If you do, each
opponent draws a card. -/
def leftoverMayDrawPerArtifactOppsDraw? : CardAction → Bool
  | .optional (.controller .this)
      (.sequence [
        .forEachVariable _ among [.draw who 1],
        .draw dest 1
      ]) =>
    leftoverYou who && among.shape.artifactYouControl && leftoverOpponents dest
  | _ => false

/-- Artifact spells you cast. -/
def leftoverArtifactSpellsYouCast? : Selector → Bool
  | s => s.shape.isSpell && s.shape.types.eqTypes [.artifact] && s.shape.sameController

/-- Artifact spells you cast this turn cost that much less. -/
def leftoverArtifactSpellsCostLessThisTurn? : CardAction → Option Nat
  | .continuous [.reduceCost who costs] .endOfTurn =>
    let n := ManaCost.manaValue (Cost.manaCost costs)
    if n != 0 && leftoverArtifactSpellsYouCast? who then some n else none
  | _ => none

/-- This deals X damage to target opponent, where X is the greatest mana
value among artifacts you control. -/
def leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv? :
    CardAction → Bool
  | .dealDamage src dest (.greatestManaValue among) =>
    leftoverThis src && leftoverTargetOpponent? dest && among.shape.artifactYouControl
  | _ => false

/-- Leftovers that compile to a named `Effect` only as a printed Saga chapter. -/
def leftoverSagaChapterOnly? (action : CardAction) : Option Effect :=
  match action with
  | .dealDamage src (.target _ sel) (.nat n) =>
    if (src == Selector.this || leftoverSourceThis src) &&
        sel.toTargetKind == EffectTargetKind.oppCreature then
      some (Effect.chapterDealDamageToOppCreature n)
    else none
  | .destroy (.target _ sel) =>
    if sel == Selector.intersection
        [.zone .battlefield, .cardType .artifact, .controlled (.opponent (.controller .this))] then
      some Effect.chapterDestroyOppArtifact
    else none
  | .destroy (.targets _ (.range (.nat 0) (.nat 1)) among) =>
    if among == .intersection [.zone .battlefield, .not (.cardType .land)] then
      some Effect.destroyUpToOneNonland
    else none
  | .loseLife (.opponent (.controller .this)) (.nat n) =>
    some (Effect.eachOpponentLosesLife n)
  | .addMana who [sym] =>
    if leftoverYou who then (addedManaType? sym).map Effect.chapterAddMana else none
  | .searchLibraryThenShuffle who actions =>
    if leftoverYou who && leftoverSearchActions? actions == some Effect.searchBasicLandToHand then
      some Effect.chapterSearchBasicLandToHand
    else none
  | .continuous
      [.gainAbility .this
        (.triggered (.enter lands) (.createTokens who (.nat 1) parts []))] .endOfGame =>
    if lands.shape.landYouControl && leftoverYou who &&
        leftoverTokenKind? parts == some TokenKind.elf then
      some Effect.chapterGainLandfallCreateElf
    else none
  | .sequence [
      treasure,
      .if (.greaterOrEqual (.count sel) (.nat 4)) [
        .actionId id (.sacrifice .this),
        .if (.happened (.actionWithId id') .gameStart) [dragon]]] =>
    if id == id' &&
        sel == Selector.intersection
          [.zone .battlefield, .subtype .treasure, .controlled (.controller .this)] &&
        leftoverCreateTokensKindN? treasure == some (TokenKind.treasure, 1) &&
        leftoverCreateTokensKindN? dragon == some (TokenKind.dragon, 1) then
      some Effect.chapterTreasureThenDragonIfFour
    else none
  | .continuous [.addPower sel (.int p), .gainAbility sel' (.keyword .vigilance)] .endOfTurn =>
    if sel == sel' &&
        sel == Selector.intersection [.zone .battlefield, .subtype .elf, .controlled (.controller .this)] then
      some (Effect.chapterElvesGetVigilance p)
    else none
  | .keyword who (.amass .goblin (.nat n)) =>
    if n != 0 && leftoverYou who then some (Effect.chapterAmassGoblins n) else none
  | .sequence [
      .loseLife (.target _ (.opponent who)) (.nat n),
      .gainLife gainer (.nat n')
    ] =>
    if n != 0 && n == n' && leftoverYou who && leftoverYou gainer then
      some (Effect.chapterOpponentLosesYouGain n)
    else none
  | .sequence [
      .actionId id
        (.reveal
          (.intersection [
            .zone .hand,
            .owner (.target _ (.opponent who))])),
      .defineSelectorVariable v
        (.selected chooser (.range 1 1)
          (.intersection [.wasObjectOfAction id', .not (.cardType .land)])),
      .discard (.variable v') 1
    ] =>
    if id == id' && v == v' && leftoverYou who && leftoverYou chooser then
      some Effect.chapterOpponentDiscardsNonland
    else none
  | .keyword who .recruit =>
    if leftoverYou who then some Effect.chapterRecruit else none
  | .putOntoBattlefield
      (.target _ (.intersection [
        .zone .graveyard,
        .cardType .creature,
        .owner (.controller .this),
        .manaValueAtMost (.nat k)])) =>
    if k != 0 then some (Effect.chapterReturnCreatureFromGyMvAtMost k) else none
  | .putCounter
      (.targets _ (.range (.nat 0) (.nat 1))
        (.intersection [.zone .battlefield, .cardType .creature]))
      .plusOnePlusOne
      (.nat 1) =>
    some Effect.chapterPlusOneUpToOne
  | _ => none

/-- This deals N damage to each creature that isn't of a subtype and to each
opponent. -/
def leftoverDamageNonSubtypeAndOpponents? : CardAction → Option (Nat × String)
  | .sequence [
      .dealDamage src (.intersection [.zone .battlefield, .cardType .creature, .not (.subtype st)]) (.nat n),
      .dealDamage src' (.opponent who) (.nat n')] =>
    if n != 0 && n == n' && (src == .this || src == .source .this) && src == src' &&
        who == .controller .this then
      some (n, st.toString)
    else none
  | _ => none

/-- Legendary 16/16 black Elder Alien Galactus with flying and trample. -/
def leftoverGalactusToken? (parts : List CardPart) : Bool :=
  let p := collectTokenParts parts
  let legendary :=
    parts.any fun
      | .supertype .legendary => true
      | _ => false
  p.name == "Galactus" && legendary && p.types.contains .creature &&
    p.subtypes.contains "Elder" && p.subtypes.contains "Alien" &&
    leftoverIsColor p .black && p.power == some 16 && p.toughness == some 16 &&
    p.keywords.flying && p.keywords.trample

/-- `Create N <token>s.` or `Create a <token> for each <subtype> you control.` -/
def leftoverChapterCreateTokens? : CardAction → Option Effect
  | .createTokens who (.nat n) parts [] =>
    if leftoverYou who && n == 1 && leftoverGalactusToken? parts then
      some Effect.createGalactus
    else if leftoverYou who && n != 0 then
      (leftoverTokenKind? parts).map (Effect.createTokens · n)
    else none
  | .forEachVariable _ (.intersection [.zone .battlefield, .subtype st, .controlled (.controller .this)])
      [.createTokens who (.nat 1) parts []] =>
    if leftoverYou who then
      (leftoverTokenKind? parts).map (Effect.createTokensPerSubtype · st.toString)
    else none
  | _ => none

/-- Saga-chapter leftovers that compile to a named `Effect`. -/
def leftoverChapterCompiled? (action : CardAction) : Option Effect :=
  (leftoverDamageNonSubtypeAndOpponents? action).map (fun (n, st) =>
    Effect.chapterDealDamageToEachNonSubtypeAndOpponents n st) |>.orElse fun _ =>
  if leftoverMayDrawPerArtifactOppsDraw? action then
    some Effect.mayDrawPerArtifactOppsDraw
  else
    match leftoverArtifactSpellsCostLessThisTurn? action with
    | some n => some (Effect.artifactSpellsCostLessThisTurn n)
    | none =>
      if leftoverChapterDealXDamageToTargetOpponentGreatestArtifactMv? action then
        some Effect.chapterDealXDamageToTargetOpponentGreatestArtifactMv
      else none

/-- Compile printed Saga-chapter actions. -/
def leftoverChapterEffect? (actions : List CardAction) : Option Effect :=
  let action :=
    match actions with
    | [a] => a
    | as => .sequence as
  leftoverSagaChapterOnly? action |>.orElse fun _ =>
  leftoverChapterCreateTokens? action |>.orElse fun _ => leftoverChapterCompiled? action

/-- Continuous leftovers that compile to a named `Effect`. -/
def leftoverContinuousCompiled? : CardAction → Option Effect
  | .continuous effects _ =>
    if leftoverGrantCombatDamageCreateTreasure? effects then
      some Effect.grantCombatDamageCreateTreasure
    else
      match leftoverSubtypesGainMenace? effects with
      | some sts => some (Effect.subtypesGainMenace sts)
      | none => leftoverTeamGain? effects |>.map Effect.teamGain
  | _ => none

/-- This selector excludes the numbered target, so a later mass effect
can mean “each other” relative to that target. -/
def leftoverExcludesTarget (n : Nat) : Selector → Bool
  | .not (.targetReference id) => id == n
  | .intersection parts => go parts
  | _ => false
where
  go : List Selector → Bool
    | [] => false
    | .not (.targetReference id) :: rest => id == n || go rest
    | .intersection nested :: rest => go nested || go rest
    | _ :: rest => go rest

/-- Creatures this object's controller controls, not announced as targets.
Power bounds and a +1/+1 counter are a different set of creatures. -/
def leftoverCreaturesYouControlMass? (s : Selector) : Bool :=
  s.among?.isNone &&
    s.shape.sameController &&
    s.shape.mustBePermanent &&
    s.shape.types.eqTypes [.creature] &&
    !s.shape.other &&
    s.shape.subtype.isNone &&
    !s.shape.opponentControls &&
    s.shape.powerAtLeast.isNone &&
    s.shape.powerAtMost.isNone &&
    !s.shape.hasPlusOneCounter &&
    !s.shape.chosenCreatureType

/-- Draw N, or draw more when this spell was cast from a graveyard.
Amass Goblins N, or amass more in that same case. The “instead” branch is
the cast-from-graveyard amount. -/
def leftoverDrawOrAmassIfFromGy? : CardAction → Option Effect
  | .ifElse (.happened (.castSpellFromGraveyard .this) .gameStart) [thenA] [elseA] =>
    match thenA, elseA with
    | .draw whoFrom (.nat fromGy), .draw who (.nat n) =>
      if leftoverYou who && leftoverYou whoFrom then
        some (Effect.drawIfFromGy n fromGy)
      else none
    | .keyword whoFrom (.amass .goblin (.nat fromGy)),
      .keyword who (.amass .goblin (.nat n)) =>
      if leftoverYou who && leftoverYou whoFrom then
        some (Effect.amassGoblinsOrFromGy n fromGy)
      else none
    | _, _ => none
  | _ => none

/-- Put +1/+1 counters on target creature you control, then it fights
target creature an opponent controls. -/
def leftoverPlusOneThenFight? : CardAction → Option Nat
  | .sequence [
      .putCounter (.target id among) .plusOnePlusOne (.nat k),
      .fight (.targetReference id') (.target id2 dest)
    ] =>
    if id == id' && id2 == id + 1 &&
        among.toTargetKind == .creatureYouControl &&
        dest.toTargetKind == .oppCreature then
      some k
    else none
  | _ => none

/-- This object's owner shuffles it into their library and draws N cards.
The owner is recorded before the shuffle and that player draws. -/
def leftoverOwnerShuffleSourceDraw? : CardAction → Option Nat
  | .sequence [
      .defineSelectorVariable id (.owner who),
      .shuffleIntoOwnersLibrary who',
      .draw (.variable id') (.nat n)
    ] =>
    if id == id' && who == who' && (who == .this || who == .source .this) then
      some n
    else none
  | _ => none

/-- Return this card from a graveyard attached to a creature you control
with power at most N. It enters the battlefield already attached
(CR 303.4f). -/
def leftoverReturnFromGyAttachPowerAtMost? : CardAction → Option Int
  | .putOntoBattlefieldInState src [.attachedTo (.target _ among)] =>
    let s := among.shape
    if src == .intersection [.zone .graveyard, .source .this] &&
        s.sameController && s.types.eqTypes [.creature] && s.subtype.isNone then
      s.powerAtMost
    else none
  | _ => none

/-- Put a +1/+1 counter on target creature you control. If this spell was
cast from a graveyard, also put one on each other creature you control.
The cast is an event since the start of the game. -/
def leftoverPlusOneThenEachOtherIfFromGy? : CardAction → Bool
  | .sequence [
      .putCounter (.target id among) .plusOnePlusOne 1,
      .if (.happened (.castSpellFromGraveyard .this) .gameStart)
        [.putCounter others .plusOnePlusOne 1]
    ] =>
    among.toTargetKind == .creatureYouControl &&
      leftoverExcludesTarget id others &&
      leftoverCreaturesYouControlMass? others
  | _ => false

/-- Target creature, with no further restriction. -/
def leftoverCreaturePermanent? : Selector → Bool
  | .intersection [.zone .battlefield, .cardType .creature] => true
  | _ => false

/-- Each creature an opponent of this object's controller controls. -/
def leftoverEachOppCreature? : Selector → Bool
  | .intersection
      [.zone .battlefield, .cardType .creature, .controlled (.opponent (.controller .this))] => true
  | _ => false

/-- Each creature that is not a Dragon. -/
def leftoverEachNonDragonCreature? : Selector → Bool
  | .intersection
      [.zone .battlefield, .cardType .creature, .not (.subtype .dragon)] => true
  | _ => false

/-- Target artifact token. -/
def leftoverArtifactTokenTarget? : Selector → Bool
  | .target _ (.intersection [.zone .battlefield, .cardType .artifact, .token]) => true
  | _ => false

/-- Deal damage to target creature; if it would die this turn, exile it. -/
def leftoverDealDamageExileIfDies? : CardAction → Option Nat
  | .sequence [
      .dealDamage src (.target id among) (.nat n),
      .continuous
        [.replace (.putToGraveyard (.targetReference id')) [.exile .replacingObject]] _
    ] =>
    if id == id' && n != 0 &&
        (src == .this || src == .source .this) &&
        leftoverCreaturePermanent? among then
      some n
    else none
  | _ => none

/-- Destroy target artifact token. -/
def leftoverDestroyArtifactToken? : CardAction → Bool
  | .destroy sel => leftoverArtifactTokenTarget? sel
  | _ => false

/-- Deal damage to each creature opponents control. -/
def leftoverDealDamageToEachOppCreature? : CardAction → Option Nat
  | .dealDamage src dest (.nat n) =>
    if n != 0 && (src == .this || src == .source .this) &&
        leftoverEachOppCreature? dest then
      some n
    else none
  | _ => none

/-- Spend this mana only to cast a Dragon spell. -/
def leftoverDragonSpellSpend? : Trigger → Bool
  | .not (.castSpell (.subtype .dragon)) => true
  | _ => false

/-- Damage each non-Dragon creature, then add four mana in any combination
of colors that can be spent only on Dragon spells. -/
def leftoverNonDragonThenDragonMana? : CardAction → Option Nat
  | .sequence [
      .dealDamage src dest (.nat n),
      .actionId id (.addManaInAnyCombination who syms (.nat k)),
      .continuous [.forbid (.spendManaCreatedByAction id' restriction)] _
    ] =>
    if id == id' && n != 0 && k == 4 &&
        who == .controller .this && syms == ManaSymbol.anyColor &&
        leftoverDragonSpellSpend? restriction &&
        (src == .this || src == .source .this) &&
        leftoverEachNonDragonCreature? dest then
      some n
    else none
  | _ => none

/-- Exile every attacking creature the targeted player controls, then that
player may search for up to that many basic lands and put them in tapped.
The player may find fewer, including none (CR 701.19b). -/
def leftoverExileAttackersSearchBasics? : CardAction → Bool
  | .sequence [
      .actionId id
        (.exile
          (.intersection [
            .zone .battlefield,
            .cardType .creature,
            .attacking .all,
            .controlled (.target tid .player)])),
      .optional chooser
        (.searchLibraryThenShuffle
          (.targetReference sid)
          [
            .putOntoBattlefieldInState
              (.selected
                (.targetReference sid')
                (.range (.nat 0) (.count (.wasObjectOfAction cid)))
                (.intersection [
                  .zone .library,
                  .cardType .land,
                  .supertype .basic]))
              [.tapped]])
    ] =>
    id == tid && id == sid && sid == sid' && id == cid &&
      chooser == .targetReference sid
  | _ => false

/-- Look at the top `n` cards, exile them face down, and play them while
exiled if you control this subtype. -/
def leftoverExileTopFaceDownPlayIf? : CardAction → Option (Nat × String)
  | .sequence [
      .actionId lookId (.lookAt (.topOfLibrary who (.nat n))),
      .actionId exileId
        (.exileFaceDown (.wasObjectOfAction looked)),
      .continuous
        [.if
          (.any
            (.intersection [
              .zone .battlefield,
              .subtype st,
              .controlled (.controller .this)]))
          [.canPlay permit
            (.intersection [.zone .exile, .wasCreatedByAction exiled])]]
        .endOfGame
    ] =>
    if n != 0 && lookId == looked && exileId == exiled &&
        leftoverYou who && permit == .controller .this then
      some (n, st.toString)
    else none
  | _ => none

/-- A colorless Equipment artifact token named Axe with “equipped creature
gets +1/+0” and equip {2}. Colorless is an empty color indicator. -/
def leftoverAxeToken? (parts : List CardPart) : Bool :=
  let p := collectTokenParts parts
  let abilities :=
    parts.filter fun
      | .ability _ => true
      | _ => false
  let colorless :=
    parts.any fun
      | .colorIndicator [] => true
      | _ => false
  p.name == "Axe" && p.types == [.artifact] && p.subtypes == ["Equipment"] &&
    colorless && p.colors == ColorSet.empty && p.power.isNone &&
    p.toughness.isNone && p.keywords == Keywords.none &&
    abilities == [
      .ability (.static (.addPower (.hostOf .this) (Value.int 1))),
      .ability (.keywordWithCost .equip [.mana [.generic 2]])]

/-- Sequences that put +1/+1 counters on this creature alongside another
action, as printed on power-up abilities. -/
def leftoverSourcePlusOneSequence? : CardAction → Option Effect
  | .sequence [.putCounter (.source .this) .plusOnePlusOne (.nat k), .draw who (.nat n)] =>
    if leftoverYou who then some (Effect.plusOneAndDraw k n) else none
  | .sequence [.putCounter (.source .this) .plusOnePlusOne 1, .fight src dest] =>
    match dest with
    | .targets _ (.range 0 1) among =>
      if (src == .this || src == .source .this) && among.toTargetKind == .oppCreature then
        some Effect.plusOneThenFightUpToOne
      else none
    | _ => none
  | .sequence [.putCounter (.source .this) .plusOnePlusOne 1, .continuous effects .endOfTurn] =>
    let onSelf := effects.all fun
      | .gainAbility (.source .this) (.keyword _) => true
      | _ => false
    if onSelf && !effects.isEmpty then some (Effect.plusOneAndGrant (grantedKeywords effects))
    else none
  | .sequence [.putCounter (.source .this) .plusOnePlusOne (.nat k), create] =>
    match leftoverCreateTokensKindN? create with
    | some (kind, 1) => some (Effect.plusOneAndCreateTokens k kind)
    | _ => none
  | .sequence [.discard (.opponent (.controller .this)) (.nat 1),
      .putCounter (.source .this) .plusOnePlusOne 1] =>
    some Effect.eachOppDiscardThenPlusOne
  | .sequence [.destroy (.targets _ (.range 0 1) among),
      .putCounter (.source .this) .plusOnePlusOne 1] =>
    if among.toTargetKind == .artifactOrEnchantment then
      some Effect.destroyUpToOneThenPlusOne
    else none
  | .sequence [.returnToHand (.targets _ (.range 0 1) among),
      .putCounter (.source .this) .plusOnePlusOne (.nat k)] =>
    if leftoverYourGyCreatures? among then
      some (Effect.returnGyCreatureThenPlusOne k)
    else none
  | _ => none

/-- Printed actions of cards read with `parseOracleParts` that compile to one
named `Effect`. -/
def leftoverPrintedCompiled? : CardAction → Option Effect
  | .playerSelectAction who (.range 1 1) [
      .searchLibraryThenShuffle searcher [
        .defineSelectorVariable id
          (.selected chooser (.range 1 1)
            (.intersection [
              .union [.zone .library, .zone .graveyard],
              .cardType .artifact,
              .cardType .creature,
              .manaValueAtMost .x])),
        .putOntoBattlefield (.variable id1),
        .putCounter (.variable id2) .plusOnePlusOne .x,
        .if (.greaterOrEqual .x (.nat 4))
          [.continuous [.gainAbility (.variable id3) (.keyword .haste)] .endOfTurn]],
      .sequence [
        .defineSelectorVariable id4
          (.selected chooser2 (.range 1 1)
            (.intersection [
              .zone .graveyard,
              .cardType .artifact,
              .cardType .creature,
              .manaValueAtMost .x])),
        .putOntoBattlefield (.variable id5),
        .putCounter (.variable id6) .plusOnePlusOne .x,
        .if (.greaterOrEqual .x (.nat 4))
          [.continuous [.gainAbility (.variable id7) (.keyword .haste)] .endOfTurn]]
    ] =>
    if CardAction.leftoverYou who && CardAction.leftoverYou searcher &&
        CardAction.leftoverYou chooser && CardAction.leftoverYou chooser2 &&
        id == id1 && id == id2 && id == id3 &&
        id == id4 && id == id5 && id == id6 && id == id7 then
      some Effect.searchLibraryOrGyArtifactCreatureX
    else none
  | .draw (.targets _ (.range (.nat 2) (.nat 2)) .player) (.nat 1) => some Effect.twoPlayersDraw
  | .sequence [
      .actionId id (.lookAt (.topOfLibrary who (.nat k))),
      .searchLibraryThenShuffle searcher [
        .putOntoBattlefieldInState
          (.selected chooser .any (.intersection [.wasObjectOfAction id', .cardType .land]))
          [.tapped]],
      .gainLife gainer (.nat life)] =>
    if id == id' && leftoverYou who && leftoverYou searcher && leftoverYou chooser &&
        leftoverYou gainer then
      some (Effect.lookAtTopLandsGainLife k life)
    else none
  | .forEachVariable _ sel [.addMana who [.colored .red]] =>
    if leftoverYou who &&
        sel == .intersection
          [.zone .battlefield, .cardType .artifact, .controlled (.opponent (.controller .this))] then
      some Effect.addRedPerOppArtifacts
    else none
  | .sequence [
      .draw who (.greatestToughness among),
      .putOntoBattlefield (.selected chooser .any
        (.intersection [.zone .hand, .owner owner, .cardType .creature]))] =>
    if leftoverYou who && leftoverYou chooser && leftoverYou owner &&
        among == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] then
      some Effect.drawEqualToughnessThenPutCreatures
    else none
  | .sequence [
      .actionId id (.chooseCreatureType who),
      .returnToHand
        (.intersection [.zone .battlefield, .cardType .creature, .not (.hasCreatureTypeChosenByAction id')])] =>
    if id == id' && leftoverYou who then some Effect.chooseTypeReturnOthers else none
  | .continuous
      [.forbid (.block .all
        (.target _ (.intersection [.zone .battlefield, .cardType .creature, .powerAtMost (.int k)])))]
      .endOfTurn =>
    some (Effect.targetCantBeBlockedPowerAtMost k)
  | .putOntoBattlefieldInState (.intersection [.zone .graveyard, .source .this]) [.tapped] =>
    some Effect.returnFromGraveyardTapped
  | .dealDamage src (.opponent who) (.nat n) =>
    if (src == .this || leftoverSourceThis src) && leftoverYou who then
      some (Effect.damageEachOpponent n)
    else none
  | .sequence [
      .defineSelectorVariable n (.selected who (.range (.nat 0) (.nat 2)) kind),
      .destroy (.intersection [.zone .battlefield, .cardType .creature, .not (.variable n')])] =>
    if n == n' && leftoverYou who &&
        kind == .intersection [.zone .battlefield, .cardType .creature] then
      some Effect.chooseTwoDestroyRest
    else none
  | .sequence [
      .actionId id (.addManaOfOneColor who syms (.nat 1)),
      .continuous [.forbid (.spendManaCreatedByAction id' restriction)] .endOfTurn] =>
    if id != id' || !leftoverYou who || syms != ManaSymbol.anyColor then none
    else
      match restriction with
      | .not (.or (.castSpell (.intersection [.spell, .subtype st]))
          (.activateAbility (.subtype st'))) =>
        if st == st' then some (Effect.addAnyColorSpendOnlySubtype st.toString) else none
      | .not (.castSpell (.intersection [.spell, .cardType .artifact])) =>
        some Effect.addAnyColorSpendOnlyArtifactSpell
      | _ => none
  | .sequence [
      .actionId id (.addMana who [.colored .blue]),
      .continuous [.forbid (.spendManaCreatedByAction id'
        (.castSpell (.intersection [.spell, .not (.cardType .artifact)])))] .endOfTurn] =>
    if id == id' && leftoverYou who then some Effect.addBlueCantNonartifact else none
  | .sequence [
      .actionId lookId (.lookAt (.topOfLibrary who (.nat k))),
      .optional chooser (.sequence [
        .actionId revealId
          (.reveal (.selected picker (.range (.nat 1) (.nat 1))
            (.intersection [.wasObjectOfAction looked, .subtype st]))),
        .returnToHand (.wasObjectOfAction revealed)]),
      .putOnBottomOfLibrary
        (.intersection [.wasObjectOfAction looked', .not (.wasObjectOfAction revealed')])] =>
    if k != 0 && lookId == looked && lookId == looked' && revealId == revealed &&
        revealId == revealed' && leftoverYou who && leftoverYou chooser && leftoverYou picker then
      some (Effect.lookAtTopRevealSubtype k st.toString)
    else none
  | .keyword (.target _ (.intersection [.zone .battlefield, .cardType .creature, .subtype st, you]))
      (.connive (.nat 1)) =>
    if you == .controlled (.controller .this) then
      some (Effect.targetSubtypeConnives st.toString)
    else none
  | .returnToHand (.target _ (.intersection [.zone .graveyard, .subtype st, .owner owner])) =>
    if leftoverYou owner then some (Effect.returnGySubtypeToHand st.toString) else none
  | .draw who (.count (.wasObjectSince (.discard who') .turnStart)) =>
    if leftoverYou who && leftoverYou who' then some Effect.drawPerDiscardedThisTurn else none
  | .createTokens who (.count among) parts [] =>
    match Selector.subtypesYouControl? among, leftoverTokenKind? parts with
    | some (#[st], false), some kind =>
      if leftoverYou who then some (Effect.createTokensEqualSubtype kind st) else none
    | _, _ => none
  | .dealDamage src (.intersection [.zone .battlefield, .cardType .creature]) (.nat n) =>
    if n != 0 && (src == .this || leftoverSourceThis src) then
      some (Effect.dealDamageToEachCreature n)
    else none
  | .sequence [
      .destroy (.target t (.intersection [.zone .battlefield, .cardType .land])),
      .optional who (.searchLibraryThenShuffle searcher [
        .putOntoBattlefieldInState (.selected chooser (.range (.nat 1) (.nat 1))
          (.intersection [.zone .library, .cardType .land, .supertype .basic])) [.tapped]])] =>
    let controller := Selector.controller (.targetReference t)
    if who == controller && searcher == controller && chooser == controller then
      some Effect.destroyLandSearchBasic
    else none
  | .continuous [
      .addPower (.target t (.intersection [.zone .battlefield, .cardType .creature]))
        (.greatestPower (.targetReference t1)),
      .addToughness (.targetReference t2) (.greatestToughness (.targetReference t3))] .endOfTurn =>
    if t == t1 && t == t2 && t == t3 then some Effect.doublePowerAndToughness else none
  | .fight (.target _ src) (.target _ dest) =>
    if src == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] &&
        dest == .intersection
          [.zone .battlefield, .cardType .creature, .controlled (.opponent (.controller .this))] then
      some Effect.fight
    else none
  | .dealDamage (.target t src) (.target _ dest) (.product (.totalPower (.targetReference t')) (.int 2)) =>
    if t == t' &&
        src == .intersection [.zone .battlefield, .cardType .creature, .controlled (.controller .this)] &&
        dest == .intersection
          [.zone .battlefield, .cardType .creature, .controlled (.opponent (.controller .this))] then
      some Effect.creatureYouControlDealsTwicePower
    else none
  | .sequence [
      .actionId id (.exile (.intersection [.zone .battlefield, .cardType .creature])),
      .forEachVariable v .player [
        .optional p (.putOntoBattlefield (.selected p' .any
          (.intersection [.zone .hand, .owner p'', .cardType .creature])))],
      .returnToHand (.wasCreatedByAction id'),
      .exile .this] =>
    if id == id' && p == .variable v && p' == p && p'' == p then
      some Effect.worldsWithinWorlds
    else none
  | _ => none

/-- First alternatives of `leftoverCompiled?`. Separate from the rest so the
code generator does not duplicate a long `orElse` chain while simplifying it. -/
@[noinline]
private def leftoverCompiledHead? (action : CardAction) : Option Effect :=
  match leftoverSourcePlusOneSequence? action with
  | some e => some e
  | none =>
  match leftoverPrintedCompiled? action with
  | some e => some e
  | none =>
  if leftoverExileAttackersSearchBasics? action then
    some Effect.exileAttackersSearchBasics
  else
  match leftoverExileTopFaceDownPlayIf? action with
  | some (n, st) => some (Effect.exileTopPlayIfYouControlSubtype n st)
  | none =>
  match leftoverNonDragonThenDragonMana? action with
  | some n => some (Effect.dealDamageToEachNonDragonThenAddDragonMana n)
  | none =>
  match leftoverDealDamageExileIfDies? action with
  | some n => some (Effect.dealDamageToCreatureExileIfDies n)
  | none =>
  match leftoverDealDamageToEachOppCreature? action with
  | some n => some (Effect.dealDamageToEachOppCreature n)
  | none =>
  if leftoverDestroyArtifactToken? action then some Effect.destroyArtifactToken
  else leftoverChapterCompiled? action

/-- Middle alternatives of `leftoverCompiled?`. -/
@[noinline]
private def leftoverCompiledMiddle? (action : CardAction) : Option Effect :=
  if leftoverPlusOneThenEachOtherIfFromGy? action then
    some Effect.plusOneThenEachOtherIfFromGy
  else
    match leftoverDrawOrAmassIfFromGy? action with
    | some e => some e
    | none =>
      match leftoverPlusOneThenFight? action with
      | some n => some (Effect.plusOneThenFight n)
      | none =>
        match leftoverOwnerShuffleSourceDraw? action with
        | some n => some (Effect.ownerShuffleSourceDraw n)
        | none =>
          match leftoverReturnFromGyAttachPowerAtMost? action with
          | some n => some (Effect.returnFromGyAttachPowerAtMost n)
          | none =>
            if leftoverOwnerPutsLibraryThenConnive? action then
              some Effect.ownerPutsLibraryThenConnive
            else if leftoverExileThenReturnYouControl? action then
              some Effect.exileThenReturnYouControl
            else
              match leftoverMillThenPutCompiled? action with
              | some e => some e
              | none =>
                match leftoverCreateThenTeamPump? action with
                | some e => some e
                | none => leftoverContinuousCompiled? action

/-- Last alternatives of `leftoverCompiled?`. -/
@[noinline]
private def leftoverCompiledTail? (action : CardAction) : Option Effect :=
  match leftoverDrawLoseLifeThenAmass? action with
  | some n => some (Effect.drawLoseLifeThenAmass n)
  | none =>
    match leftoverReturnCreatureFromGyThenAmass? action with
    | some n => some (Effect.returnCreatureFromGyThenAmass n)
    | none =>
      match leftoverCounterThenRecruitIfMvAtMost? action with
      | some n => some (Effect.counterThenRecruitIfMvAtMost n)
      | none =>
        match leftoverTapScryDraw? action with
        | some (scryN, drawN) => some (Effect.tapScryDraw scryN drawN)
        | none =>
          if leftoverReturnSpellDraw? action then some Effect.returnSpellDraw
          else if leftoverReturnSpellCantCastIfGift? action then
            some Effect.returnSpellCantCastIfGift
          else if leftoverDestroyArtOrLandNonflyers? action then
            some Effect.destroyArtifactOrLandNonflyersCantBlock
          else if leftoverDestroyCreatureSurveil? action then
            some Effect.destroyCreatureSurveil
          else if leftoverBecomeArtifactIndestructible? action then
            some Effect.becomeArtifactGainIndestructible
          else if leftoverPlusOneLifelinkIndestructible? action then
            some Effect.plusOneLifelinkIndestructible
          else if leftoverGrantVigilanceUnblockable? action then
            some Effect.grantVigilanceUnblockable
          else
            match leftoverPumpThenExileTopPlay? action with
            | some (p, t) => some (Effect.pumpThenExileTopPlay p t)
            | none =>
              match leftoverDestroyArtEnchGainLife? action with
              | some n => some (Effect.destroyArtifactOrEnchantmentGainLife n)
              | none =>
                match leftoverMaySacArtifactOrDiscardDraw? action with
                | some n => some (Effect.maySacArtifactOrDiscardDraw n)
                | none =>
                  match leftoverDrawThreeDiscardUnlessArtifact? action with
                  | some _ => some Effect.drawThreeDiscardUnlessArtifact
                  | none =>
                    match leftoverReturnUpToTwoGyModal? action with
                    | some _ => some Effect.returnUpToTwoGyModal
                    | none =>
                      match leftoverGainLifeSearchBasicPlusOne? action with
                      | some n => some (Effect.gainLifeSearchBasicPlusOne n)
                      | none => leftoverPlusOneOnEachOtherSubtype? action

/-- Sequence leftovers that compile to a named `Effect` without taking
only the first action. -/
def leftoverCompiled? (action : CardAction) : Option Effect :=
  match leftoverCompiledHead? action with
  | some e => some e
  | none =>
    match leftoverCompiledMiddle? action with
    | some e => some e
    | none => leftoverCompiledTail? action

/-- The number of artifact permanents opponents of this object's controller
control. -/
def isOpponentArtifactsCount : Value → Bool
  | .count among =>
    let s := among.shape
    s.mustBePermanent && s.opponentControls && !s.sameController &&
      s.types.eqTypes [.artifact] && s.subtype.isNone && !s.other &&
      !s.token && !s.nontoken && !s.flying && !s.tapped && !s.attacking
  | _ => false

/-- Look at the top `n` cards of your library, reveal one of two subtypes,
and put the rest on the bottom in a random order. -/
def leftoverLookAtTopReveal? : CardAction → Option (Nat × Array String)
  | .sequence [
      .actionId lookId (.lookAt (.topOfLibrary who (.nat n))),
      .optional (.controller .this) (.sequence [
        .actionId revealId
          (.reveal
            (.selected chooser (.range 1 1)
              (.intersection [
                .wasObjectOfAction looked,
                kind]))),
        .returnToHand (.wasObjectOfAction returned)]),
      .putOnLibraryBottomInRandomOrder
        (.intersection [
          .wasObjectOfAction bottomFrom,
          .not (.wasObjectOfAction excluded)])
    ] =>
    let types : Option (Array String) :=
      match kind with
      | .union [.subtype a, .subtype b] => some #[a.toString, b.toString]
      | .zone .battlefield => some #["permanent"]
      | _ => none
    if lookId == looked && lookId == bottomFrom &&
        revealId == returned && revealId == excluded &&
        lookId != revealId &&
        leftoverYou who && leftoverYou chooser then
      types.map (n, ·)
    else none
  | _ => none

/-- You may discard your hand, then draw that many cards. With an enduring
story, this deals that much damage to each opponent. -/
def leftoverMayDiscardHandDrawDamageIfStory? : CardAction → Bool
  | .sequence [
      .optional (.controller .this)
        (.actionId id
          (.discard (.controller .this)
            (.count (.intersection [.zone .hand, .owner (.controller .this)])))),
      .draw (.controller .this) (.count (.wasObjectOfAction id')),
      .if (.enduringStory (.controller .this))
        [.dealDamage src (.opponent (.controller .this))
          (.count (.wasObjectOfAction id''))]
    ] =>
    id == id' && id == id'' && leftoverSourceThis src
  | _ => false

/-- `for each opponent, exile up to one target nonland permanent that player
controls until this leaves the battlefield.` The exile is numbered. When
this ability's source leaves the battlefield, a replacement puts that
exiled card onto the battlefield and the leave still happens. -/
def leftoverExileOppNonlandEachUntilLeaves? : CardAction → Bool
  | .forEachVariable v (.opponent who) [
      .sequence [
        .actionId id
          (.exile
            (.targets _ (.range 0 1)
              (.intersection [
                .zone .battlefield,
                .not (.cardType .land),
                .controlled (.variable v')]))),
        .continuous
          [.replace (.leaveBattlefield src) [
            .putOntoBattlefield (.wasCreatedByAction id'),
            .keepReplacedAction]]
          .endOfGame
      ]
    ] =>
    v == v' && id == id' && leftoverYou who && leftoverSourceThis src
  | _ => false

/-- Enters-the-battlefield actions that compile to a named trigger. -/
def leftoverEnterThisAction? : CardAction → Option TriggeredAbility
  | .createTokens who n parts states =>
    match valToNat? n with
    | some n =>
      if leftoverYou who then
        if states == [] then
          if n == 1 && leftoverAxeToken? parts then
            some TriggeredAbility.onEnterCreateAxe
          else if n == 1 && leftoverRedwingToken? parts then
            some (TriggeredAbility.onEnter Effect.enterCreateRedwing)
          else
            leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onEnterCreateTokens k n)
        else if leftoverTappedOnly states then
          leftoverTokenKind? parts |>.map (fun k => TriggeredAbility.onEnterCreateTokens k n true)
        else none
      else none
    | none =>
      if leftoverYou who && leftoverTappedOnly states &&
          leftoverTokenKind? parts == some .treasure &&
          isOpponentArtifactsCount n then
        some TriggeredAbility.onEnterCreateTappedTreasuresEqualOppArtifacts
      else none
  | .sequence [
      .actionId id (.createTokens who n parts []),
      .attach .this (.wasCreatedByAction id')
    ] =>
    if id == id' && n == 1 && leftoverYou who then
      leftoverTokenKind? parts |>.map TriggeredAbility.onEnterCreateThenAttach
    else none
  | .playerSelectAction who (.range 1 1) actions =>
    if leftoverYou who && leftoverCreateFoodOrTreasure? actions then
      some TriggeredAbility.onEnterCreateFoodOrTreasure
    else none
  | .keyword who .recruit =>
    if leftoverYou who then some TriggeredAbility.onEnterRecruit else none
  | .keyword who (.amass .goblin (.nat n)) =>
    if leftoverYou who then some (TriggeredAbility.onEnterAmassGoblins n) else none
  | .keyword who (.connive (.nat 1)) =>
    if leftoverSourceThis who then some TriggeredAbility.onEnterConnive else none
  | .sequence [
      .actionId id (.returnToHand sel),
      .if (.happened (.actionWithId id') _)
        [.putCounter (.source .this) .plusOnePlusOne 1]
    ] =>
    if id == id' then
      match sel with
      | .targets _ (.range 0 1) among =>
        if among.shape.other && among.shape.sameController then
          some TriggeredAbility.onEnterReturnOtherPlusOne
        else none
      | _ => none
    else none
  | .sequence [
      .gainLife _ (.nat n),
      .optional (.controller .this) search
    ] =>
    if leftoverSearchBasicOnTop? search then
      some (TriggeredAbility.onEnterGainLifeSearchBasicOnTop n)
    else none
  | .sequence [
      .draw (.controller .this) 1,
      .if (.any among) [.gainLife _ 2]
    ] =>
    if among.shape.other && among.shape.sameController &&
        among.shape.subtype == some "Hero" then
      some TriggeredAbility.onEnterDrawGainLifeIfAnotherHero
    else none
  | .sequence [
      .putCounter sel .plusOnePlusOne 1,
      .if (.anySubtype among .hero)
        [.putCounter _ .plusOnePlusOne 1]
    ] =>
    -- “If that creature is another Hero”: the extra counter is about the
    -- chosen target, and must not fire when that target is the source.
    if (sel.toTargetKind == .creature || sel.toTargetKind == .creatureYouControl) &&
        among.shape.other && among.includesTargetReference then
      some TriggeredAbility.onEnterPlusOneOrTwoIfAnotherHero
    else none
  | .sequence [
      .actionId id (.keyword who (.amass .goblin (.nat n))),
      .attach .this (.wasObjectOfAction id')
    ] =>
    if id == id' && leftoverYou who then
      some (TriggeredAbility.onEnterAmassThenAttach n)
    else none
  | .sequence [
      .defineValueVariable power (.greatestPower (.targets tid (.range 0 1) among)),
      .defineSelectorVariable ctl (.controller (.targetReference tid')),
      .destroy (.targetReference tid''),
      .keyword (.variable ctl') (.amass .goblin (.variable power')),
      .if (.any (.intersection [.variable ctl'', .controller .this]))
        [.draw (.controller .this) 1]
    ] =>
    -- The power and controller are recorded before the destroy, so they are
    -- the creature's last-known information (CR 608.2h).
    if tid == tid' && tid == tid'' && power == power' && ctl == ctl' &&
        ctl == ctl'' && among.shape.otherCreatures && among.shape.mustBePermanent &&
        !among.shape.sameController && !among.shape.opponentControls then
      some TriggeredAbility.onEnterDestroyOtherAmassControllerPower
    else none
  | .destroy (.target _ sel) =>
    some (TriggeredAbility.onEnter (Effect.enterDestroy sel.toTargetKind))
  | action =>
    if leftoverExileOppNonlandEachUntilLeaves? action then
      some TriggeredAbility.onEnterExileOppNonlandEachUntilLeaves
    else
    match leftoverMillThenSubtypeToHand? action with
    | some (n, st) => some (TriggeredAbility.onEnterMillThenSubtypeToHand n st)
    | none =>
      if leftoverMaySacDrawTreasure? action then
        some TriggeredAbility.onEnterMaySacDrawTreasure
      else if leftoverEnterReturnGyPermanentThisTurn? action then
        some (TriggeredAbility.onEnter Effect.enterReturnGyPermanentThisTurn)
      else if leftoverEnterReturnCreatureFromGyToHand? action then
        some TriggeredAbility.onEnterReturnCreatureFromGyToHand
      else if leftoverEnterReturnNonlandNontoken? action then
        some (TriggeredAbility.onEnter Effect.enterReturnNonlandNontoken)
      else if leftoverEnterFightUpToOne? action then
        some (TriggeredAbility.onEnter Effect.enterFightUpToOne)
      else if leftoverEnterMaySacAnotherThenDestroyOppNonland? action then
        some (TriggeredAbility.onEnter Effect.enterMaySacAnotherThenDestroyOppNonland)
      else if leftoverEnterMaySacOrDiscardNonlandThenDamage? action then
        some (TriggeredAbility.onEnter Effect.enterMaySacOrDiscardNonlandThenDamage)
      else
        match leftoverLookAtTopReveal? action with
        | some (n, types) =>
          some (TriggeredAbility.onEnterLookAtTopRevealTypes n types)
        | none => none

/-- Enters-the-battlefield library searches. -/
def leftoverEnterSearch? : List CardAction → Option TriggeredAbility
  | [.putOntoBattlefield sel] =>
    match sel.selectedAmong? with
    | some among =>
      if among.includesInLibrary && among.includedSubtype? == some "Forest" then
        some TriggeredAbility.onEnterSearchForest
      else none
    | none => none
  | [.defineSelectorVariable id sel, .reveal (.variable id'), .returnToHand (.variable id'')] =>
    if id == id' && id == id'' then
      match sel.selectedAmong? with
      | some among =>
        if among.basicLandInLibrary then
          some TriggeredAbility.onEnterSearchBasicToHand
        else none
      | none => none
    else none
  | _ => none

end CardAction

end Mtg.Engine
