import Mtg.Engine.Card.Definition

/-!
# Separate action ids from target numbers

The parsers thread one counter through a card. `parseOracleParts` then
splits that counter into two sequences. Target numbers (`target`,
`targets`, `targetSet`, and the other uses of that counter, such as
trigger ids and variables) stay in one sequence. Action ids are the
other. Each sequence is `1`, `2`, `3`, … with no number taken by the
other sequence. A number that was both a target and an action id stays
that number in both sequences.
-/

namespace Mtg.Engine.OracleParts

def insertUnique (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs =>
    if n == x then x :: xs
    else if n < x then n :: x :: xs
    else x :: insertUnique n xs

def sortUnique (ns : List Nat) : List Nat :=
  ns.foldl (fun acc n => insertUnique n acc) []

/-- `n`'s place in `sorted`, counting from 1. A missing number stays `n`. -/
def rank (sorted : List Nat) (n : Nat) : Nat :=
  go sorted 1
where
  go : List Nat → Nat → Nat
    | [], _ => n
    | x :: xs, i => if x == n then i else go xs (i + 1)

structure IdMaps where
  actions : List Nat
  targets : List Nat

def IdMaps.action (m : IdMaps) (n : Nat) : Nat :=
  rank m.actions n

def IdMaps.target (m : IdMaps) (n : Nat) : Nat :=
  rank m.targets n

def appendIds : List (List Nat × List Nat) → List Nat × List Nat
  | [] => ([], [])
  | (a, t) :: rest =>
    let (a', t') := appendIds rest
    (a ++ a', t ++ t')

mutual

def collectValue : Value → List Nat × List Nat
  | .nat _ | .int _ | .x => ([], [])
  | .greatestManaValue s | .greatestToughness s | .greatestPower s | .count s | .totalPower s
  | .greatestManaSpent s =>
    collectSelector s
  | .product a b => appendIds [collectValue a, collectValue b]
  | .variable n => ([], [n])

def collectRange : Range → List Nat × List Nat
  | .range a b => appendIds [collectValue a, collectValue b]
  | .any => ([], [])
  | .from v => collectValue v

def collectKeyword : Keyword → List Nat × List Nat
  | .amass _ v | .connive v => collectValue v
  | _ => ([], [])

def collectSelector : Selector → List Nat × List Nat
  | .this | .caster | .all | .zone _ | .tapped | .spell | .ability | .permanentSpell
  | .player | .token | .replacingObject =>
    ([], [])
  | .source s | .controller s | .not s | .controlled s | .hasTarget s | .isTargetOf s
  | .opponent s | .owner s | .attacking s | .blocking s | .hostOf s =>
    collectSelector s
  | .target n s => appendIds [([], [n]), collectSelector s]
  | .targets n r s | .targetSet n r s _ =>
    appendIds [([], [n]), collectRange r, collectSelector s]
  | .targetReference n | .abilityWithId n | .variable n => ([], [n])
  | .selected who r s => appendIds [collectSelector who, collectRange r, collectSelector s]
  | .intersection ss | .union ss => appendIds (ss.map collectSelector)
  | .cardType _ | .hasCounter _ | .subtype _ | .supertype _ => ([], [])
  | .keyword k | .keywordAbility k => collectKeyword k
  | .powerAtLeast v | .powerAtMost v | .manaValueAtMost v => collectValue v
  | .castFromZone _ => ([], [])
  | .wasObjectOfAction n | .wasCreatedByAction n | .affectedByAction n
  | .hasCreatureTypeChosenByAction n =>
    ([n], [])
  | .wasArgumentOfTrigger n _ => ([], [n])
  | .wasObjectSince a b => appendIds [collectTrigger a, collectTrigger b]
  | .topOfLibrary s v => appendIds [collectSelector s, collectValue v]

def collectTrigger : Trigger → List Nat × List Nat
  | .endOfGame | .endOfTurn | .turnStart | .gameStart => ([], [])
  | .endOfPlayerTurn s | .combatStart s | .upkeep s | .endStep s | .drawStep s | .enter s | .die s
  | .discard s | .leaveGraveyard s | .leaveBattlefield s | .returnToHand s | .putToGraveyard s
  | .giftPromised s | .counter s | .activateAbility s | .castSpell s
  | .castSpellFromGraveyard s | .precombatMainPhase s | .createTokens s
  | .abilityTriggers s =>
    collectSelector s
  | .attack a b | .draw a b | .damage a b | .block a b | .target a b | .combatDamage a b
  | .putCountersSimultaneously a b _ =>
    appendIds [collectSelector a, collectSelector b]
  | .enterSimultaneously s _ | .dieSimultaneously s _ => collectSelector s
  | .damageSimultaneously a b _ | .attackSimultaneously a b _ =>
    appendIds [collectSelector a, collectSelector b]
  | .ordinal _ inner window => appendIds [collectTrigger inner, collectTrigger window]
  | .sacrifice s => collectSelector s
  | .abilityWithIdActivated n | .abilityWithIdResolved n => ([], [n])
  | .actionWithId n => ([n], [])
  | .triggerId n inner => appendIds [([], [n]), collectTrigger inner]
  | .modeWithIdChosen who _ => collectSelector who
  | .spendManaCreatedByAction n inner => appendIds [([n], []), collectTrigger inner]
  | .spendManaFrom s inner => appendIds [collectSelector s, collectTrigger inner]
  | .sequence ts => appendIds (ts.map collectTrigger)
  | .not t => collectTrigger t
  | .or a b => appendIds [collectTrigger a, collectTrigger b]

def collectCondition : Condition → List Nat × List Nat
  | .any s | .timeToCastSorcery s | .turn s | .drawStep s | .enduringStory s => collectSelector s
  | .targetsIncludeAny a b => appendIds [collectSelector a, collectSelector b]
  | .anySubtype s _ => collectSelector s
  | .didNotHappen a b | .happened a b => appendIds [collectTrigger a, collectTrigger b]
  | .and a b => appendIds [collectCondition a, collectCondition b]
  | .not c => collectCondition c
  | .less a b | .lessOrEqual a b | .greater a b | .greaterOrEqual a b | .equal a b =>
    appendIds [collectValue a, collectValue b]

def collectCost : Cost → List Nat × List Nat
  | .mana _ | .life _ | .tapSymbol => ([], [])
  | .sacrifice s | .discard s => collectSelector s
  | .sacrificeCount s _ => collectSelector s
  | .or cs => appendIds (cs.map collectCost)

def collectState : CardState → List Nat × List Nat
  | .tapped | .attacking => ([], [])
  | .controlled s | .attachedTo s => collectSelector s

def collectParts : List CardPart → List Nat × List Nat
  | [] => ([], [])
  | p :: ps => appendIds [collectPart p, collectParts ps]

def collectPart : CardPart → List Nat × List Nat
  | .name _ | .manaCost _ | .type _ | .supertype _ | .subtype _ | .colorIndicator _
  | .power _ | .toughness _ =>
    ([], [])
  | .ability a => collectAbility a
  | .alternative ps => collectParts ps
  | .actions as => appendIds (as.map collectAction)

def collectAbility : Ability → List Nat × List Nat
  | .keyword k => collectKeyword k
  | .keywordWithCost k cs => appendIds [collectKeyword k, appendIds (cs.map collectCost)]
  | .keywordWithSubtypeAndCost k _ c => appendIds [collectKeyword k, collectCost c]
  | .keywordWithTarget _ n s => appendIds [([], [n]), collectSelector s]
  | .keywordWithEffect k as => appendIds [collectKeyword k, appendIds (as.map collectAction)]
  | .keywordWithAbility k a => appendIds [collectKeyword k, collectAbility a]
  | .activated cs action => appendIds [appendIds (cs.map collectCost), collectAction action]
  | .activatedIf c cs action =>
    appendIds [collectCondition c, appendIds (cs.map collectCost), collectAction action]
  | .activatedWithStaticIf c cs action e =>
    appendIds [
      collectCondition c, appendIds (cs.map collectCost), collectAction action, collectEffect e]
  | .graveyardActivatedIf c cs action =>
    appendIds [collectCondition c, appendIds (cs.map collectCost), collectAction action]
  | .abilityId n a => appendIds [([], [n]), collectAbility a]
  | .triggered t action => appendIds [collectTrigger t, collectAction action]
  | .triggeredWhile t c action =>
    appendIds [collectTrigger t, collectCondition c, collectAction action]
  | .static e | .stackStatic e | .everywhereStatic e => collectEffect e

def collectEffect : ContinuousEffect → List Nat × List Nat
  | .gainAbility s a => appendIds [collectSelector s, collectAbility a]
  | .if c es => appendIds [collectCondition c, appendIds (es.map collectEffect)]
  | .reduceCost s cs | .additionalCost s cs | .alternativeCost s cs =>
    appendIds [collectSelector s, appendIds (cs.map collectCost)]
  | .reduceCostWithX s cs v =>
    appendIds [collectSelector s, appendIds (cs.map collectCost), collectValue v]
  | .replace t as => appendIds [collectTrigger t, appendIds (as.map collectAction)]
  | .forbid t => collectTrigger t
  | .canCastWithoutPayingManaCost a b | .canPlay a b | .cantAttackUnlessPays a b _ =>
    appendIds [collectSelector a, collectSelector b]
  | .setBasePower s v | .setBaseToughness s v | .setPower s v | .setToughness s v
  | .addPower s v | .addToughness s v | .increaseLandPlayLimit s v =>
    appendIds [collectSelector s, collectValue v]
  | .gainType s _ | .gainSubtype s _ | .gainAllSubtypes s _ | .doesntUntap s | .removeAllAbilities s =>
    collectSelector s
  | .canBeCastAsThoughWithFlashIf s c => appendIds [collectSelector s, collectCondition c]

def collectModes : List (Nat × Condition × List CardAction) → List Nat × List Nat
  | [] => ([], [])
  | (_, c, as) :: rest =>
    appendIds [collectCondition c, appendIds (as.map collectAction), collectModes rest]

def collectAction : CardAction → List Nat × List Nat
  | .continuous es t => appendIds [appendIds (es.map collectEffect), collectTrigger t]
  | .tap s | .untap s | .exile s | .exileFaceDown s | .exchangeControl s | .destroy s
  | .putOnTopOfLibrary s | .putOnBottomOfLibrary s | .sacrifice s | .returnToHand s
  | .putOntoBattlefield s | .holdOutInLibrary s | .reveal s | .healAllDamage s
  | .shuffleIntoOwnersLibrary s | .lookAt s | .putOnLibraryBottomInRandomOrder s
  | .chooseCreatureType s | .removeAllCounters s =>
    collectSelector s
  | .dealDamage a b v =>
    appendIds [collectSelector a, collectSelector b, collectValue v]
  | .draw a v | .scry a v | .discard a v | .putCounter a _ v
  | .removeCounter a _ v | .gainLife a v | .putIntoLibraryFromTop a v | .loseLife a v
  | .mill a v | .surveil a v =>
    appendIds [collectSelector a, collectValue v]
  | .divideDamage a b c v =>
    appendIds [collectSelector a, collectSelector b, collectSelector c, collectValue v]
  | .sequence as | .chooseUniqueModes _ as => appendIds (as.map collectAction)
  | .if c as => appendIds [collectCondition c, appendIds (as.map collectAction)]
  | .ifElse c a b =>
    appendIds [collectCondition c, appendIds (a.map collectAction), appendIds (b.map collectAction)]
  | .optional who action => appendIds [collectSelector who, collectAction action]
  | .attach a b | .copyWithNewTargets a b | .fight a b | .mayCast a b =>
    appendIds [collectSelector a, collectSelector b]
  | .chooseModeRestricted who modes => appendIds [collectSelector who, collectModes modes]
  | .counter s => collectSelector s
  | .preventable who cs action =>
    appendIds [collectSelector who, appendIds (cs.map collectCost), collectAction action]
  | .optionalPayFor who cs as =>
    appendIds [collectSelector who, appendIds (cs.map collectCost), appendIds (as.map collectAction)]
  | .playerSelectAction who r as =>
    appendIds [collectSelector who, collectRange r, appendIds (as.map collectAction)]
  | .actionId n action => appendIds [([n], []), collectAction action]
  | .putOntoBattlefieldInState s states =>
    appendIds [collectSelector s, appendIds (states.map collectState)]
  | .searchLibraryThenShuffle who as =>
    appendIds [collectSelector who, appendIds (as.map collectAction)]
  | .defineSelectorVariable n s => appendIds [([], [n]), collectSelector s]
  | .defineValueVariable n v => appendIds [([], [n]), collectValue v]
  | .forEachVariable n s as =>
    appendIds [([], [n]), collectSelector s, appendIds (as.map collectAction)]
  | .addManaOfOneColor who _ v | .addManaInAnyCombination who _ v =>
    appendIds [collectSelector who, collectValue v]
  | .addMana who _ => collectSelector who
  | .keyword who k => appendIds [collectSelector who, collectKeyword k]
  | .createTokens who n parts states =>
    appendIds [
      collectSelector who, collectValue n, collectParts parts, appendIds (states.map collectState)]
  | .modifyReplacementCreatedTokenCount _ => ([], [])
  | .duplicateReplacingTrigger v => collectValue v
  | .keepReplacedAction => ([], [])

end

def idMaps (parts : List CardPart) : IdMaps :=
  let (actions, targets) := collectParts parts
  { actions := sortUnique actions, targets := sortUnique targets }

mutual

def mapValue (m : IdMaps) : Value → Value
  | .nat n => .nat n
  | .int n => .int n
  | .x => .x
  | .greatestManaValue s => .greatestManaValue (mapSelector m s)
  | .greatestToughness s => .greatestToughness (mapSelector m s)
  | .greatestPower s => .greatestPower (mapSelector m s)
  | .count s => .count (mapSelector m s)
  | .totalPower s => .totalPower (mapSelector m s)
  | .product a b => .product (mapValue m a) (mapValue m b)
  | .variable n => .variable (m.target n)
  | .greatestManaSpent s => .greatestManaSpent (mapSelector m s)

def mapRange (m : IdMaps) : Range → Range
  | .range a b => .range (mapValue m a) (mapValue m b)
  | .any => .any
  | .from v => .from (mapValue m v)

def mapKeyword (m : IdMaps) : Keyword → Keyword
  | .amass st v => .amass st (mapValue m v)
  | .connive v => .connive (mapValue m v)
  | k => k

def mapSelectors (m : IdMaps) : List Selector → List Selector
  | [] => []
  | s :: ss => mapSelector m s :: mapSelectors m ss

def mapSelector (m : IdMaps) : Selector → Selector
  | .this => .this
  | .source s => .source (mapSelector m s)
  | .controller s => .controller (mapSelector m s)
  | .caster => .caster
  | .target n s => .target (m.target n) (mapSelector m s)
  | .targets n r s => .targets (m.target n) (mapRange m r) (mapSelector m s)
  | .targetSet n r s ps => .targetSet (m.target n) (mapRange m r) (mapSelector m s) ps
  | .not s => .not (mapSelector m s)
  | .targetReference n => .targetReference (m.target n)
  | .selected who r s => .selected (mapSelector m who) (mapRange m r) (mapSelector m s)
  | .intersection ss => .intersection (mapSelectors m ss)
  | .all => .all
  | .cardType t => .cardType t
  | .union ss => .union (mapSelectors m ss)
  | .zone z => .zone z
  | .controlled s => .controlled (mapSelector m s)
  | .tapped => .tapped
  | .keyword k => .keyword (mapKeyword m k)
  | .keywordAbility k => .keywordAbility (mapKeyword m k)
  | .powerAtLeast v => .powerAtLeast (mapValue m v)
  | .powerAtMost v => .powerAtMost (mapValue m v)
  | .hasCounter k => .hasCounter k
  | .subtype st => .subtype st
  | .spell => .spell
  | .ability => .ability
  | .abilityWithId n => .abilityWithId (m.target n)
  | .permanentSpell => .permanentSpell
  | .hasTarget s => .hasTarget (mapSelector m s)
  | .isTargetOf s => .isTargetOf (mapSelector m s)
  | .player => .player
  | .opponent s => .opponent (mapSelector m s)
  | .owner s => .owner (mapSelector m s)
  | .attacking s => .attacking (mapSelector m s)
  | .blocking s => .blocking (mapSelector m s)
  | .token => .token
  | .wasObjectOfAction n => .wasObjectOfAction (m.action n)
  | .wasArgumentOfTrigger n k => .wasArgumentOfTrigger (m.target n) k
  | .replacingObject => .replacingObject
  | .wasCreatedByAction n => .wasCreatedByAction (m.action n)
  | .affectedByAction n => .affectedByAction (m.action n)
  | .hostOf s => .hostOf (mapSelector m s)
  | .wasObjectSince a b => .wasObjectSince (mapTrigger m a) (mapTrigger m b)
  | .supertype s => .supertype s
  | .variable n => .variable (m.target n)
  | .topOfLibrary s v => .topOfLibrary (mapSelector m s) (mapValue m v)
  | .hasCreatureTypeChosenByAction n => .hasCreatureTypeChosenByAction (m.action n)
  | .manaValueAtMost v => .manaValueAtMost (mapValue m v)
  | .castFromZone z => .castFromZone z

def mapTriggers (m : IdMaps) : List Trigger → List Trigger
  | [] => []
  | t :: ts => mapTrigger m t :: mapTriggers m ts

def mapTrigger (m : IdMaps) : Trigger → Trigger
  | .endOfGame => .endOfGame
  | .endOfTurn => .endOfTurn
  | .endOfPlayerTurn s => .endOfPlayerTurn (mapSelector m s)
  | .combatStart s => .combatStart (mapSelector m s)
  | .upkeep s => .upkeep (mapSelector m s)
  | .endStep s => .endStep (mapSelector m s)
  | .drawStep s => .drawStep (mapSelector m s)
  | .turnStart => .turnStart
  | .gameStart => .gameStart
  | .attack a b => .attack (mapSelector m a) (mapSelector m b)
  | .enter s => .enter (mapSelector m s)
  | .enterSimultaneously s ps => .enterSimultaneously (mapSelector m s) ps
  | .draw a b => .draw (mapSelector m a) (mapSelector m b)
  | .ordinal n inner window => .ordinal n (mapTrigger m inner) (mapTrigger m window)
  | .combatDamage a b => .combatDamage (mapSelector m a) (mapSelector m b)
  | .damage a b => .damage (mapSelector m a) (mapSelector m b)
  | .damageSimultaneously a b ps =>
    .damageSimultaneously (mapSelector m a) (mapSelector m b) ps
  | .putToGraveyard s => .putToGraveyard (mapSelector m s)
  | .leaveGraveyard s => .leaveGraveyard (mapSelector m s)
  | .leaveBattlefield s => .leaveBattlefield (mapSelector m s)
  | .returnToHand s => .returnToHand (mapSelector m s)
  | .discard s => .discard (mapSelector m s)
  | .putCountersSimultaneously a b k =>
    .putCountersSimultaneously (mapSelector m a) (mapSelector m b) k
  | .block a b => .block (mapSelector m a) (mapSelector m b)
  | .die s => .die (mapSelector m s)
  | .dieSimultaneously s ps => .dieSimultaneously (mapSelector m s) ps
  | .sacrifice s => .sacrifice (mapSelector m s)
  | .attackSimultaneously a b ps =>
    .attackSimultaneously (mapSelector m a) (mapSelector m b) ps
  | .abilityWithIdActivated n => .abilityWithIdActivated (m.target n)
  | .abilityWithIdResolved n => .abilityWithIdResolved (m.target n)
  | .actionWithId n => .actionWithId (m.action n)
  | .triggerId n inner => .triggerId (m.target n) (mapTrigger m inner)
  | .modeWithIdChosen who n => .modeWithIdChosen (mapSelector m who) n
  | .spendManaCreatedByAction n inner =>
    .spendManaCreatedByAction (m.action n) (mapTrigger m inner)
  | .spendManaFrom s inner => .spendManaFrom (mapSelector m s) (mapTrigger m inner)
  | .castSpell s => .castSpell (mapSelector m s)
  | .castSpellFromGraveyard s => .castSpellFromGraveyard (mapSelector m s)
  | .giftPromised s => .giftPromised (mapSelector m s)
  | .counter s => .counter (mapSelector m s)
  | .activateAbility s => .activateAbility (mapSelector m s)
  | .sequence ts => .sequence (mapTriggers m ts)
  | .not t => .not (mapTrigger m t)
  | .or a b => .or (mapTrigger m a) (mapTrigger m b)
  | .target a b => .target (mapSelector m a) (mapSelector m b)
  | .precombatMainPhase s => .precombatMainPhase (mapSelector m s)
  | .createTokens s => .createTokens (mapSelector m s)
  | .abilityTriggers s => .abilityTriggers (mapSelector m s)

def mapCondition (m : IdMaps) : Condition → Condition
  | .any s => .any (mapSelector m s)
  | .targetsIncludeAny a b => .targetsIncludeAny (mapSelector m a) (mapSelector m b)
  | .anySubtype s st => .anySubtype (mapSelector m s) st
  | .didNotHappen a b => .didNotHappen (mapTrigger m a) (mapTrigger m b)
  | .happened a b => .happened (mapTrigger m a) (mapTrigger m b)
  | .timeToCastSorcery s => .timeToCastSorcery (mapSelector m s)
  | .turn s => .turn (mapSelector m s)
  | .drawStep s => .drawStep (mapSelector m s)
  | .enduringStory s => .enduringStory (mapSelector m s)
  | .and a b => .and (mapCondition m a) (mapCondition m b)
  | .not c => .not (mapCondition m c)
  | .less a b => .less (mapValue m a) (mapValue m b)
  | .lessOrEqual a b => .lessOrEqual (mapValue m a) (mapValue m b)
  | .greater a b => .greater (mapValue m a) (mapValue m b)
  | .greaterOrEqual a b => .greaterOrEqual (mapValue m a) (mapValue m b)
  | .equal a b => .equal (mapValue m a) (mapValue m b)

def mapCosts (m : IdMaps) : List Cost → List Cost
  | [] => []
  | c :: cs => mapCost m c :: mapCosts m cs

def mapCost (m : IdMaps) : Cost → Cost
  | .mana syms => .mana syms
  | .life n => .life n
  | .sacrifice s => .sacrifice (mapSelector m s)
  | .sacrificeCount s n => .sacrificeCount (mapSelector m s) n
  | .tapSymbol => .tapSymbol
  | .discard s => .discard (mapSelector m s)
  | .or cs => .or (mapCosts m cs)

def mapStates (m : IdMaps) : List CardState → List CardState
  | [] => []
  | s :: ss => mapState m s :: mapStates m ss

def mapState (m : IdMaps) : CardState → CardState
  | .tapped => .tapped
  | .attacking => .attacking
  | .controlled s => .controlled (mapSelector m s)
  | .attachedTo s => .attachedTo (mapSelector m s)

def mapParts (m : IdMaps) : List CardPart → List CardPart
  | [] => []
  | p :: ps => mapPart m p :: mapParts m ps

def mapPart (m : IdMaps) : CardPart → CardPart
  | .name n => .name n
  | .manaCost c => .manaCost c
  | .type t => .type t
  | .supertype s => .supertype s
  | .subtype s => .subtype s
  | .colorIndicator cs => .colorIndicator cs
  | .power n => .power n
  | .toughness n => .toughness n
  | .ability a => .ability (mapAbility m a)
  | .alternative ps => .alternative (mapParts m ps)
  | .actions as => .actions (mapActions m as)

def mapAbility (m : IdMaps) : Ability → Ability
  | .keyword k => .keyword (mapKeyword m k)
  | .keywordWithCost k cs => .keywordWithCost (mapKeyword m k) (mapCosts m cs)
  | .keywordWithSubtypeAndCost k st c =>
    .keywordWithSubtypeAndCost (mapKeyword m k) st (mapCost m c)
  | .keywordWithTarget k n s => .keywordWithTarget k (m.target n) (mapSelector m s)
  | .keywordWithEffect k as => .keywordWithEffect (mapKeyword m k) (mapActions m as)
  | .keywordWithAbility k a => .keywordWithAbility (mapKeyword m k) (mapAbility m a)
  | .activated cs action => .activated (mapCosts m cs) (mapAction m action)
  | .activatedIf c cs action =>
    .activatedIf (mapCondition m c) (mapCosts m cs) (mapAction m action)
  | .activatedWithStaticIf c cs action e =>
    .activatedWithStaticIf (mapCondition m c) (mapCosts m cs) (mapAction m action) (mapEffect m e)
  | .graveyardActivatedIf c cs action =>
    .graveyardActivatedIf (mapCondition m c) (mapCosts m cs) (mapAction m action)
  | .abilityId n a => .abilityId (m.target n) (mapAbility m a)
  | .triggered t action => .triggered (mapTrigger m t) (mapAction m action)
  | .triggeredWhile t c action =>
    .triggeredWhile (mapTrigger m t) (mapCondition m c) (mapAction m action)
  | .static e => .static (mapEffect m e)
  | .stackStatic e => .stackStatic (mapEffect m e)
  | .everywhereStatic e => .everywhereStatic (mapEffect m e)

def mapEffects (m : IdMaps) : List ContinuousEffect → List ContinuousEffect
  | [] => []
  | e :: es => mapEffect m e :: mapEffects m es

def mapEffect (m : IdMaps) : ContinuousEffect → ContinuousEffect
  | .gainAbility s a => .gainAbility (mapSelector m s) (mapAbility m a)
  | .if c es => .if (mapCondition m c) (mapEffects m es)
  | .reduceCost s cs => .reduceCost (mapSelector m s) (mapCosts m cs)
  | .reduceCostWithX s cs v =>
    .reduceCostWithX (mapSelector m s) (mapCosts m cs) (mapValue m v)
  | .additionalCost s cs => .additionalCost (mapSelector m s) (mapCosts m cs)
  | .alternativeCost s cs => .alternativeCost (mapSelector m s) (mapCosts m cs)
  | .replace t as => .replace (mapTrigger m t) (mapActions m as)
  | .forbid t => .forbid (mapTrigger m t)
  | .canCastWithoutPayingManaCost a b =>
    .canCastWithoutPayingManaCost (mapSelector m a) (mapSelector m b)
  | .canPlay a b => .canPlay (mapSelector m a) (mapSelector m b)
  | .setBasePower s v => .setBasePower (mapSelector m s) (mapValue m v)
  | .setBaseToughness s v => .setBaseToughness (mapSelector m s) (mapValue m v)
  | .gainType s t => .gainType (mapSelector m s) t
  | .gainSubtype s st => .gainSubtype (mapSelector m s) st
  | .gainAllSubtypes s t => .gainAllSubtypes (mapSelector m s) t
  | .setPower s v => .setPower (mapSelector m s) (mapValue m v)
  | .setToughness s v => .setToughness (mapSelector m s) (mapValue m v)
  | .addPower s v => .addPower (mapSelector m s) (mapValue m v)
  | .addToughness s v => .addToughness (mapSelector m s) (mapValue m v)
  | .increaseLandPlayLimit s v => .increaseLandPlayLimit (mapSelector m s) (mapValue m v)
  | .canBeCastAsThoughWithFlashIf s c =>
    .canBeCastAsThoughWithFlashIf (mapSelector m s) (mapCondition m c)
  | .doesntUntap s => .doesntUntap (mapSelector m s)
  | .cantAttackUnlessPays a b cs =>
    .cantAttackUnlessPays (mapSelector m a) (mapSelector m b) (mapCosts m cs)
  | .removeAllAbilities s => .removeAllAbilities (mapSelector m s)

def mapActions (m : IdMaps) : List CardAction → List CardAction
  | [] => []
  | a :: as => mapAction m a :: mapActions m as

def mapModes (m : IdMaps) : List (Nat × Condition × List CardAction) →
    List (Nat × Condition × List CardAction)
  | [] => []
  | (n, c, as) :: rest => (n, mapCondition m c, mapActions m as) :: mapModes m rest

def mapAction (m : IdMaps) : CardAction → CardAction
  | .continuous es t => .continuous (mapEffects m es) (mapTrigger m t)
  | .tap s => .tap (mapSelector m s)
  | .untap s => .untap (mapSelector m s)
  | .dealDamage a b v => .dealDamage (mapSelector m a) (mapSelector m b) (mapValue m v)
  | .divideDamage a b c v =>
    .divideDamage (mapSelector m a) (mapSelector m b) (mapSelector m c) (mapValue m v)
  | .draw a v => .draw (mapSelector m a) (mapValue m v)
  | .scry a v => .scry (mapSelector m a) (mapValue m v)
  | .sequence as => .sequence (mapActions m as)
  | .if c as => .if (mapCondition m c) (mapActions m as)
  | .ifElse c a b => .ifElse (mapCondition m c) (mapActions m a) (mapActions m b)
  | .optional who action => .optional (mapSelector m who) (mapAction m action)
  | .attach a b => .attach (mapSelector m a) (mapSelector m b)
  | .chooseUniqueModes r as => .chooseUniqueModes (mapRange m r) (mapActions m as)
  | .chooseModeRestricted who modes =>
    .chooseModeRestricted (mapSelector m who) (mapModes m modes)
  | .counter s => .counter (mapSelector m s)
  | .preventable who cs action =>
    .preventable (mapSelector m who) (mapCosts m cs) (mapAction m action)
  | .optionalPayFor who cs as =>
    .optionalPayFor (mapSelector m who) (mapCosts m cs) (mapActions m as)
  | .discard a v => .discard (mapSelector m a) (mapValue m v)
  | .putCounter a k v => .putCounter (mapSelector m a) k (mapValue m v)
  | .removeCounter a k v => .removeCounter (mapSelector m a) k (mapValue m v)
  | .removeAllCounters s => .removeAllCounters (mapSelector m s)
  | .exile s => .exile (mapSelector m s)
  | .exileFaceDown s => .exileFaceDown (mapSelector m s)
  | .exchangeControl s => .exchangeControl (mapSelector m s)
  | .destroy s => .destroy (mapSelector m s)
  | .gainLife a v => .gainLife (mapSelector m a) (mapValue m v)
  | .playerSelectAction who r as =>
    .playerSelectAction (mapSelector m who) (mapRange m r) (mapActions m as)
  | .putOnTopOfLibrary s => .putOnTopOfLibrary (mapSelector m s)
  | .putOnBottomOfLibrary s => .putOnBottomOfLibrary (mapSelector m s)
  | .putIntoLibraryFromTop a v => .putIntoLibraryFromTop (mapSelector m a) (mapValue m v)
  | .actionId n action => .actionId (m.action n) (mapAction m action)
  | .loseLife a v => .loseLife (mapSelector m a) (mapValue m v)
  | .sacrifice s => .sacrifice (mapSelector m s)
  | .returnToHand s => .returnToHand (mapSelector m s)
  | .putOntoBattlefield s => .putOntoBattlefield (mapSelector m s)
  | .putOntoBattlefieldInState s states =>
    .putOntoBattlefieldInState (mapSelector m s) (mapStates m states)
  | .searchLibraryThenShuffle who as =>
    .searchLibraryThenShuffle (mapSelector m who) (mapActions m as)
  | .holdOutInLibrary s => .holdOutInLibrary (mapSelector m s)
  | .defineSelectorVariable n s => .defineSelectorVariable (m.target n) (mapSelector m s)
  | .defineValueVariable n v => .defineValueVariable (m.target n) (mapValue m v)
  | .forEachVariable n s as =>
    .forEachVariable (m.target n) (mapSelector m s) (mapActions m as)
  | .reveal s => .reveal (mapSelector m s)
  | .fight a b => .fight (mapSelector m a) (mapSelector m b)
  | .addManaOfOneColor who syms v =>
    .addManaOfOneColor (mapSelector m who) syms (mapValue m v)
  | .addManaInAnyCombination who syms v =>
    .addManaInAnyCombination (mapSelector m who) syms (mapValue m v)
  | .addMana who syms => .addMana (mapSelector m who) syms
  | .keyword who k => .keyword (mapSelector m who) (mapKeyword m k)
  | .createTokens who n parts states =>
    .createTokens (mapSelector m who) (mapValue m n) (mapParts m parts) (mapStates m states)
  | .modifyReplacementCreatedTokenCount f => .modifyReplacementCreatedTokenCount f
  | .duplicateReplacingTrigger v => .duplicateReplacingTrigger (mapValue m v)
  | .mill a v => .mill (mapSelector m a) (mapValue m v)
  | .surveil a v => .surveil (mapSelector m a) (mapValue m v)
  | .copyWithNewTargets a b => .copyWithNewTargets (mapSelector m a) (mapSelector m b)
  | .keepReplacedAction => .keepReplacedAction
  | .healAllDamage s => .healAllDamage (mapSelector m s)
  | .shuffleIntoOwnersLibrary s => .shuffleIntoOwnersLibrary (mapSelector m s)
  | .lookAt s => .lookAt (mapSelector m s)
  | .putOnLibraryBottomInRandomOrder s => .putOnLibraryBottomInRandomOrder (mapSelector m s)
  | .chooseCreatureType s => .chooseCreatureType (mapSelector m s)
  | .mayCast a b => .mayCast (mapSelector m a) (mapSelector m b)

end

/-- Give action ids their own `1`, `2`, `3`, … sequence. Target numbers,
trigger ids, ability ids, and variables keep a separate sequence. -/
def separateActionIds (parts : List CardPart) : List CardPart :=
  mapParts (idMaps parts) parts

#guard separateActionIds [
    .ability (.triggered (.enter .this)
      (.sequence [
        .actionId 3 (.attach (.targets 1 Range.any (.zone .battlefield)) (.target 2 (.zone .battlefield))),
        .dealDamage (.targetReference 2)
          (.targets 4 (.range 0 1) (.zone .battlefield))
          (.greatestPower (.targetReference 2))]))] ==
  [
    .ability (.triggered (.enter .this)
      (.sequence [
        .actionId 1 (.attach (.targets 1 Range.any (.zone .battlefield)) (.target 2 (.zone .battlefield))),
        .dealDamage (.targetReference 2)
          (.targets 3 (.range 0 1) (.zone .battlefield))
          (.greatestPower (.targetReference 2))]))]
#guard separateActionIds [.actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .actionId 2 (.exile .replacingObject)]] ==
  [.actions [
    .actionId 1 (.counter (.target 1 .spell)),
    .actionId 2 (.exile .replacingObject)]]
#guard separateActionIds [.actions [
    .continuous [.addPower (.target 1 (.zone .battlefield)) 3] .endOfTurn,
    .actionId 2 (.exile (.topOfLibrary (.controller .this) 1))]] ==
  [.actions [
    .continuous [.addPower (.target 1 (.zone .battlefield)) 3] .endOfTurn,
    .actionId 1 (.exile (.topOfLibrary (.controller .this) 1))]]

end OracleParts

end Mtg.Engine
