import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Parser.FrameSplit
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.DiscourseBind
import Mtg.Engine.Card.Parser.TokenEmblemGrammar
import Mtg.Engine.Card.Parser.InspectSearchGrammar
import Mtg.Engine.Card.Parser.InstructionGrammar

/-!
# Stage-4c Compositional Ability Grammar & Recursive Quoted-Ability Knot

Ties the recursive `QuotedAbilityParsers` knot across:
- `parseStaticAbilityComp` (CR 113.3d / 604 / 613 / 614–616): all 6 `StaticAbility`
  constructors including recursive quoted `"..."` granted abilities (`Planeswalkers you
  control have "[+1]: ..."`, `Creatures you control have "{T}: ..."`, `Equipped creature
  has "Whenever ..."`), copy replacements, and token/death replacements.
- `parseActivatedAbilityComp` (CR 113.3b / 602 / 605.1a / 606): loyalty, mana,
  `Power-up` / `Exhaust` / `Boast` mechanic labels, Equip-with-cost-reduction,
  zone inference (hand/graveyard/battlefield), and trailing activation restrictions.
- `parseTriggeredAbilityComp` (CR 113.3c / 603 / 714.2b): Saga chapters,
  em-dash mechanic labels (`Mardu`, `Jeskai`, `Eminence`, `Threshold`, `Corrupted`),
  all trigger headers, modal triggers, and one-shot effect bodies.
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-! ### Helper: Scope & Attachment Filter Parsing for Static Abilities -/

private def equippedCreatureFilter : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .hasAttachment { zones := .battlefield
                       pred := .all #[.sameAs .this, .hasSubtype (.literal .equipment)] }
    ] }

private def enchantedCreatureFilter : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .hasAttachment { zones := .battlefield
                       pred := .all #[.sameAs .this, .hasSubtype (.literal .aura)] }
    ] }

private def enchantedPermanentFilter : ObjectFilter :=
  { zones := .battlefield
    pred := .hasAttachment { zones := .battlefield
                             pred := .all #[.sameAs .this, .hasSubtype (.literal .aura)] } }

private def parseStaticScope? (raw : String) (cardName : String) : Option ObjectFilter :=
  let s := pClean (replaceCardNameOutsideQuotes raw cardName "this permanent")
  let l := pLower s
  if DiscourseCtx.isSelfPhrase l || l == "this" then
    some { zones := .battlefield, pred := .sameAs .this }
  else if l == "equipped creature" then
    some equippedCreatureFilter
  else if l == "enchanted creature" then
    some enchantedCreatureFilter
  else if l == "enchanted permanent" then
    some enchantedPermanentFilter
  else if l == "planeswalkers you control" then
    some { zones := .battlefield, pred := .all #[.hasType .planeswalker, .controlledBy .you] }
  else if l == "artifacts and creatures you control" then
    some { zones := .battlefield, pred := .all #[.any #[.hasType .artifact, .hasType .creature], .controlledBy .you] }
  else if l == "creatures you control that are equipped" then
    some { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you, .hasAttachment { zones := .battlefield, pred := .hasSubtype (.literal .equipment) }] }
  else if l == "each creature you control that you've put one or more +1/+1 counters on this turn" then
    some { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you, .receivedCounterThisTurn (some .plusOnePlusOne) (some .you)] }
  else if l == "other heroes you control" then
    some { zones := .battlefield, pred := .all #[.otherThan .this, .hasSubtype (.literal .hero), .controlledBy .you] }
  else
    let multiSub? : Option ObjectFilter :=
      match pDropPrefixCI? s "other " >>= fun r => pDropSuffixCI? r " you control" with
      | some mid =>
        match pSplitFirstCI? mid " and " with
        | some (a, b) =>
          match CardSubtype.ofOracle? a, CardSubtype.ofOracle? b with
          | some sa, some sb => some (StaticAbility.scopeOtherCreaturesOfSubtypesYouControl #[sa, sb])
          | _, _ => none
        | none => none
      | none => none
    match multiSub? with
    | some f => some f
    | none =>
      match parseNounPhrase s with
      | some np =>
        match np.filter.zones.zones.toList, np.filter.pred with
        | [.battlefield], .all #[.otherThan .this, subPred@(.hasSubtype (.literal _)), .hasType .creature, .controlledBy .you] =>
          some { zones := .battlefield, pred := .all #[.otherThan .this, .hasType .creature, subPred, .controlledBy .you] }
        | [.battlefield], .all #[.otherThan .this, subPred@(.any _), .hasType .creature, .controlledBy .you] =>
          some { zones := .battlefield, pred := .all #[.otherThan .this, .hasType .creature, subPred, .controlledBy .you] }
        | _, _ => some np.filter
      | none => none

/-! ### Helper: Peel Leading or Trailing Condition on Static Abilities -/

private partial def parseStaticCondExtra? (raw cardName : String) : Option Condition := Id.run do
  let s := pClean (replaceCardNameOutsideQuotes raw cardName "this permanent")
  let l := pLower s
  if l == "you have an enduring story" then
    return some (.playerPred .you (.hasDesignation .enduringStory))
  if l == "an opponent has cast a spell this turn" then
    return some (.turnHistory (.eventOccurredThisTurn .opponent (.castSpell .anyObject)))
  if l == "you've scried or surveilled this turn" || l == "you've scried this turn or you've surveilled this turn" then
    return some (.any #[.turnHistory (.scriedThisTurn .you), .turnHistory (.surveilledThisTurn .you)])
  if l == "they haven't dealt combat damage yet" || l == "it hasn't dealt combat damage yet" then
    return some (.not (.exists (.filter .this (.dealtDamageThisTurn true none false))))
  if l == "this has a shield counter on it" || l == "this permanent has a shield counter on it" then
    return some (.exists (.filter .this (.counterCount (some .shield) .ge (.const 1))))
  if l == "its power is 1 or less" || l == "this permanent's power is 1 or less" then
    return some (.forAll .this (.stat .power .le (.const 1)))
  if let some rest := (pDropPrefixCI? s "its power is ").orElse (fun _ => pDropPrefixCI? s "this permanent's power is ") then
    if let some nStr := pDropSuffixCI? rest " or less" then
      if let some n := parseNatWord? nStr then
        return some (.forAll .this (.stat .power .le (.const (Int.ofNat n))))
    if let some nStr := pDropSuffixCI? rest " or greater" then
      if let some n := parseNatWord? nStr then
        return some (.forAll .this (.stat .power .ge (.const (Int.ofNat n))))
  if let some rest := pDropPrefixCI? s "you control " then
    if let some np := parseNounPhrase (rest ++ " you control") then
      return some (.exists np.filter.toExpr)
    if let some (a, b) := pSplitFirstCI? rest " or " then
      match parseStaticCondExtra? ("you control " ++ a) cardName,
            parseStaticCondExtra? ("you control " ++ b) cardName with
      | some c1, some c2 => return some (.any #[c1, c2])
      | _, _ => pure ()
  if let some c := parseInstrCondition? s cardName then
    return some c
  return none

private def peelStaticCond (raw cardName : String) : Option Condition × String :=
  let s := pClean raw
  if let some r := pDropPrefixCI? s "during your turn, " then
    (some .isYourTurn, r)
  else if let some r := pDropPrefixCI? s "as long as " then
    match pSplitFirstCI? r ", " with
    | some (cStr, rest) =>
      match parseStaticCondExtra? cStr cardName with
      | some c => (some c, rest)
      | none => (none, s)
    | none => (none, s)
  else if let some (body, cStr) := pSplitLastCI? s " as long as " then
    match parseStaticCondExtra? cStr cardName with
    | some c => (some c, body)
    | none => (none, s)
  else if let some (body, cStr) := pSplitLastCI? s " if " then
    if !(pLower body).startsWith "if " && pLower cStr != "able" then
      match parseStaticCondExtra? cStr cardName with
      | some c => (some c, body)
      | none => (none, s)
    else (none, s)
  else (none, s)

/-! ### Helper: Activation Cost-Zone & Trailing Restrictions -/

private def inferActiveZonesFromCost (cost : CostSpec) (rawCost : String) : Array ZoneKind :=
  let l := pLower rawCost
  if l.contains "this card from your graveyard" || l.contains "this permanent from your graveyard" ||
      l.contains "this card is in your graveyard" then
    #[.graveyard]
  else if l.contains "discard this" || l.contains "this card from your hand" then
    #[.hand]
  else
    let hasGraveyardSelfExile := cost.items.any fun
      | .exile _ zs .self _ => zs.zones.contains .graveyard
      | _ => false
    let hasHandSelfDiscard := cost.items.any fun
      | .discard _ .self => true
      | _ => false
    if hasGraveyardSelfExile then #[.graveyard]
    else if hasHandSelfDiscard then #[.hand]
    else #[.battlefield]

/-- Peel trailing activation restriction sentences (`"Activate only as a sorcery."`,
`"Activate only during your turn."`, `"Activate only once each turn."`,
`"Activate only once."`, `"Activate only if <cond>."`,
`"This ability costs {N} less to activate for each <X>."`) from an activated
ability's effect sentences. -/
private structure ActRestrictions where
  timing : ActivationTiming := .instant
  turnLimit? : Option Nat := none
  lifetimeLimit? : Option Nat := none
  condition? : Option Condition := none
  extraZones? : Option (Array ZoneKind) := none
  costReductions : Array ActivationCostReduction := #[]

private def peelActivatedRestrictions (sents : Array String) (cardName : String) :
    Array String × ActRestrictions := Id.run do
  let mut kept : Array String := #[]
  let mut r : ActRestrictions := {}
  for s0 in sents do
    let s := pClean s0
    let l := pLower s
    if l == "activate only as a sorcery" then
      r := { r with timing := .sorcery }
    else if l == "activate only during your turn" then
      r := { r with condition? := some .isYourTurn }
    else if l == "activate only once each turn" then
      r := { r with turnLimit? := some 1 }
    else if l == "activate only once" then
      r := { r with lifetimeLimit? := some 1 }
    else if l == "activate only during your turn and only once each turn" then
      r := { r with condition? := some .isYourTurn, turnLimit? := some 1 }
    else if l == "activate only as a sorcery and only once each turn" then
      r := { r with timing := .sorcery, turnLimit? := some 1 }
    else if l == "activate only if this card is in your graveyard" ||
        l == "activate only from your graveyard" then
      r := { r with extraZones? := some #[.graveyard] }
    else if let some condStr := pDropPrefixCI? s "activate only if " then
      if let some c := parseStaticCondExtra? condStr cardName then
        r := { r with condition? := some c }
      else
        kept := kept.push s0
    else if let some redRest := pDropPrefixCI? s "this ability costs " then
      if let some (amtPart, eachPart) := pSplitFirstCI? redRest " less to activate for each " then
        let perN :=
          match parseManaCost? amtPart with
          | some mc => mc.genericCount
          | none => (parseNatWord? amtPart).getD 1
        let eLow := pLower eachPart
        if eLow.contains "+1/+1 counter on the creature it targets" ||
            eLow.contains "+1/+1 counter on target creature" ||
            eLow.contains "+1/+1 counter on that creature" then
          let val := ValueExpr.counterCount (some .plusOnePlusOne) (.target 0)
          let scaled := if perN == 1 then val else .binary .mul (.const (Int.ofNat perN)) val
          r := { r with costReductions := r.costReductions.push { amount := scaled } }
        else if let some np := parseNounPhrase eachPart then
          let cnt := ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
          let scaled := if perN == 1 then cnt else .binary .mul (.const (Int.ofNat perN)) cnt
          r := { r with costReductions := r.costReductions.push { amount := scaled } }
        else kept := kept.push s0
      else if let some (amtPart, condPart) := pSplitFirstCI? redRest " less to activate if " then
        let amt :=
          match parseManaCost? amtPart with
          | some mc => ValueExpr.const (Int.ofNat mc.genericCount)
          | none => (parseCountVal? amtPart).getD (.const 1)
        let cond? : Option Condition :=
          if let some tgtPredStr := pDropPrefixCI? condPart "it targets " then
            (parseNounPhrase tgtPredStr).map fun np =>
              Condition.exists (.filter (.target 0) np.filter.pred)
          else parseStaticCondExtra? condPart cardName
        match cond? with
        | some cond =>
          r := { r with costReductions := r.costReductions.push { amount := amt, condition? := some cond } }
        | none => kept := kept.push s0
      else kept := kept.push s0
    else
      kept := kept.push s0
  return (kept, r)

/-! ### Mutual Recursive Stage-4c Ability Parsers -/

mutual

/-- Build the `QuotedAbilityParsers` callback table tied to this mutual block. -/
partial def mkQuotedParsers (_ : Unit := ()) : QuotedAbilityParsers := {
  parseStatic := fun raw cn => (parseStaticAbilityComp raw cn).bind (·[0]?)
  parseTriggered := fun raw cn => (parseTriggeredAbilityComp raw cn).bind (·[0]?)
  parseActivated := fun raw cn => parseActivatedAbilityComp raw cn
  parseEffect := fun raw cn => parseCompositionalEffect (mkQuotedParsers ()) raw cn false
}

/-- Stage-4c compositional parser for `StaticAbility` lines (CR 113.3d / 604 / 613 / 614–616),
including recursive quoted granted abilities (`have "..."`), copy replacements, and
token/death replacements. -/
partial def parseStaticAbilityComp (raw : String) (cardName : String := "") :
    Option (Array StaticAbility) := Id.run do
  let pre := (preprocessOracleLine raw).trimAscii.copy
  if pre.isEmpty then return none
  let (lbl?, body0) := extractLeadingLabel pre
  let qp := mkQuotedParsers ()

  -- 1. Quoted `"..."` granted abilities (`<scope> have "..."` or
  -- `Equipped/Enchanted creature gets ... and has "..."`), parsed recursively via `qp`!
  if body0.contains '"' then
    let (cond?, body1) := peelStaticCond body0 cardName
    for sep in #[" have ", " has "] do
      if let some (scopeStr, grantRest) := pSplitFirstCI? body1 sep then
        if let some scope := parseStaticScope? scopeStr cardName then
          if let some (cm, _) := parseContinuousMod? qp { cardName } (sep.trimAscii.copy ++ " " ++ grantRest) then
            return some #[.continuous cond? scope cm]
    for sep in #[" gets ", " get "] do
      if let some (scopeStr, modRest) := pSplitFirstCI? body1 sep then
        if let some scope := parseStaticScope? scopeStr cardName then
          if let some (cm, _) := parseContinuousMod? qp { cardName } (sep.trimAscii.copy ++ " " ++ modRest) then
            return some #[.continuous cond? scope cm]

  -- 2. Try `SubGrammars.parseStaticAbilityLine` (Enchant, cost modifiers, rules, ETB, CDAs, buffs)
  if let some sas := parseStaticAbilityLine pre cardName then
    if !sas.isEmpty then return some sas
  if body0 != pre then
    if let some sas := parseStaticAbilityLine body0 cardName then
      if !sas.isEmpty then return some sas

  -- 3. Additional compositional static forms:
  let norm := pClean (replaceCardNameOutsideQuotes body0 cardName "this permanent")
  let low := pLower norm
  let (cond?, body1) := peelStaticCond norm cardName
  let bLow := pLower body1

  -- 3a. CDAs (`This power is equal to ...`, `Tarmogoyf` power+toughness CDA)
  if bLow.startsWith "this power is equal to " || bLow.startsWith "this permanent's power is equal to " ||
      bLow.startsWith "this permanent's base power is equal to " || bLow.startsWith "this creature's base power is equal to " then
    let valStr :=
      ((pDropPrefixCI? body1 "this power is equal to ").orElse fun _ =>
      (pDropPrefixCI? body1 "this permanent's power is equal to ").orElse fun _ =>
      (pDropPrefixCI? body1 "this permanent's base power is equal to ").orElse fun _ =>
      pDropPrefixCI? body1 "this creature's base power is equal to ") |>.getD ""
    if let some v := parseValueExpr valStr then
      return some #[.characteristicDefining (.setPT (some v) none)]
  if bLow.startsWith "this creature's power is equal to " || bLow.startsWith "this permanent's power is equal to " then
    if let some (pPart, tPart) := pSplitFirstCI? body1 " and its toughness is equal to " then
      let pValStr := ((pDropPrefixCI? pPart "this creature's power is equal to ").orElse fun _ =>
        pDropPrefixCI? pPart "this permanent's power is equal to ") |>.getD pPart
      if pLower tPart == "that number plus 1" then
        if let some pv := parseValueExpr pValStr then
          return some #[.characteristicDefining (.setPT (some pv) (some (.binary .add pv (.const 1))))]
      else if let some pv := parseValueExpr pValStr then
        if let some tv := parseValueExpr tPart then
          return some #[.characteristicDefining (.setPT (some pv) (some tv))]

  -- 3b. Hand-size, opening-hand, look-top-library, cast-unless, combat-phase lock, zero-loyalty, haste-activate, extra-activation, flash, free-cast, toughness-damage
  if bLow == "you may look at the top card of your library any time" then
    return some #[.ruleModifying cond? (.play (.lookAtTopOfLibrary .you))]
  if let some uStr := pDropPrefixCI? body1 "you can't cast this spell unless " then
    if let some uCond := parseStaticCondExtra? uStr cardName then
      return some #[.ruleModifying cond? (.play (.castRestriction uCond))]
  if bLow == "each creature you control with toughness greater than its power assigns combat damage equal to its toughness rather than its power" ||
      bLow == "creatures you control assign combat damage equal to toughness if greater" then
    return some #[.ruleModifying cond? (.combat (.assignCombatDamageByToughness { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] } true))]
  if bLow == "you have no maximum hand size" then
    return some #[.ruleModifying cond? (.player (.maxHandSize .you none))]
  if bLow == "you have hexproof" then
    return some #[.ruleModifying cond? (.player (.hexproof .you none))]
  if let some nStr := pDropPrefixCI? bLow "your maximum hand size is " then
    if let some n := parseNatWord? nStr then
      return some #[.ruleModifying cond? (.player (.maxHandSize .you (some n)))]
  if bLow == "your opponents can't cast spells during your turn" then
    return some #[StaticAbility.opponentsCantCastOnYourTurn]
  if bLow == "if this card is in your opening hand, you may begin the game with it on the battlefield" ||
      bLow == "if this permanent is in your opening hand, you may begin the game with it on the battlefield" then
    return some #[StaticAbility.mayBeginOnBattlefield]
  if bLow == "planeswalkers you control aren't put into their owners' graveyards for having 0 loyalty" then
    return some #[StaticAbility.planeswalkersSurviveZeroLoyalty]
  if bLow == "during combat phase, players can't cast spells or activate abilities that aren't mana abilities" ||
      bLow == "during combat, players can't cast spells or activate abilities that aren't mana abilities" then
    return some #[StaticAbility.noSpellsOrAbilitiesDuringCombat]
  if bLow == "you may activate abilities of creatures you control as though those creatures had haste" then
    return some #[StaticAbility.activateCreaturesAsThoughHaste]
  if bLow == "each power-up ability of permanents you control can be activated an additional time" then
    return some #[StaticAbility.extraPowerUpActivation]
  if bLow == "you may cast spells as though they had flash" then
    return some #[.ruleModifying cond? (.play (.castAsThoughFlash .you .anyObject false none))]
  if bLow == "you may cast spells with mana value less than or equal to the number of creatures you control from your hand without paying their mana costs" then
    return some #[StaticAbility.castFromHandFreeUpToCreatures]
  if bLow == "artifacts and creatures entering the battlefield don't cause abilities to trigger" then
    return some #[StaticAbility.enteringArtifactsCreaturesDontTrigger]
  if bLow == "noncreature spells you cast have improvise" then
    return some #[StaticAbility.noncreatureSpellsHaveImprovise]
  if bLow == "instant and sorcery spells you control have split second" then
    return some #[StaticAbility.instantSorcerySplitSecond]

  -- 3c. Extra triggers (`If a triggered ability of <scope> triggers, that ability triggers an additional time`)
  if let some r := pDropPrefixCI? body1 "if a triggered ability of " then
    if let some (scopeStr, _) := pSplitFirstCI? r " triggers, that ability triggers an additional time" then
      if let some scope := parseStaticScope? scopeStr cardName then
        return some #[.ruleModifying cond? (.trigger (.extraTrigger scope 1))]

  -- 3d. Combat & untap rules (`can't be blocked`, `can't block`, `can't attack`, `attacks each combat if able`, `doesn't untap`, `defender`, `maxAttackers`, `assigns combat damage`)
  if bLow == "creatures with flying can't attack you or block creatures you control" then
    return some #[.ruleModifying cond? (.all #[
      .combat (.cantAttackPlayer (.all #[.hasType .creature, .hasKeyword .flying]) .you none),
      .combat (.cantBlockMatching (.all #[.hasType .creature, .hasKeyword .flying]) (.all #[.hasType .creature, .controlledBy .you]))
    ])]
  if let some r := pDropPrefixCI? bLow "creatures can't attack you unless their controller pays " then
    let costStr := (pSplitFirstCI? r " for each").map Prod.fst |>.getD r
    if let some cs := parseCostSpec costStr then
      return some #[.ruleModifying cond? (.combat (.attackTax (.hasType .creature) .you cs))]
  if let some rest := pDropPrefixCI? bLow "no more than " then
    if let some (nPart, tail) := (pSplitFirstCI? rest " creatures can attack ").orElse
        (fun _ => pSplitFirstCI? rest " creature can attack ") then
      if let some n := parseNatWord? nPart then
        let subjStr := (pDropSuffixCI? tail " each combat").getD tail
        let subj : StaticSubject :=
          if DiscourseCtx.isSelfPhrase subjStr then .self
          else match parseNounPhrase subjStr with | some np => .matching np.filter | none => .self
        return some #[.ruleModifying cond? (.combat (.maxAttackersPerPermanent subj n))]
  let parseRuleSubject? (subjStr : String) : Option StaticSubject :=
    if DiscourseCtx.isSelfPhrase subjStr then some .self
    else (parseStaticScope? subjStr cardName).map .matching
  if let some subjStr := pDropSuffixCI? body1 " attacks each combat if able" then
    if let some subj := parseRuleSubject? subjStr then
      return some #[.ruleModifying cond? (.combat (.attacksEachCombatIfAble subj))]
  if let some subjStr := (pDropSuffixCI? body1 " can attack as though it didn't have defender").orElse
      (fun _ => pDropSuffixCI? body1 " can attack as though they didn't have defender") then
    if let some subj := parseRuleSubject? subjStr then
      return some #[.ruleModifying cond? (.combat (.attackDespiteDefender subj))]
  if let some subjStr := pDropSuffixCI? body1 " can't be blocked" then
    if let some subj := parseRuleSubject? subjStr then
      return some #[.ruleModifying cond? (.combat (.cantBeBlocked subj))]
  if let some (subjStr, byStr) := pSplitFirstCI? body1 " can't be blocked by " then
    if let some subj := parseRuleSubject? subjStr then
      if let some np := parseNounPhrase byStr then
        return some #[.ruleModifying cond? (.combat (.cantBeBlockedBy subj np.filter.pred))]
  if let some (subjStr, excStr) := pSplitFirstCI? body1 " can't be blocked except by " then
    if let some subj := parseRuleSubject? subjStr then
      let nWord := (pWords excStr).getD 0 ""
      if let some n := parseNatWord? nWord then
        return some #[.ruleModifying cond? (.combat (.minBlockers subj n))]
  if let some (subjStr, uStr) := pSplitFirstCI? body1 " can't attack unless " then
    if let some subj := parseRuleSubject? subjStr then
      if let some uCond := parseStaticCondExtra? uStr cardName then
        return some #[.ruleModifying cond? (.combat (.cantAttackUnless subj uCond))]
  if let some (subjStr, uStr) := pSplitFirstCI? body1 " can't block unless " then
    if let some subj := parseRuleSubject? subjStr then
      if let some uCond := parseStaticCondExtra? uStr cardName then
        return some #[.ruleModifying cond? (.combat (.cantBlock subj (some uCond)))]
  if let some subjStr := pDropSuffixCI? body1 " can't block" then
    if let some subj := parseRuleSubject? subjStr then
      return some #[.ruleModifying cond? (.combat (.cantBlock subj none))]
  if let some (subjStr, tail) := pSplitFirstCI? body1 " doesn't untap during " then
    if let some subj := parseRuleSubject? subjStr then
      let uCond? : Option Condition :=
        match pSplitFirstCI? tail " unless " with
        | some (_, cStr) => parseStaticCondExtra? cStr cardName
        | none => none
      return some #[.ruleModifying cond? (.game (.doesntUntapDuringUntapStep subj uCond?))]

  -- 3e. Cost modifiers (`Equip abilities ...`, `Power-up abilities ...`, `Instant and sorcery spells ...`, `you may pay {0} rather than pay the equip cost...`)
  if bLow == "you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn" then
    return some #[StaticAbility.firstEquipFreeIfEnduringStory]
  if let some r := pDropPrefixCI? body1 "equip abilities you activate that target " then
    if let some (subjStr, rest) := pSplitFirstCI? r " cost " then
      if let some amtStr := pDropSuffixCI? rest " less to activate" then
        if let some mc := parseManaCost? amtStr then
          if DiscourseCtx.isSelfPhrase subjStr then
            return some #[StaticAbility.equipAbilitiesTargetingThisCostLess mc.genericCount]
  if let some r := pDropPrefixCI? body1 "power-up abilities of " then
    if let some (scopeStr, rest) := pSplitFirstCI? r " cost " then
      if let some amtStr := pDropSuffixCI? rest " less to activate" then
        if let some mc := parseManaCost? amtStr then
          if let some scope := parseStaticScope? scopeStr cardName then
            return some #[.costModifier cond? (.abilities .you (some .powerUp) scope none none) (.reduceGeneric (.const (Int.ofNat mc.genericCount)))]
  if bLow == "instant and sorcery spells you cast cost {x} less to cast, where x is equipped creature's power" then
    return some #[StaticAbility.instantSorceryCostReductionEqualEquippedPower]
  if bLow == "instant and sorcery spells you cast with mana value 4 or greater cost {x} less to cast, where x is this permanent's power" ||
      bLow == "instant and sorcery spells you cast with mana value 4 or greater cost {x} less to cast, where x is this creature's power" then
    return some #[StaticAbility.instantSorceryCostLessEqualPower]

  -- 3f. Replacements (`Prevent all damage`, `Double all damage`, `noncombat damage plus`, `heal other damage`, `counters plus one`, `connive draw`, `As ... choose Mardu or Jeskai`, `As ... may copy`, `would die`, `tokens`)
  if bLow == "prevent all damage that would be dealt to this" || bLow == "prevent all damage that would be dealt to this permanent" then
    return some #[StaticAbility.preventAllDamageToThis]
  if bLow == "double all damage equipped creature would deal" then
    return some #[StaticAbility.equippedDealsDoubleDamage]
  if bLow.contains "would deal noncombat damage to an opponent or a permanent an opponent controls" then
    if bLow.contains "plus x" && bLow.contains "power" then
      return some #[StaticAbility.noncombatDamagePlusSourcePower]
    else if bLow.contains "plus 1" then
      return some #[StaticAbility.noncombatDamagePlusOne]
  if bLow.contains "all other damage already dealt to it is healed" then
    return some #[StaticAbility.healOtherDamageWhenDealt]
  if bLow == "if one or more +1/+1 counters would be put on a creature you control, that many plus one +1/+1 counters are put on it instead" then
    return some #[StaticAbility.extraPlusOneCounter]
  if bLow == "if you would put one or more counters on a permanent you control, put that many plus one of each of those kinds of counters on that permanent instead" then
    return some #[StaticAbility.extraCounterOnPermanents]
  if bLow == "if a creature you control would connive, instead you draw a card, then that creature connives" then
    return some #[StaticAbility.extraDrawOnConnive]
  if bLow.startsWith "as " && bLow.contains " enters, choose mardu or jeskai" then
    return some #[StaticAbility.asEntersChooseNamedAnchors #["Mardu", "Jeskai"]]
  if low.startsWith "as " && low.contains " enters, you may have it become a copy of " then
    if let some (_, afterCopy) := pSplitFirstCI? norm " become a copy of " then
      let (refAndDur, excStr?) :=
        match pSplitFirstCI? afterCopy ", except " with
        | some (a, b) => (a, some b)
        | none => (afterCopy, none)
      let (filterStr, dur?) :=
        if let some b := pDropSuffixCI? refAndDur " until end of turn" then (b, some DurationExpr.untilEndOfTurn)
        else (refAndDur, none)
      let fClean := ((pDropPrefixCI? filterStr "any ").orElse fun _ =>
        (pDropPrefixCI? filterStr "a ").orElse fun _ => pDropPrefixCI? filterStr "an ") |>.getD filterStr
      if let some np := parseNounPhrase fClean then
        let copyMods? :=
          match excStr? with
          | none => some #[]
          | some ex => parseCopyModifications? qp ex cardName
        if let some copyMods := copyMods? then
          return some #[.replacement none (.asEntersMayCopy np.filter (dur?.getD .indefinite) copyMods)]
  if let some ifRest := pDropPrefixCI? norm "if " then
    if let some (scopeStr, afterDie) := pSplitFirstCI? ifRest " would die, exile it instead" then
      if let some np := parseNounPhrase scopeStr then
        let bonusTok? : Option TokenSpec :=
          match pSplitFirstCI? afterDie "create " with
          | some (_, tokRest) =>
            let ws := pWords tokRest
            if ws.size >= 2 then
              let desc := String.intercalate " " (ws.extract 1 ws.size).toList
              (parseTokenDesc? qp { cardName } desc parseObjWithCtx).map Prod.fst
            else none
          | none => none
        return some #[.replacement none (.exileInsteadOfDying np.filter bonusTok?)]
  if let some ifRest := pDropPrefixCI? norm "if one or more " then
    if let some (fromStr, afterCtrl) := pSplitFirstCI? ifRest " tokens would be created under your control, that many " then
      if let some replStr := pDropSuffixCI? afterCtrl " are created instead" then
        if let some np := parseNounPhrase fromStr then
          if let some (tok, _, _) := parseTokenDesc? qp { cardName } replStr parseObjWithCtx then
            return some #[.replacement none (.replaceTokens .you np.filter.pred tok)]
  if let some ifRest := pDropPrefixCI? norm "if you would create " then
    if let some (fromStr, afterCreate) := pSplitFirstCI? ifRest ", create " then
      if let some tokPart := pDropSuffixCI? afterCreate " in addition" then
        let fClean := ((pDropPrefixCI? fromStr "a ").orElse fun _ => pDropPrefixCI? fromStr "an ") |>.getD fromStr
        let fPred :=
          match parsePredefinedTokenWord? ((pDropSuffixCI? fClean " token").getD fClean) with
          | some .food => ObjectPred.hasSubtype (.literal .food)
          | some .treasure => ObjectPred.hasSubtype (.literal .treasure)
          | some .clue => ObjectPred.hasSubtype (.literal .clue)
          | _ => (parseNounPhrase fClean).map (·.filter.pred) |>.getD .anyObject
        let tws := pWords tokPart
        if tws.size >= 2 then
          let cnt := (parseNatWord? tws[0]!).getD 1
          let desc := String.intercalate " " (tws.extract 1 tws.size).toList
          if let some (tok, _, _) := parseTokenDesc? qp { cardName } desc parseObjWithCtx then
            return some #[.replacement none (.extraTokenWith .you fPred tok cnt)]

  -- 3g. `"You and <scope> have hexproof"` (`Captain America`)
  if let some r := pDropPrefixCI? body1 "you and " then
    if let some scopeStr := pDropSuffixCI? r " have hexproof" then
      if let some scope := parseStaticScope? scopeStr cardName then
        return some #[
          .ruleModifying cond? (.player (.hexproof .you none)),
          .continuous cond? scope (.grantKeywords #[Keyword.hexproof])
        ]

  -- 3h. Specialized scaling buffs (`for every seven cards in your graveyard`, `for each graveyard with seven or more cards in it`, `for each creature and planeswalker card in your graveyard`, `for each instant and sorcery card in your graveyard`)
  if bLow == "this permanent gets +2/+0 for every seven cards in your graveyard" ||
      bLow == "this creature gets +2/+0 for every seven cards in your graveyard" then
    return some #[StaticAbility.powerPerSevenInGraveyard]
  if bLow == "this permanent gets +2/+0 for each graveyard with seven or more cards in it" ||
      bLow == "this creature gets +2/+0 for each graveyard with seven or more cards in it" then
    return some #[StaticAbility.powerPerFatGraveyard 2]
  if bLow == "this permanent gets +1/+0 for each creature and planeswalker card in your graveyard" ||
      bLow == "this creature gets +1/+0 for each creature and planeswalker card in your graveyard" then
    return some #[StaticAbility.powerPerCreatureAndPlaneswalkerCard]
  if bLow == "equipped creature has first strike and gets +1/+0 for each instant and sorcery card in your graveyard" ||
      bLow == "equipped creature has first strike and gets +1/+0 for the number of instant or sorcery cards in your graveyard" then
    return some #[.continuous cond? equippedCreatureFilter (.all #[
      .grantKeywords #[Keyword.firstStrike],
      .modifyPT (.aggregate .count .one (.inZones .yourGraveyard (.any #[.hasType .instant, .hasType .sorcery]))) (.const 0)
    ])]

  -- 3i. `"<This> has all activated abilities of all <filter>."` (`Thranduil, the Elvenking`)
  if let some (subjStr, srcStr) := pSplitFirstCI? norm " has all activated abilities of " then
    if let some scope := parseStaticScope? subjStr cardName then
      let srcClean := (pDropPrefixCI? srcStr "all ").getD srcStr
      if let some np := parseNounPhrase srcClean then
        return some #[.continuous none scope (.copyActivatedFrom np.filter)]

  -- 3j. General `cond?` + `<scope> <ContinuousMod>` fallback
  let rec normStaticCm : ContinuousModification → ContinuousModification
    | .applyRule (.combat (.cantBeBlocked .self)) => .grantStatic #[StaticAbility.cantBeBlocked]
    | .all ms => .all (ms.attach.map fun ⟨m, _⟩ => normStaticCm m)
    | other => other
  for sep in #[" gets ", " get ", " has ", " have ", " loses ", " lose ", " is ", " are "] do
    if let some (scopeStr, modRest) := pSplitFirstCI? body1 sep then
      if let some scope := parseStaticScope? scopeStr cardName then
        if let some (cm, _) := parseContinuousMod? qp { cardName } (sep.trimAscii.copy ++ " " ++ modRest) then
          return some #[.continuous cond? scope (normStaticCm cm)]

  -- 3k. `SubGrammars.parseNovelStaticAbilityLine`
  if let some sas := parseNovelStaticAbilityLine pre cardName then
    if !sas.isEmpty then return some sas

  let _ := lbl?
  return none

/-- Stage-4c compositional parser for `ActivatedAbility` lines (CR 113.3b / 602 / 605.1a / 606),
including loyalty abilities, mana abilities, `Power-up` / `Exhaust` / `Boast`,
Equip-with-cost-reduction, and recursive quoted effects. -/
partial def parseActivatedAbilityComp (raw : String) (cardName : String := "") :
    Option ActivatedAbility := Id.run do
  let pre := (preprocessOracleLine raw).trimAscii.copy
  if pre.isEmpty then return none
  let (lbl?, body0) := extractLeadingLabel pre
  let qp := mkQuotedParsers ()

  -- 1. Equip with explicit cost-reduction sentence (`"Equip {3}. This ability costs {1} less to activate for each ..."`)
  if (pLower body0).startsWith "equip " && !hasTopLevelColon body0 then
    let sents := splitTopLevelSentences body0
    if sents.size >= 2 then
      if let some (.equip eqFilter eqCost) := parseKeywordAbility sents[0]! then
        let (_, restr) := peelActivatedRestrictions (sents.extract 1 sents.size) cardName
        if !restr.costReductions.isEmpty then
          let isPlain := eqFilter == .all #[.hasType .creature, .controlledBy .you]
          let extraPred? : Option ObjectPred := if isPlain then none else some eqFilter
          let pred : ObjectPred :=
            if isPlain then eqFilter
            else .all #[eqFilter, .hasType .creature, .controlledBy .you]
          return some {
            cost := eqCost
            effect := {
              targets := TargetSpec.single { domain := .object .battlefield pred }
              body := .permanent (.attach .this (.target 0))
            }
            timing := .sorcery
            costReductions := restr.costReductions
            tag? := some (.equip extraPred?)
          }

  -- 2. Must have a top-level unquoted `:` separating `<Cost>` and `<Effect>`
  let some (rawCost0, rawEff0) := splitTopLevelColon body0 | return none

  -- 3. Try `SubGrammars.parseManaAbilityLine` first when there's no mechanic label
  -- and no quoted sub-ability inside the effect
  if lbl?.isNone && !rawEff0.contains '"' then
    if let some manaAb := parseManaAbilityLine body0 cardName then
      return some manaAb

  -- 4. Parse `<CostSpec>` — ensure bare loyalty costs (`+1`, `0`, `−2`, `-X`) are bracketed
  -- because `SubGrammars.parseLoyaltySymbol?` expects `[+1]` / `[0]` / `[-2]`!
  let costNorm := replaceCardNameOutsideQuotes rawCost0 cardName "this permanent"
  let costStr :=
    let c0 := costNorm.trimAscii.copy.replace "\u2212" "-"
    if c0.startsWith "[" && c0.endsWith "]" then c0
    else if c0 == "0" || c0 == "+X" || c0 == "-X" || c0 == "+x" || c0 == "-x" ||
        ((c0.startsWith "+" || c0.startsWith "-") && c0.length >= 2 && (c0.drop 1).all Char.isDigit) then
      s!"[{c0}]"
    else costNorm
  let some cost0 := parseCostSpec costStr | return none

  -- 5. Peel trailing activation restrictions from effect sentences
  let rawEffNorm := replaceCardNameOutsideQuotes rawEff0 cardName "this permanent"
  let effSents := splitTopLevelSentences rawEffNorm
  let (keptSents, restr) := peelActivatedRestrictions effSents cardName
  if keptSents.isEmpty then return none
  let effBodyText := String.intercalate ". " keptSents.toList
  let eff? : Option Effect :=
    if (pLower keptSents[0]!).startsWith "add " then
      match parseManaProductionSpec keptSents cardName with
      | some mp => some { targets := .none, body := .player (.addMana .you mp) }
      | none => parseCompositionalEffect qp effBodyText cardName false
    else
      parseCompositionalEffect qp effBodyText cardName false
  let some eff := eff? | return none

  let cost : CostSpec :=
    if cost0.bindVar?.isNone && Effect.usesCostPaidObjects eff.body then
      { cost0 with bindVar? := some ⟨0⟩ }
    else cost0

  -- 6. Derive timing, zones, limits, tag, and condition from loyalty + `MechanicLabel` + restrictions
  let isLoyalty := cost.items.any fun | .loyalty _ => true | _ => false
  let timing := if isLoyalty then ActivationTiming.loyalty else restr.timing
  let mut turnLimit? := restr.turnLimit?
  let mut lifetimeLimit? := restr.lifetimeLimit?
  let mut condition? := restr.condition?
  let mut tag? : Option ActivationMechanicTag := none
  let effLow := pLower effBodyText
  let effGyZone : Bool :=
    effLow.contains "this card from your graveyard" || effLow.contains "this permanent from your graveyard"
  let activeZones :=
    restr.extraZones?.getD (if effGyZone then #[.graveyard] else inferActiveZonesFromCost cost costNorm)

  match lbl? with
  | some .powerUp =>
    tag? := some .powerUp
    if lifetimeLimit?.isNone then lifetimeLimit? := some 1
  | some .exhaust =>
    tag? := some .exhaust
    if lifetimeLimit?.isNone then lifetimeLimit? := some 1
  | some .boast =>
    tag? := some .boast
    if turnLimit?.isNone then turnLimit? := some 1
    if condition?.isNone then
      condition? := some ActivatedAbility.condSourceAttackedThisTurn
  | _ => pure ()

  return some {
    cost
    effect := eff
    timing
    activeZones
    turnLimit?
    lifetimeLimit?
    condition?
    costReductions := restr.costReductions
    tag?
  }

/-- Stage-4c compositional parser for `TriggeredAbility` lines (CR 113.3c / 603 / 714.2b),
including Saga chapters (`I, II — ...`), mechanic labels (`Mardu —`, `Jeskai —`, `Eminence —`),
all trigger headers via `parseTriggerClauses`, and compositional effect bodies. -/
partial def parseTriggeredAbilityComp (raw : String) (cardName : String := "") :
    Option (Array TriggeredAbility) := Id.run do
  let pre := (preprocessOracleLine raw).trimAscii.copy
  if pre.isEmpty then return none
  let qp := mkQuotedParsers ()

  -- 1. Saga chapter lines (`"I — ..."`, `"I, II — ..."`, `"III — ..."`) (CR 714.2b)
  if let some (roman, body) := parseChapterHeader pre then
    let (_, bodyClean) := extractLeadingLabel body
    if let some eff := parseCompositionalEffect qp bodyClean cardName true then
      return some #[TriggeredAbility.sagaChapters (parseChapterNumbers roman) eff]

  -- 2. Extract optional mechanic label (`Mardu —`, `Jeskai —`, `Eminence —`, `Threshold —`, `Corrupted —`)
  let (lbl?, body0) := extractLeadingLabel pre
  let hdrs := parseTriggerClauses body0 cardName
  if hdrs.isEmpty then return none

  let rec isSelfTriggerPattern : TriggerPattern → Bool
    | .zoneChange (.sameAs .this) _ _ _ _ => true
    | .attacks (.sameAs .this) _ _ _ _ _ => true
    | .blocks (.sameAs .this) => true
    | .becomesBlocked (.sameAs .this) => true
    | .becomesTapped (.sameAs .this) _ _ _ => true
    | .becomesUntapped (.sameAs .this) => true
    | .phasesOut (.sameAs .this) => true
    | .becomesTarget (.object (.sameAs .this)) _ _ => true
    | .damageDealt (.sameAs .this) _ _ _ _ => true
    | .damageDealt _ (.object { pred := .sameAs .this, .. }) _ _ _ => true
    | .putCounters _ _ (.sameAs .this) => true
    | .discard _ (.sameAs .this) _ => true
    | .stepBegins _ _ => true
    | .whenCond inner _ => isSelfTriggerPattern inner
    | .or l r => isSelfTriggerPattern l && isSelfTriggerPattern r
    | _ => false

  let rec isAttachedHostTriggerPattern : TriggerPattern → Bool
    | .zoneChange (.sameAs .attachedHost) _ _ _ _ => true
    | .attacks (.sameAs .attachedHost) _ _ _ _ _ => true
    | .blocks (.sameAs .attachedHost) => true
    | .becomesBlocked (.sameAs .attachedHost) => true
    | .becomesTapped (.sameAs .attachedHost) _ _ _ => true
    | .becomesUntapped (.sameAs .attachedHost) => true
    | .phasesOut (.sameAs .attachedHost) => true
    | .damageDealt (.sameAs .attachedHost) _ _ _ _ => true
    | .whenCond inner _ => isAttachedHostTriggerPattern inner
    | .or l r => isAttachedHostTriggerPattern l && isAttachedHostTriggerPattern r
    | _ => false

  let rec triggerPlayerRoleOf : TriggerPattern → Option PlayerExpr
    | .damageDealt _ (.player _) _ _ _ => some (.triggerPlayer .damagedPlayer)
    | .damageDealt _ (.playerOrObject _ _) _ _ _ => some (.triggerPlayer .damagedPlayer)
    | .stepBegins _ (.controllerOf obj) => some (.controllerOf obj)
    | .stepBegins _ (.player pf) =>
      if pf.pred == .matchesExpr (.controllerOf .attachedHost) then some (.controllerOf .attachedHost)
      else some .activePlayer
    | .zoneChange pred _ _ _ _ =>
      if pred == .sameAs .this then none else some (.controllerOf .triggerSubject)
    | .attacks pred _ _ _ _ _ | .blocks pred | .becomesBlocked pred
    | .becomesTapped pred _ _ _ | .becomesUntapped pred | .phasesOut pred =>
      if pred == .sameAs .this then none else some (.controllerOf .triggerSubject)
    | .castSpell .. | .activateAbility .. | .playerAction ..
    | .drawCard .. | .discard .. | .sacrifice .. | .gainLife .. | .loseLife .. | .createTokens .. =>
      some (.triggerPlayer .actor)
    | .whenCond inner _ => triggerPlayerRoleOf inner
    | .or l r => (triggerPlayerRoleOf l).orElse fun _ => triggerPlayerRoleOf r
    | _ => none

  let mut out : Array TriggeredAbility := #[]
  for hdr in hdrs do
    let trigRole? := triggerPlayerRoleOf hdr.pattern
    let some eff0 := parseCompositionalEffect qp hdr.effectText cardName true (isSelfTriggerPattern hdr.pattern) none trigRole? (isAttachedHostTriggerPattern hdr.pattern) | return none
    let mut zones := hdr.activeZones
    let mut interv? := hdr.interveningIf?
    let mut eff := eff0
    -- On `"Whenever you cast a spell that targets one or more <pred>, those creatures ..."`,
    -- `"those creatures"` refers to the targeted objects of the triggering spell, not the spell itself (`Storm, Windrider`).
    match hdr.pattern, eff.body with
    | .castSpell _ _ _ _ _ _ (some (.object tgtFilter)), .installEffect (.applyContinuous dur .triggerSubject mod) =>
      if (pLower hdr.effectText).contains "those creatures" then
        eff := { eff with body := .installEffect (.applyContinuous dur (.filter (.targetsOf .triggerSubject) tgtFilter.pred) mod) }
    | _, _ => pure ()
    -- Fold `chosenAnchorIs` intervening-if onto `effect.body` for round-trip parity with `Core.lean` (`Windcrag Siege`).
    match interv? with
    | some cond@(.exists (.filter .this (.chosenAnchorIs _))) =>
      eff := { eff with body := .ifCond cond eff.body .noop }
      interv? := none
    | _ => pure ()
    let mut pat := hdr.pattern
    match lbl? with
    | some .eminence =>
      if !zones.contains .command then zones := zones.push .command
    | some .infinity =>
      pat := .whenCond pat (Condition.thisMatches (.hasDesignation .harnessed))
    | some (.anchor name) =>
      let anchorCond := Condition.exists (.filter .this (.chosenAnchorIs name))
      eff := { eff with body := .ifCond anchorCond eff.body .noop }
    | _ => pure ()
    out := out.push {
      word := hdr.word
      pattern := pat
      grouping := hdr.grouping
      interveningIf? := interv?
      activeZones := zones
      limit := hdr.limit
      effect := eff
    }
  return some out

end

/-- Parse an arbitrary one-shot spell/ability `Effect` using the fully-tied
Stage-4b/4c compositional grammar. -/
def parseEffectComp (raw : String) (cardName : String := "") (isTrigger : Bool := false)
    (isSpell : Bool := false) :
    Option Effect :=
  parseCompositionalEffect (mkQuotedParsers ()) raw cardName isTrigger (isSpell := isSpell)

end Mtg.Engine.Parser
