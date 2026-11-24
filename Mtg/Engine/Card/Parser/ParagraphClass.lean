import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Parser.FrameSplit
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.AbilityGrammar

/-!
# Stage-3 Deterministic Paragraph Classifier & Full Compositional Card Parser

Classifies and parses every rules paragraph of a card face or sub-face using
Stages 1–5 exclusively (zero prototype tables, zero legacy fallback matchers):
1. CR 100.2a `DeckLimit` (`"A deck can have any number of / up to N cards named ..."`).
2. CR 714.2b Saga chapter headers (`I, II — ...`).
3. CR 606 loyalty & CR 602 / 605.1a activated abilities (unquoted top-level `:`,
   plus Equip-with-cost-reduction).
4. CR 603 triggered abilities (`When` / `Whenever` / `At` after optional mechanic/ability word).
5. CR 702 keywords (`parseKeywordLine`, including `Equip` and `Cycling` directly on
   `CardDef.keywords`).
6. CR 113.3a spell abilities on Instants / Sorceries / `SubFace`s (`additionalCosts`,
   spell-modifying `StaticAbility`s, and one-shot `Effect` bodies).
7. CR 113.3d static abilities (`Enchant`, CDAs, continuous, rule-modifying, cost-modifying,
   replacement).
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-! ### Paragraph Grouping & Modal Bullet Reassembly -/

/-- Reassemble raw rules lines into logical paragraphs by attaching `• ...` modal
bullet lines to their preceding modal header line and skipping blank/pure-reminder lines. -/
def groupRulesParagraphs (lines : List String) : Array String := Id.run do
  let mut out : Array String := #[]
  for raw in lines do
    let pre := (preprocessOracleLine raw).trimAscii.copy
    if pre.isEmpty then continue
    if pre.startsWith "•" && !out.isEmpty then
      let prev := out[out.size - 1]!
      let prevLow := pLower prev
      let isModalHeader :=
        prevLow.contains "choose one" || prevLow.contains "choose two" ||
        prevLow.contains "choose up to" || prevLow.contains "choose both" ||
        prevLow.contains "choose any number" || prevLow.contains "choose x" ||
        prev.endsWith "—"
      if isModalHeader then
        out := out.set! (out.size - 1) (prev ++ " " ++ pre)
      else
        let stripped := (pre.drop 1).trimAscii.copy
        if !stripped.isEmpty then
          out := out.push stripped
    else
      out := out.push pre
  return out

/-! ### CR 100.2a Deck-Limit Line Parser -/

/-- Parse `"A deck can have any number of cards named <X>."` or
`"A deck can have up to <N> cards named <X>."` (CR 100.2a). -/
def parseDeckLimitLine? (line : String) : Option DeckLimit :=
  let low := pLower (pClean line)
  if low.startsWith "a deck can have any number of cards named " then
    some .unlimited
  else if let some rest := pDropPrefixCI? low "a deck can have up to " then
    match (pSplitFirstCI? rest " cards named ").orElse (fun _ => pSplitFirstCI? rest " card named ") with
    | some (nStr, _) => (parseNatWord? nStr).map .maxCopies
    | none => none
  else none

/-! ### CR 305.6 Intrinsic Basic-Land Mana Line Detection -/

private def isRedundantBasicLandManaLine (c : CardDef) (line : String) : Bool :=
  if !c.isLand then false
  else
    let l := pLower (pClean line)
    c.basicLandMana.any fun col =>
      l == s!"\{t}: add \{{pLower col.letter}}"

/-! ### Spell Effect Merging -/

private def appendSpellEffect (c : CardDef) (eff : Effect) : CardDef :=
  let sa : SpellAbility :=
    match c.spellAbility with
    | none => { effect := eff }
    | some cur =>
      if cur.effect.body == .noop && cur.effect.targets.isEmpty then
        { cur with effect := eff }
      else
        let mergedTargets : TargetSpec := {
          slots := cur.effect.targets.slots ++ eff.targets.slots
          crossSlotConstraints := cur.effect.targets.crossSlotConstraints ++ eff.targets.crossSlotConstraints
        }
        { cur with effect := { targets := mergedTargets, body := flattenInstrSeq #[cur.effect.body, eff.body] } }
  { c with spellAbility := some sa }

private def appendAdditionalCost (c : CardDef) (ac : AdditionalCostSpec) : CardDef :=
  let sa : SpellAbility :=
    match c.spellAbility with
    | none => { effect := { body := .noop }, additionalCosts := #[ac] }
    | some cur => { cur with additionalCosts := cur.additionalCosts.push ac }
  { c with spellAbility := some sa }

/-! ### Stage-3 Rules Paragraph Classifier -/

/-- Parse all rules paragraphs of a `CardDef` face using the compositional Stage 2–5
pipeline. Every paragraph must parse cleanly; unrecognized lines return `.error`. -/
def parseRulesCompositional (base : CardDef) (rules : List String) : Except String CardDef := Id.run do
  let paras := groupRulesParagraphs rules
  let mut c := base
  let isSpell := c.isInstantOrSorcery

  -- Group consecutive pure one-shot spell paragraphs on Instants/Sorceries that share
  -- discourse anaphora (`"Exile target creature."` / `"Its controller..."`) when needed,
  -- while classifying keywords, additional costs, static cost/cast modifiers, and
  -- triggered/activated abilities individually.
  let mut spellParas : Array String := #[]
  let flushSpell (card : CardDef) (sp : Array String) : Except String CardDef :=
    if sp.isEmpty then .ok card
    else
      let joined := String.intercalate " " sp.toList
      match parseEffectComp joined card.name false isSpell with
      | some eff => .ok (appendSpellEffect card eff)
      | none => .error s!"unrecognized spell text on {card.name}: {joined}"

  for para in paras do
    let pre := para.trimAscii.copy
    if pre.isEmpty then continue
    let (lbl?, body) := extractLeadingLabel pre
    let bLow := pLower body

    -- 1. Redundant basic land mana reminder (`({T}: Add {W}.)` already dropped, handle unparenthesized too)
    if isRedundantBasicLandManaLine c pre then
      continue

    -- 1b. Default Aura `Enchant creature` (CR 303.4a — represented by empty `enchantRestriction`)
    if bLow == "enchant creature" then
      continue

    -- 1c. `Mardu — If a creature attacking causes a triggered ability ...` on `Windcrag Siege`
    -- (already modeled via `asEntersChoose (.namedAnchors #["Mardu", "Jeskai"])` and `Core.lean`'s
    -- `isMarduOrJeskaiChoice` attack-trigger doubling).
    if lbl? == some (.anchor "Mardu") && bLow.contains "if a creature attacking causes a triggered ability" then
      continue

    -- 2. CR 100.2a `DeckLimit`
    if let some dl := parseDeckLimitLine? pre then
      c := { c with deckLimitOverride := some dl }
      continue

    -- 3. Additional cost on spells (`"As an additional cost to cast this spell, ..."`)
    if bLow.startsWith "as an additional cost to cast " then
      let norm := replaceCardNameOutsideQuotes body c.name "this spell"
      if let some ac := parseAdditionalCostSpec norm then
        c := appendAdditionalCost c ac
        continue

    -- 4. CR 714.2b Saga chapter line (`"I — ..."`, `"I, II — ..."`)
    if (parseChapterHeader pre).isSome then
      match parseTriggeredAbilityComp pre c.name with
      | some trs =>
        c := { c with triggeredAbilities := c.triggeredAbilities ++ trs }
        continue
      | none => return .error s!"unrecognized chapter on {c.name}: {pre}"

    -- 5. Equip-with-cost-reduction (`"Equip {3}. This ability costs ..."`)
    if bLow.startsWith "equip " && !hasTopLevelColon body && body.contains '.' then
      if let some ab := parseActivatedAbilityComp pre c.name then
        c := { c with activatedAbilities := c.activatedAbilities.push ab }
        continue

    -- 6. Keyword line (`parseKeywordLine` — includes plain `Equip`, `Equip <Subtype>`,
    -- `Equip worthy`, `Cycling`, `<Type>cycling`, `Ward`, `Kicker`, `Flashback`, `Gift`,
    -- `Morph`, `Impending`, `Crew`, `Sneak`, `Affinity`, `Protection`, `Toxic`, etc.)
    -- Note: must not have a top-level `:` (which denotes an activated ability).
    if !hasTopLevelColon body && !body.contains '"' then
      if let some kws := parseKeywordLine body then
        if !kws.isEmpty then
          c := { c with keywords := c.keywords ++ kws }
          continue

    -- 7. Top-level unquoted `:` -> Activated ability (loyalty, mana, or general),
    -- plus any linked trailing `"When that mana is spent ..."` triggered ability (`Path of Ancestry`).
    if hasTopLevelColon body then
      let (actText, trailingTrig?) :=
        match pSplitFirstCI? pre " When that mana is spent " with
        | some (a, b) => (a, some ("When that mana is spent " ++ b))
        | none => (pre, none)
      match parseActivatedAbilityComp actText c.name with
      | some ab =>
        c := { c with activatedAbilities := c.activatedAbilities.push ab }
        if let some trigLine := trailingTrig? then
          match parseTriggeredAbilityComp trigLine c.name with
          | some trs => c := { c with triggeredAbilities := c.triggeredAbilities ++ trs }
          | none => return .error s!"unrecognized Oracle line on {c.name}: {trigLine}"
        continue
      | none => return .error s!"unrecognized Oracle line on {c.name}: {pre}"

    -- 8. Starts with `When` / `Whenever` / `At` (unless it's a delayed trigger on a spell
    -- like `"When you next cast ..."` / `"At the beginning of the next end step, ..."`)
    let isSpellDelayed :=
      isSpell && (bLow.startsWith "when you next " || bLow.startsWith "at the beginning of the next ")
    if !isSpellDelayed &&
        (bLow.startsWith "when " || bLow.startsWith "whenever " || bLow.startsWith "at ") then
      match parseTriggeredAbilityComp pre c.name with
      | some trs =>
        c := { c with triggeredAbilities := c.triggeredAbilities ++ trs }
        continue
      | none => return .error s!"unrecognized Oracle line on {c.name}: {pre}"

    -- 9. Spell-modifying static abilities on Instants/Sorceries (`"This spell costs..."`,
    -- `"This spell can't be countered"`, `"You may cast this spell as though it had flash..."`,
    -- `"You can't cast this spell unless..."`, `"If you control a commander, you may cast this spell without paying its mana cost"`)
    if isSpell then
      let looksLikeSpellStatic :=
        bLow.startsWith "this spell costs " ||
        bLow.startsWith "this spell can't be countered" ||
        bLow.startsWith "you can't cast this spell" ||
        bLow.startsWith "you may cast this spell as though it had flash" ||
        (bLow.contains "you may cast this spell without paying its mana cost")
      if looksLikeSpellStatic then
        if let some sas := parseStaticAbilityComp pre c.name then
          c := { c with staticAbilities := c.staticAbilities ++ sas }
          continue
      -- Otherwise accumulate as one-shot spell text!
      spellParas := spellParas.push body
      continue

    -- 10. Permanent non-activated/non-triggered paragraph -> Static ability
    -- (Plane cards may also carry standalone one-shot `{CHAOS}` effects.)
    match parseStaticAbilityComp pre c.name with
    | some sas =>
      c := { c with staticAbilities := c.staticAbilities ++ sas }
      continue
    | none =>
      if c.hasType .plane then
        spellParas := spellParas.push body
        continue
      return .error s!"unrecognized Oracle line on {c.name}: {pre}"

  flushSpell c spellParas

/-! ### Stage 1 + Stage 3 Full Face, Sub-Face & Card Entry Points -/

/-- Parse a Stage-1 `SubFaceFrame` (`//ADV//` or `//PREP//`) into `SubFace`. -/
def parseSubFaceCompositional (sf : SubFaceFrame) : Except String SubFace := do
  let c ← parseRulesCompositional sf.base sf.rules
  pure {
    kind := sf.kind
    name := c.name
    manaCost := c.manaCost
    colorIndicator := c.colorIndicator
    supertypes := c.supertypes
    types := c.types
    subtypes := c.subtypes
    keywords := c.keywords
    spellAbility := c.spellAbility
    staticAbilities := c.staticAbilities
  }

/-- Parse a Stage-1 `FaceFrame` into a `CardDef`. -/
def parseFaceCompositional (ff : FaceFrame) : Except String CardDef := do
  let mut c ← parseRulesCompositional ff.base ff.rules
  for sf in ff.subFaces do
    let parsed ← parseSubFaceCompositional sf
    c := c.withSubFace parsed
  pure c

/-- Parse a complete printed Oracle card (including `//` back faces and `//ADV//` /
`//PREP//` sub-faces) exclusively through the Stage 1–5 compositional pipeline. -/
def parseOracleCardCompositional (text : String) : Except String CardDef := do
  let frame ← splitCardFrame text
  let front ← parseFaceCompositional frame.front
  let full ←
    match frame.back? with
    | none => pure front
    | some bf =>
      let back ← parseFaceCompositional bf
      pure { front with otherFace := some back }
  match full.modellingError? with
  | some e => .error e
  | none => .ok full

end Mtg.Engine.Parser
