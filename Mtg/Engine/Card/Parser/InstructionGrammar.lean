import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.DiscourseBind
import Mtg.Engine.Card.Parser.TokenEmblemGrammar
import Mtg.Engine.Card.Parser.InspectSearchGrammar

/-!
# Stage-4b-iii Compositional `Instruction` & `Effect` Grammar (CR 608 / 603.12 / 700.2)

Verb-dispatched compositional parser covering all 18 `Instruction` constructors and
every action sub-family (`moveZone`, `create`, `permanent`, `damage`, `life`, `player`,
`turn`, `stack`, `installEffect`, `queueReflexiveTrigger`, plus all 8 combinators),
threaded with Stage-5 `DiscourseCtx` (`Instruction.bind`, anaphora, `where X is ...`,
and `"When you do"` reflexive triggers).
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-! ### Helper: Peel Leading/Trailing Duration & Conditions -/

private def parseDurOrDefault (raw : String) : Option DurationExpr :=
  let l := pLower (pClean raw)
  if l == "until end of turn" || l == "this turn" then some .untilEndOfTurn
  else if l == "until your next turn" || l == "until the beginning of your next turn" then
    some (.untilNextTurnOf .you)
  else if l == "until the end of your next turn" then some (.untilEndOfNextTurnOf .you)
  else if l == "until end of combat" then some .untilEndOfCombat
  else if l == "for the rest of the game" then some .indefinite
  else if l == "until this leaves the battlefield" ||
      l == "until this permanent leaves the battlefield" ||
      l == "until this creature leaves the battlefield" ||
      l == "until this aura leaves the battlefield" ||
      l == "until this artifact leaves the battlefield" ||
      l == "until this enchantment leaves the battlefield" ||
      l == "for as long as this permanent remains on the battlefield" ||
      l == "for as long as you control this permanent" then
    some (.whileOnBattlefield .this)
  else if l == "for as long as this permanent remains exiled" ||
      l == "for as long as it remains exiled" then
    some (.whileInZone .this .exile)
  else parseDuration raw

/-- Peel a trailing duration (`"until end of turn"`, `"until your next turn"`,
`"this turn"`, `"until this ... leaves the battlefield"`, `"for the rest of the game"`,
`"for as long as this permanent remains on the battlefield"`) from a clause. -/
private def peelTrailingDuration (raw : String) (ctx? : Option DiscourseCtx := none) : String × Option DurationExpr := Id.run do
  let s := pClean raw
  let candidates : Array (String × DurationExpr) := #[
    (" for as long as this permanent remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as this creature remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as this saga remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as this enchantment remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as this artifact remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as this remains on the battlefield", .whileOnBattlefield .this),
    (" for as long as you control this permanent", .whileOnBattlefield .this),
    (" for as long as you control this creature", .whileOnBattlefield .this),
    (" for as long as you control this", .whileOnBattlefield .this),
    (" for as long as this permanent remains exiled", .whileInZone .this .exile),
    (" for as long as this card remains exiled", .whileInZone .this .exile),
    (" until this card is cast from exile", .whileInZone .this .exile),
    (" until this permanent is cast from exile", .whileInZone .this .exile),
    (" for the rest of the game", .indefinite),
    (" until the beginning of your next turn", .untilNextTurnOf .you),
    (" until the end of your next turn", .untilEndOfNextTurnOf .you),
    (" until your next turn", .untilNextTurnOf .you),
    (" until end of combat", .untilEndOfCombat),
    (" until end of turn", .untilEndOfTurn),
    (" until this permanent leaves the battlefield", .whileOnBattlefield .this),
    (" until this creature leaves the battlefield", .whileOnBattlefield .this),
    (" until this aura leaves the battlefield", .whileOnBattlefield .this),
    (" until this artifact leaves the battlefield", .whileOnBattlefield .this),
    (" until this enchantment leaves the battlefield", .whileOnBattlefield .this),
    (" until this leaves the battlefield", .whileOnBattlefield .this),
    (" this turn", .untilEndOfTurn)
  ]
  for (sfx, dur) in candidates do
    if let some b := pDropSuffixCI? s sfx then
      return (b, some dur)
  -- `" for as long as <obj> has a <kind> counter on it"` (`Minas Morgul, Dark Fortress`)
  if let some (before, after) := pSplitLastCI? s " for as long as " then
    if let some (objStr, ctrPart) := pSplitFirstCI? after " has " then
      let cCore := ((pDropSuffixCI? ctrPart " on it").orElse fun _ => some ctrPart) |>.getD ctrPart
      if let some (k, _) := parseCounterSpec? cCore then
        let ctx := ctx?.getD {}
        let obj := (parseObjWithCtx ctx objStr).map Prod.fst |>.getD (.target (ctx.lastTargetSlot?.getD 0))
        return (before, some (.whileHasCounter obj k))
  -- `" until <player>'s next turn"` (`Construct a Cosmic Cube`, `Teferi's Reproach`)
  if let some (before, after) := pSplitLastCI? s " until " then
    if let some whoRaw := pDropSuffixCI? after " next turn" then
      let ctx := ctx?.getD {}
      if let some (p, _) := parsePossessivePlayerWithCtx ctx whoRaw then
        return (before, some (.untilNextTurnOf p))
  return (s, none)

/-- Parse a `Condition` with `cardName` self-aliasing and both `parseCondition` +
extra common one-shot condition forms (`"if X is 5 or greater"`, `"if this is the first/second/third time..."`,
`"if there is <obj>"`, `"if <obj>'s controller is you"`, `"if you have an enduring story"`). -/
partial def parseInstrCondition? (raw : String) (cardName : String := "") (ctx? : Option DiscourseCtx := none) : Option Condition := Id.run do
  let s := pClean (replaceCardNameOutsideQuotes raw cardName "this permanent")
  let l := pLower s
  let ctx := ctx?.getD { cardName }
  if l == "not" || l == "not " || l == "not (you do)" || l == "you don't" then
    return some (.not (.stepSucceeded (ctx.lastActionVar?.getD ⟨0⟩)))
  if let some inner := pDropPrefixCI? s "not (" then
    if let some core := pDropSuffixCI? inner ")" then
      if let some c := parseInstrCondition? core cardName (some ctx) then
        return some (.not c)
  if l == "this spell was kicked" || l == "it was kicked" then
    return some (.castPred (.wasKicked .this))
  if l == "this spell was cast using teamwork" || l == "its teamwork cost was paid" ||
      l == "this spell's teamwork cost was paid" then
    return some (.castPred (.teamworkPaid .this))
  if l == "this spell was cast from a graveyard" || l == "it was cast from a graveyard" then
    return some (.castPred (.castFrom .graveyard .this))
  if l == "this spell was cast from exile" || l == "it was cast from exile" then
    return some (.castPred (.castFrom .exile .this))
  if l == "this spell wasn't cast from your hand" || l == "it wasn't cast from your hand" then
    return some (.not (.castPred (.castFrom .hand .this)))
  if l == "the gift was promised" || l == "its gift was promised" then
    return some (.castPred (.giftPromised .this))
  if l == "you have an enduring story" then
    return some (.playerPred .you (.hasDesignation .enduringStory))
  if l == "this optional effect hasn't been used this turn" then
    return some (.not (.turnHistory (.nthResolutionThisTurn 1)))
  if l == "this is the first time this ability has resolved this turn" then
    return some (.turnHistory (.nthResolutionThisTurn 1))
  if l == "this is the second time this ability has resolved this turn" || l == "it's the second time" then
    return some (.turnHistory (.nthResolutionThisTurn 2))
  if l == "this is the third time this ability has resolved this turn" || l == "it's the third time" then
    return some (.turnHistory (.nthResolutionThisTurn 3))
  if l == "it's attacking" || l == "this permanent is attacking" || l == "this creature is attacking" then
    let subj := ctx.lastSubject?.getD (if ctx.isTrigger && !ctx.isSelfTrigger then .triggerSubject else .this)
    return some (.exists (.filter subj (.combatRole .attacking)))
  if l == "it wasn't attacking" || l == "it isn't attacking" then
    let subj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.not (.exists (.filter subj (.combatRole .attacking))))
  if l == "it isn't a token" || l == "they're not a token" then
    let subj := ctx.lastSubject?.getD (if ctx.isSelfTrigger then .this else .triggerSubject)
    return some (.not (.exists (.filter subj .isToken)))
  if l == "it isn't a creature" || l == "the token isn't a creature" then
    let subj := ctx.lastActionVar?.map .stepObjects |>.getD (ctx.lastSubject?.getD .this)
    return some (.not (.exists (.filter subj (.hasType .creature))))
  if l == "this permanent isn't a creature" || l == "this equipment isn't a creature" then
    return some (.not (.exists (.filter .this (.hasType .creature))))
  if l == "your library has no cards in it" then
    return some (.cmp .eq (.playerMetric .librarySize .you) (.const 0))
  if l.contains "excess damage was dealt" && l.contains "this way" then
    let v := ctx.lastActionVar?.getD ⟨0⟩
    return some (.cmp .gt (.stepMetric .excessDamage v) (.const 0))
  -- `"you sacrificed a <pred> this way"` (`Garruk, Veiled Butcher`)
  if let some sacRest := pDropPrefixCI? s "you sacrificed " then
    if let some whatStr := pDropSuffixCI? sacRest " this way" then
      if let some np := parseNounPhrase whatStr then
        let v := ctx.lastActionVar?.getD ⟨0⟩
        return some (.exists (.filter (.stepObjects v) np.filter.pred))
  -- `"you put a <pred> into your graveyard this way"` (`Chandra, Chill of Compliance`, `Enlightened Confidant`)
  if let some putRest := pDropPrefixCI? s "you put " then
    if let some whatStr := pDropSuffixCI? putRest " into your graveyard this way" then
      if let some np := parseNounPhrase whatStr then
        let v := ctx.lastActionVar?.getD ⟨0⟩
        return some (.exists (.filter (.stepObjects v) np.filter.pred))
  -- `"you discard a <pred> card this way"` (`Silvan Reveler`)
  if let some discRest := pDropPrefixCI? s "you discard " then
    if let some whatStr := pDropSuffixCI? discRest " this way" then
      if let some np := parseNounPhrase whatStr then
        let v := ctx.lastActionVar?.getD ⟨0⟩
        return some (.exists (.filter (.stepObjects v) np.filter.pred))
  -- `"a <pred> is dealt damage this way"` (`The Black Arrow`)
  if let some whatStr := pDropSuffixCI? s " is dealt damage this way" then
    if let some np := parseNounPhrase whatStr then
      let v := ctx.lastActionVar?.getD ⟨0⟩
      return some (.exists (.filter (.stepObjects v) np.filter.pred))
  -- `"<obj> was <pred>"` (`Budding Insurgent`: `"that permanent was a legendary enchantment"`)
  if let some (oStr, pStr) := pSplitFirstCI? s " was " then
    if !(pLower oStr).contains "mana value" then
      match parseObjWithCtx ctx oStr, parseNounPhrase pStr with
      | some (obj, _), some np => return some (.exists (.filter obj np.filter.pred))
      | _, _ => pure ()
  -- `"<obj>'s mana value was N or less"` (`Sound the Trumpets`, `Vindictive Triumph`)
  if let some (oStr, tail) := pSplitFirstCI? s "'s mana value was " then
    if let some nStr := pDropSuffixCI? tail " or less" then
      match parseObjWithCtx ctx oStr, parseNatWord? nStr with
      | some (obj, _), some n => return some (.cmp .le (.objectStat .manaValue obj) (.const (Int.ofNat n)))
      | _, _ => pure ()
    if let some nStr := pDropSuffixCI? tail " or greater" then
      match parseObjWithCtx ctx oStr, parseNatWord? nStr with
      | some (obj, _), some n => return some (.cmp .ge (.objectStat .manaValue obj) (.const (Int.ofNat n)))
      | _, _ => pure ()
  -- `"you controlled <obj>"` (`Azog, Moria's Ruin`)
  if let some ctrlObjStr := pDropPrefixCI? s "you controlled " then
    if let some (obj, _) := parseObjWithCtx ctx ctrlObjStr then
      return some (.exists (.filter obj (.controlledBy .you)))
  -- `"you control a <pred> with greater mana value than <obj>"` (`Evil's Thrall`)
  if let some ctrlRest := pDropPrefixCI? s "you control " then
    if let some (predStr, thanStr) := pSplitFirstCI? ctrlRest " with greater mana value than " then
      match parseNounPhrase predStr, parseObjWithCtx ctx thanStr with
      | some np, some (thanObj, _) =>
        return some (.exists (.inZones .battlefield (.all #[np.filter.pred, .controlledBy .you, .stat .manaValue .gt (.objectStat .manaValue thanObj)])))
      | _, _ => pure ()
  -- Compound `"<c1> and <c2>"` / `"<c1> or <c2>"`
  if let some (a, b) := pSplitFirstCI? s " and " then
    if !(pLower a).contains "between " then
      match parseInstrCondition? a cardName (some ctx), parseInstrCondition? b cardName (some ctx) with
      | some c1, some c2 => return some (.all #[c1, c2])
      | _, _ => pure ()
  if let some (a, b) := pSplitFirstCI? s " or " then
    match parseInstrCondition? a cardName (some ctx), parseInstrCondition? b cardName (some ctx) with
    | some c1, some c2 => return some (.any #[c1, c2])
    | _, _ => pure ()
  -- `"there is <obj>"` (`"there is this permanent"`, `"there is target"`, `"there is those objects matching land"`, `"there is an another Hero you control"`)
  if let some rest0 := pDropPrefixCI? s "there is " then
    let rest := (pDropPrefixCI? rest0 "an another ").map ("another " ++ ·) |>.getD rest0
    if let some (obj, _) := parseObjWithCtx ctx rest then
      return some (.exists obj)
  -- `"every <obj> is <pred>"`
  if let some rest := pDropPrefixCI? s "every " then
    if let some (oStr, pStr) := pSplitFirstCI? rest " is " then
      match parseObjWithCtx ctx oStr, parseNounPhrase pStr with
      | some (obj, _), some np => return some (.forAll obj np.filter.pred)
      | _, _ => pure ()
  -- `"<obj>'s controller is you"` / `"target's controller is you"`
  if let some oStr := pDropSuffixCI? s "'s controller is you" then
    if let some (obj, _) := parseObjWithCtx ctx oStr then
      return some (.playerPred (.controllerOf obj) (.matchesExpr .you))
  -- Helper for LHS/RHS value expressions inside condition comparisons (supports `the number of <objWithCtx>`)
  let parseCondVal (vRaw : String) : Option ValueExpr :=
    let vl := pLower (pClean vRaw)
    if vl == "x" then some .chosenX
    else if vl == "its mana value" || vl == "that card's mana value" then
      let o := match ctx.lastActionVar? with | some v => .stepObjects v | none => ctx.lastSubject?.getD .triggerSubject
      some (.objectStat .manaValue o)
    else if let some ofRest := pDropPrefixCI? vRaw "the number of " then
      if (pLower ofRest).startsWith "cards in " then
        (parseValueExpr vRaw).orElse (fun _ => (parseObjWithCtx ctx ofRest).map (fun (o, _) => .aggregate .count .one o))
      else
        (parseObjWithCtx ctx ofRest).map (fun (o, _) => .aggregate .count .one o)
          |>.orElse (fun _ => parseValueExpr vRaw)
    else
      (ctx.resolveStepMetric? vRaw).orElse (fun _ => (parseCountVal? vRaw).orElse (fun _ => parseValueExpr vRaw))
  -- `"<val> is less than or equal to <val2>"` (`Part in Friendship`)
  if let some (lhsStr, rhsStr) := pSplitFirstCI? s " is less than or equal to " then
    match parseCondVal lhsStr, parseCondVal rhsStr with
    | some v1, some v2 =>
      -- If `lhs` was `its mana value`, match `Part in Friendship`'s filter form or direct cmp
      return some (.cmp .le v1 v2)
    | _, _ => pure ()
  -- `"<val> is less than <val2>"` (`Garruk, Veiled Butcher`)
  if let some (lhsStr, rhsStr) := pSplitFirstCI? s " is less than " then
    match parseCondVal lhsStr, parseCondVal rhsStr with
    | some v1, some v2 => return some (.cmp .lt v1 v2)
    | _, _ => pure ()
  -- `"<val> is greater than or equal to <val2>"`
  if let some (lhsStr, rhsStr) := pSplitFirstCI? s " is greater than or equal to " then
    match parseCondVal lhsStr, parseCondVal rhsStr with
    | some v1, some v2 => return some (.cmp .ge v1 v2)
    | _, _ => pure ()
  -- `"<val> is greater than <val2>"` / `"<val> is N or greater"` / `"<val> is N or less"` / `"<val> is N"`
  if let some (lhsStr, rhsStr) := pSplitFirstCI? s " is greater than " then
    match parseCondVal lhsStr, parseCondVal rhsStr with
    | some v1, some v2 => return some (.cmp .gt v1 v2)
    | _, _ => pure ()
  if let some (lhsStr, rhsStr) := pSplitFirstCI? s " is " then
    if let some nStr := pDropSuffixCI? rhsStr " or greater" then
      match parseCondVal lhsStr, parseCondVal nStr with
      | some v1, some v2 => return some (.cmp .ge v1 v2)
      | _, _ => pure ()
    if let some nStr := pDropSuffixCI? rhsStr " or less" then
      match parseCondVal lhsStr, parseCondVal nStr with
      | some v1, some v2 => return some (.cmp .le v1 v2)
      | _, _ => pure ()
    if let some n := parseNatWord? rhsStr then
      if let some v1 := parseCondVal lhsStr then
        return some (.cmp .eq v1 (.const (Int.ofNat n)))
    -- `"<obj> is <pred>"` (`"that creature is a Bear"`, `"it is permanent with mana value 3 or less"`)
    match parseObjWithCtx ctx lhsStr, parseNounPhrase rhsStr with
    | some (obj, _), some np =>
      return some (.exists (.filter obj np.filter.pred))
    | _, _ => pure ()
  -- `"it's a <pred>"` (`Teyo`, `The Invincible Iron Man`)
  if let some predStr := (pDropPrefixCI? s "it's ").orElse (fun _ => pDropPrefixCI? s "that creature's ") then
    if let some np := parseNounPhrase predStr then
      let subj := ctx.lastSubject?.getD (ctx.lastActionVar?.map .stepObjects |>.getD .triggerSubject)
      return some (.exists (.filter subj np.filter.pred))
  if let some rest := pDropPrefixCI? s "excess damage was dealt" then
    let _ := rest
    return some (.cmp .ge (.stepMetric .excessDamage (ctx.lastActionVar?.getD ⟨0⟩)) (.const 1))
  if let some c := parseCondition s then
    return some c
  return none

/-- Parse a `ValueExpr` with `DiscourseCtx` support (including `"that many"`,
`"that much"`, `"excess damage dealt this way"`, `"its power"`, `"twice its power"`,
`"target's loyalty"`, `"the number of ..."`, `"one plus ..."`, etc.). -/
partial def parseValueWithCtx (ctx : DiscourseCtx) (raw : String) : Option ValueExpr := Id.run do
  let s := pClean raw
  let l := pLower s
  if let some (a, b) := pSplitFirstCI? s " plus " then
    match parseValueWithCtx ctx a, parseValueWithCtx ctx b with
    | some va, some vb => return some (.binary .add va vb)
    | _, _ => pure ()
  if let some sm := ctx.resolveStepMetric? s then
    return some sm
  if l == "x" then return some .chosenX
  if l == "that many" || l == "that much" || l == "that amount" then
    return some (match ctx.lastActionVar? with | some v => .stepMetric .movedCount v | none => .eventAmount)
  if l == "that card's power" then
    match ctx.lastActionVar? with
    | some v => return some (.stepMetric .sumPower v)
    | none => pure ()
  if l == "its power" || l == "that creature's power" || l == "that permanent's power" ||
      l == "that card's power" || l == "target's power" then
    let obj :=
      if l == "target's power" then .target (ctx.lastTargetSlot?.getD 0)
      else ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.objectStat .power obj)
  if l == "target's loyalty" || l == "its loyalty" then
    let obj :=
      if l == "target's loyalty" then .target (ctx.lastTargetSlot?.getD 0)
      else ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.objectStat .loyalty obj)
  if l == "this toughness" || l == "this permanent's toughness" || l == "this creature's toughness" then
    return some (.objectStat .toughness .this)
  if l == "this power" || l == "this permanent's power" || l == "this creature's power" then
    return some (.objectStat .power .this)
  if l == "the sacrificed creature's power" || l == "those exiled cards's power" then
    return some (.objectStat .power .costPaidObjects)
  if l == "twice its power" || l == "twice that creature's power" then
    let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.binary .mul (.const 2) (.objectStat .power obj))
  if l == "its toughness" || l == "that creature's toughness" || l == "that permanent's toughness" then
    let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.objectStat .toughness obj)
  if l == "its mana value" || l == "that creature's mana value" || l == "that spell's mana value" ||
      l == "that card's mana value" || l == "that object's mana value" then
    let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    return some (.objectStat .manaValue obj)
  if l == "the amount of mana spent to cast that spell" ||
      l == "the amount of mana spent to cast that object" then
    return some (.manaSpent .triggerSubject)
  if l == "the total power of those exiled cards" then
    let obj := match ctx.lastActionVar? with | some v => .stepObjects v | none => .costPaidObjects
    return some (.aggregate .sum (.stat .power) obj)
  if l == "the total mana value of those objects" || l == "the total mana value of those cards" then
    let obj := match ctx.lastActionVar? with | some v => .stepObjects v | none => .triggerSubject
    return some (.aggregate .sum (.stat .manaValue) obj)
  if l == "the total mana value of other spells you've cast this turn" then
    return some (.playerMetric .otherSpellsManaValueThisTurn .you)
  if l == "the number of cards moved this way" || l == "the number of creatures exiled this way" ||
      l == "the number of creatures destroyed this way" || l == "the number of permanents destroyed this way" ||
      l == "the number of cards drawn this way" then
    return some (match ctx.lastActionVar? with | some v => .stepMetric .movedCount v | none => .eventAmount)
  if l == "the excess damage dealt this way" || l == "that excess damage" then
    return some (.stepMetric .excessDamage (ctx.lastActionVar?.getD ⟨0⟩))
  if l == "the number of cards you've discarded this turn" then
    return some (.playerMetric .cardsDiscardedThisTurn .you)
  if let some rest := (pDropPrefixCI? s "the number of cards that were put into ").orElse
      (fun _ => pDropPrefixCI? s "the number of cards put into ") then
    if let some whoStr := (pDropSuffixCI? rest " graveyard from target player's library this turn").orElse
        (fun _ => (pDropSuffixCI? rest " graveyard from that player's library this turn").orElse
          (fun _ => pDropSuffixCI? rest " graveyard from their library this turn")) then
      if let some (who, _) := parsePossessivePlayerWithCtx ctx whoStr then
        return some (.playerMetric .cardsMilledThisTurn who)
  if let some rest := pDropPrefixCI? s "the number of colors among " then
    if let some (obj, _) := parseObjWithCtx ctx rest then
      return some (.colorCountAmong obj)
  if let some rest := pDropPrefixCI? s "the greatest mana value among " then
    if let some (obj, _) := parseObjWithCtx ctx rest then
      return some (.aggregate .max (.stat .manaValue) obj)
  if let some rest := pDropPrefixCI? s "the number of " then
    if pLower rest == "creatures you control of the chosen type" then
      let subRef : SubtypeRef := match ctx.lastActionVar? with | some v => .fromStep v | none => .chosenOnSource
      return some (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .hasSubtype subRef])))
    if let some (ctrPart, onPart) := pSplitFirstCI? rest " counters on " then
      if let some (kind, _) := CounterKind.ofPrefix ((pWords ctrPart).toList.map pLower) then
        if let some (obj, _) := parseObjWithCtx ctx onPart then
          return some (.counterCount (some kind) obj)
    if let some attPart := pDropSuffixCI? rest " attached to this permanent" then
      if let some np := parseNounPhrase attPart then
        return some (.aggregate .count .one (.inZones .battlefield (.all #[np.filter.pred, .attachedTo .this])))
    if (pLower rest).startsWith "cards in " then
      if let some v := parseValueExpr s then
        return some v
    if let some (obj, _) := parseObjWithCtx ctx rest then
      return some (.aggregate .count .one obj)
  if let some n := parseNatWord? s then
    return some (.const (Int.ofNat n))
  if let some v := parseValueExpr s then
    return some v
  return none

/-! ### Divided-Damage Phrase Parser (CR 601.2d) -/

private def parseDividedMaxTargets? (raw : String) : Option (Nat × TargetDomain) :=
  let l := pLower (pClean raw)
  let dom : TargetDomain :=
    if l.contains "creature" && l.contains "planeswalker" then
      .object .battlefield (.any #[.hasType .creature, .hasType .planeswalker])
    else if l.contains "creature" then
      .object .battlefield (.hasType .creature)
    else .anyTarget
  if l.contains "one, two, or three" || l.contains "up to three" || l.contains "up to 3" then
    some (3, dom)
  else if l.contains "one or two" || l.contains "up to two" || l.contains "up to 2" then
    some (2, dom)
  else if l.contains "one target" || l.contains "up to one" || l.contains "up to 1" then
    some (1, dom)
  else if let some r := pDropPrefixCI? l "up to " then
    let w := (pWords r).getD 0 ""
    (parseNatWord? w).map fun n => (n, dom)
  else none

/-! ### Atomic Instruction Parser (Lead-Verb Dispatched) -/

/-- Parse one atomic one-shot instruction clause using $O(1)$ lead-word dispatch,
updating `DiscourseCtx`. Returns `(Instruction × Bool_mayBind × DiscourseCtx)` where
`Bool_mayBind` indicates whether this step can be an antecedent for `"this way"` /
`"those cards"` / `"that token"` `Instruction.bind` wrapping. -/
partial def parseAtomicInstr (qp : QuotedAbilityParsers) (ctx : DiscourseCtx) (raw : String) :
    Option (Instruction × Bool × DiscourseCtx) := Id.run do
  let norm := pClean (replaceCardNameOutsideQuotes raw ctx.cardName "this permanent")
  if norm.isEmpty then return none
  let low := pLower norm

  -- 0. Standalone fixed idioms
  if low == "recruit" || low == "you recruit" then
    return some (Instruction.recruit .you, true, ctx)
  if low == "investigate" then
    return some (Instruction.createTokensFixed .clue 1 .you, true, ctx)
  if let some invWho := pDropSuffixCI? norm " investigates" then
    if let some (who, ctx1) := parsePlayerWithCtx ctx invWho then
      return some (Instruction.createTokensFixed .clue 1 who, true, ctx1)
  if low == "proliferate" then
    return some (.player (.proliferate .you), false, ctx)
  if low == "proliferate twice" then
    return some (.player (.proliferate .you (.const 2)), false, ctx)
  if let some prRest := pDropPrefixCI? norm "for each kind of counter on " then
    if let some (tgtStr, _) := pSplitFirstCI? prRest ", give " then
      if let some (obj, ctx1) := parseObjWithCtx ctx tgtStr then
        return some (.player (.proliferate .you (.const 1) (some obj)), false, ctx1)
  if low == "the ring tempts you" then
    return some (.player (.temptWithRing .you), false, ctx)
  if low == "you become the monarch" then
    return some (.player (.becomeMonarch .you), false, ctx)
  if low == "you win the game" then
    return some (.player (.setStatus .you .winGame), false, ctx)
  if low == "you get the city's blessing" || low == "you get the city's blessing for the rest of the game" then
    return some (.player (.setPlayerDesignation .you .citysBlessing), false, ctx)
  if low == "you get enduring story" || low == "you get enduring story for the rest of the game" then
    return some (.player (.setPlayerDesignation .you .enduringStory), false, ctx)
  if low == "shuffle" || low == "shuffle your library" then
    return some (.player (.shuffle .you), false, ctx)
  if low == "choose a creature type" then
    return some (.player (.choose .you .creatureType), true, ctx)
  if low == "choose odd or even" then
    return some (.player (.choose .you .oddOrEven), true, ctx)
  if low == "choose a player with the most life or tied for most life" then
    return some (.player (.choose .you .playerWithMostLife), true, ctx)
  if low == "you may play an additional land this turn" then
    return some (.installEffect (.applyRule .untilEndOfTurn (.player (.additionalLands .you 1))), false, ctx)
  if low == "the \"legend rule\" doesn't apply to permanents you control this turn" ||
      low == "the legend rule doesn't apply to permanents you control this turn" ||
      low == "the legend rule doesn't apply to permanents you control until end of turn" ||
      low == "the legend rule doesn't apply to permanents you control" then
    return some (.installEffect (.applyRule .untilEndOfTurn (.game (.legendRuleDisabled .you))), false, ctx)
  if low == "after this phase, there is an additional combat phase" ||
      low == "after this main phase, there is an additional combat phase" ||
      low == "there is an additional combat phase after this phase" then
    return some (.turn (.extraPhase .combat true), false, ctx)
  if low == "there is an additional combat phase" then
    return some (.turn (.extraPhase .combat false), false, ctx)
  if low == "take an extra turn after this one" then
    return some (.turn (.extraTurn .you none), false, ctx)
  if let some prepObjStr := (pDropSuffixCI? norm " becomes prepared").orElse (fun _ => pDropSuffixCI? norm " become prepared") then
    if let some (obj, ctx1) := parseObjWithCtx ctx prepObjStr then
      return some (.permanent (.setDesignation obj .prepared true), false, ctx1)
  if let some incRest := pDropPrefixCI? norm "incubate " then
    if let some v := parseValueWithCtx ctx incRest then
      return some (.create (.tokens .you (.const 1) (.predefined .incubator) { counters := #[(.plusOnePlusOne, v)] }), true, ctx)
  if let some dblRest := pDropPrefixCI? norm "double " then
    let (dblCore, dur?) := peelTrailingDuration dblRest (some ctx)
    if let some objStr0 := (pDropSuffixCI? dblCore "'s power and toughness").orElse
        (fun _ => pDropSuffixCI? dblCore " power and toughness") then
      let objStr := if pLower objStr0 == "its" then "it" else objStr0
      if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
        return some (.installEffect (.applyContinuous (dur?.getD .untilEndOfTurn) obj (.modifyPT (.objectStat .power obj) (.objectStat .toughness obj))), false, ctx1)

  -- One-shot spell cost/cant-be-countered rules (`The next ... spell(s) you cast ...`, `<pred> spells you cast this turn cost {N} less to cast`)
  let stripSpellKind (p : ObjectPred) : ObjectPred :=
    match p with
    | .isKind .spell => .anyObject
    | .all ps => ObjectPred.andAll (ps.filter (· != .isKind .spell))
    | other => other
  if let some nextRest := pDropPrefixCI? norm "the next " then
    let (nextCore, dur?) := peelTrailingDuration nextRest (some ctx)
    if let some spellPart := (pDropSuffixCI? nextCore " you cast this turn can't be countered").orElse
        (fun _ => pDropSuffixCI? nextCore " you cast can't be countered") then
      let pStr := ((pDropSuffixCI? spellPart " spells").orElse fun _ => pDropSuffixCI? spellPart " spell") |>.getD spellPart
      let pred := stripSpellKind ((parseNounPhrase pStr).orElse (fun _ => parseNounPhrase (pStr ++ " spell")) |>.map (·.filter.pred) |>.getD .anyObject)
      return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.play (.nextSpellCantBeCountered .you pred))), false, ctx)
    if let some spellPart := (pDropSuffixCI? nextCore " you cast this turn can be cast without paying its mana cost").orElse
        (fun _ => pDropSuffixCI? nextCore " you cast can be cast without paying its mana cost") then
      let pStr := ((pDropSuffixCI? spellPart " spells").orElse fun _ => pDropSuffixCI? spellPart " spell") |>.getD spellPart
      let pred := stripSpellKind ((parseNounPhrase pStr).orElse (fun _ => parseNounPhrase (pStr ++ " spell")) |>.map (·.filter.pred) |>.getD .anyObject)
      return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.costMod (.spells .you pred none none #[.battlefield]) .alternativeFree true)), false, ctx)
  if let some (spellPart, costPart) := pSplitFirstCI? norm " spells you cast this turn cost " then
    if let some amtStr := pDropSuffixCI? costPart " less to cast" then
      let pStr := ((pDropSuffixCI? spellPart " spells").orElse fun _ => pDropSuffixCI? spellPart " spell") |>.getD spellPart
      let pred := stripSpellKind ((parseNounPhrase pStr).orElse (fun _ => parseNounPhrase (pStr ++ " spell")) |>.map (·.filter.pred) |>.getD .anyObject)
      let amt := match parseManaCost? amtStr with
        | some mc => ValueExpr.const (Int.ofNat mc.genericCount)
        | none => (parseValueWithCtx ctx amtStr).getD (.const 1)
      return some (.installEffect (.applyRule .untilEndOfTurn (.costMod (.spells .you pred none none #[.battlefield]) (.reduceGeneric amt) false)), false, ctx)

  -- First word dispatch
  let ws := pWords norm
  if ws.isEmpty then return none
  let lead := pLower ws[0]!

  -- 1. `"Add [an additional] <mana>"`
  if lead == "add" then
    let addNorm :=
      match pDropPrefixCI? norm "add an additional " with
      | some r => "Add " ++ r
      | none => norm
    if let some mp := parseManaProductionSpec #[addNorm] ctx.cardName then
      return some (.player (.addMana .you mp), false, ctx)

  -- 2. `"Draw ..."`
  if lead == "draw" then
    if let some rest := pDropPrefixCI? norm "draw " then
      -- `"draw cards equal to <V>"` (`Last March of the Ents`, `Tom, Bert, and William`, `Rise of the Deathbringer`, `The Ten Rings`)
      if let some eqStr := pDropPrefixCI? rest "cards equal to " then
        if pLower eqStr == "the difference" then
          return some (.player (.drawCards .you (.binary .max (.const 0) (.binary .sub (.const 10) (.playerMetric .handSize .you)))), true, ctx)
        if let some v := parseValueWithCtx ctx eqStr then
          return some (.player (.drawCards .you v), true, ctx)
      -- `"draw a card for each <X>"` (including `"for each color among ..."`, `"for each card you've discarded this turn"`, `"for each Human tapped this way"`)
      if let some eachStr := pDropPrefixCI? rest "a card for each " then
        let eLow := pLower eachStr
        if eLow == "card you've discarded this turn" || eLow == "card you discarded this turn" then
          return some (.player (.drawCards .you (.playerMetric .cardsDiscardedThisTurn .you)), true, ctx)
        if let some amongStr := pDropPrefixCI? eachStr "color among " then
          if let some (obj, ctx1) := parseObjWithCtx ctx amongStr then
            return some (.player (.drawCards .you (.colorCountAmong obj)), true, ctx1)
        if eLow == "graveyard with seven or more cards in it" then
          let amt := ValueExpr.playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7)))
          return some (.player (.drawCards .you amt), false, ctx)
        if eLow.endsWith " tapped this way" || eLow.endsWith " destroyed this way" ||
            eLow.endsWith " exiled this way" || eLow.endsWith " sacrificed this way" then
          let amt := match ctx.lastActionVar? with | some v => ValueExpr.stepMetric .movedCount v | none => .eventAmount
          return some (.player (.drawCards .you amt), false, ctx)
        if let some (kPart, srcPart) := pSplitFirstCI? eachStr " counter on " then
          match CounterKind.ofPrefix ((pWords kPart).toList.map pLower), parseObjWithCtx ctx srcPart with
          | some (ek, _), some (srcObj, ctx1) =>
            return some (.player (.drawCards .you (.counterCount (some ek) srcObj)), true, ctx1)
          | _, _ => pure ()
        if let some np := parseNounPhrase eachStr then
          let amt := ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
          return some (.player (.drawCards .you amt), false, ctx)
      if let some nStr0 := (pDropSuffixCI? rest " cards").orElse (fun _ => pDropSuffixCI? rest " card") then
        let (nStr, ctxD) : String × DiscourseCtx :=
          if (pLower nStr0).contains "target player's" then
            let (idx, c1) := ctx.pushTargetSlot { domain := .player .any }
            (nStr0.replace "target player's" "that player's", { c1 with lastPlayer? := some (.target idx) })
          else if (pLower nStr0).contains "target opponent's" then
            let (idx, c1) := ctx.pushTargetSlot { domain := .player .opponent }
            (nStr0.replace "target opponent's" "that player's", { c1 with lastPlayer? := some (.target idx) })
          else (nStr0, ctx)
        if let some v := parseValueWithCtx ctxD nStr then
          let isBindable := match v with | .const 1 | .stepMetric _ _ => false | _ => true
          return some (.player (.drawCards .you v), isBindable, ctxD)

  -- 3. `"Scry N"` / `"Surveil N"` / `"Proliferate ..."` / `"Amass ..."` / `"Empower ..."`
  if lead == "scry" then
    if let some nStr := pDropPrefixCI? norm "scry " then
      if let some v := parseValueWithCtx ctx nStr then
        return some (.player (.scry .you v), false, ctx)
  if lead == "surveil" then
    if let some nStr := pDropPrefixCI? norm "surveil " then
      if let some v := parseValueWithCtx ctx nStr then
        return some (.player (.surveil .you v), true, ctx)
  if lead == "proliferate" then
    if let some rest := pDropPrefixCI? norm "proliferate " then
      if let some (cntStr, tgtStr?) :=
          match pSplitFirstCI? rest " times on " with
          | some (a, b) => some (a, some b)
          | none => (pDropSuffixCI? rest " times").map (·, none) then
        if let some v := parseValueWithCtx ctx cntStr then
          match tgtStr? with
          | none => return some (.player (.proliferate .you v none), false, ctx)
          | some ts =>
            if let some (obj, ctx1) := parseObjWithCtx ctx ts then
              return some (.player (.proliferate .you v (some obj)), false, ctx1)
  if lead == "amass" then
    if let some rest := pDropPrefixCI? norm "amass " then
      let aws := pWords rest
      if aws.size >= 2 then
        let subW := (pDropSuffixCI? aws[0]! "s").getD aws[0]!
        let amtStr := String.intercalate " " (aws.extract 1 aws.size).toList
        match CardSubtype.ofOracle? subW, parseValueWithCtx ctx amtStr with
        | some sub, some amt => return some (.player (.amass .you sub amt), true, ctx)
        | _, _ => pure ()
  if lead == "empower" then
    if let some rest := pDropPrefixCI? norm "empower " then
      let ews := pWords rest
      if ews.size >= 2 then
        let amtStr := String.intercalate " " (ews.extract 1 ews.size).toList
        match CardSubtype.ofOracle? ews[0]!, parseValueWithCtx ctx amtStr with
        | some sub, some amt => return some (.player (.empowerPlaneswalker sub amt), true, ctx)
        | _, _ => pure ()

  -- 4. `"Create <count> <TokenDesc> [for each <X>]"` (and `"create <A> or [create] <B>"`)
  if lead == "create" then
    if let some (lhsC, rhsC) := pSplitFirstCI? norm " or create " then
      match parseAtomicInstr qp ctx lhsC, parseAtomicInstr qp ctx ("create " ++ rhsC) with
      | some (i1, _, c1), some (i2, _, _) =>
        return some (.chooseModes {
          minModes := .const 1
          maxModes := .const 1
          modes := #[{ targets := c1.toTargetSpec, body := i1 }, { targets := .none, body := i2 }]
        }, true, ctx)
      | _, _ => pure ()
    if let some (lhsC, rhsC) := (pSplitFirstCI? norm " token or a ").orElse (fun _ => pSplitFirstCI? norm " token or an ") then
      let rhsTok := (if norm.contains " token or an " then "create an " else "create a ") ++ rhsC
      match parseAtomicInstr qp ctx (lhsC ++ " token"), parseAtomicInstr qp ctx rhsTok with
      | some (i1, _, c1), some (i2, _, _) =>
        return some (.chooseModes {
          minModes := .const 1
          maxModes := .const 1
          modes := #[{ targets := c1.toTargetSpec, body := i1 }, { targets := .none, body := i2 }]
        }, true, ctx)
      | _, _ => pure ()
    if let some rest0 := pDropPrefixCI? norm "create " then
      let (rest, eachMult?) :=
        match pSplitLastCI? rest0 " for each " with
        | some (a, b) => (a, some b)
        | none => (rest0, none)
      let applyMult (baseCnt : ValueExpr) (c : DiscourseCtx) : ValueExpr :=
        match eachMult? with
        | none => baseCnt
        | some eachStr =>
          let mult :=
            if (pLower eachStr).contains "of that type" then
              let v := c.lastActionVar?.getD ⟨0⟩
              ValueExpr.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you, .hasSubtype (.fromStep v)]))
            else if (pLower eachStr).endsWith " this way" then
              match c.lastActionVar? with | some v => .stepMetric .movedCount v | none => .eventAmount
            else if let some np := parseNounPhrase eachStr then
              ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
            else (parseValueWithCtx c eachStr).getD (.const 1)
          if baseCnt == .const 1 then mult else .binary .mul baseCnt mult
      if let some (spec, mods, ctx1) := parseTokenDesc? qp ctx rest parseObjWithCtx then
        return some (.create (.tokens .you (applyMult (.const 1) ctx1) spec mods), true, ctx1)
      let rws := pWords rest
      if rws.size >= 2 then
        if let some cnt := parseCountVal? rws[0]! then
          let descStr := String.intercalate " " (rws.extract 1 rws.size).toList
          if let some (spec, mods, ctx1) := parseTokenDesc? qp ctx descStr parseObjWithCtx then
            return some (.create (.tokens .you (applyMult cnt ctx1) spec mods), true, ctx1)
        for splitIdx in [2 : rws.size] do
          let cntStr := String.intercalate " " (rws.extract 0 splitIdx).toList
          let descStr := String.intercalate " " (rws.extract splitIdx rws.size).toList
          if let some cnt := parseValueWithCtx ctx cntStr then
            if let some (spec, mods, ctx1) := parseTokenDesc? qp ctx descStr parseObjWithCtx then
              return some (.create (.tokens .you (applyMult cnt ctx1) spec mods), true, ctx1)

  -- 5. `"Destroy ..."` (including `"destroy <choice> [(move the rest)] among <pool>"`)
  if lead == "destroy" then
    if let some rest := pDropPrefixCI? norm "destroy " then
      if let some (chPart0, poolPart) := pSplitFirstCI? rest " among " then
        let (inv, chPart) :=
          match pDropSuffixCI? chPart0 " (move the rest)" with
          | some x => (true, x)
          | none => (false, chPart0)
        if let some (poolObj, ctx1) := parseObjWithCtx ctx poolPart then
          let cntR := (parseExprCountRange? (chPart ++ " card")).map Prod.fst |>.getD (.upTo (.const 2))
          let ch : MoveChoiceSpec := { chooser := .controller, count := cntR, invertSelection := inv }
          return some (.moveZone poolObj .graveyard .destroy { choice? := some ch }, true, ctx1)
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (Instruction.destroy obj, true, ctx1)

  -- 6. `"Exile ..."` (including `"exile the top [N] card(s) of <player>'s library"`, `"exile <choice> from <pool>"`, `"exile <A> or <B> until ..."`)
  if lead == "exile" then
    if let some rest := pDropPrefixCI? norm "exile " then
      let (objRaw0, untilLeaves) :=
        match (pDropSuffixCI? rest " until this permanent leaves the battlefield").orElse
            (fun _ => (pDropSuffixCI? rest " until this creature leaves the battlefield").orElse
              (fun _ => (pDropSuffixCI? rest " until this aura leaves the battlefield").orElse
                (fun _ => (pDropSuffixCI? rest " until this artifact leaves the battlefield").orElse
                  (fun _ => (pDropSuffixCI? rest " until this enchantment leaves the battlefield").orElse
                    (fun _ => pDropSuffixCI? rest " until this leaves the battlefield"))))) with
        | some b => (b, true)
        | none => (rest, false)
      let (objRaw1, linkedSrc) :=
        match pDropSuffixCI? objRaw0 " linked to this permanent" with
        | some b => (b, true)
        | none => (objRaw0, false)
      let (objRaw, faceDown) :=
        match pDropSuffixCI? objRaw1 " face down" with
        | some b => (b, true)
        | none => (objRaw1, false)
      -- `"exile the top card of <player>'s library"` / `"exile the top N cards of <player>'s library [face down]"`
      if let some topRest := pDropPrefixCI? objRaw "the top " then
        if let some libStr := pDropPrefixCI? topRest "card of " then
          let whoRaw := (pDropSuffixCI? libStr " library").getD libStr
          if let some (who, ctx1) := parsePossessivePlayerWithCtx ctx whoRaw then
            return some (.moveZone (.topOfLibrary who (.const 1)) .exile .exile { enterFaceDown := faceDown, linkToSource := linkedSrc }, true, ctx1)
        if let some (cntStr, libStr) := (pSplitFirstCI? topRest " cards of ").orElse
            (fun _ => pSplitFirstCI? topRest " card of ") then
          let cnt := if cntStr.isEmpty then .const 1 else (parseValueWithCtx ctx cntStr).getD (.const 1)
          let whoRaw := (pDropSuffixCI? libStr " library").getD libStr
          if let some (who, ctx1) := parsePossessivePlayerWithCtx ctx whoRaw then
            return some (.moveZone (.topOfLibrary who cnt) .exile .exile { enterFaceDown := faceDown, linkToSource := linkedSrc }, true, ctx1)
      -- `"exile all the cards from your hand"` / `"exile card in your hand"` (`Hex Magic`)
      if pLower objRaw == "all the cards from your hand" || pLower objRaw == "all cards from your hand" ||
          pLower objRaw == "card in your hand" then
        return some (.moveZone (.inZones .yourHand .anyObject) .exile .exile { exileUntilSourceLeaves := untilLeaves, enterFaceDown := faceDown, linkToSource := linkedSrc }, true, ctx)
      -- `"exile this spell and four cards named <Name> from your graveyard"` (`Sphinx's Approach`)
      if let some (selfPart, restEx) := pSplitFirstCI? objRaw " and " then
        if DiscourseCtx.isSelfPhrase selfPart && (pLower restEx).contains " named " then
          let rNoGy := (pDropSuffixCI? restEx " from your graveyard").getD restEx
          if let some (cntPredStr, nameStr) := pSplitFirstCI? rNoGy " named " then
            let ws := pWords cntPredStr
            let cnt := (ws[0]?.bind parseNatWord?).getD 1
            let pool := ObjectExpr.inZones .yourGraveyard (.all #[.isKind .card, .named (.literal nameStr)])
            let ch : MoveChoiceSpec := { chooser := .controller, count := .exact (.const (Int.ofNat cnt)) }
            return some (.seq #[
              .moveZone .this .exile .exile {},
              .moveZone pool .exile .exile { choice? := some ch }
            ], true, ctx)
      -- `"exile a nonland card from their hand or the chosen creature"` (`Cloak and Dagger`)
      if let some (lhsEx, rhsEx) := pSplitFirstCI? objRaw " or the chosen " then
        let _ := rhsEx
        let lhsNorm := lhsEx.replace " from " " in "
        if let some (objA, ctx1) := parseObjWithCtx ctx lhsNorm then
          let _ := objA
          let chosenSlot := if ctx.slots.size >= 2 then ObjectExpr.target 1 else .target 0
          return some (.ifCond (.exists .this)
            (.moveZone chosenSlot .exile .exile { exileUntilSourceLeaves := untilLeaves }) .noop, true, ctx1)
      -- `"exile that card / it from your/a graveyard"` (`Currency Converter`, `Moonstone`)
      let objRawClean :=
        if (pLower objRaw).startsWith "that card from " || (pLower objRaw).startsWith "it from " then
          ((pDropSuffixCI? objRaw " from your graveyard").orElse fun _ =>
           (pDropSuffixCI? objRaw " from a graveyard").orElse fun _ =>
           pDropSuffixCI? objRaw " from its owner's graveyard") |>.getD objRaw
        else objRaw
      -- `"exile <choice> [(reveal first)] from <pool>"` (`Null Summoner`, `Sphinx's Approach`)
      if let some (chPart0, poolPart) := pSplitFirstCI? objRawClean " from " then
        let (rev, chPart) :=
          match pDropSuffixCI? chPart0 " (reveal first)" with
          | some x => (true, x)
          | none => (false, chPart0)
        if rev || pLower chPart == "a" || pLower chPart == "an" || (parseCountVal? chPart).isSome then
          if let some (poolObj, ctx1) := parseObjWithCtx ctx poolPart then
            let cntR := (parseExprCountRange? (chPart ++ " card")).map Prod.fst |>.getD (.exact (.const 1))
            let ch : MoveChoiceSpec := { chooser := .controller, count := cntR, revealFirst := rev }
            return some (.moveZone poolObj .exile .exile { choice? := some ch, exileUntilSourceLeaves := untilLeaves, enterFaceDown := faceDown, linkToSource := linkedSrc }, true, ctx1)
      if let some (obj, ctx1) := parseObjWithCtx ctx objRawClean then
        return some (.moveZone obj .exile .exile { exileUntilSourceLeaves := untilLeaves, enterFaceDown := faceDown, linkToSource := linkedSrc }, true, ctx1)

  -- 7. `"Return ..."`
  if lead == "return" then
    if let some rest := pDropPrefixCI? norm "return " then
      for sep in #[
        " to its owner's hand", " to their owners' hands", " to your hand", " into your hand",
        " to the battlefield", " onto the battlefield"
      ] do
        if let some (objPart0, tailPart0) := pSplitFirstCI? rest sep then
          let (tailPart, delayedEndStep) :=
            match pDropSuffixCI? tailPart0 " at the beginning of the next end step" with
            | some a => (a, true)
            | none => (tailPart0, false)
          let objPart :=
            if (pLower objPart0).startsWith "that card from " || (pLower objPart0).startsWith "it from " ||
                (pLower objPart0).startsWith "this card from " || (pLower objPart0).startsWith "this permanent from " then
              ((pDropSuffixCI? objPart0 " from your graveyard").orElse fun _ =>
               pDropSuffixCI? objPart0 " from a graveyard") |>.getD objPart0
            else objPart0
          let destFull := (sep.trimAscii.copy ++ " " ++ tailPart).trimAscii.copy
          if let some (obj, ctx1) := parseObjWithCtx ctx objPart then
            if let some (dest0, mods, ctx2) := parseDestZoneWithMods? ctx1 destFull then
              let (dest, verb) : DestZoneSpec × ZoneVerb :=
                match dest0 with
                | .hand .controller =>
                  if obj == .this then (.hand .owner, .returnToHand)
                  else (.hand .controller, .returnToHand)
                | .hand _ => (dest0, .returnToHand)
                | _ => (dest0, .put)
              let moveI := Instruction.moveZone obj dest verb mods
              if delayedEndStep then
                let dt : DelayedTriggerSpec := {
                  pattern := .stepBegins .end (.player .any)
                  duration := .untilEndOfTurn
                  oneShot := true
                  effect := { targets := .none, body := moveI }
                }
                return some (.installEffect (.createDelayedTrigger dt), false, ctx2)
              return some (moveI, true, ctx2)

  -- 8. `"Put ..."` (counters OR zone movement OR `"put <choice> from <pool> <dest>"`)
  if lead == "put" then
    if let some rest := pDropPrefixCI? norm "put " then
      -- 8a. Counter placement: `"put <counters> on <obj> [for each <X> / for every <N> ...]"`
      let counterOnSplit? : Option (String × String) :=
        if (pLower rest).startsWith "the number of " then
          pSplitLastCI? rest " on "
        else
          pSplitFirstCI? rest " on "
      if let some (ctrPart0, onRest0) := counterOnSplit? then
        if pLower ctrPart0 == "each keyword counter" then
          if let some (dstStr, kwSrcTail) := pSplitFirstCI? onRest0 " for each keyword " then
            let srcStr := (pDropSuffixCI? kwSrcTail " has").getD kwSrcTail
            match parseObjWithCtx ctx dstStr, parseObjWithCtx ctx srcStr with
            | some (dstObj, c1), some (srcObj, c2) =>
              let _ := c1
              return some (.permanent (.modifyCounters (.copyMissingKeywords srcObj) dstObj), false, c2)
            | _, _ => pure ()
        if pLower ctrPart0 == "its counters" || pLower ctrPart0 == "those counters" then
          if let some (dstObj, ctx1) := parseObjWithCtx ctx onRest0 then
            let srcObj :=
              if pLower ctrPart0 == "those counters" && ctx.isTrigger && !ctx.isSelfTrigger then ObjectExpr.triggerSubject
              else if ctx.isTrigger then ObjectExpr.this
              else ctx.lastSubject?.getD .this
            return some (.permanent (.modifyCounters (.copyFromLki srcObj) dstObj), false, ctx1)
        -- `"for every <N> cards in your graveyard"` (`Recursive Recruitment`)
        let (onRest1, divEvery?) : String × Option (Nat × ValueExpr) :=
          match pSplitFirstCI? onRest0 " for every " with
          | some (a, b) =>
            let bws := pWords b
            if bws.size >= 2 then
              match parseNatWord? bws[0]! with
              | some d =>
                let rem := String.intercalate " " (bws.extract 1 bws.size).toList
                let numV :=
                  if pLower rem == "cards in your graveyard" then .playerMetric .graveyardSize .you
                  else (parseNounPhrase rem).map (fun np => .aggregate .count .one (.inZones np.filter.zones np.filter.pred)) |>.getD (.const 0)
                (a, some (d, numV))
              | none => (onRest0, none)
            else (onRest0, none)
          | none => (onRest0, none)
        let (onRest, eachMult?) :=
          match pSplitFirstCI? onRest1 " for each " with
          | some (a, b) =>
            if (pLower a).endsWith "each of" || (pLower a).isEmpty then (onRest1, none)
            else (a, some b)
          | none => (onRest1, none)
        let (ctrPart, eqVal?) :=
          match pSplitFirstCI? onRest " equal to " with
          | some (o1, vStr) => (ctrPart0, some (o1, vStr))
          | none => (ctrPart0, none)
        if let some (o1, vStr) := eqVal? then
          if let some kindPart := pDropPrefixCI? ctrPart "a number of " then
            let kCore := ((pDropSuffixCI? kindPart " counters").orElse fun _ => pDropSuffixCI? kindPart " counter") |>.getD kindPart
            if let some (kind, _) := CounterKind.ofPrefix ((pWords kCore).toList.map pLower) then
              if let some (obj, ctx1) := parseObjWithCtx ctx o1 then
                if let some amt := parseValueWithCtx ctx1 vStr then
                  return some (.permanent (.modifyCounters (.put kind amt) obj), true, ctx1)
        if let some (o1Part, secondPart) := pSplitFirstCI? onRest0 " and " then
          if (pLower secondPart).contains " counter on " || (pLower secondPart).contains " counters on " then
            match parseAtomicInstr qp ctx ("put " ++ ctrPart0 ++ " on " ++ o1Part) with
            | some (i1, _, c1) =>
              match parseAtomicInstr qp c1 ("put " ++ secondPart) with
              | some (i2, _, c2) => return some (flattenInstrSeq #[i1, i2], true, c2)
              | none => pure ()
            | none => pure ()
        -- Multiple counters on the same target (`"put a +1/+1 counter and an indestructible counter on ..."`)
        if let some (c1Str, c2Str) := pSplitFirstCI? ctrPart " and " then
          match parseCounterSpec? c1Str, parseCounterSpec? c2Str with
          | some (k1, v1), some (k2, v2) =>
            let onTarget := (pDropPrefixCI? onRest "each of ").getD onRest
            if let some (obj, ctx1) := parseObjWithCtx ctx onTarget then
              return some (.seq #[
                .permanent (.modifyCounters (.put k1 v1) obj),
                .permanent (.modifyCounters (.put k2 v2) obj)
              ], true, ctx1)
          | _, _ => pure ()
        let parsedCtr? : Option (CounterKind × ValueExpr) :=
          (parseCounterSpec? ctrPart).orElse fun _ => Id.run do
            let cNoWord := ((pDropSuffixCI? ctrPart " counters").orElse fun _ => pDropSuffixCI? ctrPart " counter") |>.getD ""
            if cNoWord.isEmpty then return none
            let cws := pWords cNoWord
            if cws.size < 2 then return none
            for kLen in #[1, 2] do
              if cws.size > kLen then
                let kWords := (cws.extract (cws.size - kLen) cws.size).toList.map pLower
                if let some (k, consumed) := CounterKind.ofPrefix kWords then
                  if consumed == kLen then
                    let cntStr := String.intercalate " " (cws.extract 0 (cws.size - kLen)).toList
                    if let some v := parseValueWithCtx ctx cntStr then
                      return some (k, v)
            return none
        if let some (kind, baseCnt) := parsedCtr? then
          let onTarget := (pDropPrefixCI? onRest "each of ").getD onRest
          if let some (obj, ctx1) := parseObjWithCtx ctx onTarget then
            let (finalCnt, ctxOut) : ValueExpr × DiscourseCtx :=
              match divEvery?, eachMult? with
              | some (d, numV), _ =>
                let q := ValueExpr.binary .divFloor numV (.const (Int.ofNat d))
                (if baseCnt == .const 1 then q else .binary .mul baseCnt q, ctx1)
              | none, none => (baseCnt, ctx1)
              | none, some eachStr =>
                let (mult, cMult) : ValueExpr × DiscourseCtx :=
                  if pLower eachStr == "card you've discarded this turn" || pLower eachStr == "card you discarded this turn" then
                    (ValueExpr.playerMetric .cardsDiscardedThisTurn .you, ctx1)
                  else
                  -- `"for each <kind> counter on <obj>"` (`Alien Invasion`)
                  match pSplitFirstCI? eachStr " counter on " with
                  | some (kPart, srcPart) =>
                    match CounterKind.ofPrefix ((pWords kPart).toList.map pLower), parseObjWithCtx ctx1 srcPart with
                    | some (ek, _), some (srcObj, cS) => (ValueExpr.counterCount (some ek) srcObj, cS)
                    | _, _ => (.const 1, ctx1)
                  | none =>
                    match parseObjWithCtx ctx1 eachStr with
                    | some (eachObj, cE) => (ValueExpr.aggregate .count .one eachObj, cE)
                    | none =>
                      if let some np := parseNounPhrase eachStr then
                        (ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred), ctx1)
                      else ((parseValueWithCtx ctx1 eachStr).getD (.const 1), ctx1)
                (if baseCnt == .const 1 then mult else .binary .mul baseCnt mult, cMult)
            return some (.permanent (.modifyCounters (.put kind finalCnt) obj), true, ctxOut)
        if let some srcRaw := pDropPrefixCI? ctrPart0 "counters matching " then
          let srcStr := (pDropSuffixCI? srcRaw "'s counters").getD srcRaw
          match parseObjWithCtx ctx srcStr, parseObjWithCtx ctx onRest with
          | some (srcObj, c1), some (dstObj, c2) =>
            let _ := c1
            return some (.permanent (.modifyCounters (.copyFromLki srcObj) dstObj), false, c2)
          | _, _ => pure ()
      -- 8a2. Leading destination (`"put onto the battlefield under your control <objs>"`, `Supper for Spiders`)
      if let some objsRest := pDropPrefixCI? rest "onto the battlefield under your control " then
        if let some (obj, ctx1) := parseObjWithCtx ctx objsRest then
          return some (.moveZone obj (.battlefield .controller) .put {}, true, ctx1)
      -- 8b. Choice zone placement: `"put <who> chooses <choice> from <pool> <dest>"` OR `"put <choice> [<pred>] from <pool/zone> <dest>"`
      let choiceFromPair? : Option (MoveChooser × String × String × DiscourseCtx) :=
        match pSplitFirstCI? rest " chooses " with
        | some (wStr, afterCh) =>
          match parsePlayerWithCtx ctx wStr, pSplitFirstCI? afterCh " from " with
          | some (p, c1), some (chS, afterF) => some (.player p, chS, afterF, c1)
          | _, _ => none
        | none =>
          match pSplitFirstCI? rest " from " with
          | some (chS, afterF) =>
            -- Ensure `chS` is a non-targeted count/choice phrase (not `"it"` or `"up to one target ..."`)
            if DiscourseCtx.isSelfPhrase chS || pLower chS == "it" || pLower chS == "them" ||
                (pLower chS).startsWith "that " || (pLower chS).contains "target " then none
            else some (.controller, chS, afterF, ctx)
          | none => none
      if let some (chooser, choicePart, afterFrom, ctx0) := choiceFromPair? then
        for sep in #[
          " onto the battlefield", " into your hand", " into its owner's hand", " to its owner's hand",
          " into your graveyard", " into exile", " on top of ", " on the bottom of "
        ] do
          if let some (poolPart, tailPart) := pSplitFirstCI? afterFrom sep then
            let destFull := (sep.trimAscii.copy ++ " " ++ tailPart).trimAscii.copy
            -- Pool may be an object expression OR a zone combined with the filter in `choicePart`
            -- (e.g. `"put any number of creature cards from your hand onto the battlefield"`).
            let poolAndCount? : Option (ObjectExpr × ExprCountRange × DiscourseCtx) :=
              match parseObjWithCtx ctx0 poolPart with
              | some (poolObj0, ctx1) =>
                let poolObj := match poolObj0 with
                  | .inZones zs (.isKind .card) => .inZones zs .anyObject
                  | other => other
                let cntR : ExprCountRange :=
                  if pLower choicePart == "any number of" then .anyNumber
                  else match parseCountVal? choicePart with
                  | some v => .exact v
                  | none => (parseExprCountRange? (choicePart ++ " card")).map Prod.fst |>.getD (.exact (.const 1))
                some (poolObj, cntR, ctx1)
              | none =>
                match parseZoneSetWithCtx ctx0 poolPart with
                | some (zs, ctx1) =>
                  let (cntR, fStr) : ExprCountRange × String :=
                    if let some r := pDropPrefixCI? choicePart "any number of " then (.anyNumber, r)
                    else (parseExprCountRange? choicePart).getD (.exact (.const 1), choicePart)
                  let rawPred : ObjectPred := (parseNounPhrase fStr).map (fun np => np.filter.pred) |>.getD .anyObject
                  let pred : ObjectPred := if rawPred == .isKind .card then .anyObject else rawPred
                  some (.inZones zs pred, cntR, ctx1)
                | none => none
            if let some (poolObj, cntR, ctx1) := poolAndCount? then
              if let some (dest, mods, ctx2) := parseDestZoneWithMods? ctx1 destFull then
                let ch : MoveChoiceSpec := { chooser, count := cntR }
                return some (.moveZone poolObj dest .put { mods with choice? := some ch }, true, ctx2)
      -- 8c. Zone placement: `"put <obj> [from your graveyard/hand] <dest>"` (`Silvan Reveler`, `Worlds Within Worlds`, etc.)
      for sep in #[
        " onto the battlefield", " into your hand", " into its owner's hand", " to its owner's hand",
        " into their owners' hands", " to their owners' hands", " into their owner's hand",
        " into your graveyard", " into its owner's graveyard", " into exile",
        " on top of ", " on the bottom of ", " on the bottom", " on their choice of ", " on its owner's choice of ",
        " into its owner's library", " into their library"
      ] do
        if let some (objPart0, tailPart) := pSplitFirstCI? rest sep then
          let objPart :=
            if (pLower objPart0).contains "target " then objPart0
            else
              ((pDropSuffixCI? objPart0 " from your graveyard").orElse fun _ =>
                (pDropSuffixCI? objPart0 " from a graveyard").orElse fun _ =>
                (pDropSuffixCI? objPart0 " from your hand").orElse fun _ =>
                some objPart0) |>.getD objPart0
          let destFull :=
            if sep == " on the bottom" && tailPart.isEmpty then "on the bottom of its owner's library"
            else (sep.trimAscii.copy ++ " " ++ tailPart).trimAscii.copy
          if let some (obj, ctx1) := parseObjWithCtx ctx objPart then
            if let some (dest, mods0, ctx2) := parseDestZoneWithMods? ctx1 destFull then
              let ol := pLower objPart
              let mods :=
                if obj == .linkedExile .this && mods0.choice?.isNone &&
                    (ol.startsWith "a " || ol.startsWith "an " || ol.startsWith "one ") then
                  { mods0 with choice? := some { chooser := .controller, count := .exact (.const 1) } }
                else mods0
              return some (.moveZone obj dest .put mods, true, ctx2)

  -- 9. `"Remove <count|all> [<kind>] counter(s) from [choice among] <obj>"` / `"Move ..."` / `"Double ... counters ..."`
  if lead == "remove" then
    if let some rest := pDropPrefixCI? norm "remove " then
      if let some (ctrPart, fromPart0) := pSplitFirstCI? rest " from " then
        let (ch?, fromPart) : Option MoveChoiceSpec × String :=
          match pSplitFirstCI? fromPart0 " among " with
          | some (chS, poolS) =>
            let cntR := (parseExprCountRange? (chS ++ " card")).map Prod.fst |>.getD (.exact (.const 1))
            (some { chooser := .controller, count := cntR }, poolS)
          | none => (none, fromPart0)
        if let some (obj0, ctx1) := parseObjWithCtx ctx fromPart then
          let ctx1 := { ctx1 with lastSubject? := some obj0 }
          let fl := pLower fromPart
          let isSingleIndefPool := ch?.isNone && (fl.startsWith "a " || fl.startsWith "an ") && !fl.contains "target "
          let refinePool (kind? : Option CounterKind) : ObjectExpr × Option MoveChoiceSpec :=
            if isSingleIndefPool then
              match obj0 with
              | .inZones zs pred =>
                let ctrPred := ObjectPred.counterCount kind? .ge (.const 1)
                let pred' :=
                  match pred with
                  | .all ps => if ps.contains ctrPred then pred else .all (ps.push ctrPred)
                  | p => if p == ctrPred then p else .all #[p, ctrPred]
                (.inZones zs pred', some { chooser := .controller, count := .exact (.const 1) })
              | _ => (obj0, ch?)
            else (obj0, ch?)
          if pLower ctrPart == "all counters" then
            let (obj, ch) := refinePool none
            return some (.permanent (.modifyCounters (.remove none .anyNumber) obj ch), true, ctx1)
          if let some allRest := pDropPrefixCI? ctrPart "all " then
            let kCore := ((pDropSuffixCI? allRest " counters").orElse fun _ => pDropSuffixCI? allRest " counter") |>.getD allRest
            if let some (k, _) := CounterKind.ofPrefix ((pWords kCore).toList.map pLower) then
              let (obj, ch) := refinePool (some k)
              return some (.permanent (.modifyCounters (.remove (some k) .anyNumber) obj ch), true, ctx1)
          if let some (k, v) := parseCounterSpec? ctrPart then
            let (obj, ch) := refinePool (some k)
            return some (.permanent (.modifyCounters (.remove (some k) (.exact v)) obj ch), true, ctx1)
          if let some (cntR, kindRest) := parseExprCountRange? ctrPart then
            let kCore := ((pDropSuffixCI? kindRest " counter(s)").orElse fun _ =>
              (pDropSuffixCI? kindRest " counters").orElse fun _ => pDropSuffixCI? kindRest " counter") |>.getD kindRest
            let kind? :=
              if kCore.isEmpty then none
              else (CounterKind.ofPrefix ((pWords kCore).toList.map pLower)).map Prod.fst
            let (obj, ch) := refinePool kind?
            return some (.permanent (.modifyCounters (.remove kind? cntR) obj ch), true, ctx1)
  if lead == "move" then
    if let some rest := pDropPrefixCI? norm "move " then
      if let some (whatPart, ontoPart) := pSplitFirstCI? rest " onto " then
        if let some (ctrPart, fromPart) := pSplitFirstCI? whatPart " from " then
          match parseObjWithCtx ctx fromPart, parseObjWithCtx ctx ontoPart with
          | some (srcObj, c1), some (dstObj, c2) =>
            let _ := c1
            let cl := pLower ctrPart
            if cl.startsWith "all " then
              let rem := (pDropPrefixCI? ctrPart "all ").getD ""
              let kCore := ((pDropSuffixCI? rem " counters").orElse fun _ => pDropSuffixCI? rem " counter") |>.getD rem
              let kind? := if kCore.isEmpty then none else (CounterKind.ofPrefix ((pWords kCore).toList.map pLower)).map Prod.fst
              return some (.permanent (.modifyCounters (.moveAll srcObj kind?) dstObj), false, c2)
            else if let some (k, _) := parseCounterSpec? ctrPart then
              return some (.permanent (.modifyCounters (.moveOne srcObj k) dstObj), false, c2)
          | _, _ => pure ()
      for sep in #[
        " into its owner's hand", " into your hand", " into its owner's graveyard", " into your graveyard",
        " onto the battlefield", " into exile"
      ] do
        if let some (objPart, tailPart) := pSplitFirstCI? rest sep then
          let destFull := (sep.trimAscii.copy ++ " " ++ tailPart).trimAscii.copy
          if let some (obj, ctx1) := parseObjWithCtx ctx objPart then
            if let some (dest, mods, ctx2) := parseDestZoneWithMods? ctx1 destFull then
              return some (.moveZone obj dest .put mods, true, ctx2)
  if lead == "double" then
    if let some rest := pDropPrefixCI? norm "double the number of " then
      if let some (ctrPart, onPart) := pSplitFirstCI? rest " on " then
        if let some (obj, ctx1) := parseObjWithCtx ctx onPart then
          let kCore := ((pDropSuffixCI? ctrPart " counters").orElse fun _ => pDropSuffixCI? ctrPart " counter") |>.getD ctrPart
          let kind? := if kCore.isEmpty then none else (CounterKind.ofPrefix ((pWords kCore).toList.map pLower)).map Prod.fst
          return some (.permanent (.modifyCounters (.double kind?) obj), false, ctx1)

  -- 10. `"Tap ..."`, `"Untap ..."`, `"Attach ..."`, `"Transform ..."`, `"Turn ... face up"`, `"Goad ..."`, `"Harness ..."`
  if lead == "tap" then
    if let some rest := pDropPrefixCI? norm "tap " then
      if let some anyRest0 := pDropPrefixCI? rest "any number of " then
        let anyRest := (pDropPrefixCI? anyRest0 "among ").getD anyRest0
        if let some (obj, ctx1) := parseObjWithCtx ctx anyRest then
          let ch : MoveChoiceSpec := { chooser := .controller, count := .anyNumber }
          return some (.permanent (.setTapped obj true (some ch)), true, ctx1)
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        let ctx2 :=
          match obj with
          | .attachedHost | .target _ | .triggerSubject => { ctx1 with lastSubject? := some obj }
          | _ => ctx1
        return some (Instruction.tap obj, false, ctx2)
  if lead == "untap" then
    if let some rest := pDropPrefixCI? norm "untap " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (Instruction.untap obj, false, ctx1)
  if lead == "attach" then
    if let some rest := pDropPrefixCI? norm "attach " then
      let attachSplit? : Option (String × String) :=
        match pSplitFirstCI? rest " to up to " with
        | some (a, b) => some (a, "up to " ++ b)
        | none =>
          match pSplitLastCI? rest " to " with
          | some (a, b) =>
            if (pLower a).endsWith " up" || pLower a == "up" then pSplitFirstCI? rest " to "
            else some (a, b)
          | none => none
      if let some (aRaw0, bRaw) := attachSplit? then
        let (explicitPool, aRaw) :=
          match pDropSuffixCI? aRaw0 " (chosen)" with
          | some x => (true, x)
          | none => (false, aRaw0)
        let prevSlotCount := ctx.slots.size
        if let some (aObj0, ctx1) := parseObjWithCtx ctx aRaw then
          let bCtx := { ctx1 with lastSubject? := ctx.lastSubject?, attachedHostCtx := ctx.attachedHostCtx }
          if let some (bObj, ctx2) := parseObjWithCtx bCtx bRaw then
            let aObj :=
              if aObj0 == .allTargets && ctx2.slots.size > ctx1.slots.size then .target prevSlotCount
              else aObj0
            let choosePool := explicitPool || (match aObj with | .inZones _ _ => true | _ => false)
            return some (.permanent (.attach aObj bObj choosePool), true, ctx2)
  if lead == "transform" then
    if let some rest := pDropPrefixCI? norm "transform " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (.permanent (.transform obj), false, ctx1)
  if lead == "turn" then
    if let some rest := pDropPrefixCI? norm "turn " then
      if let some objStr := pDropSuffixCI? rest " face up" then
        if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
          return some (.permanent (.turnFaceUp obj), false, ctx1)
  if lead == "goad" then
    if let some rest := pDropPrefixCI? norm "goad " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (.permanent (.setDesignation obj .goaded true), false, ctx1)
  if lead == "harness" then
    if let some rest := pDropPrefixCI? norm "harness " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (.permanent (.setDesignation obj .harnessed true), false, ctx1)

  -- 11. `"Sacrifice ..."`, `"Discard ..."`, `"Mill ..."`, `"Shuffle ... into ..."`
  if lead == "sacrifice" then
    if let some rest := pDropPrefixCI? norm "sacrifice " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        let ctx2 := if obj == .this then { ctx1 with lastSubject? := some .this } else ctx1
        return some (.moveZone obj .graveyard .sacrifice {}, true, ctx2)
      let restClean := (pDropPrefixCI? rest "a ").orElse (fun _ => pDropPrefixCI? rest "an ") |>.getD rest
      if let some np := parseNounPhrase restClean then
        let pool := ObjectExpr.inZones .battlefield (.all #[np.filter.pred, .controlledBy .you])
        let ch : MoveChoiceSpec := { chooser := .player .you, count := .exact (.const 1), filter? := some np.filter.pred }
        return some (.moveZone pool .graveyard .sacrifice { choice? := some ch }, true, ctx)
  if lead == "discard" then
    if let some rest := pDropPrefixCI? norm "discard " then
      if pLower rest == "your hand" || pLower rest == "their hand" then
        let who := if pLower rest == "their hand" then ctx.lastPlayer?.getD .you else .you
        return some (.moveZone (.inZones (.handOf who) .anyObject) .graveyard .discard {}, true, ctx)
      let (rest1, unlessPred?) :=
        match pSplitFirstCI? rest " unless you discard " with
        | some (a, b) =>
          let bClean := ((pDropPrefixCI? b "a ").orElse fun _ => pDropPrefixCI? b "an ") |>.getD b
          let bClean := (pDropSuffixCI? bClean " card").getD bClean
          (a, (parseNounPhrase (bClean ++ " card")).map (·.filter.pred))
        | none => (rest, none)
      let (rest2, atRand) :=
        match pDropSuffixCI? rest1 " at random" with
        | some a => (a, true)
        | none => (rest1, false)
      if let some nStr := (pDropSuffixCI? rest2 " cards").orElse (fun _ => pDropSuffixCI? rest2 " card") then
        if let some v := parseValueWithCtx ctx nStr then
          let ch : MoveChoiceSpec := {
            chooser := .player .you
            count := .exact v
            atRandom := atRand
            unlessMatching? := unlessPred?
          }
          return some (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard { choice? := some ch }, true, ctx)
  if lead == "mill" then
    if let some rest := pDropPrefixCI? norm "mill " then
      if let some nStr := (pDropSuffixCI? rest " cards").orElse (fun _ => pDropSuffixCI? rest " card") then
        if let some v := parseValueWithCtx ctx nStr then
          return some (Instruction.mill v .you, true, ctx)
  if lead == "shuffle" then
    if let some rest := pDropPrefixCI? norm "shuffle " then
      if let some (objStr, _) := pSplitFirstCI? rest " into " then
        if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
          return some (.moveZone obj (.library .owner .shuffledIn false) .shuffleIntoLibrary {}, true, ctx1)

  -- 12. `"Counter ..."`, `"Copy ..."`, `"Choose ..."`, `"Gain ..."`, `"Exchange ..."`, `"Lose ..."`, `"Take an extra turn..."`, `"Prevent ..."`
  if lead == "counter" then
    if let some rest := pDropPrefixCI? norm "counter " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (.stack (.counterStack obj false false), false, ctx1)
  if lead == "copy" then
    if let some rest := pDropPrefixCI? norm "copy " then
      if pLower rest == "those cards" || pLower rest == "those exiled cards" then
        return some (.noop, false, ctx)
      let (objStr, copies) : String × ValueExpr :=
        match pDropSuffixCI? rest " twice" with
        | some b => (b, .const 2)
        | none =>
          match pDropSuffixCI? rest " times" with
          | some b =>
            let bws := pWords b
            if bws.size >= 2 then
              match parseCountVal? bws[bws.size - 1]! with
              | some v => (String.intercalate " " (bws.extract 0 (bws.size - 1)).toList, v)
              | none => (rest, .const 1)
            else (rest, .const 1)
          | none => (rest, .const 1)
      if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
        return some (.stack (.copyStackObject obj copies false), true, ctx1)
  if lead == "choose" then
    if let some rest := pDropPrefixCI? norm "choose " then
      -- `"choose up to N <NP>, then destroy the rest"` (`Mount Doom`)
      if let some (pickStr, _) := pSplitFirstCI? rest ", then destroy the rest" then
        if let some (cntR, predRaw) := parseExprCountRange? pickStr then
          if let some np := parseNounPhrase predRaw then
            let ch : MoveChoiceSpec := { chooser := .controller, count := cntR, invertSelection := true }
            return some (.moveZone (.inZones .battlefield np.filter.pred) .graveyard .destroy { choice? := some ch }, true, ctx)
      if let some (lhs, rhs) := pSplitFirstCI? rest " and " then
        if (pLower lhs).contains "target " && (pLower rhs).contains "target " then
          match parseTargetSlot lhs, parseTargetSlot rhs with
          | some s1, some s2 =>
            let (_, ctx1) := ctx.pushTargetSlot s1
            let (_, ctx2) := ctx1.pushTargetSlot s2
            return some (.noop, false, ctx2)
          | _, _ => pure ()
      if (pLower rest).contains "target " then
        if let some slot := parseTargetSlot rest then
          let (idx, ctx1) := ctx.pushTargetSlot slot
          let ctx2 :=
            match slot.domain with
            | .player _ => { ctx1 with lastPlayer? := some (.target idx) }
            | _ => { ctx1 with lastSubject? := some (if slot.count == .exact 1 || slot.count == .upTo 1 then .target idx else .allTargets) }
          return some (.noop, false, ctx2)
  if lead == "gain" then
    if let some ctrlRest := pDropPrefixCI? norm "gain control of " then
      let (objStr, dur?) := peelTrailingDuration ctrlRest (some ctx)
      if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
        return some (.installEffect (.applyContinuous (dur?.getD .indefinite) obj (.gainControl .you)), false, ctx1)
    if let some rest := pDropPrefixCI? norm "gain " then
      if let some nStr := pDropSuffixCI? rest " life" then
        if let some v := parseValueWithCtx ctx nStr then
          return some (.life (.gain .you v), true, ctx)
  if lead == "exchange" then
    if let some rest := pDropPrefixCI? norm "exchange control of " then
      let (exCore, dur?) := peelTrailingDuration rest (some ctx)
      -- Handle `"two target nonland permanents that share a card type and target 2"` (`Burglar's Plot`)
      if let some (aStr, bStr) := pSplitFirstCI? exCore " and " then
        if pLower bStr == "target 2" || pLower bStr == "target 1" then
          if let some slot := parseTargetSlot aStr then
            let (_, ctx1) := ctx.pushTargetSlot slot
            return some (.installEffect (.applyContinuous (dur?.getD .indefinite) (.target 0) (.exchangeControl (.target 1))), false, ctx1)
        if let some (aObj, ctx1) := parseObjWithCtx ctx aStr then
          if let some (bObj, ctx2) := parseObjWithCtx ctx1 bStr then
            return some (.installEffect (.applyContinuous (dur?.getD .indefinite) aObj (.exchangeControl bObj)), false, ctx2)
      if let some slot := parseTargetSlot exCore then
        let (_, ctx1) := ctx.pushTargetSlot slot
        return some (.installEffect (.applyContinuous (dur?.getD .indefinite) (.target 0) (.exchangeControl (.target 1))), false, ctx1)
  if lead == "lose" then
    if let some rest := pDropPrefixCI? norm "lose " then
      if let some nStr := pDropSuffixCI? rest " life" then
        if let some v := parseValueWithCtx ctx nStr then
          return some (.life (.lose .you v), true, ctx)
  if lead == "take" then
    if low.startsWith "take an extra turn" then
      let rule? : Option RuleModification :=
        if low.contains "can't activate power-up abilities" then
          some (.player (.forbidAbilityActivation .any .powerUp))
        else none
      return some (.turn (.extraTurn .you rule?), false, ctx)
  if lead == "prevent" then
    if let some rest := pDropPrefixCI? norm "prevent all combat damage that would be dealt this turn" then
      let _ := rest
      return some (.installEffect (.applyReplacement .untilEndOfTurn (.preventDamage (.matching { zones := .battlefield, pred := .hasType .creature }) none)), false, ctx)
    if let some rest := pDropPrefixCI? norm "prevent all damage that would be dealt by " then
      let (subjStr, dur?) := peelTrailingDuration rest (some ctx)
      let (subj, ctxOut) : StaticSubject × DiscourseCtx :=
        if DiscourseCtx.isSelfPhrase subjStr then (.self, ctx)
        else if (pLower subjStr).contains "target " then
          match parseObjWithCtx ctx subjStr with
          | some (.target idx, c1) => (.matching { zones := .battlefield, pred := .sameAs (.target idx) }, c1)
          | some (.allTargets, c1) => (.matching { zones := .battlefield, pred := .sameAs (.target (c1.lastTargetSlot?.getD 0)) }, c1)
          | _ => (.self, ctx)
        else match parseNounPhrase subjStr with
          | some np => (.matching np.filter, ctx)
          | none => (.self, ctx)
      return some (.installEffect (.applyReplacement (dur?.getD .untilEndOfTurn) (.preventDamage subj none)), false, ctxOut)
    if let some rest := pDropPrefixCI? norm "prevent the next " then
      if let some (amtStr, toPart) := pSplitFirstCI? rest " damage that would be dealt to " then
        let (subjStr, dur?) := peelTrailingDuration toPart (some ctx)
        if let some amt := parseValueWithCtx ctx amtStr then
          let subj : StaticSubject :=
            if DiscourseCtx.isSelfPhrase subjStr then .self
            else match parseNounPhrase subjStr with
              | some np => .matching np.filter
              | none => .self
          return some (.installEffect (.applyReplacement (dur?.getD .untilEndOfTurn) (.preventDamage subj (some amt))), false, ctx)
  if lead == "deals" then
    if let some (instr, bindable, ctx1) := parseAtomicInstr qp ctx ("this permanent " ++ norm) then
      return some (instr, bindable, ctx1)

  -- 13. `"You ..."` lead clauses
  if lead == "you" then
    if let some rest := pDropPrefixCI? norm "you create " then
      if let some res := parseAtomicInstr qp ctx ("create " ++ rest) then
        return some res
    if let some rest := pDropPrefixCI? norm "you gain " then
      if let some (lifePart, eachPart) := pSplitFirstCI? rest " life for each " then
        if let some baseV := parseValueWithCtx ctx lifePart then
          let mult :=
            if (pLower eachPart).endsWith " destroyed this way" ||
                (pLower eachPart).endsWith " exiled this way" ||
                (pLower eachPart).endsWith " tapped this way" then
              match ctx.lastActionVar? with | some v => ValueExpr.stepMetric .movedCount v | none => .eventAmount
            else if let some np := parseNounPhrase eachPart then
              ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
            else (parseValueWithCtx ctx eachPart).getD (.const 1)
          let amt := if baseV == .const 1 then mult else .binary .mul baseV mult
          return some (.life (.gain .you amt), true, ctx)
      if let some eqPart := pDropPrefixCI? rest "life equal to " then
        if let some v := parseValueWithCtx ctx eqPart then
          return some (.life (.gain .you v), true, ctx)
      if let some nStr := pDropSuffixCI? rest " life" then
        if let some v := parseValueWithCtx ctx nStr then
          return some (.life (.gain .you v), true, ctx)
    if let some rest := pDropPrefixCI? norm "you lose " then
      if let some (lifePart, eachPart) := pSplitFirstCI? rest " life for each " then
        if let some baseV := parseValueWithCtx ctx lifePart then
          let mult :=
            match pSplitFirstCI? eachPart " counter on " with
            | some (kPart, srcPart) =>
              match CounterKind.ofPrefix ((pWords kPart).toList.map pLower), parseObjWithCtx ctx srcPart with
              | some (ek, _), some (srcObj, _) => ValueExpr.counterCount (some ek) srcObj
              | _, _ => .const 1
            | none =>
              if let some np := parseNounPhrase eachPart then
                ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
              else (parseValueWithCtx ctx eachPart).getD (.const 1)
          let amt := if baseV == .const 1 then mult else .binary .mul baseV mult
          return some (.life (.lose .you amt), true, ctx)
      if let some eqPart := pDropPrefixCI? rest "life equal to " then
        if let some v := parseValueWithCtx ctx eqPart then
          return some (.life (.lose .you v), true, ctx)
      if let some nStr := pDropSuffixCI? rest " life" then
        if let some v := parseValueWithCtx ctx nStr then
          return some (.life (.lose .you v), true, ctx)
    if let some rest := pDropPrefixCI? norm "you mill " then
      if let some res := parseAtomicInstr qp ctx ("mill " ++ rest) then
        return some res
    if let some rest := pDropPrefixCI? norm "you draw " then
      if let some nStr := (pDropSuffixCI? rest " cards").orElse (fun _ => pDropSuffixCI? rest " card") then
        if let some v := parseValueWithCtx ctx nStr then
          return some (.player (.drawCards .you v), true, ctx)
    if let some rest := pDropPrefixCI? norm "you get " then
      if let some emb := parseEmblemSpec? qp rest then
        return some (.create (.emblem .you emb), false, ctx)
    if let some rest := pDropPrefixCI? norm "you control " then
      let (ctrlCore, dur?) := peelTrailingDuration rest (some ctx)
      if let some whoStr := pDropSuffixCI? ctrlCore " during their next turn" then
        if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
          return some (.installEffect (.applyRule (dur?.getD (.untilNextTurnOf who)) (.player (.controlPlayer { relation := .anyPlayer, pred := .matchesExpr who }))), false, ctx1)
    if let some rest := pDropPrefixCI? norm "you may activate loyalty abilities of " then
      let (loyCore, dur?) := peelTrailingDuration rest (some ctx)
      if let some subPart0 := (pDropSuffixCI? loyCore " on any player's turn any time you could cast an instant").orElse
          (fun _ => pDropSuffixCI? loyCore " any time you could cast an instant") then
        let subPart := (pDropSuffixCI? subPart0 " you control").getD subPart0
        let subPart := (pDropSuffixCI? subPart " planeswalkers").getD subPart
        let pred : ObjectPred :=
          match CardSubtype.ofOracle? subPart with
          | some sub => .hasSubtype (.literal sub)
          | none => (parseNounPhrase subPart).map (·.filter.pred) |>.getD (.hasType .planeswalker)
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.play (.activateLoyaltyAsInstant .you pred))), false, ctx)
    if let some rest := pDropPrefixCI? norm "you may choose new targets for " then
      if let some (obj, ctx1) := parseObjWithCtx ctx rest then
        return some (.stack (.chooseNewTargets obj true), false, ctx1)
    if let some (obj, perm, ctx1) := parseGrantPlayPermClause? ctx norm then
      return some (.stack (.mayCastOrPlay obj perm), false, ctx1)
    if let some rest := (pDropPrefixCI? norm "you have protection from ").orElse
        (fun _ => (pDropPrefixCI? norm "you has protection from ").orElse
          (fun _ => pDropPrefixCI? norm "you gain protection from ")) then
      let (qStr, dur?) := peelTrailingDuration rest (some ctx)
      if let some q := parseProtectionQuality? qStr then
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.player (.protectionFrom .you q))), false, ctx)
    if let some rest := pDropPrefixCI? norm "you have hexproof" then
      let (_, dur?) := peelTrailingDuration rest (some ctx)
      return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.player (.hexproof .you none))), false, ctx)
    -- `"you may have <obj> <base-verb action>"` (`The Sensational She-Hulk`, `Baron Strucker`)
    if let some haveRest := pDropPrefixCI? norm "you may have " then
      let normalizedHave :=
        haveRest.replace " deal " " deals " |>.replace " connive" " connives" |>.replace " fight " " fights "
      if let some (inner, b, ctx1) := parseAtomicInstr qp ctx normalizedHave then
        return some (.optional .you none inner .noop, b, ctx1)

  -- 14. `"For as long as ..., ..."` & `"Until <dur>, ..."`
  if lead == "for" then
    if let some (obj, perm, ctx1) := parseGrantPlayPermClause? ctx norm then
      return some (.stack (.mayCastOrPlay obj perm), false, ctx1)
    if let some afterLong := pDropPrefixCI? norm "for as long as " then
      if let some (condDur, bodyStr) := pSplitFirstCI? afterLong ", " then
        let (_, dur?) := peelTrailingDuration ("x for as long as " ++ condDur) (some ctx)
        if let some dur := dur? then
          let rec patchDurF : Instruction → Instruction
            | .installEffect (.applyContinuous _ o cm) => .installEffect (.applyContinuous dur o cm)
            | .installEffect (.applyRule _ r) => .installEffect (.applyRule dur r)
            | .seq xs => .seq (xs.attach.map fun ⟨x, _⟩ => patchDurF x)
            | other => other
          if let some (inner, b, ctx1) := parseAtomicInstr qp ctx bodyStr then
            return some (patchDurF inner, b, ctx1)
  if lead == "until" then
    if let some (obj, perm, ctx1) := parseGrantPlayPermClause? ctx norm then
      return some (.stack (.mayCastOrPlay obj perm), false, ctx1)
    if let some (durStr, bodyStr) := pSplitFirstCI? norm ", " then
      let dur? : Option DurationExpr :=
        let ctxNextTurn? : Option DurationExpr :=
          match pDropPrefixCI? durStr "until " with
          | some r =>
            match pDropSuffixCI? r " next turn" with
            | some wStr =>
              if pLower wStr == "your" then some (.untilNextTurnOf .you)
              else (parsePossessivePlayerWithCtx ctx wStr).map fun (p, _) => .untilNextTurnOf p
            | none => none
          | none => none
        ctxNextTurn?.orElse fun _ => parseDurOrDefault durStr
      if let some dur := dur? then
        let bLow := pLower bodyStr
        -- `"Until <dur>, whenever/when <event>, <effect>"` (`Jace, Reality Sculptor`, `Garruk, Curse Breaker`, `Molten Tide`)
        if bLow.startsWith "whenever " || bLow.startsWith "when " then
          if let some tr := qp.parseTriggered bodyStr ctx.cardName then
            return some (.installEffect (.createDelayedTrigger {
              pattern := tr.pattern
              grouping := tr.grouping
              interveningIf? := tr.interveningIf?
              effect := tr.effect
              duration := dur
              oneShot := false
            }), false, ctx)
        for vSep in #[" becomes ", " become ", " gets ", " get ", " gains ", " gain ", " has ", " have ", " loses ", " lose "] do
          if let some (objStr, modTail) := pSplitFirstCI? bodyStr vSep then
            if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
              if let some (cm, ctx2) := parseContinuousMod? qp ctx1 (vSep.trimAscii.copy ++ " " ++ modTail) then
                return some (.installEffect (.applyContinuous dur obj cm), false, ctx2)
        -- General recursive fallback: parse `bodyStr` and patch any default `.untilEndOfTurn` duration to `dur`
        let rec patchDur : Instruction → Instruction
          | .installEffect (.applyContinuous _ o cm) => .installEffect (.applyContinuous dur o cm)
          | .installEffect (.applyRule _ r) => .installEffect (.applyRule dur r)
          | .seq xs => .seq (xs.attach.map fun ⟨x, _⟩ => patchDur x)
          | other => other
        if let some (inner, b, ctx1) := parseAtomicInstr qp ctx bodyStr then
          return some (patchDur inner, b, ctx1)
        -- Compound `"Until <dur>, <c1> and <c2>"` (`World War Hulk`, `Moon Girl`, `Teferi's Reproach`)
        if let some (c1Str, c2Str) := pSplitFirstCI? bodyStr " and " then
          if let some (i1, b1, ctx1) := parseAtomicInstr qp ctx c1Str then
            if let some (i2, b2, ctx2) := parseAtomicInstr qp ctx1 c2Str then
              return some (.seq #[patchDur i1, patchDur i2], b1 || b2, ctx2)
        if let some (c1Str, c2Str) := pSplitFirstCI? bodyStr " and it " then
          if let some (i1, b1, ctx1) := parseAtomicInstr qp ctx c1Str then
            if let some (i2, b2, ctx2) := parseAtomicInstr qp ctx1 ("it " ++ c2Str) then
              return some (.seq #[patchDur i1, patchDur i2], b1 || b2, ctx2)
        if let some (c1Str, c2Str) := pSplitFirstCI? bodyStr " and they " then
          if let some (i1, b1, ctx1) := parseAtomicInstr qp ctx c1Str then
            if let some (i2, b2, ctx2) := parseAtomicInstr qp ctx1 ("they " ++ c2Str) then
              return some (.seq #[patchDur i1, patchDur i2], b1 || b2, ctx2)

  -- 14b. Standalone rule-modifying one-shot sentences (`Bilbo's Gambit`, `The Kingpin of Crime`, `Jace, Multiverse Architect`)
  if low == "players can't cast spells this turn" || low == "players can't cast spells until end of turn" then
    return some (.installEffect (.applyRule .untilEndOfTurn (.player (.cantCastSpells .any .anyObject))), false, ctx)
  if low == "creatures you control with toughness greater than their power assign combat damage equal to their toughness rather than their power" ||
      low == "creatures you control assign combat damage equal to toughness if greater" then
    return some (.installEffect (.applyRule .untilEndOfTurn (.combat (.assignCombatDamageByToughness { zones := .battlefield, pred := .all #[.hasType .creature, .controlledBy .you] } true))), false, ctx)
  if let some restCantAtk := pDropPrefixCI? norm "creatures they control can't attack " then
    let (atkCore, dur?) := peelTrailingDuration restCantAtk (some ctx)
    if let some subRaw := pDropSuffixCI? atkCore " you control" then
      let subTrim := (pDropSuffixCI? subRaw "s").getD subRaw
      if let some sub := CardSubtype.ofOracle? subTrim then
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.combat (.cantAttackPlayer
          (.all #[.hasType .creature, .controlledBy { relation := .anyPlayer, pred := .matchesExpr .activePlayer }])
          .you (some (.all #[.hasSubtype (.literal sub), .hasType .planeswalker]))))), false, ctx)

  -- 15. Subject-verb clauses:
  -- 15a. `"<src> deals <amt> damage [divided as you choose among ...] to <recipient> [and <amt2> damage to <rec2>]"`
  if let some (srcStr, tail) := pSplitFirstCI? norm " deals " then
    if let some (firstDmg, secondDmg) := pSplitFirstCI? tail " and " then
      if (pLower secondDmg).contains " damage to " then
        match parseAtomicInstr qp ctx (srcStr ++ " deals " ++ firstDmg) with
        | some (i1, b1, c1) =>
          match parseAtomicInstr qp c1 (srcStr ++ " deals " ++ secondDmg) with
          | some (i2, b2, c2) => return some (flattenInstrSeq #[i1, i2], b1 || b2, c2)
          | none => pure ()
        | none => pure ()
    if let some (amtStr, divPart) := pSplitFirstCI? tail " damage divided as you choose among " then
      match parseObjWithCtx ctx srcStr, parseValueWithCtx ctx amtStr, parseDividedMaxTargets? divPart with
      | some (src, ctx1), some amt, some (maxT, dom) =>
        let (_, ctx2) := ctx1.pushTargetSlot {
          domain := dom
          count := .between 1 maxT
          division? := some (.damage, amt)
        }
        return some (.damage (.deal src .allTargets amt { divided := true }), true, ctx2)
      | _, _, _ => pure ()
    if let some afterEq := pDropPrefixCI? tail "damage equal to " then
      if let some (eqStr, recStr) := pSplitFirstCI? afterEq " to " then
        match parseObjWithCtx ctx srcStr with
        | some (src, ctx1) =>
          let ctxForVal :=
            if (pLower eqStr).startsWith "that " then ctx1
            else { ctx1 with lastSubject? := some src }
          let ctxForRec := { ctx1 with lastSubject? := ctx.lastSubject? }
          if pLower eqStr == "its power" && src != .this then
            if let some (recObj, ctx2) := parseObjWithCtx ctxForRec recStr then
              let isCreatureTarget : Bool :=
                match recObj with
                | .target slotIdx =>
                  match (ctx2.slots[slotIdx]?.map (·.domain) : Option TargetDomain) with
                  | some (.object _ pred) =>
                    let rec hasPlaneswalker : ObjectPred → Bool
                      | .hasType .planeswalker => true
                      | .all ps => ps.attach.any fun ⟨p, _⟩ => hasPlaneswalker p
                      | .any ps => ps.attach.any fun ⟨p, _⟩ => hasPlaneswalker p
                      | _ => false
                    !hasPlaneswalker pred
                  | _ => false
                | _ => false
              if isCreatureTarget then
                return some (.damage (.fight src recObj true), true, ctx2)
          if let some amt := parseValueWithCtx ctxForVal eqStr then
            if let some (rec, ctx2) := parseRecipientWithCtx ctxForRec recStr then
              return some (.damage (.deal src rec amt), true, ctx2)
        | none => pure ()
    -- `"<src> deals damage to <rec> equal to <V>"` (`Call Forth the Tempest`)
    if let some afterDmgTo := pDropPrefixCI? tail "damage to " then
      if let some (recStr, eqStr) := pSplitFirstCI? afterDmgTo " equal to " then
        if let some (src, ctx1) := parseObjWithCtx ctx srcStr then
          let ctxForVal := { ctx1 with lastSubject? := some src }
          if let some amt := parseValueWithCtx ctxForVal eqStr then
            if let some (rec, ctx2) := parseRecipientWithCtx ctx1 recStr then
              return some (.damage (.deal src rec amt), true, ctx2)
    if let some (amtStr, recStr) := pSplitLastCI? tail " damage to " then
      let recLow := pLower (pClean recStr)
      let isSelfDmgToAnaphor :=
        pLower (pClean srcStr) == "it" &&
          (recLow == "that creature" || recLow == "that permanent" || recLow == "that planeswalker" ||
           recLow == "that target" || recLow == "it")
      let srcRes? :=
        if isSelfDmgToAnaphor then some (.this, ctx)
        else parseObjWithCtx ctx srcStr
      if let some (src, ctx1) := srcRes? then
        if let some amt := parseValueWithCtx ctx1 amtStr then
          if let some (rec, ctx2) := parseRecipientWithCtx ctx1 recStr then
            return some (.damage (.deal src rec amt), true, ctx2)

  -- 15b. `"<a> fights <b>"` / `"<obj> connives"`
  if let some (aStr, bStr) := pSplitFirstCI? norm " fights " then
    if let some (aObj, ctx1) := parseObjWithCtx ctx aStr then
      if let some (bObj, ctx2) := parseObjWithCtx ctx1 bStr then
        return some (.damage (.fight aObj bObj false), true, ctx2)
  if let some connObjStr := (pDropSuffixCI? norm " connives").orElse (fun _ => pDropSuffixCI? norm " connive") then
    if let some (obj, ctx1) := parseObjWithCtx ctx connObjStr then
      return some (.player (.connive obj), true, ctx1)

  -- 15c. Owner library placement & shuffle (`"The owner of <obj> puts it ..."`, `"<obj>'s owner puts/shuffles ..."`, `"<who> puts/exiles ..."`)
  let extractLibDest (restOwn : String) : Option String :=
    (pSplitFirstCI? restOwn " into ").map (fun (_, r) => "into " ++ r)
      |>.orElse fun _ => (pSplitFirstCI? restOwn " second from the top").map (fun (_, r) => ("second from the top " ++ r).trimAscii.copy)
      |>.orElse fun _ => (pSplitFirstCI? restOwn " third from the top").map (fun (_, r) => ("third from the top " ++ r).trimAscii.copy)
      |>.orElse fun _ => (pSplitFirstCI? restOwn " on ").map (fun (_, r) => "on " ++ r)
  if let some afterTheOwn := pDropPrefixCI? norm "the owner of " then
    if let some (objRaw, restOwn) := pSplitFirstCI? afterTheOwn " puts " then
      if let some libDest := extractLibDest restOwn then
        if let some (obj, ctx1) := parseObjWithCtx ctx objRaw then
          if let some (dest, mods, ctx2) := parseDestZoneWithMods? ctx1 libDest then
            return some (.moveZone obj dest .put mods, true, ctx2)
  if let some (objRaw, restOwn) := pSplitFirstCI? norm "'s owner puts " then
    if let some libDest := extractLibDest restOwn then
      if let some (obj, ctx1) := parseObjWithCtx ctx objRaw then
        if let some (dest, mods, ctx2) := parseDestZoneWithMods? ctx1 libDest then
          return some (.moveZone obj dest .put mods, true, ctx2)
  if let some (objRaw, shufTail) := pSplitFirstCI? norm "'s owner shuffles " then
    if (pLower shufTail).contains " into their library" then
      if let some (obj, ctx1) := parseObjWithCtx ctx objRaw then
        return some (.moveZone obj (.library .owner .top false) .put { shuffleAfter := true }, true, ctx1)
  if let some shufTail := pDropPrefixCI? norm "its owner shuffles " then
    if (pLower shufTail).contains " into their library" then
      let obj := ctx.lastSubject?.getD (.target (ctx.lastTargetSlot?.getD 0))
      return some (.moveZone obj (.library .owner .top false) .put { shuffleAfter := true }, true, ctx)
  if let some (whoStr, putTail) := (pSplitFirstCI? norm " puts ").orElse (fun _ => pSplitFirstCI? norm " put ") then
    if pLower whoStr != "you" then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some (instr, b, ctx2) := parseAtomicInstr qp { ctx1 with lastPlayer? := some who } ("put " ++ putTail) then
          return some (instr, b, ctx2)
  if let some (whoStr, exTail) := pSplitFirstCI? norm " exiles " then
    if pLower whoStr != "you" then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some (instr, b, ctx2) := parseAtomicInstr qp { ctx1 with lastPlayer? := some who } ("exile " ++ exTail) then
          return some (instr, b, ctx2)

  -- 15d. `"<player> ..."`
  if let some (whoStr, tail) := (pSplitFirstCI? norm " has protection from ").orElse
      (fun _ => (pSplitFirstCI? norm " gains protection from ").orElse
        (fun _ => pSplitFirstCI? norm " gain protection from ")) then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      let ctx1p := { ctx1 with lastPlayer? := some who }
      let (qStr, dur?) := peelTrailingDuration tail (some ctx1p)
      if let some q := parseProtectionQuality? qStr then
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.player (.protectionFrom { relation := .anyPlayer, pred := .matchesExpr who } q))), false, ctx1p)
  if let some (whoStr, tail) := (pSplitFirstCI? norm "'s life total can't change").orElse
      (fun _ => pSplitFirstCI? norm " life total can't change") then
    let (_, dur?) := peelTrailingDuration ("x " ++ tail) (some ctx)
    if let some (who, ctx1) := parsePossessivePlayerWithCtx ctx whoStr then
      let dur :=
        match pDropPrefixCI? tail.trimAscii.copy "until " with
        | some r =>
          match pDropSuffixCI? r " next turn" with
          | some wS =>
            match parsePossessivePlayerWithCtx ctx1 wS with
            | some (p, _) => DurationExpr.untilNextTurnOf p
            | none => dur?.getD .untilEndOfTurn
          | none => dur?.getD .untilEndOfTurn
        | none => dur?.getD .untilEndOfTurn
      return some (.installEffect (.applyRule dur (.player (.lifeTotalCantChange { relation := .anyPlayer, pred := .matchesExpr who }))), false, ctx1)
  if let some (whoStr, tail) := (pSplitFirstCI? norm " reveals ").orElse (fun _ => pSplitFirstCI? norm " reveal ") then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if pLower tail == "their hand" || pLower tail == "his or her hand" then
        return some (.player (.reveal who (.inZones (.handOf who) .anyObject)), false, ctx1)
      if let some eqPart := pDropPrefixCI? tail "a number of cards from their hand equal to " then
        if let some cnt := parseValueWithCtx ctx1 eqPart then
          return some (.player (.reveal who (.inZones (.handOf who) .anyObject) (some (.exact cnt))), true, ctx1)
      if let some (obj, ctx2) := parseObjWithCtx ctx1 tail then
        return some (.player (.reveal who obj), false, ctx2)
  if let some (whoStr, tail) := (pSplitFirstCI? norm " each draw ").orElse
      (fun _ => (pSplitFirstCI? norm " each draws ").orElse (fun _ => pSplitFirstCI? norm " draws ")) then
    if let some nStr := (pDropSuffixCI? tail " cards").orElse (fun _ => pDropSuffixCI? tail " card") then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some v := parseValueWithCtx ctx1 nStr then
          return some (.player (.drawCards who v), true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " discards " then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if pLower tail == "their hand" || pLower tail == "his or her hand" then
        return some (.moveZone (.inZones (.handOf who) .anyObject) .graveyard .discard {}, true, ctx1)
      let (t1, atRand) := match pDropSuffixCI? tail " at random" with | some a => (a, true) | none => (tail, false)
      if let some nStr := (pDropSuffixCI? t1 " cards").orElse (fun _ => pDropSuffixCI? t1 " card") then
        if let some val := parseValueWithCtx ctx1 nStr then
          match who with
          | .matching rel pred =>
            let (v, ctx2) := ctx1.allocVar
            let ch : MoveChoiceSpec := { chooser := .player (.stepPlayers v), count := .exact val, atRandom := atRand }
            let body := Instruction.moveZone (.inZones (.handOf (.stepPlayers v)) .anyObject) .graveyard .discard { choice? := some ch }
            return some (.forEach (.eachPlayer { relation := rel, pred }) v body, true, ctx2)
          | _ =>
            let ch : MoveChoiceSpec := { chooser := .player who, count := .exact val, atRandom := atRand }
            return some (.moveZone (.inZones (.handOf who) .anyObject) .graveyard .discard { choice? := some ch }, true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " mills " then
    if let some nStr := (pDropSuffixCI? tail " cards").orElse (fun _ => pDropSuffixCI? tail " card") then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some v := parseValueWithCtx ctx1 nStr then
          return some (Instruction.mill v who, true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " gains " then
    if let some eqPart := pDropPrefixCI? tail "life equal to " then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some v := parseValueWithCtx ctx1 eqPart then
          return some (.life (.gain who v), true, ctx1)
    if let some nStr := pDropSuffixCI? tail " life" then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some v := parseValueWithCtx ctx1 nStr then
          return some (.life (.gain who v), true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " loses " then
    if let some eqPart := pDropPrefixCI? tail "life equal to " then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        match who with
        | .matching rel pred =>
          let eqLow := pLower eqPart
          if eqLow.contains "that player" || eqLow.contains "they " || eqLow.contains "their " then
            let (v, ctx2) := ctx1.allocVar
            let ctxForVal := { ctx2 with lastPlayer? := some (.stepPlayers v) }
            if let some val := parseValueWithCtx ctxForVal eqPart then
              return some (.forEach (.eachPlayer { relation := rel, pred }) v (.life (.lose (.stepPlayers v) val)), true, ctx2)
        | _ => pure ()
        let ctxForVal := { ctx1 with lastPlayer? := some who }
        if let some v := parseValueWithCtx ctxForVal eqPart then
          return some (.life (.lose who v), true, ctx1)
    if let some nStr := pDropSuffixCI? tail " life" then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        if let some v := parseValueWithCtx ctx1 nStr then
          return some (.life (.lose who v), true, ctx1)
  if let some (whoStr, tail) := (pSplitFirstCI? norm " creates ").orElse (fun _ => pSplitFirstCI? norm " create ") then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if let some (spec, mods, ctx2) := parseTokenDesc? qp ctx1 tail parseObjWithCtx then
        return some (.create (.tokens who (.const 1) spec mods), true, ctx2)
      let tws := pWords tail
      if tws.size >= 2 then
        if let some cnt := parseCountVal? tws[0]! then
          let descStr := String.intercalate " " (tws.extract 1 tws.size).toList
          if let some (spec, mods, ctx2) := parseTokenDesc? qp ctx1 descStr parseObjWithCtx then
            return some (.create (.tokens who cnt spec mods), true, ctx2)
  if let some (whoStr, tail0) := pSplitFirstCI? norm " sacrifices " then
    let tail := (pDropSuffixCI? tail0 " of their choice").getD tail0
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if let some basePart := (pSplitFirstCI? tail " with the least power among ").map Prod.fst
          |>.orElse (fun _ => pDropSuffixCI? tail " with the least power") then
        let bClean := ((pDropPrefixCI? basePart "a ").orElse fun _ => pDropPrefixCI? basePart "an ") |>.getD basePart
        if let some np := parseNounPhrase bClean then
          let pool := ObjectExpr.inZones .battlefield (.all #[np.filter.pred, .controlledBy { relation := .anyPlayer, pred := .matchesExpr who }])
          let ch : MoveChoiceSpec := { chooser := .player who, count := .exact (.const 1), filter? := some np.filter.pred, extremeMetric? := some (false, .stat .power) }
          return some (.moveZone pool .graveyard .sacrifice { choice? := some ch }, true, ctx1)
      if let some basePart := (pSplitFirstCI? tail " with the greatest mana value among ").map Prod.fst
          |>.orElse (fun _ => pDropSuffixCI? tail " with the greatest mana value") then
        let bClean := ((pDropPrefixCI? basePart "a ").orElse fun _ => pDropPrefixCI? basePart "an ") |>.getD basePart
        if let some np := parseNounPhrase bClean then
          let pool := ObjectExpr.inZones .battlefield (.all #[np.filter.pred, .controlledBy { relation := .anyPlayer, pred := .matchesExpr who }])
          let ch : MoveChoiceSpec := { chooser := .player who, count := .exact (.const 1), filter? := some np.filter.pred, extremeMetric? := some (true, .stat .manaValue) }
          return some (.moveZone pool .graveyard .sacrifice { choice? := some ch }, true, ctx1)
      let (cntR, predRaw) := (parseExprCountRange? tail).getD (.exact (.const 1), tail)
      let predClean := ((pDropPrefixCI? predRaw "a ").orElse fun _ => pDropPrefixCI? predRaw "an ") |>.getD predRaw
      if let some np := parseNounPhrase predClean then
        let stripCtrl : ObjectPred → ObjectPred
          | .controlledBy _ => .anyObject
          | .all ps => ObjectPred.andAll (ps.filter fun | .controlledBy _ => false | _ => true)
          | other => other
        let basePred := stripCtrl np.filter.pred
        match who with
        | .matching rel pred =>
          let (v, ctx2) := ctx1.allocVar
          let pool := ObjectExpr.inZones .battlefield (ObjectPred.andAll #[basePred, .controlledBy { relation := .anyPlayer, pred := .matchesExpr (.stepPlayers v) }])
          let ch : MoveChoiceSpec := { chooser := .player (.stepPlayers v), count := cntR }
          return some (.forEach (.eachPlayer { relation := rel, pred }) v (.moveZone pool .graveyard .sacrifice { choice? := some ch }), true, ctx2)
        | _ =>
          let pool := ObjectExpr.inZones .battlefield (ObjectPred.andAll #[basePred, .controlledBy { relation := .anyPlayer, pred := .matchesExpr who }])
          let ch : MoveChoiceSpec := { chooser := .player who, count := cntR }
          return some (.moveZone pool .graveyard .sacrifice { choice? := some ch }, true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " amasses " then
    let tws := pWords tail
    if tws.size >= 2 then
      let subW := (pDropSuffixCI? tws[0]! "s").getD tws[0]!
      if let some sub := CardSubtype.ofOracle? subW then
        let amtStr := String.intercalate " " (tws.extract 1 tws.size).toList
        if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
          if let some v := parseValueWithCtx ctx1 amtStr then
            return some (.player (.amass who sub v), true, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " scries " then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if let some v := parseValueWithCtx ctx1 tail then
        return some (.player (.scry who v), false, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm " surveils " then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if let some v := parseValueWithCtx ctx1 tail then
        return some (.player (.surveil who v), true, ctx1)
  if let some whoStr := pDropSuffixCI? norm " shuffles" then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      return some (.player (.shuffle who), false, ctx1)
  if let some (whoStr, tail) := pSplitFirstCI? norm "'s life total becomes " then
    if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
      if let some v := parseValueWithCtx ctx1 tail then
        return some (.life (.set who v), false, ctx1)
  if let some valStr := pDropPrefixCI? norm "your life total becomes " then
    if let some v := parseValueWithCtx ctx valStr then
      return some (.life (.set .you v), false, ctx)

  -- 15e. `"<player> can't cast <pred> spells [dur]"` / `"<creatures> assign combat damage equal to toughness if greater [dur]"` / `"<creatures> can't attack you or <sub/pw> [dur] unless <who> pays <cost>"`
  if let some (whoStr, tail) := pSplitFirstCI? norm " can't cast " then
    let (core, dur?) := peelTrailingDuration tail (some ctx)
    if let some pStr := (pDropSuffixCI? core " spells").orElse (fun _ => pDropSuffixCI? core " spell") then
      let pf := (parsePlayerFilter? whoStr).getD .any
      let pred := if pStr.isEmpty then .anyObject else (parseNounPhrase (pStr ++ " spell")).map (·.filter.pred) |>.getD .anyObject
      return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.player (.cantCastSpells pf pred))), false, ctx)
  if let some (scopeStr, tail) := pSplitFirstCI? norm " assign combat damage equal to toughness if greater" then
    let (_, dur?) := peelTrailingDuration ("x" ++ tail) (some ctx)
    if let some np := parseNounPhrase scopeStr then
      return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.combat (.assignCombatDamageByToughness np.filter true))), false, ctx)
  if let some (atkStr, tail) := pSplitFirstCI? norm " can't attack you or " then
    if let some (pwPart, taxPart) := pSplitFirstCI? tail " unless " then
      if let some (_, costStr) := pSplitFirstCI? taxPart " pays " then
        let (pwClean, dur?) := peelTrailingDuration pwPart (some ctx)
        match parseNounPhrase atkStr, parseNounPhrase pwClean, parseCostSpec costStr with
        | some atkNp, some pwNp, some cs =>
          return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn) (.all #[
            .combat (.attackTax atkNp.filter.pred .you cs),
            .combat (.attackPlaneswalkerTax atkNp.filter.pred pwNp.filter.pred cs)
          ])), false, ctx)
        | _, _, _ => pure ()
    else
      let (pwClean, dur?) := peelTrailingDuration tail (some ctx)
      match parseNounPhrase atkStr, parseNounPhrase pwClean with
      | some atkNp, some pwNp =>
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn)
          (.combat (.cantAttackPlayer atkNp.filter.pred .you (some pwNp.filter.pred)))), false, ctx)
      | _, _ => pure ()

  -- 15f. `"<obj> explores"`, `"<obj> connives"`, `"<obj> phases out [until ...]"`, `"<obj> becomes prepared/unprepared/your Ring-bearer"`, `"<obj> can't become untapped [dur]"`
  if let some objStr := (pDropSuffixCI? norm " explores").orElse (fun _ => pDropSuffixCI? norm " explore") then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.player (.explore obj), true, ctx1)
  if let some objStr := (pDropSuffixCI? norm " connives").orElse (fun _ => pDropSuffixCI? norm " connive") then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.player (.connive obj), true, ctx1)
  if let some (objStr, phaseTail) := (pSplitFirstCI? norm " phases out").orElse (fun _ => pSplitFirstCI? norm " phase out") then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      let untilP? : Option PlayerExpr :=
        match pDropPrefixCI? phaseTail "until " with
        | some r =>
          let wStr := (pDropSuffixCI? r " next turn").getD r
          (parsePossessivePlayerWithCtx ctx1 wStr).map Prod.fst
        | none => none
      return some (.permanent (.phaseOut obj untilP?), false, ctx1)
  if let some objStr := pDropSuffixCI? norm " becomes prepared" then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.permanent (.setDesignation obj .prepared true), false, ctx1)
  if let some objStr := pDropSuffixCI? norm " becomes unprepared" then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.permanent (.setDesignation obj .prepared false), false, ctx1)
  if let some objStr := pDropSuffixCI? norm " becomes your ring-bearer" then
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.permanent (.setDesignation obj .ringBearer true), false, ctx1)
  if let some (objStr, untapTail) := pSplitFirstCI? norm " can't become untapped" then
    let (_, dur?) := peelTrailingDuration ("x " ++ untapTail) (some ctx)
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.installEffect (.applyContinuous (dur?.getD .untilEndOfTurn) obj (.applyRule (.game (.cantBecomeUntapped .self)))), false, ctx1)

  -- 15g. `"<obj> gains your choice of <kw1>, <kw2>, or <kw3> until end of turn"` (`Hungering Puppetbeast`)
  if let some (objStr, choiceRest) := pSplitFirstCI? norm " gains your choice of " then
    let (kwOrStr, _) := peelTrailingDuration choiceRest (some ctx)
    let kwNorm := kwOrStr.replace ", or " ", " |>.replace " or " ", "
    let kwParts := kwNorm.splitOn "," |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
    let kws := kwParts.filterMap parseKeywordAbility |>.toArray
    if kws.size >= 2 && kws.size == kwParts.length then
      if let some (_, ctx1) := parseObjWithCtx ctx objStr then
        return some (.player (.choose .you (.keyword kws)), false, ctx1)
  -- 15g2. `"<obj> gains flashback until end of turn"` (`Stingcaster Mage`)
  if let some (objStr, fbTail) := pSplitFirstCI? norm " gains flashback" then
    let (_, dur?) := peelTrailingDuration ("x " ++ fbTail) (some ctx)
    if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
      return some (.stack (.mayCastOrPlay obj { duration := dur?.getD .untilEndOfTurn, landsAllowed := false, asFlashback := true }), false, ctx1)

  -- 15h. `"[have] <obj>'s base power and toughness become [equal to ...] [dur]"`
  let basePtNorm := (pDropPrefixCI? norm "have ").getD norm
  let (corePt, durPt?) := peelTrailingDuration basePtNorm (some ctx)
  if let some (objStr, ptStr) := (pSplitFirstCI? corePt "'s base power and toughness become ").orElse
      (fun _ => pSplitFirstCI? corePt " base power and toughness become ") then
    let objClean := if pLower objStr == "its" then "it" else objStr
    if let some (obj, ctx1) := parseObjWithCtx ctx objClean then
      if let some eqRest := pDropPrefixCI? ptStr "equal to " then
        if let some srcStr := pDropSuffixCI? eqRest "'s power and toughness" then
          if let some (srcObj, ctx2) := parseObjWithCtx ctx1 srcStr then
            return some (.installEffect (.applyContinuous (durPt?.getD .untilEndOfTurn) obj
              (.setBasePT (some (.objectStat .power srcObj)) (some (.objectStat .toughness srcObj)))), false, ctx2)
      let pts := ptStr.splitOn "/"
      if pts.length == 2 then
        match parseCountVal? pts[0]!, parseCountVal? pts[1]! with
        | some pv, some tv =>
          return some (.installEffect (.applyContinuous (durPt?.getD .untilEndOfTurn) obj (.setBasePT (some pv) (some tv))), false, ctx1)
        | _, _ => pure ()

  -- 15i. Continuous modification on `<obj> <ContinuousMod> [dur]` (expanding `"they're "` / `"it's "`)
  let normExp :=
    if let some r := pDropPrefixCI? norm "they're " then "they are " ++ r
    else if let some r := pDropPrefixCI? norm "it's " then "it is " ++ r
    else norm
  let (coreNoDur, dur?) := peelTrailingDuration normExp (some ctx)
  -- Quantified `"<creatures> can't block [this turn]"` -> CR 611.2c rule-modifying effect (`Fire of Orthanc`)
  if let some cbSubj := pDropSuffixCI? coreNoDur " can't block" then
    let cbl := pLower cbSubj
    if !cbl.contains "target " && !DiscourseCtx.isSelfPhrase cbl && (ctx.resolveObjectAnaphor? cbSubj).isNone then
      if let some np := parseNounPhrase cbSubj then
        return some (.installEffect (.applyRule (dur?.getD .untilEndOfTurn)
          (.combat (.cantBlock (.matching np.filter) none))), false, ctx)
  for vSep in #[
    " gets ", " get ", " gains ", " gain ", " loses ", " lose ",
    " becomes ", " become ", " has ", " have ", " can't ", " is ", " are "
  ] do
    if let some (objStr, modTail) := pSplitFirstCI? coreNoDur vSep then
      if let some (obj, ctx1) := parseObjWithCtx ctx objStr then
        let verb := vSep.trimAscii.copy
        if let some (cm, ctx2) := parseContinuousMod? qp ctx1 (verb ++ " " ++ modTail) then
          let dur :=
            match dur? with
            | some d => d
            | none =>
              let ml := pLower modTail
              if ml.contains "until end of turn" || ml.contains "this turn" then .untilEndOfTurn
              else match cm with | .modifyPT _ _ => .untilEndOfTurn | _ => .indefinite
          return some (.installEffect (.applyContinuous dur obj cm), false, ctx2)

  return none

/-! ### Intra-Sentence Combinator Parser -/

/-- Parse one single-sentence clause (handling `", where X is ..."`, leading `"Then "`,
`", then "`, `"unless <player> pays <cost>"`, `"For each ..., ..."`, `"You may ..."`,
`"If <cond>, ..."`, `"When you do, ..."`, single-sentence search, compound `"A and B"`,
and atomic instructions). -/
partial def parseSingleClause (qp : QuotedAbilityParsers) (ctx : DiscourseCtx) (raw : String) :
    Option (Instruction × Bool × DiscourseCtx) := Id.run do
  let s0 := pClean raw
  if s0.isEmpty then return none

  -- Peel optional leading `"Then "` (`"Then if ..."`, `"Then shuffle"`, `"Then creatures you control ..."`)
  if let some rest := pDropPrefixCI? s0 "then " then
    return parseSingleClause qp ctx rest

  -- Scoped multi-step sequence joined by `"; "` (inside `ifCond` / `optional` / `Otherwise`)
  if s0.contains ';' && !(pLower s0).startsWith "if " && !(pLower s0).startsWith "for each " &&
      !(pLower s0).startsWith "when you do, " && !(pLower s0).startsWith "if you do, " then
    let semiParts := (s0.splitOn ";").map pClean |>.filter (!·.isEmpty)
    if semiParts.length >= 2 then
      let mut sSteps : Array (Option VarId × Instruction) := #[]
      let mut curCtx := ctx
      let mut ok := true
      for sp in semiParts do
        match parseSingleClause qp curCtx sp with
        | some (si, sb, cNext) =>
          let (sv?, cAlloc) := if sb then let (v, c) := cNext.allocVar; (some v, c) else (none, cNext)
          sSteps := sSteps.push (sv?, si)
          curCtx := cAlloc
        | none => ok := false; break
      if ok && !sSteps.isEmpty then
        return some (assembleBoundSteps sSteps, false, curCtx)

  -- Split `", and that player ..."` / `", and they ..."` before `", where X is "` (`Palantír of Orthanc`)
  if let some (lhs, rhs) := pSplitFirstCI? s0 ", and that player " then
    if let some (i1, b1, ctx1) := parseSingleClause qp ctx lhs then
      let (v1?, ctxMid) := if b1 then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
      if let some (i2, b2, ctx2) := parseSingleClause qp ctxMid ("that player " ++ rhs) then
        return some (assembleBoundSteps #[(v1?, i1), (none, i2)], b2, ctx2)

  -- Peel trailing `", where X is <ValueExpr>"` (normalizing self cardName and pushing target player once if present)
  if let some (lhs, xStr0) := pSplitLastCI? s0 ", where x is " then
    let xStr := pClean (replaceCardNameOutsideQuotes xStr0 ctx.cardName "this permanent")
    if let some (instr, bindable, ctx1) := parseSingleClause qp ctx lhs then
      let (xStrEff, ctxVal) : String × DiscourseCtx :=
        if (pLower xStr).contains "target player's" then
          let (idx, c2) := ctx1.pushTargetSlot { domain := .player .any }
          (xStr.replace "target player's" "that player's", { c2 with lastPlayer? := some (.target idx) })
        else if (pLower xStr).contains "target opponent's" then
          let (idx, c2) := ctx1.pushTargetSlot { domain := .player .opponent }
          (xStr.replace "target opponent's" "that player's", { c2 with lastPlayer? := some (.target idx) })
        else (xStr, ctx1)
      if let some xVal := parseValueWithCtx ctxVal xStrEff then
        return some (substInstrX xVal instr, bindable, ctxVal)

  -- Keep `"Put <obj> on top of its owner's library, then shuffle"` atomic (`Gandalf`, `Living Library`)
  if (pLower s0).startsWith "put " && (pLower s0).endsWith "library, then shuffle" then
    if let some res := parseAtomicInstr qp ctx s0 then
      return some res

  -- Single-sentence search library inside combinators (`"you may search ..."`, `"if you do, search ..."`)
  if (pLower s0).startsWith "search " || (pLower s0).contains " searches " then
    if let some (instr, _, ctx1) := parseSearchLibrarySeq? ctx #[s0] 0 then
      return some (instr, true, ctx1)
  if (pLower s0).startsWith "reveal cards from the top of " || (pLower s0).startsWith "look at the top " then
    if let some (instr, _, ctx1) := parseInspectLibrarySeq? ctx #[s0] 0 then
      return some (instr, true, ctx1)

  -- Replacement-effect one-shot sentences
  let s0Low := pLower s0
  if s0Low.startsWith "if this spell would leave the stack, exile it instead" then
    return some (.installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack), false, ctx)
  if s0Low.startsWith "if a spell cast this way would be put into a graveyard, exile it instead" then
    return some (.installEffect (.applyReplacement .untilEndOfTurn (.exileInsteadOfDying { zones := .stack, pred := .anyObject } none)), false, ctx)
  if let some ifRest := pDropPrefixCI? s0 "if " then
    if let some (subjStr, _) := (pSplitFirstCI? ifRest " would die this turn, exile it instead").orElse
        (fun _ => pSplitFirstCI? ifRest " would die, exile it instead") then
      let scope : ObjectFilter :=
        if pLower subjStr == "that creature" || pLower subjStr == "it" then
          { zones := .battlefield, pred := .sameAs (.target (ctx.lastTargetSlot?.getD 0)) }
        else match parseNounPhrase subjStr with
          | some np => np.filter
          | none => { zones := .battlefield, pred := .hasType .creature }
      return some (.installEffect (.applyReplacement .untilEndOfTurn (.exileInsteadOfDying scope none)), false, ctx)

  -- `"If you do, when you do, <reflexive>"` (`Thorin, Mountain-king`)
  if let some reflStr := pDropPrefixCI? s0 "if you do, when you do, " then
    let reflCtx : DiscourseCtx := {
      cardName := ctx.cardName
      isTrigger := true
      lastSubject? := none
      lastPlayer? := ctx.lastPlayer?
      lastActionVar? := none
      nextVarIdx := ctx.nextVarIdx
    }
    if let some (reflBody, _, reflCtx') := parseSingleClause qp reflCtx reflStr then
      let reflEff : Effect := { targets := reflCtx'.toTargetSpec, body := reflBody }
      let cond := Condition.stepSucceeded (ctx.lastActionVar?.getD ⟨0⟩)
      return some (.ifCond cond (mkReflexiveWhenYouDo reflEff) .noop, false, ctx)

  -- `"When you do, <reflexive>"` (CR 603.12)
  if let some reflStr := pDropPrefixCI? s0 "when you do, " then
    let reflCtx : DiscourseCtx := {
      cardName := ctx.cardName
      isTrigger := true
      lastSubject? := ctx.lastSubject?
      lastPlayer? := ctx.lastPlayer?
      lastActionVar? := ctx.lastActionVar?
      nextVarIdx := ctx.nextVarIdx
    }
    if let some (reflBody, _, reflCtx') := parseSingleClause qp reflCtx reflStr then
      let reflEff : Effect := { targets := reflCtx'.toTargetSpec, body := reflBody }
      return some (mkReflexiveWhenYouDo reflEff, false, ctx)

  -- `"For each <iter>, <body>"`
  if let some rest := pDropPrefixCI? s0 "for each " then
    if let some (iterStr0, bodyStr) := pSplitFirstCI? rest ", " then
      let iterStr := ((pDropPrefixCI? iterStr0 "a ").orElse fun _ => pDropPrefixCI? iterStr0 "an ") |>.getD iterStr0
      -- CR 115.1 / 601.2c: when `"For each opponent/player, <body>"` introduces a target
      -- referencing `"that player"` (e.g. *Bilbo's Burglaring*, *The Theorist, Jace Beleren*),
      -- hoist `forEach?` onto that `TargetSlot` and replace `.target idx` with `.allTargets`.
      if let some pfFilter := (parsePlayerFilter? iterStr0).orElse (fun _ => parsePlayerFilter? iterStr) then
        if pfFilter == .opponent || pfFilter == .any then
          let slotsBefore := ctx.slots.size
          let probeCtx := { ctx with lastPlayer? := some (.matching .anyPlayer .thatPlayer) }
          if let some (bodyT, bT, ctxT) := parseSingleClause qp probeCtx bodyStr then
            if ctxT.slots.size == slotsBefore + 1 then
              let slot := ctxT.slots[slotsBefore]!
              if slot.domain != slot.domain.substitutePlayerFilter .thatPlayer .you then
                let rec replaceTargetSlot : Instruction → Instruction
                  | .moveZone o d v m =>
                    .moveZone (if o == .target slotsBefore then .allTargets else o) d v m
                  | .installEffect (.applyContinuous dur aff cm) =>
                    .installEffect (.applyContinuous dur (if aff == .target slotsBefore then .allTargets else aff) cm)
                  | .permanent (.setTapped o t ch) =>
                    .permanent (.setTapped (if o == .target slotsBefore then .allTargets else o) t ch)
                  | .permanent (.modifyCounters cm o ch) =>
                    .permanent (.modifyCounters cm (if o == .target slotsBefore then .allTargets else o) ch)
                  | .permanent (.phaseOut o dur) =>
                    .permanent (.phaseOut (if o == .target slotsBefore then .allTargets else o) dur)
                  | .damage (.deal src (.targetSlot idx) amt fl) =>
                    .damage (.deal src (if idx == slotsBefore then .allTargets else .targetSlot idx) amt fl)
                  | .seq xs => .seq (xs.attach.map fun ⟨x, _⟩ => replaceTargetSlot x)
                  | .bind bv st cont => .bind bv (replaceTargetSlot st) (replaceTargetSlot cont)
                  | .ifCond c t e => .ifCond c (replaceTargetSlot t) (replaceTargetSlot e)
                  | .optional w cs y n m => .optional w cs (replaceTargetSlot y) (replaceTargetSlot n) m
                  | other => other
                let normDom :=
                  if pfFilter == .opponent then
                    slot.domain.substitutePlayerFilter .thatPlayer .opponent
                  else slot.domain
                let newSlot : TargetSlot := { slot with domain := normDom, forEach? := some pfFilter }
                let slots' := ctxT.slots.set! slotsBefore newSlot
                return some (replaceTargetSlot bodyT, bT, { ctxT with slots := slots' })
      let (v, ctx1) := ctx.allocLoopVar
      if let some (pf, iterCtx) :=
          (match parsePlayerFilter? iterStr0 |>.orElse (fun _ => parsePlayerFilter? iterStr) with
           | some pf => some (ForEachSpec.eachPlayer pf, { ctx1 with lastPlayer? := some (.stepPlayers v) })
           | none =>
             match parseObjWithCtx ctx1 iterStr0 with
             | some (oe, c2) => some (ForEachSpec.eachObject oe, { c2 with lastSubject? := some (.stepObjects v) })
             | none =>
               if pLower iterStr0 == "target" then some (.eachTargetSlot, ctx1)
               else none) then
        if let some (body, _, ctx2) := parseSingleClause qp iterCtx bodyStr then
          let isOptPutFromHand :=
            match body with
            | .optional _ none (.moveZone (.inZones { zones := #[.hand], .. } _) (.battlefield _) .put _) .noop _ => true
            | _ => false
          if isOptPutFromHand then
            return some (.forEach pf v body, false, { ctx2 with lastActionVar? := ctx.lastActionVar? })
          return some (.forEach pf v body, true, ctx2)

  -- `", then "` sequential split (also handling `", then searches ..."` inheriting subject player!)
  if let some (lhs, rhs0) := pSplitFirstCI? s0 ", then " then
    if let some (i1, b1, ctx1) := parseSingleClause qp ctx lhs then
      let (v1?, ctxMid) := if b1 then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
      let rhs :=
        if (pLower rhs0).startsWith "searches " then
          "that player " ++ rhs0
        else rhs0
      if let some (i2Raw, b2, ctx2) := parseSingleClause qp ctxMid rhs then
        -- On a spell (`isSpell`), `"Create a <Token>, then put ... on each other <Pred>"` refers
        -- to permanents other than the newly created token (`.diff _ (.stepObjects v1)`),
        -- not `.otherThan .this` (which is the sorcery/instant on the stack — e.g. *Command the Stage*).
        let i2 :=
          match ctx.isSpell, i1, v1?, i2Raw with
          | true, .create (.tokens ..), some v1, .permanent (.modifyCounters cm (.inZones zs (.all ps)) ch) =>
            if ps.any (· == .otherThan .this) then
              let ps' := ps.filter (· != .otherThan .this)
              .permanent (.modifyCounters cm (.diff (.inZones zs (.all ps')) (.stepObjects v1)) ch)
            else i2Raw
          | _, _, _, _ => i2Raw
        let combined := assembleBoundSteps #[(v1?, i1), (none, i2)]
        let ctxOut :=
          match v1?, combined with
          | some v, .bind u _ _ =>
            if u == v then ctx2
            else if ctx2.lastActionVar? == some v then { ctx2 with lastActionVar? := none } else ctx2
          | some v, _ =>
            if ctx2.lastActionVar? == some v then { ctx2 with lastActionVar? := none } else ctx2
          | none, _ => ctx2
        return some (combined, b2, ctxOut)

  -- `"<action> unless <player> pays <cost>"` (CR 118.12a)
  if let some (actStr, unlessTail) := pSplitFirstCI? s0 " unless " then
    if let some (payerStr, costStr) := pSplitFirstCI? unlessTail " pays " then
      if let some (act, b1, ctx1) := parseSingleClause qp ctx actStr then
        if let some (payer, ctx2) := parsePlayerWithCtx ctx1 payerStr then
          let costNorm := replaceCardNameOutsideQuotes costStr ctx.cardName "this permanent"
          if let some cost := parseCostSpec costNorm then
            return some (.unlessPays payer cost act, b1, ctx2)

  -- `"If <cond>, <then>"` (trying both first and last `, ` for comma-containing conditions like `"noncreature, nonland card"`)
  if let some ifRest := pDropPrefixCI? s0 "if " then
    for split? in #[pSplitFirstCI? ifRest ", ", pSplitLastCI? ifRest ", "] do
      if let some (condStr, thenStr) := split? then
        if let some cond := parseInstrCondition? condStr ctx.cardName (some ctx) then
          if let some (tInstr, tb, ctx1) := parseSingleClause qp ctx thenStr then
            return some (.ifCond cond tInstr .noop, tb, ctx1)

  -- Delayed triggers (`When you next ...`, `Until end of turn, when/whenever/at ...`, `Whenever ... this turn, ...`, `At the beginning of the next ...`)
  let low0 := pLower s0
  if low0.startsWith "when you next " || low0.startsWith "until end of turn, when" ||
      low0.startsWith "until end of turn, at " || low0.startsWith "at the beginning of the next " ||
      low0.startsWith "at the beginning of each " ||
      ((low0.startsWith "whenever " || low0.startsWith "when ") && (low0.contains " until " || low0.contains " this turn,")) then
    let (dur, trigStr, oneShot) : DurationExpr × String × Bool :=
      if let some r := pDropPrefixCI? s0 "until end of turn, " then
        (.untilEndOfTurn, r, false)
      else if let some r := pDropPrefixCI? s0 "when you next " then
        (.untilEndOfTurn, "whenever you " ++ r.replace " this turn" "", true)
      else if low0.contains " until your next turn," then
        (.untilNextTurnOf .you, s0.replace " until your next turn" "", false)
      else if low0.contains " until end of turn," then
        (.untilEndOfTurn, s0.replace " until end of turn" "", false)
      else if low0.contains " this turn," then
        (.untilEndOfTurn, s0.replace " this turn," ",", false)
      else if low0.contains " for the rest of the game," then
        (.indefinite, s0.replace " for the rest of the game" "", false)
      else (.untilEndOfTurn, s0, true)
    let hdrs := parseTriggerClauses trigStr ctx.cardName
    if let some hdr := hdrs[0]? then
      let subCtx : DiscourseCtx := { cardName := ctx.cardName, isTrigger := true, lastSubject? := ctx.lastSubject?, lastActionVar? := ctx.lastActionVar?, nextVarIdx := ctx.nextVarIdx }
      if let some (effBody, _, subCtx') := parseSingleClause qp subCtx hdr.effectText then
        let eff : Effect := { targets := subCtx'.toTargetSpec, body := effBody }
        return some (.installEffect (.createDelayedTrigger {
          pattern := hdr.pattern
          grouping := hdr.grouping
          duration := dur
          oneShot
          interveningIf? := hdr.interveningIf?
          effect := eff
        }), false, ctx)

  -- `"You may <rest>"` / `"<player> may <rest>"` (wrapping `each player` / `each opponent` in `forEach`)
  if let some mayRest := pDropPrefixCI? s0 "you may " then
    let ml := pLower mayRest
    if !ml.startsWith "cast " && !ml.startsWith "play " && !ml.startsWith "choose new targets" &&
        !ml.startsWith "activate loyalty abilities" then
      if let some (inner, b, ctx1) := parseSingleClause qp ctx mayRest then
        match inner with
        | .player (.searchLibrary _)
        | .permanent (.setTapped _ _ (some { count := .anyNumber, .. })) =>
          return some (inner, b, ctx1)
        | _ => return some (.optional .you none inner .noop, b, ctx1)
  if let some (whoStr, mayRest0) := pSplitFirstCI? s0 " may " then
    if pLower whoStr != "you" then
      if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
        match who with
        | .matching rel pred =>
          let (v, ctx2) := ctx1.allocLoopVar
          let loopCtx : DiscourseCtx := { ctx2 with lastPlayer? := some (.stepPlayers v) }
          if let some (inner0, b, ctx3) := parseSingleClause qp loopCtx mayRest0 then
            let rec bindLoopPlayer : Instruction → Instruction
              | .moveZone pool (.battlefield .controller) verb mods =>
                if !(pLower mayRest0).contains "under your control" then
                  .moveZone pool (.battlefield (.player (.stepPlayers v))) verb mods
                else .moveZone pool (.battlefield .controller) verb mods
              | .player (.drawCards .you n) => .player (.drawCards (.stepPlayers v) n)
              | .seq xs => .seq (xs.attach.map fun ⟨x, _⟩ => bindLoopPlayer x)
              | other => other
            let inner := bindLoopPlayer inner0
            let isPutFromHand :=
              match inner with
              | .moveZone (.inZones { zones := #[.hand], .. } _) (.battlefield _) .put _ => true
              | _ => false
            if isPutFromHand then
              return some (.forEach (.eachPlayer { relation := rel, pred }) v (.optional (.stepPlayers v) none inner .noop), false, { ctx3 with lastActionVar? := ctx.lastActionVar? })
            return some (.forEach (.eachPlayer { relation := rel, pred }) v (.optional (.stepPlayers v) none inner .noop), b, ctx3)
        | _ =>
          let tryInner :=
            (parseSingleClause qp { ctx1 with lastPlayer? := some who } mayRest0).orElse fun _ =>
              match pDropPrefixCI? mayRest0 (whoStr ++ " ") with
              | some r => parseSingleClause qp ctx1 r
              | none => none
          if let some (inner0, b, ctx2) := tryInner then
            let inner :=
              match inner0 with
              | .player (.searchLibrary spec) =>
                if spec.searcher == .you then
                  let zones' :=
                    if spec.zones.owner == .ofPlayer who then spec.zones
                    else { spec.zones with owner := .ofPlayer who }
                  let dest' :=
                    match spec.dest with
                    | .battlefield .controller => DestZoneSpec.battlefield (.player who)
                    | .hand .controller => DestZoneSpec.hand (.player who)
                    | d => d
                  .player (.searchLibrary { spec with searcher := who, zones := zones', dest := dest' })
                else inner0
              | other => other
            return some (.optional who none inner .noop, b, ctx2)

  -- Try direct atomic parse first
  if let some res := parseAtomicInstr qp ctx s0 then
    return some res

  -- Trailing conditional (`"<clause> if <cond>"`)
  if let some (bodyStr, condStr) := pSplitLastCI? s0 " if " then
    if !(pLower bodyStr).startsWith "if " then
      if let some cond := parseInstrCondition? condStr ctx.cardName (some ctx) then
        if let some (inner, b, ctx1) := parseSingleClause qp ctx bodyStr then
          return some (.ifCond cond inner .noop, b, ctx1)

  -- Compound `"<A>, <B>, and <C>"` (`Archon of Cruelty`, etc.)
  if let some (headA, restBC) := pSplitFirstCI? s0 ", " then
    if (pLower restBC).contains ", and " then
      if let some (midB, tailC) := pSplitFirstCI? restBC ", and " then
        if let some (i1, b1, ctx1) := parseAtomicInstr qp ctx headA then
          let addPlayerSubj (s : String) : String :=
            let ml := pLower s
            if ml.startsWith "lose " || ml.startsWith "gain " || ml.startsWith "draw " then "you " ++ s
            else if ml.startsWith "discards " || ml.startsWith "loses " || ml.startsWith "gains " ||
                ml.startsWith "draws " || ml.startsWith "sacrifices " || ml.startsWith "mills " then
              match ctx1.lastPlayer? with
              | some _ => "that player " ++ s
              | none => s
            else s
          if let some (i2, b2, ctx2) := parseSingleClause qp ctx1 (addPlayerSubj midB) then
            if let some (i3, b3, ctx3) := parseSingleClause qp ctx2 (addPlayerSubj tailC) then
              return some (flattenInstrSeq #[i1, i2, i3], b1 || b2 || b3, ctx3)

  -- Compound `"<A> and <B>"`
  if let some (a, b) := pSplitFirstCI? s0 " and " then
    if let some (i1, b1, ctx1) := parseAtomicInstr qp ctx a then
      let bCandidate :=
        let bl := pLower b
        if bl.startsWith "lose " || bl.startsWith "gain " then "you " ++ b
        else if bl.startsWith "loses " || bl.startsWith "gains " || bl.startsWith "discards " || bl.startsWith "draws " then
          match ctx1.lastPlayer? with
          | some _ => "that player " ++ b
          | none => b
        else if bl.startsWith "can't " then "this permanent " ++ b
        else b
      if let some (i2, b2, ctx2) := parseSingleClause qp ctx1 bCandidate then
        return some (flattenInstrSeq #[i1, i2], b1 || b2, ctx2)

  return none

/-! ### Multi-Sentence & Modal Effect Parser -/

private def parseModalHeader? (header : String) : Option ModalSpec := Id.run do
  let h := pClean header
  let hl := pLower h
  if hl.contains "teamwork" && hl.contains "choose both instead" then
    return some {
      minModes := .const 1
      maxModes := .const 1
      altCountIf? := some (.castPred (.teamworkPaid .this), .const 2, .const 2)
      modes := #[]
    }
  if let some (_, afterIf) := pSplitFirstCI? h "if you control " then
    if let some (subPart0, _) := pSplitFirstCI? afterIf ", you may choose two instead" then
      let subPart := (pDropSuffixCI? subPart0 " as you cast this spell").getD subPart0
      let subWord := ((pDropPrefixCI? subPart "an ").orElse fun _ => pDropPrefixCI? subPart "a ") |>.getD subPart
      if let some sub := CardSubtype.ofOracle? subWord then
        return some {
          minModes := .const 1
          maxModes := .const 1
          altCountIf? := some (.playerPred .you (.controls { zones := .battlefield, pred := .hasSubtype (.literal sub) } (.const 1)), .const 1, .const 2)
          modes := #[]
        }
  if hl.contains "choose one that hasn't been chosen this turn" then
    return some { minModes := .const 1, maxModes := .const 1, unusedThisTurn := true, modes := #[] }
  if hl.contains "choose one that hasn't been chosen" then
    return some { minModes := .const 1, maxModes := .const 1, unusedEver := true, modes := #[] }
  if hl.contains "choose up to x" then
    return some { minModes := .const 0, maxModes := .chosenX, modes := #[] }
  if hl.contains "choose up to that many" then
    return some { minModes := .const 0, maxModes := .eventAmount, modes := #[] }
  if hl.contains "choose up to two" then
    return some { minModes := .const 0, maxModes := .const 2, modes := #[] }
  if hl.contains "choose one or both" then
    return some { minModes := .const 1, maxModes := .const 2, modes := #[] }
  if hl.contains "choose two" then
    return some { minModes := .const 2, maxModes := .const 2, modes := #[] }
  if hl.contains "choose one" then
    return some { minModes := .const 1, maxModes := .const 1, modes := #[] }
  return none

/-- Parse a complete multi-sentence one-shot Oracle text into `Effect`. -/
partial def parseCompositionalEffect (qp : QuotedAbilityParsers) (raw : String)
    (cardName : String := "") (isTrigger : Bool := false)
    (isSelfTrigger : Bool := false)
    (initLastPlayer? : Option PlayerExpr := none)
    (initTriggerPlayerRole? : Option PlayerExpr := none)
    (attachedHostCtx : Bool := false)
    (initLastActionVar? : Option VarId := none)
    (isSpell : Bool := false) : Option Effect := Id.run do
  let cleaned := (preprocessOracleLine raw).trimAscii.copy
  if cleaned.isEmpty then return none

  -- 1. Modal bullets `•` (including target-only bullet lists like `Call Damage Control`)
  if cleaned.contains "•" then
    let parts := cleaned.splitOn "•" |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
    match parts with
    | hdr :: modeTexts =>
      if modeTexts.isEmpty then return none
      -- Target-only bullet shorthand (`"Choose up to two. Return those cards from your graveyard to your hand. • Target artifact card. • ..."`)
      if (pLower hdr).contains "return those cards from your graveyard to your hand" &&
          modeTexts.all (fun m => (pLower (pClean m)).startsWith "target ") then
        let mut typePreds : Array ObjectPred := #[]
        for mTxt in modeTexts do
          if let some np := parseNounPhrase (pClean mTxt) then
            let cleanedPred :=
              match np.filter.pred with
              | .all ps =>
                let kept := ps.filter (· != .isKind .card)
                match kept.toList with | [p] => p | _ => .all kept
              | p => p
            typePreds := typePreds.push cleanedPred
        if !typePreds.isEmpty then
          let maxN : Nat :=
            if (pLower hdr).contains "up to two" then 2
            else if (pLower hdr).contains "up to three" then 3
            else 1
          let slot : TargetSlot := {
            domain := .object .yourGraveyard (.all #[.any typePreds, .isKind .card])
            count := .upTo maxN
          }
          return some { targets := TargetSpec.single slot, body := .moveZone .allTargets (.hand .controller) .returnToHand {} }
      let some baseSpec := parseModalHeader? hdr | return none
      let mut modes : Array Effect := #[]
      for mTxt in modeTexts do
        let mBody := (extractLeadingLabel mTxt).snd
        let some mEff := parseCompositionalEffect qp mBody cardName isTrigger isSelfTrigger initLastPlayer? initTriggerPlayerRole? attachedHostCtx initLastActionVar? isSpell | return none
        modes := modes.push mEff
      return some { targets := .none, body := .chooseModes { baseSpec with modes } }
    | _ => return none

  -- 2. Split top-level sentences (quote-aware!)
  let sents := splitTopLevelSentences cleaned
  if sents.isEmpty then return none

  let mut ctx : DiscourseCtx := {
    cardName
    isTrigger
    isSelfTrigger
    isSpell
    attachedHostCtx
    lastPlayer? := initLastPlayer?
    triggerPlayerRole? := initTriggerPlayerRole?
    lastActionVar? := initLastActionVar?
    nextVarIdx :=
      let a := initLastActionVar?.map (·.idx + 1) |>.getD 0
      let b := match initLastPlayer? with | some (.stepPlayers v) => v.idx + 1 | _ => 0
      max a b
  }
  let mut steps : Array (Option VarId × Instruction) := #[]
  let mut idx : Nat := 0

  while idx < sents.size do
    let sent := pClean sents[idx]!
    let sLow := pLower sent

    -- 2a0. Standalone `"Exile <this spell>."` on instants/sorceries (`Worlds Within Worlds`, etc.)
    if isSpell then
      let selfExileNorm := pLower (replaceCardNameOutsideQuotes sent cardName "this spell")
      if selfExileNorm == "exile this spell" || selfExileNorm == "exile this card" then
        steps := steps.push (none, .installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack))
        idx := idx + 1
        continue

    -- 2a. Multi-sentence `Add <mana>. Spend this mana only to ...` (`Desolation of Smaug`)
    if sLow.startsWith "add " && idx + 1 < sents.size && (pLower sents[idx + 1]!).startsWith "spend this mana only" then
      if let some mp := parseManaProductionSpec #[sents[idx]!, sents[idx + 1]!] cardName then
        steps := steps.push (none, .player (.addMana .you mp))
        idx := idx + 2
        continue

    -- 2b. Multi-sentence `InspectLibrarySpec`
    if let some (instr, consumed, ctx1) := parseInspectLibrarySeq? ctx sents idx then
      let (v, ctx2) := ctx1.allocVar
      let revPred? : Option ObjectPred :=
        match instr with
        | .player (.inspectLibrary { source := .revealUntil _ pred _ _, action := .none, .. }) => some pred
        | _ => none
      steps := steps.push (some v, instr)
      ctx := { ctx2 with lastRevealUntilPred? := revPred? }
      idx := idx + consumed
      continue

    -- 2c. Multi-sentence `SearchLibrarySpec` (including `", shuffle, then <follow>"` and `"You may search ..."`)
    if let some (searchHead, followTail) := pSplitFirstCI? sent ", shuffle, then " then
      if let some (sInstr, _, ctx1) := parseSearchLibrarySeq? ctx #[searchHead ++ ", then shuffle"] 0 then
        let (v, ctx2) := ctx1.allocVar
        if let some (fInstr, fb, ctx3) := parseSingleClause qp ctx2 followTail then
          let (vf?, ctx4) := if fb then let (vf, c) := ctx3.allocVar; (some vf, c) else (none, ctx3)
          steps := steps.push (some v, sInstr)
          steps := steps.push (vf?, fInstr)
          ctx := ctx4
          idx := idx + 1
          continue
    if let some (instr, consumed, ctx1) := parseSearchLibrarySeq? ctx sents idx then
      let (v, ctx2) := ctx1.allocVar
      steps := steps.push (some v, instr)
      ctx := ctx2
      idx := idx + consumed
      continue
    if let some maySearch := pDropPrefixCI? sent "you may search " then
      let mut fakeSents : Array String := #["search " ++ maySearch]
      for k in [idx + 1 : sents.size] do
        fakeSents := fakeSents.push sents[k]!
      if let some (instr, consumed, ctx1) := parseSearchLibrarySeq? ctx fakeSents 0 then
        let wrapped :=
          match instr with
          | .player (.searchLibrary { dest := .battlefield _, .. }) =>
            Instruction.optional .you none instr .noop
          | _ => instr
        let (v, ctx2) := ctx1.allocVar
        steps := steps.push (some v, wrapped)
        ctx := ctx2
        idx := idx + consumed
        continue
    if let some (whoStr, maySearch) := pSplitFirstCI? sent " may search " then
      if pLower whoStr != "you" then
        if let some (who, ctx0) := parsePlayerWithCtx ctx whoStr then
          let mut fakeSents : Array String := #["search " ++ maySearch]
          for k in [idx + 1 : sents.size] do
            fakeSents := fakeSents.push sents[k]!
          if let some (instr0, consumed, ctx1) := parseSearchLibrarySeq? { ctx0 with lastPlayer? := some who } fakeSents 0 then
            let instr :=
              match instr0 with
              | .player (.searchLibrary spec) =>
                let zones' := if spec.zones.owner == .ofPlayer who then spec.zones else .libraryOf who
                let dest' := match spec.dest with | .battlefield .controller => .battlefield (.player who) | d => d
                .player (.searchLibrary { spec with searcher := who, zones := zones', dest := dest' })
              | other => other
            let (v, ctx2) := ctx1.allocVar
            steps := steps.push (some v, .optional who none instr .noop)
            ctx := ctx2
            idx := idx + consumed
            continue

    -- 2c1. `", then reveal cards ..."` / `", then look at ..."` spanning this sentence + following sentences (`Mass Polymorph`, `Nick Fury`)
    if (sLow.contains ", then reveal cards from the top of " || sLow.contains ", then look at the top ") then
      if let some (lhsS, rhsS) := pSplitFirstCI? sent ", then " then
        if let some (i1, b1, ctx1) := parseSingleClause qp ctx lhsS then
          let (v1?, ctxMid) := if b1 then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
          let mut fakeSents : Array String := #[rhsS]
          for k in [idx + 1 : sents.size] do
            fakeSents := fakeSents.push sents[k]!
          if let some (inspI, consumed, ctx2) := parseInspectLibrarySeq? ctxMid fakeSents 0 then
            let (v2, ctx3) := ctx2.allocVar
            steps := steps.push (v1?, i1)
            steps := steps.push (some v2, inspI)
            ctx := ctx3
            idx := idx + consumed
            continue

    -- 2c2. 3-sentence `"choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until ..."` (`Cloak and Dagger`)
    if sLow == "choose target opponent and up to one target creature they control" && idx + 2 < sents.size then
      let s1 := pLower (pClean sents[idx + 1]!)
      let s2 := pLower (pClean sents[idx + 2]!)
      if s1 == "they reveal their hand" && s2.startsWith "you may exile a nonland card from their hand or the chosen creature until " then
        let (_, ctx1) := ctx.pushTargetSlot { domain := .player .opponent, count := .upTo 1 }
        steps := steps.push (none, .player (.reveal (.target 0) (.inZones (.handOf (.target 0)) .anyObject)))
        steps := steps.push (none, Instruction.ifThen (.exists .this) (Instruction.exile (.target 1) { exileUntilSourceLeaves := true }))
        ctx := ctx1
        idx := idx + 3
        continue

    -- 2c3. 2-sentence keyword-counter copying (`Super-Adaptoid`: `"If that creature has haste and ... doesn't, put a haste counter on .... Do the same for ..."`)
    if sLow.contains "has haste and " && idx + 1 < sents.size && (pLower (pClean sents[idx + 1]!)).startsWith "do the same for " then
      let srcObj := ctx.lastSubject?.getD (.target (ctx.lastTargetSlot?.getD 0))
      steps := steps.push (none, .permanent (.modifyCounters (.copyMissingKeywords srcObj) .this))
      idx := idx + 2
      continue

    -- 2d. `"<opponent> reveals [their hand / a number of cards from their hand equal to V]. You choose <card> from it/them. <who> discards/exiles that card."` (`Klaw`, `Null Summoner`, `Stinging Vitriol`)
    if (sLow.endsWith " reveals their hand" || sLow.contains " reveals a number of cards from their hand equal to ") && idx + 2 < sents.size then
      let s1 := pClean sents[idx + 1]!
      let s2 := pLower (pClean sents[idx + 2]!)
      let isDiscard := s2.contains "discards that card" || s2.contains "discard that card"
      let isExile := s2.contains "exile that card" || s2.contains "exiles that card"
      if (pLower s1).startsWith "you choose " && (isDiscard || isExile) then
        if let some (whoStr, eqStr) := pSplitFirstCI? sent " reveals a number of cards from their hand equal to " then
          if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
            if let some cnt := parseValueWithCtx ctx1 eqStr then
              steps := steps.push (none, .player (.reveal who (.inZones (.handOf who) .anyObject) (some (.exact cnt))))
              ctx := ctx1
              idx := idx + 3
              continue
        let whoStr := (pDropSuffixCI? sent " reveals their hand").getD ""
        if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
          let whatRaw := ((pDropPrefixCI? s1 "you choose ").bind fun r =>
            (pDropSuffixCI? r " from it").orElse fun _ => some r) |>.getD "a card"
          let whatClean := ((pDropPrefixCI? whatRaw "a ").orElse fun _ => pDropPrefixCI? whatRaw "an ") |>.getD whatRaw
          let whatCore := (pDropSuffixCI? whatClean " card").getD whatClean
          let pred : ObjectPred :=
            if whatCore.isEmpty || pLower whatCore == "card" then .anyObject
            else (parseNounPhrase (whatCore ++ " card")).map (·.filter.pred) |>.getD .anyObject
          let ch : MoveChoiceSpec := { chooser := .player .you, count := .exact (.const 1), revealFirst := true }
          let (dest, verb) := if isExile then (DestZoneSpec.exile, ZoneVerb.exile) else (DestZoneSpec.graveyard, ZoneVerb.discard)
          steps := steps.push (none, .moveZone (.inZones (.handOf who) pred) dest verb { choice? := some ch })
          ctx := ctx1
          idx := idx + 3
          continue

    -- 2d2. Multi-sentence reflexive trigger (`"When you do, <s1>. <s2>..."`, `"When one or more ... this way, ..."`, `"When you discard ... this way, ..."`)
    let reflPrefix? : Option (Option ObjectPred × String) :=
      if let some r := pDropPrefixCI? sent "when one or more cards are milled this way, " then some (none, r)
      else if let some r := pDropPrefixCI? sent "when you do, " then
        if idx + 1 < sents.size then some (none, r) else none
      else if let some afterWhen := pDropPrefixCI? sent "when " then
        if let some (evPart, bodyPart) := pSplitFirstCI? afterWhen " this way, " then
          let filt? : Option ObjectPred :=
            if let some dRest := pDropPrefixCI? evPart "you discard one or more " then
              (parseNounPhrase dRest).map (·.filter.pred)
            else none
          some (filt?, bodyPart)
        else none
      else none
    if let some (filt?, reflStart) := reflPrefix? then
      let mut reflSents : Array String := #[reflStart]
      for k in [idx + 1 : sents.size] do
        reflSents := reflSents.push (pClean sents[k]!)
      let reflJoined := String.intercalate ". " reflSents.toList
      if let some reflEff := parseCompositionalEffect qp reflJoined cardName true then
        let v := ctx.lastActionVar?.getD ⟨0⟩
        let cond : Condition :=
          match filt? with
          | some fp => .exists (.filter (.stepObjects v) fp)
          | none => .stepSucceeded v
        steps := steps.push (none, .ifCond cond (mkReflexiveWhenYouDo reflEff) .noop)
        idx := sents.size
        continue

    -- 2d3. Multi-sentence delayed trigger (`"Until end of turn, at the beginning of ..."` OR `"At the beginning of the next end step, <inspect/multi-sent>"`)
    if (sLow.startsWith "until end of turn, at the beginning of " ||
        (sLow.startsWith "at the beginning of the next end step, " &&
          (sLow.contains "reveal cards " || sLow.contains "look at " || idx + 1 < sents.size))) then
      let trigStr := (pDropPrefixCI? sent "until end of turn, ").getD sent
      let hdrs := parseTriggerClauses trigStr cardName
      if let some hdr := hdrs[0]? then
        let mut bodySents : Array String := #[hdr.effectText]
        for k in [idx + 1 : sents.size] do
          bodySents := bodySents.push (pClean sents[k]!)
        let bodyJoined := String.intercalate ". " bodySents.toList
        if let some bodyEff := parseCompositionalEffect qp bodyJoined cardName true false none none false ctx.lastActionVar? then
          let isOneShot := sLow.startsWith "at the beginning of the next " || sLow.startsWith "when you next "
          steps := steps.push (none, .installEffect (.createDelayedTrigger {
            pattern := hdr.pattern
            grouping := hdr.grouping
            duration := .untilEndOfTurn
            oneShot := isOneShot
            interveningIf? := hdr.interveningIf?
            effect := bodyEff
          }))
          idx := sents.size
          continue

    -- 2d4. Multi-sentence `"For each a player / an opponent, <s1>. <s2>"` (`Variable Chaser` / `Arc of Fortune`, `Garruk, Veiled Butcher`)
    if let some forRest := pDropPrefixCI? sent "for each " then
      if idx + 1 < sents.size then
        let nxt := pClean sents[idx + 1]!
        let nxtLow := pLower nxt
        if nxtLow.startsWith "if that player does, " || nxtLow.startsWith "if the number of those objects " then
          if let some (iterStr0, bodyStart) := pSplitFirstCI? forRest ", " then
            let iterStr := ((pDropPrefixCI? iterStr0 "a ").orElse fun _ => pDropPrefixCI? iterStr0 "an ") |>.getD iterStr0
            if let some pf := (parsePlayerFilter? iterStr0).orElse (fun _ => parsePlayerFilter? iterStr) then
              let (v, ctx1) := ctx.allocVar
              let subJoined := bodyStart ++ ". " ++ nxt
              if let some subEff := parseCompositionalEffect qp subJoined cardName isTrigger false (some (.stepPlayers v)) then
                steps := steps.push (none, .forEach (.eachPlayer pf) v subEff.body)
                ctx := ctx1
                idx := idx + 2
                continue

    -- 2d4b. `"Each opponent discards <N> cards. For each opponent who didn't discard <M> <pred> cards this way, <follow>."` (`Garruk, Veiled Butcher`)
    if let some discRest := pDropPrefixCI? sent "each opponent discards " then
      if idx + 1 < sents.size then
        let nxt := pClean sents[idx + 1]!
        if let some afterWho := pDropPrefixCI? nxt "for each opponent who didn't discard " then
          if let some (reqStr, followStr) := pSplitFirstCI? afterWho " this way, " then
            let nStr := ((pDropSuffixCI? discRest " cards").orElse fun _ => pDropSuffixCI? discRest " card") |>.getD discRest
            if let some n := parseNatWord? nStr then
              let ws := pWords reqStr
              if ws.size >= 2 then
                if let some m := parseNatWord? ws[0]! then
                  let predRaw := String.intercalate " " (ws.extract 1 ws.size).toList
                  let predCore := ((pDropSuffixCI? predRaw " cards").orElse fun _ => pDropSuffixCI? predRaw " card") |>.getD predRaw
                  let filtPred : ObjectPred :=
                    if pLower predCore == "nonland" then .not (.hasType .land)
                    else (parseNounPhrase ("a " ++ predCore)).map (·.filter.pred) |>.getD .anyObject
                  if let some (followInstr, _, ctx1) := parseSingleClause qp ctx followStr then
                    let (vLoop, ctx2) := ctx1.allocLoopVar
                    let (vDisc, ctx3) := ctx2.allocLoopVar
                    let body := Instruction.bind vDisc (Instruction.discardFixed n (.stepPlayers vLoop))
                      (.ifCond (.cmp .lt (.aggregate .count .one (.filter (.stepObjects vDisc) filtPred)) (.const m)) followInstr .noop)
                    steps := steps.push (none, .forEach (.eachPlayer .opponent) vLoop body)
                    ctx := ctx3
                    idx := idx + 2
                    continue

    -- 2e. `"If <castPred>, instead choose <altTarget>."` (`Too Evil to Stay Dead`, `The Eagles Are Coming!`)
    if let some ifRest := pDropPrefixCI? sent "if " then
      if let some (condStr, insteadRest) := pSplitFirstCI? ifRest ", instead choose " then
        if let some cond := parseInstrCondition? condStr cardName (some ctx) then
          if let some altSlot := parseTargetSlot insteadRest then
            if !ctx.slots.isEmpty then
              let lastI := ctx.slots.size - 1
              ctx := { ctx with slots := ctx.slots.set! lastI { ctx.slots[lastI]! with altDomainIf? := some (cond, altSlot.domain) } }
              idx := idx + 1
              continue

    -- 2f. Multi-sentence replacement / bonus (`"If <cond>, <s1>... instead."`, `"If <cond>, instead <s1>."`, `"<alt> instead if <cond>."`, `"If <cond>, [it] also <bonus>."`)
    if !steps.isEmpty then
      -- Form 0: `"If <cond>, instead create N of those tokens that are tapped and attacking"` (`Andúril`)
      if let some ifRest := pDropPrefixCI? sent "if " then
        if let some (condStr, insteadRest) := pSplitFirstCI? ifRest ", instead create " then
          if (pLower insteadRest).contains "of those tokens" && (pLower insteadRest).contains "attacking" then
            if let some cond := parseInstrCondition? condStr cardName (some { ctx with lastActionVar? := none }) then
              let (v?, prev) := steps[steps.size - 1]!
              match prev with
              | .create (.tokens w c sp m) =>
                let alt := Instruction.create (.tokens w c sp { m with tapped := true, attacking := true })
                steps := steps.set! (steps.size - 1) (v?, .ifCond cond alt prev)
                idx := idx + 1
                continue
              | _ => pure ()
      -- Form 1: `"<alt> instead if <cond>"` (`We Say Thee Nay!`)
      if let some (altPart, condPart) := pSplitFirstCI? sent " instead if " then
        if let some cond := parseInstrCondition? condPart cardName (some ctx) then
          if let some altEff := parseCompositionalEffect qp altPart cardName isTrigger then
            let prevBody := assembleBoundSteps steps
            steps := #[(none, .ifCond cond altEff.body prevBody)]
            idx := idx + 1
            continue
      -- Form 2: `"If <cond>, [also | <subj> also] <bonus>"` (`Moment of Glory`, `Repulsor Blast`, `Team Tactics`)
      if let some ifRest := pDropPrefixCI? sent "if " then
        if let some (condStr, bonusRaw) := pSplitFirstCI? ifRest ", " then
          let cleanedBonus? : Option String :=
            if let some r := pDropPrefixCI? bonusRaw "also " then some r
            else if bonusRaw.contains " also " then some (bonusRaw.replace " also " " ")
            else none
          if let some bonusStr := cleanedBonus? then
            if let some cond := parseInstrCondition? condStr cardName (some ctx) then
              if let some (bonusInstr, bBonus, ctx1) := parseSingleClause qp ctx bonusStr then
                let (v?, ctx2) := if bBonus then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
                steps := steps.push (v?, .ifCond cond bonusInstr .noop)
                ctx := ctx2
                idx := idx + 1
                continue
      -- Form 3: `"If <cond>, instead <alt>"` (`Cruel Alliance`)
      if let some ifRest := pDropPrefixCI? sent "if " then
        if let some (condStr, insteadBody) := pSplitFirstCI? ifRest ", instead " then
          if let some cond := parseInstrCondition? condStr cardName (some ctx) then
            if let some altEff := parseCompositionalEffect qp insteadBody cardName isTrigger then
              let prevBody := assembleBoundSteps steps
              if ctx.slots.size == 1 && altEff.targets.slots.size == 1 &&
                  ctx.slots[0]!.domain != altEff.targets.slots[0]!.domain then
                ctx := { ctx with slots := ctx.slots.set! 0 { ctx.slots[0]! with altDomainIf? := some (cond, altEff.targets.slots[0]!.domain) } }
              steps := #[(none, .ifCond cond altEff.body prevBody)]
              idx := idx + 1
              continue
      -- Form 4: `"If <cond>, <s1>. <s2>... instead."`
      if let some ifRest := pDropPrefixCI? sent "if " then
        let mut insteadIdx? : Option Nat := none
        for k in [idx : sents.size] do
          if (pLower (pClean sents[k]!)).endsWith " instead" then
            insteadIdx? := some k
            break
        if let some endK := insteadIdx? then
          if let some (condStr, firstThen) := pSplitFirstCI? ifRest ", " then
            if let some cond := parseInstrCondition? condStr cardName (some ctx) then
              let mut thenSents : Array String := #[]
              if endK == idx then
                let trimmed := (pDropSuffixCI? firstThen " instead").getD firstThen
                thenSents := #[trimmed]
              else
                thenSents := thenSents.push firstThen
                for k in [idx + 1 : endK] do
                  thenSents := thenSents.push (pClean sents[k]!)
                let lastRaw := pClean sents[endK]!
                thenSents := thenSents.push ((pDropSuffixCI? lastRaw " instead").getD lastRaw)
              let thenJoined := String.intercalate ". " thenSents.toList
              let altBodyAndTargets? : Option (Instruction × TargetSpec) :=
                if thenSents.size == 1 && !(pLower thenJoined).contains "target " then
                  (parseSingleClause qp { ctx with lastActionVar? := none } thenJoined).map fun (i, _, _) => (i, .none)
                else
                  (parseCompositionalEffect qp thenJoined cardName isTrigger).map fun e => (e.body, e.targets)
              if let some (altBody, altTargets) := altBodyAndTargets? then
                let prevSteps := steps
                let prevBody := assembleBoundSteps prevSteps
                if ctx.slots.size == 1 && altTargets.slots.size == 1 &&
                    ctx.slots[0]!.domain != altTargets.slots[0]!.domain then
                  ctx := { ctx with slots := ctx.slots.set! 0 { ctx.slots[0]! with altDomainIf? := some (cond, altTargets.slots[0]!.domain) } }
                steps := #[(none, .ifCond cond altBody prevBody)]
                idx := endK + 1
                continue

    -- 2g. Two/three-sentence `"[Then ]You may <cost/action>. If you do, <onYes>.[ Otherwise, <onNo>.]"`
    -- and `"[Then ]You may <cost/action>. When you do, <reflexive>."`
    -- and `"[Then ]<who> may <action>. If <who> does/doesn't, ..."`
    let sentNoThenMay := (pDropPrefixCI? sent "then ").getD sent
    if let some mayBody0 := pDropPrefixCI? sentNoThenMay "you may " then
      if idx + 1 < sents.size then
        let nxt := pClean sents[idx + 1]!
        let (mayBody, maxTimes) : String × Nat :=
          match pSplitLastCI? mayBody0 " up to " with
          | some (a, b) =>
            match pDropSuffixCI? b " times" with
            | some nStr => match parseNatWord? nStr with | some n => (a, n) | none => (mayBody0, 1)
            | none => (mayBody0, 1)
          | none => (mayBody0, 1)
        let hasNamedSelf := !cardName.isEmpty && (pLower mayBody).contains ("named " ++ pLower cardName)
        let costFullNorm := if hasNamedSelf then mayBody else replaceCardNameOutsideQuotes mayBody cardName "this permanent"
        let costStrippedNorm :=
          let mb := (pDropPrefixCI? mayBody "pay ").getD mayBody
          if hasNamedSelf then mb else replaceCardNameOutsideQuotes mb cardName "this permanent"
        let parsedCost? :=
          if pLower costFullNorm == "exile this permanent" then none
          else (parseCostSpec costFullNorm).orElse (fun _ => parseCostSpec costStrippedNorm)
        if let some followStr := pDropPrefixCI? nxt "if you do, " then
          let mut onNo : Instruction := .noop
          let mut extraConsumed : Nat := 0
          if let some cost := parsedCost? then
            if let some (onYes, bYes, ctx1) := parseSingleClause qp ctx followStr then
              if idx + 2 < sents.size then
                let s2 := pClean sents[idx + 2]!
                if let some elseStr := (pDropPrefixCI? s2 "otherwise, ").orElse (fun _ => pDropPrefixCI? s2 "if you don't, ") then
                  if let some (eInstr, _, ctx2) := parseSingleClause qp ctx1 elseStr then
                    onNo := eInstr; ctx := ctx2; extraConsumed := 1
              if extraConsumed == 0 then ctx := ctx1
              let (v?, ctxA) := if bYes then let (v, c) := ctx.allocVar; (some v, c) else (none, ctx)
              steps := steps.push (v?, .optional .you (some cost) onYes onNo maxTimes)
              ctx := ctxA
              idx := idx + 2 + extraConsumed
              continue
          if let some (actInstr, b1, ctx1) := parseSingleClause qp ctx mayBody then
            let (v1?, ctxMid) := if b1 then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
            if let some (onYes, _, ctx2) := parseSingleClause qp ctxMid followStr then
              let combined := assembleBoundSteps #[(v1?, actInstr), (none, onYes)]
              steps := steps.push (none, .optional .you none combined .noop maxTimes)
              ctx := ctx2
              idx := idx + 2
              continue
        else if let some reflStr := pDropPrefixCI? nxt "when you do, " then
          -- Collect remaining sentences into reflexive trigger when followed by `"If excess damage ..."` (`Bolg of the North`)
          let reflFull :=
            if idx + 2 < sents.size && (pLower (pClean sents[idx + 2]!)).startsWith "if excess damage " then
              reflStr ++ ". " ++ pClean sents[idx + 2]!
            else reflStr
          let extraR := if reflFull != reflStr then 1 else 0
          if let some cost0 := parsedCost? then
            if let some reflEff := parseCompositionalEffect qp reflFull cardName true then
              let isModalRefl := match reflEff.body with | .chooseModes _ => true | _ => false
              let (cost, reflInstr) : CostSpec × Instruction :=
                if reflEff.targets.isEmpty && !isModalRefl then
                  (cost0, reflEff.body)
                else
                  let isBolgSacRefl : Bool :=
                    match reflEff.body with
                    | .bind _ (.damage (.deal _ _ (.objectStat .power .triggerSubject) _)) _ => true
                    | _ => false
                  match cost0.items.toList with
                  | [.sacrifice _ (.filter pred)] =>
                    if isBolgSacRefl then
                      ({ cost0 with bindVar? := some ⟨0⟩ },
                        .queueReflexiveTrigger { word := .when, pattern := .sacrifice .you pred, effect := reflEff })
                    else
                      (cost0, mkReflexiveWhenYouDo reflEff)
                  | _ => (cost0, mkReflexiveWhenYouDo reflEff)
              steps := steps.push (none, .optional .you (some cost) reflInstr .noop maxTimes)
              idx := idx + 2 + extraR
              continue
          if let some (actInstr, b1, ctx1) := parseSingleClause qp ctx mayBody then
            let (v1?, _) := if b1 then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
            if let some reflEff := parseCompositionalEffect qp reflFull cardName true then
              let combined := assembleBoundSteps #[(v1?, actInstr), (none, mkReflexiveWhenYouDo reflEff)]
              steps := steps.push (none, .optional .you none combined .noop maxTimes)
              ctx := ctx1
              idx := idx + 2 + extraR
              continue
        else if let some elseStr := (pDropPrefixCI? nxt "if you don't, ").orElse (fun _ => pDropPrefixCI? nxt "otherwise, ") then
          if let some (actInstr, _, ctx1) := parseSingleClause qp ctx mayBody then
            if let some (elseInstr, eb, ctx2) := parseSingleClause qp ctx1 elseStr then
              let (v?, ctxA) := if eb then let (v, c) := ctx2.allocVar; (some v, c) else (none, ctx2)
              steps := steps.push (v?, .optional .you none actInstr elseInstr maxTimes)
              ctx := ctxA
              idx := idx + 2
              continue
    -- `"[Then ]<who> may <act>. If <who> does/doesn't, <onYes/onNo>.[ Otherwise / If they didn't ..., <onNo>.]"`
    if let some (whoStr, mayAct0) := pSplitFirstCI? sentNoThenMay " may " then
      if pLower whoStr != "you" && idx + 1 < sents.size then
        let nxt := pClean sents[idx + 1]!
        let mayAct := (pDropPrefixCI? mayAct0 "have you ").getD mayAct0
        if let some elseStr := pDropPrefixCI? nxt "otherwise, " then
          if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
            if let some (actInstr, _, ctx2) := parseSingleClause qp ctx1 mayAct then
              if let some (eInstr, eb, ctx3) := parseSingleClause qp ctx2 elseStr then
                let (v?, ctxA) := if eb then let (v, c) := ctx3.allocVar; (some v, c) else (none, ctx3)
                steps := steps.push (v?, .optional who none actInstr eInstr)
                ctx := ctxA
                idx := idx + 2
                continue
        else if let some (_, afterIfDo) := (pSplitFirstCI? nxt " does, ").orElse (fun _ => pSplitFirstCI? nxt " do, ") then
          if (pLower nxt).startsWith "if " then
            if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
              if let some (actInstr, b1, ctx2) := parseSingleClause qp { ctx1 with lastPlayer? := some who } mayAct then
                let (v1?, ctxMid) := if b1 then let (v, c) := ctx2.allocVar; (some v, c) else (none, ctx2)
                if let some (onYes, _, ctx3) := parseSingleClause qp ctxMid afterIfDo then
                  let mut onNo : Instruction := .noop
                  let mut extra := 0
                  if idx + 2 < sents.size then
                    let s2 := pClean sents[idx + 2]!
                    let eStr? : Option String :=
                      (pDropPrefixCI? s2 "otherwise, ").orElse fun _ =>
                      if (pLower s2).startsWith "if they didn't " || (pLower s2).startsWith "if that player didn't " then
                        (pSplitFirstCI? s2 ", ").map Prod.snd
                      else none
                    if let some eStr := eStr? then
                      if let some (eI, _, ctx4) := parseSingleClause qp ctx3 eStr then
                        onNo := eI; ctx := ctx4; extra := 1
                  if extra == 0 then ctx := ctx3
                  let combined := assembleBoundSteps #[(v1?, actInstr), (none, onYes)]
                  steps := steps.push (none, .optional who none combined onNo)
                  idx := idx + 2 + extra
                  continue
        else if let some (_, afterIfDont) := (pSplitFirstCI? nxt " don't, ").orElse (fun _ => pSplitFirstCI? nxt " doesn't, ") then
          if (pLower nxt).startsWith "if " then
            if let some (who, ctx1) := parsePlayerWithCtx ctx whoStr then
              let costNorm := replaceCardNameOutsideQuotes ((pDropPrefixCI? mayAct "pay ").getD mayAct) cardName "this permanent"
              if let some cost := parseCostSpec costNorm then
                if let some (onNo, _, ctx2) := parseSingleClause qp { ctx1 with lastPlayer? := some who } afterIfDont then
                  let instr :=
                    if (pLower mayAct).startsWith "pay " then
                      Instruction.unlessPays who cost onNo
                    else
                      Instruction.optional who (some cost) .noop onNo
                  steps := steps.push (none, instr)
                  ctx := ctx2
                  idx := idx + 2
                  continue
              -- Non-cost optional (`Palantír of Orthanc`: `"Then target opponent may have you draw a card. If that player doesn't, you mill X cards..."`)
              if let some (actInstr, _, ctx2) := parseSingleClause qp { ctx1 with lastPlayer? := some who } mayAct then
                if let some (onNo, _, ctx3) := parseSingleClause qp ctx2 afterIfDont then
                  steps := steps.push (none, .optional who none actInstr onNo)
                  ctx := ctx3
                  idx := idx + 2
                  continue

    -- 2h. `"If <cond>, <then>. Otherwise, <else>."` AND `"<then> if <cond>.[ Otherwise, <else>.]"`
    if let some ifRest := pDropPrefixCI? sent "if " then
      if idx + 1 < sents.size then
        let nxt := pClean sents[idx + 1]!
        if let some elseStr := pDropPrefixCI? nxt "otherwise, " then
          if let some (condStr, thenStr) := pSplitFirstCI? ifRest ", " then
            if let some cond := parseInstrCondition? condStr cardName (some ctx) then
              if idx + 2 < sents.size && (pLower (pClean sents[idx + 2]!)).startsWith "otherwise, " && (pLower thenStr).startsWith "you may " then
                let optNoStr := elseStr
                let ifElseStr := (pDropPrefixCI? (pClean sents[idx + 2]!) "otherwise, ").getD ""
                let mayAct := (pDropPrefixCI? thenStr "you may ").getD thenStr
                match parseSingleClause qp ctx mayAct,
                      parseSingleClause qp ctx optNoStr,
                      parseSingleClause qp ctx ifElseStr with
                | some (aI, _, _), some (bI, _, _), some (cI, _, ctx3) =>
                  steps := steps.push (none, .ifCond cond (.optional .you none aI bI) cI)
                  ctx := ctx3
                  idx := idx + 3
                  continue
                | _, _, _ => pure ()
              if let some (tInstr, _, ctx1) := parseSingleClause qp ctx thenStr then
                if let some (eInstr, _, ctx2) := parseSingleClause qp ctx1 elseStr then
                  steps := steps.push (none, .ifCond cond tInstr eInstr)
                  ctx := ctx2
                  idx := idx + 2
                  continue
    if !sLow.startsWith "if " then
      if let some (thenPart, condPart) := pSplitLastCI? sent " if " then
        if pLower condPart != "able" then
          if let some cond := parseInstrCondition? condPart cardName (some ctx) then
            if let some (tInstr, bT, ctx1) := parseSingleClause qp ctx thenPart then
              let mut eInstr : Instruction := .noop
              let mut ctxOut := ctx1
              let mut consumed := 1
              if idx + 1 < sents.size then
                if let some elseStr := pDropPrefixCI? (pClean sents[idx + 1]!) "otherwise, " then
                  if let some (ei, _, ctx2) := parseSingleClause qp ctx1 elseStr then
                    eInstr := ei; ctxOut := ctx2; consumed := 2
              let (v?, ctxA) := if bT then let (v, c) := ctxOut.allocVar; (some v, c) else (none, ctxOut)
              steps := steps.push (v?, .ifCond cond tInstr eInstr)
              ctx := ctxA
              idx := idx + consumed
              continue

    -- 2i. `"If you do, search ..."` spanning multiple sentences (`Last Light of Durin's Day`)
    if let some followStr := pDropPrefixCI? sent "if you do, " then
      if (pLower followStr).startsWith "search " then
        let mut fakeSents : Array String := #[followStr]
        for k in [idx + 1 : sents.size] do
          fakeSents := fakeSents.push sents[k]!
        if let some (searchI, consumed, ctx1) := parseSearchLibrarySeq? ctx fakeSents 0 then
          let cond := Condition.stepSucceeded (ctx.lastActionVar?.getD ⟨0⟩)
          steps := steps.push (none, .ifCond cond searchI .noop)
          ctx := ctx1
          idx := idx + consumed
          continue

    -- 2j. `"[Then ]If <cond>, <InspectLibrarySeq>"` spanning multiple sentences (`Nissa, Leyline Tamer`)
    let sentNoThen := (pDropPrefixCI? sent "then ").getD sent
    if let some ifRest := pDropPrefixCI? sentNoThen "if " then
      if let some (condStr, afterIf) := pSplitFirstCI? ifRest ", " then
        if (pLower afterIf).startsWith "reveal " || (pLower afterIf).startsWith "look at " || (pLower afterIf).startsWith "exile cards " then
          if let some cond := parseInstrCondition? condStr cardName (some ctx) then
            let mut fakeSents : Array String := #[afterIf]
            for k in [idx + 1 : sents.size] do
              fakeSents := fakeSents.push sents[k]!
            if let some (inspI, consumed, ctx1) := parseInspectLibrarySeq? ctx fakeSents 0 then
              steps := steps.push (none, .ifCond cond inspI .noop)
              ctx := ctx1
              idx := idx + consumed
              continue

    -- 2k. Post-step sentence modifiers:
    -- `"During that turn, power-up abilities can't be activated."` (`Kang the Conqueror`)
    if sLow == "during that turn, power-up abilities can't be activated" && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .turn (.extraTurn who _) =>
        steps := steps.set! (steps.size - 1) (v?, .turn (.extraTurn who (some (.player (.forbidAbilityActivation .any .powerUp)))))
        idx := idx + 1
        continue
      | _ => pure ()

    -- `"It's still a land."` (`Restless Anchorage`, `Restless Spire`) / `"The flashback cost is equal to its mana cost."` (`Stingcaster Mage`)
    if (sLow == "it's still a land" || sLow == "the flashback cost is equal to its mana cost") && !steps.isEmpty then
      idx := idx + 1
      continue

    -- `"If you search your library this way, shuffle."` patching earlier `searchLibrary` (`Vision Quest`)
    if (sLow == "if you search your library this way, shuffle" || sLow == "if you searched your library this way, shuffle") && !steps.isEmpty then
      let mut patched := false
      for k in [0 : steps.size] do
        let j := steps.size - 1 - k
        let (v?, st) := steps[j]!
        match st with
        | .player (.searchLibrary spec) =>
          steps := steps.set! j (v?, .player (.searchLibrary { spec with shuffle := true }))
          patched := true; break
        | _ => pure ()
      if patched then
        idx := idx + 1
        continue

    -- `"If you cast a spell this way, pay life equal to its mana value rather than pay its mana cost."` (`Inside Information`)
    if sLow.contains "pay life equal to its mana value rather than pay its mana cost" && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .stack (.mayCastOrPlay o gpp) =>
        steps := steps.set! (steps.size - 1) (v?, .stack (.mayCastOrPlay o { gpp with payLifeInsteadOfMana := true }))
        idx := idx + 1; continue
      | .moveZone obj .exile .exile mods =>
        if let some gpp := mods.grantPlayPerm? then
          steps := steps.set! (steps.size - 1) (v?, .moveZone obj .exile .exile { mods with grantPlayPerm? := some { gpp with payLifeInsteadOfMana := true } })
          idx := idx + 1; continue
      | _ => pure ()

    -- `"If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead."` (`Bilbo, Thief in the Night`)
    if sLow.contains "spell cast this way would be put into" && sLow.contains "exile it instead" && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .stack (.mayCastOrPlay o gpp) =>
        steps := steps.set! (steps.size - 1) (v?, .stack (.mayCastOrPlay o { gpp with exileOnResolveInstead := true }))
        idx := idx + 1; continue
      | _ => pure ()

    -- Trailing `"Put the rest on the bottom of your library in a random order."` / `"Shuffle the rest..."` patching earlier `inspectLibrary` (`Part in Friendship`),
    -- unless an intervening `mayCastOrPlay` step must run BEFORE moving the uncast cards (`Cosmic Cube`).
    if sLow.startsWith "put the rest " || sLow.startsWith "shuffle the rest " then
      let rp : RestPlacement :=
        if sLow.contains "random order" then .bottomRandom
        else if sLow.contains "bottom" then .bottomAnyOrder
        else if sLow.contains "shuffle" then .shuffleIntoLibrary
        else .graveyard
      let mut patched := false
      let mut sawMayCast := false
      let mut inspVar? : Option VarId := none
      for k in [0 : steps.size] do
        let j := steps.size - 1 - k
        let (v?, st) := steps[j]!
        match st with
        | .stack (.mayCastOrPlay ..) => sawMayCast := true
        | .player (.inspectLibrary spec) =>
          if sawMayCast then
            inspVar? := v?
            break
          else
            steps := steps.set! j (v?, .player (.inspectLibrary { spec with rest := rp }))
            patched := true
            break
        | _ => pure ()
      if patched then
        idx := idx + 1
        continue
      if let some v := inspVar? then
        let dest : DestZoneSpec :=
          match rp with
          | .bottomRandom => .library .owner .bottomRandom
          | .bottomAnyOrder => .library .owner .bottom
          | .shuffleIntoLibrary => .library .owner .top
          | _ => .graveyard
        let mods : MoveMods := if rp == .shuffleIntoLibrary then { shuffleAfter := true } else {}
        steps := steps.push (none, .moveZone (.stepObjects v) dest .put mods)
        idx := idx + 1
        continue

    -- `"Damage can't be prevented."`
    if sLow == "damage can't be prevented" && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .damage (.deal src to amt fl) =>
        steps := steps.set! (steps.size - 1) (v?, .damage (.deal src to amt { fl with cantBePrevented := true }))
        idx := idx + 1
        continue
      | _ => pure ()

    -- `"You may choose new targets for the copy."`
    if (sLow == "you may choose new targets for the copy" || sLow == "you may choose new targets for the copies") && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .stack (.copyStackObject o n _) =>
        steps := steps.set! (steps.size - 1) (v?, .stack (.copyStackObject o n true))
        idx := idx + 1
        continue
      | .installEffect (.createDelayedTrigger spec) =>
        match spec.effect.body with
        | .stack (.copyStackObject o n _) =>
          let spec' := { spec with effect := { spec.effect with body := .stack (.copyStackObject o n true) } }
          steps := steps.set! (steps.size - 1) (v?, .installEffect (.createDelayedTrigger spec'))
          idx := idx + 1
          continue
        | _ => pure ()
      | _ => pure ()

    -- `"If that/a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard."`
    if (sLow.startsWith "if that spell is countered this way, exile it" ||
        sLow.startsWith "if a permanent spell is countered this way, exile it") && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .stack (.counterStack o _ fc) =>
        steps := steps.set! (steps.size - 1) (v?, .stack (.counterStack o true fc))
        idx := idx + 1
        continue
      | _ => pure ()

    -- `"If it's a permanent card, you may cast it without paying its mana cost."` /
    -- `"You may cast that card without paying its mana cost for as long as it remains exiled."` (`Thranduil's Decree`)
    if (sLow == "if it's a permanent card, you may cast it without paying its mana cost" ||
        sLow == "if it is a permanent card, you may cast it without paying its mana cost" ||
        sLow == "you may cast that card without paying its mana cost for as long as it remains exiled") && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .stack (.counterStack o ex _) =>
        steps := steps.set! (steps.size - 1) (v?, .stack (.counterStack o ex true))
        idx := idx + 1
        continue
      | _ => pure ()

    -- `"It gains <kws>[ until end of turn]."` / `"They gain <kws>[ until end of turn]."`
    -- folding into `EnterMods.grantKeywordsUntilEot` on immediately preceding `CreateOp.tokens` (`Venser`, `Windcrag Siege`)
    if !steps.isEmpty then
      let kwGrantTail? : Option String :=
        (pDropPrefixCI? sent "they gain ").orElse fun _ =>
        (pDropPrefixCI? sent "it gains ").orElse fun _ =>
        (pDropPrefixCI? sent "those tokens gain ").orElse fun _ =>
        pDropPrefixCI? sent "that token gains "
      if let some kwTail0 := kwGrantTail? then
        let kwTail := (pDropSuffixCI? kwTail0 " until end of turn").getD kwTail0
        if let some kws := parseKeywordList? kwTail then
          let (v?, prev) := steps[steps.size - 1]!
          match prev with
          | .create (.tokens w c sp m) =>
            steps := steps.set! (steps.size - 1) (v?, .create (.tokens w c sp { m with grantKeywordsUntilEot := m.grantKeywordsUntilEot ++ kws }))
            idx := idx + 1
            continue
          | _ => pure ()

    -- `"Sacrifice/Exile it/them at the beginning of the next end step / end of combat"`
    -- AND `"At the beginning of the next end step, sacrifice/exile it/them"` (`Venser, Fervent Forger`, `Vindictive Triumph`)
    if (sLow.startsWith "sacrifice it at the beginning of the next end step" ||
        sLow.startsWith "sacrifice them at the beginning of the next end step" ||
        sLow.startsWith "exile it at the beginning of the next end step" ||
        sLow.startsWith "exile them at the beginning of the next end step" ||
        sLow == "at the beginning of the next end step, sacrifice it" ||
        sLow == "at the beginning of the next end step, sacrifice them" ||
        sLow == "at the beginning of the next end step, exile it" ||
        sLow == "at the beginning of the next end step, exile them" ||
        sLow == "exile it at end of combat" || sLow == "exile them at end of combat") && !steps.isEmpty then
      let da? : Option DelayedTokenAction :=
        if sLow.contains "end of combat" then some .exileAtEndOfCombat
        else if sLow.contains "exile " then some .exileAtEndStep
        else if let some (_, uStr) := pSplitFirstCI? sent " unless " then
          (parseInstrCondition? uStr cardName (some ctx)).map .sacrificeAtEndStepUnless
        else some .sacrificeAtEndStep
      if let some da := da? then
        let mut patched := false
        for k in [0 : steps.size] do
          let j := steps.size - 1 - k
          let (v?, prev) := steps[j]!
          match prev with
          | .create (.tokens w c sp m) =>
            steps := steps.set! j (v?, .create (.tokens w c sp { m with delayedAction? := some da }))
            patched := true
            break
          | _ => pure ()
        if patched then
          idx := idx + 1
          continue
        -- Also allow `"Exile it at the beginning of the next end step."` as delayed trigger (`Vindictive Triumph`)
        let obj := ctx.lastSubject?.getD (.target (ctx.lastTargetSlot?.getD 0))
        steps := steps.push (none, .installEffect (.createDelayedTrigger {
          pattern := .stepBegins .end (.player .any)
          duration := .untilEndOfTurn
          oneShot := true
          effect := { targets := .none, body := .moveZone obj .exile .exile {} }
        }))
        idx := idx + 1
        continue

    -- Conditional exile-return-exile folding (`Vindictive Triumph` and canonical `ToOracle` form)
    if sLow.startsWith "if " && sLow.contains ", return it " && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .moveZone obj .exile .exile mods =>
        if mods.delayedReturn?.isNone then
          let parseMvLePred? (rawP : String) : Option ObjectPred :=
            let pl := pLower (pClean rawP)
            let mvTail? :=
              (pDropPrefixCI? pl "permanent with mana value ").orElse fun _ =>
              (pDropPrefixCI? pl "that permanent's mana value was ").orElse fun _ =>
              (pDropPrefixCI? pl "that card's mana value was ").orElse fun _ =>
              pDropPrefixCI? pl "its mana value was "
            match mvTail? with
            | some rest =>
              match pDropSuffixCI? rest " or less" with
              | some nStr => (parseNatWord? nStr).map fun n => .stat .manaValue .le (.const (Int.ofNat n))
              | none => none
            | none =>
              (parseNounPhrase rawP).map (·.filter.pred)
          let (condRaw?, retPart?, consumedN) : Option String × Option String × Nat :=
            if let some (beforeRet, afterRet) := pSplitFirstCI? sent ", return it " then
              let condBody :=
                ((pDropPrefixCI? beforeRet "if it is ").orElse fun _ =>
                 pDropPrefixCI? beforeRet "if ") |>.getD beforeRet
              if (pLower afterRet).contains "then exile it at the beginning of the next end step" then
                (some condBody, some afterRet, 1)
              else if idx + 1 < sents.size &&
                  pLower (pClean sents[idx + 1]!) == "exile it at the beginning of the next end step" then
                (some condBody, some afterRet, 2)
              else (none, none, 0)
            else (none, none, 0)
          match condRaw?, retPart? with
          | some cRaw, some rPart =>
            if let some pred := parseMvLePred? cRaw then
              let rl := pLower rPart
              let tap := rl.contains " tapped"
              let retOwner : DestOwnerSpec :=
                if rl.contains "under your control" then .controller else .owner
              let dr : DelayedReturnSpec := .returnIfThenExileAtEndStep pred tap retOwner
              steps := steps.set! (steps.size - 1) (v?, .moveZone obj .exile .exile { mods with delayedReturn? := some dr })
              idx := idx + consumedN
              continue
          | _, _ => pure ()
      | _ => pure ()

    -- `"Return it/them to the battlefield ... [at the beginning of the next end step]"` patching preceding exile `MoveZone`
    let sLowNoThen :=
      (pDropPrefixCI? sLow "then ").orElse (fun _ => pDropPrefixCI? sLow "if you do, ") |>.getD sLow
    if (sLowNoThen.startsWith "return it to the battlefield" || sLowNoThen.startsWith "return it onto the battlefield" ||
        sLowNoThen.startsWith "return them to the battlefield" || sLowNoThen.startsWith "return them onto the battlefield" ||
        sLowNoThen.startsWith "return that card to the battlefield" || sLowNoThen.startsWith "return those cards to the battlefield" ||
        sLowNoThen.startsWith "return those cards onto the battlefield" || sLowNoThen.startsWith "return those lands to the battlefield" ||
        sLowNoThen.startsWith "return those lands onto the battlefield") &&
        sLowNoThen.contains "at the beginning of the next end step" &&
        !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev with
      | .moveZone obj .exile .exile mods =>
        if mods.delayedReturn?.isNone then
          let tap := sLowNoThen.contains " tapped"
          let retOwner : DestOwnerSpec :=
            if sLowNoThen.contains "under your control" then .controller
            else .owner
          let dr : DelayedReturnSpec :=
            if sLowNoThen.contains "at the beginning of the next end step" then
              .atNextEndStep tap retOwner
            else if sLowNoThen.contains "then exile it at the beginning of the next end step" then
              .returnThenExileAtEndStep tap retOwner
            else
              .immediately tap retOwner
          steps := steps.set! (steps.size - 1) (v?, .moveZone obj .exile .exile { mods with delayedReturn? := some dr })
          idx := idx + 1
          continue
      | _ => pure ()

    -- Trailing play-permission sentence (`"Until ..., you may play/cast it/that card/those cards..."`)
    -- folding into `MoveMods.grantPlayPerm?` on immediately preceding `.moveZone _ .exile .exile` when final sentence
    let isNearEnd :=
      idx + 1 == sents.size ||
      (idx + 2 == sents.size && (pLower sents[idx + 1]!).contains "pay life equal to its mana value")
    if isNearEnd && !steps.isEmpty then
      let (v?, prev) := steps[steps.size - 1]!
      match prev, v? with
      | .moveZone obj .exile .exile mods, some prevV =>
        if mods.grantPlayPerm?.isNone then
          if let some (playObj, gpp, _) := parseGrantPlayPermClause? ctx sent then
            if playObj == .stepObjects prevV || playObj == obj then
              steps := steps.set! (steps.size - 1) (v?, .moveZone obj .exile .exile { mods with grantPlayPerm? := some gpp })
              idx := idx + 1
              continue
      | _, _ => pure ()

    -- 2l0. `"Copy those [exiled] cards. You may cast ..."` -> `copyAndCast := true` (`Baron Helmut Zemo`, `Uldaros Theorix`)
    if (sLow == "copy those cards" || sLow == "copy those exiled cards") && idx + 1 < sents.size then
      if let some (playObj, gpp, ctx1) := parseGrantPlayPermClause? ctx sents[idx + 1]! then
        steps := steps.push (none, .stack (.mayCastOrPlay playObj { gpp with copyAndCast := true }))
        ctx := ctx1
        idx := idx + 2
        continue

    -- 2l0b. `"You may cast/play <obj>. If you don't, <consequence>."` (e.g. *Chandra, Torch of Defiance*):
    -- bind a dedicated `VarId` for `mayCastOrPlay` so `.not (.stepSucceeded vCast)` refers
    -- to the cast choice rather than the preceding exile step (keeping `lastActionVar?` intact).
    if idx + 1 < sents.size then
      let nextS := sents[idx + 1]!
      let negBody? :=
        (pDropPrefixCI? nextS "if you don't, ").orElse fun _ =>
          pDropPrefixCI? nextS "if not (you do), "
      if let some consStr := negBody? then
        if let some (playObj, gpp, ctx1) := parseGrantPlayPermClause? ctx sent then
          let (vCast, ctx2) := ctx1.allocLoopVar
          if let some (consInstr, _, ctx3) := parseSingleClause qp ctx2 consStr then
            steps := steps.push (some vCast, .stack (.mayCastOrPlay playObj gpp))
            steps := steps.push (none, .ifCond (.not (.stepSucceeded vCast)) consInstr .noop)
            ctx := ctx3
            idx := idx + 2
            continue

    -- 2l. Standard single-sentence clause
    match parseSingleClause qp ctx sent with
    | some (instr, bindable, ctx1) =>
      let (v?, ctx2) := if bindable then let (v, c) := ctx1.allocVar; (some v, c) else (none, ctx1)
      steps := steps.push (v?, instr)
      ctx := ctx2
      idx := idx + 1
    | none => return none

  if steps.isEmpty then return none
  let body0 := normalizeBoundVars (assembleBoundSteps steps)
  let body0' : Instruction :=
    match body0 with
    | .bind v (.moveZone o (.hand .controller) .returnToHand mods) (.life (.gain .you (.stepMetric .sumPower v'))) =>
      if v == v' then
        .bind v (.moveZone o (.hand .owner) .returnToHand mods) (.life (.gain .you (.stepMetric .sumPower v')))
      else body0
    | _ => body0
  let body1 : Instruction :=
    match body0' with
    | .seq #[.installEffect (.applyContinuous dur1 aff1 m1), .installEffect (.applyContinuous dur2 aff2 m2)] =>
      if dur1 == dur2 && aff1 == aff2 then
        .installEffect (.applyContinuous dur1 aff1 (.all #[m1, m2]))
      else body0'
    | _ => body0'
  let body : Instruction :=
    match body1 with
    | .seq xs =>
      if xs.size >= 2 then
        let last := xs[xs.size - 1]!
        match last with
        | .permanent (.modifyCounters (.put .plan (.const 1)) .this none) =>
          .seq (#[last] ++ xs.extract 0 (xs.size - 1))
        | _ => body1
      else body1
    | _ => body1
  return some { targets := ctx.toTargetSpec, body }

end Mtg.Engine.Parser
