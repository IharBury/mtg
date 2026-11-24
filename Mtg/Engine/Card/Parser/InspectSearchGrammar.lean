import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars
import Mtg.Engine.Card.Parser.DiscourseBind
import Mtg.Engine.Card.Parser.TokenEmblemGrammar

/-!
# Stage-4b-ii Discourse-Aware Object/Player, Search, Inspect & Continuous-Mod Grammar

Compositional sub-grammars for:
- `DiscourseCtx`-aware object, player, recipient, destination-zone, and `MoveChoiceSpec` /
  `MoveMods` / `GrantPlayPermSpec` parsing (CR 115 / 608.2c / 610.3).
- `SearchLibrarySpec` (`"search your library [and/or graveyard] for ..."`, CR 701.19).
- `InspectLibrarySpec` (`"look at the top N"`, `"reveal the top N"`, `"reveal/exile cards
  from the top of ... until ..."`, `"mill N cards. Put ... from among them ..."`,
  `"separate them into two piles"`, `"exile all but the bottom card"`, `"choose N cards from
  outside the game"`).
- `ContinuousModification`, `RuleModification`, `StaticReplacementSpec`, and
  `DelayedTriggerSpec` inside one-shot `InstallEffectOp` instructions.
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-! ### `DiscourseCtx`-Aware Object, Player & Recipient Resolution -/

/-- Parse a `PlayerExpr` with `DiscourseCtx` support (targets, anaphora, `"its controller"`,
`"its owner"`, `"that player"`, `"each opponent"`, `"each player"`, `"you"`, etc.). -/
def parsePlayerWithCtx (ctx : DiscourseCtx) (raw : String) : Option (PlayerExpr × DiscourseCtx) := Id.run do
  let s := pClean raw
  let l := pLower s
  if l.isEmpty then return none
  if l == "you" || l == "your" then return some (.you, ctx)
  if l == "each opponent" || l == "each opponent's" || l == "your opponents" || l == "opponents" then
    return some (.opponents, ctx)
  if l == "each player" || l == "each player's" || l == "all players" || l == "players" then
    return some (.eachPlayer, ctx)
  if l == "an opponent" || l == "an opponent's" then
    return some (.matching .opponent .any, ctx)
  if l == "an opponent who is target player" || l == "an opponent who is target opponent" then
    let (idx, ctx') := ctx.pushTargetSlot { domain := .player .opponent }
    return some (.target idx, ctx')
  if l == "target player" || l == "target player's" ||
      l == "target opponent" || l == "target opponent's" ||
      l.contains "target player" || l.contains "target opponent" then
    -- Check if already targeting that exact player slot and phrased as possessive/repeated anaphor
    let cleanTarget :=
      if l.endsWith "'s" then (s.dropEnd 2).trimAscii.copy else s
    if ctx.slots.size > 0 then
      if let some idx := ctx.lastTargetSlot? then
        if let some slot0 := ctx.slots[idx]? then
          match slot0.domain with
          | .player pf =>
            let wantOpp := l.contains "opponent"
            let slotIsOpp := pf == .opponent
            if l.endsWith "'s" && wantOpp == slotIsOpp then
              return some (.target idx, ctx)
          | _ => pure ()
    match parseTargetSlot cleanTarget with
    | some slot =>
      let (idx, ctx') := ctx.pushTargetSlot slot
      return some (.target idx, ctx')
    | none => pure ()
  if let some p := ctx.resolvePlayerAnaphor? s then
    return some (p, ctx)
  if let some p := parsePlayerExpr? s then
    return some (p, ctx)
  return none

/-- Parse a possessive player prefix (`"your"`, `"their"`, `"its controller's"`,
`"its owner's"`, `"that player's"`, `"target player's"`, `"target opponent's"`,
`"each opponent's"`, `"each player's"`). -/
def parsePossessivePlayerWithCtx (ctx : DiscourseCtx) (raw : String) :
    Option (PlayerExpr × DiscourseCtx) :=
  let s := pClean raw
  let l := pLower s
  if l == "your" then some (.you, ctx)
  else if l == "their" then
    match ctx.lastPlayer? with
    | some p => some (p, ctx)
    | none =>
      if ctx.isTrigger then some (ctx.triggerPlayerRole?.getD (.triggerPlayer .actor), ctx)
      else some (.you, ctx)
  else if l == "its controller's" || l == "their controller's" then
    let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    some (.controllerOf obj, ctx)
  else if l == "its owner's" || l == "their owner's" || l == "their owners'" then
    let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
    some (.ownerOf obj, ctx)
  else if l == "that player's" || l == "that opponent's" then
    match ctx.lastPlayer? with
    | some p => some (p, ctx)
    | none =>
      if ctx.isTrigger then some (ctx.triggerPlayerRole?.getD (.triggerPlayer .actor), ctx)
      else some (.opponents, ctx)
  else if l.endsWith "'s" then
    parsePlayerWithCtx ctx (s.dropEnd 2).trimAscii.copy
  else if l.endsWith "'" then
    parsePlayerWithCtx ctx (s.dropEnd 1).trimAscii.copy
  else
    parsePlayerWithCtx ctx s

/-- Parse a `ZoneSetSpec` phrase like `"your graveyard"`, `"a graveyard"`, `"your hand"`,
`"the battlefield"`, `"your library and/or graveyard"`. -/
def parseZoneSetWithCtx (ctx : DiscourseCtx) (raw : String) : Option (ZoneSetSpec × DiscourseCtx) := Id.run do
  let s := pClean raw
  let l := pLower s
  if l == "the battlefield" || l == "battlefield" then
    return some (.battlefield, ctx)
  if l == "your graveyard" then return some (.yourGraveyard, ctx)
  if l == "your hand" then return some (.yourHand, ctx)
  if l == "your library" then return some (.libraryOf .you, ctx)
  if l == "a graveyard" || l == "any graveyard" || l == "all graveyards" || l == "graveyards" then
    return some ({ zones := #[.graveyard], owner := .any }, ctx)
  if l == "exile" then return some ({ zones := #[.exile], owner := .any }, ctx)
  if l == "the stack" then return some ({ zones := #[.stack], owner := .any }, ctx)
  -- Compound `"<who> <z1> and/or <z2>"` (e.g., `"your hand and/or library"`, `"your library and/or graveyard"`)
  let (owner, rest, ctx') : ZoneOwnerSpec × String × DiscourseCtx :=
    if let some r := pDropPrefixCI? s "your " then (.matching .you, r, ctx)
    else if let some r := pDropPrefixCI? s "their " then
      let p := ctx.lastPlayer?.getD (if ctx.isTrigger then ctx.triggerPlayerRole?.getD (.triggerPlayer .actor) else .you)
      (.ofPlayer p, r, ctx)
    else if let some r := pDropPrefixCI? s "that player's " then
      let p := ctx.lastPlayer?.getD (if ctx.isTrigger then ctx.triggerPlayerRole?.getD (.triggerPlayer .actor) else .you)
      (.ofPlayer p, r, ctx)
    else if let some r := pDropPrefixCI? s "its controller's " then
      let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
      (.ofPlayer (.controllerOf obj), r, ctx)
    else if let some r := pDropPrefixCI? s "its owner's " then
      let obj := ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
      (.ofPlayer (.ownerOf obj), r, ctx)
    else if let some r := pDropPrefixCI? s "each opponent's " then
      (.ofPlayer .opponents, r, ctx)
    else if let some r := pDropPrefixCI? s "each player's " then
      (.ofPlayer .eachPlayer, r, ctx)
    else if let some r := pDropPrefixCI? s "an opponent's " then
      (.ofPlayer (.matching .opponent .any), r, ctx)
    else if let some r := pDropPrefixCI? s "target player's " then
      let (p, c2) := (parsePossessivePlayerWithCtx ctx "target player's").getD (.target 0, ctx)
      (.ofPlayer p, r, c2)
    else if let some r := pDropPrefixCI? s "target opponent's " then
      let (p, c2) := (parsePossessivePlayerWithCtx ctx "target opponent's").getD (.target 0, ctx)
      (.ofPlayer p, r, c2)
    else
      (.any, s, ctx)
  -- Parse zone list separated by `", "`, `" and/or "`, `" or "`, `" and "`
  let zParts :=
    rest.replace ", and/or " "|" |>.replace " and/or " "|" |>.replace ", " "|"
      |>.replace " or " "|" |>.replace " and " "|" |>.splitOn "|"
      |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
  let mut zs : Array ZoneKind := #[]
  for zp in zParts do
    let some zk := parseZoneKind? zp | return none
    if !zs.contains zk then zs := zs.push zk
  if zs.isEmpty then return none
  return some ({ zones := zs, owner }, ctx')

/-- Remap `PlayerExpr.target 0` inside a parsed noun-phrase filter to `PlayerExpr.target idx`
when allocating a target-player / target-opponent slot at index `idx > 0`. -/
private partial def remapPlayerTarget0 (idx : Nat) : PlayerExpr → PlayerExpr
  | .target 0 => .target idx
  | p => p

private partial def remapPlayerPredTarget0 (idx : Nat) : PlayerPred → PlayerPred
  | .matchesExpr p => .matchesExpr (remapPlayerTarget0 idx p)
  | .all ps => .all (ps.map (remapPlayerPredTarget0 idx))
  | .anyOf ps => .anyOf (ps.map (remapPlayerPredTarget0 idx))
  | .not p => .not (remapPlayerPredTarget0 idx p)
  | other => other

private partial def remapObjPredTarget0 (idx : Nat) : ObjectPred → ObjectPred
  | .controlledBy pf => .controlledBy { pf with pred := remapPlayerPredTarget0 idx pf.pred }
  | .ownedBy pf => .ownedBy { pf with pred := remapPlayerPredTarget0 idx pf.pred }
  | .all ps => .all (ps.map (remapObjPredTarget0 idx))
  | .any ps => .any (ps.map (remapObjPredTarget0 idx))
  | .not p => .not (remapObjPredTarget0 idx p)
  | other => other

private def remapZoneSetTarget0 (idx : Nat) (zs : ZoneSetSpec) : ZoneSetSpec :=
  match zs.owner with
  | .ofPlayer p => { zs with owner := .ofPlayer (remapPlayerTarget0 idx p) }
  | _ => zs

/-- Parse an `ObjectExpr` with `DiscourseCtx`:
- Self-references (`"this permanent"`, `"this creature"`, ...) -> `.this`
- Discourse anaphora (`"it"`, `"them"`, `"that creature"`, `"those cards"`, `"the cards exiled this way"`, `"equipped creature"`, `"enchanted creature"`)
- Target phrases (`"target ..."`, `"up to N target ..."`, `"another target ..."`, `"a second target ..."`)
- Quantified / filtered sets (`"all creatures"`, `"each creature you control"`, `"creatures you control"`, `"creature you control"`, `"each opponent's creatures"`, `"cards in your graveyard"`, `"the exiled card(s)"`, `"cards exiled with this permanent"`, `"those cards matching <pred>"`). -/
partial def parseObjWithCtx (ctx : DiscourseCtx) (raw : String) :
    Option (ObjectExpr × DiscourseCtx) := Id.run do
  let s := pClean raw
  let l := pLower s
  if l.isEmpty then return none
  -- Explicit self-from-zone (`"this card from your graveyard"`, `"this card from your hand"`)
  if l == "this card from your graveyard" || l == "this card from your hand" ||
      l == "this card in your graveyard" || l == "this permanent from your graveyard" then
    return some (.this, ctx)
  -- Set difference (`"<A> other than <B>"`, e.g. `"Wizard token you control other than those cards"`)
  if let some (aStr, bStr) := pSplitFirstCI? s " other than " then
    let bLow := pLower bStr
    if bLow == "those cards" || bLow == "it" || bLow == "them" || bLow == "that token" || bLow == "that creature" then
      if let some (aObj, ctx1) := parseObjWithCtx ctx aStr then
        if let some (bObj, ctx2) := parseObjWithCtx ctx1 bStr then
          return some (.diff aObj bObj, ctx2)
  -- Explicit linked exile (`"a card exiled with this permanent"`, `"cards exiled with this permanent"`)
  if l.contains "exiled with this" then
    return some (.linkedExile .this, ctx)
  -- Bare `"target"` (canonical `Expr.toOracle` rendering of `.target 0`)
  if l == "target" then
    return some (.target (ctx.lastTargetSlot?.getD 0), ctx)
  -- `"objects targeted by <obj> [matching <pred>]"` (`Storm, Windrider`)
  if let some tgtRest := pDropPrefixCI? s "objects targeted by " then
    if let some (baseStr, predStr) := pSplitFirstCI? tgtRest " matching " then
      let bLow := pLower baseStr
      let baseObj? : Option ObjectExpr :=
        if DiscourseCtx.isSelfPhrase bLow then some .this
        else ctx.resolveObjectAnaphor? baseStr
      if let some baseObj := baseObj? then
        if let some np := parseNounPhrase predStr then
          return some (.filter (.targetsOf baseObj) np.filter.pred, ctx)
    else
      let baseObj? : Option ObjectExpr :=
        if DiscourseCtx.isSelfPhrase (pLower tgtRest) then some .this
        else ctx.resolveObjectAnaphor? tgtRest
      if let some baseObj := baseObj? then
        return some (.targetsOf baseObj, ctx)
  -- `"the sacrificed creature"` / `"the exiled card(s) ..."` / `"each chosen <noun>"`
  if l == "the exiled card" && ctx.isTrigger && ctx.lastActionVar?.isNone then
    return some (.linkedExile .this, ctx)
  if l == "the sacrificed creature" || l == "the sacrificed permanent" || l == "the sacrificed artifact" ||
      l == "the exiled cards that weren't cast this way" || l == "cards exiled this way" ||
      l == "all cards exiled this way" then
    return some (.stepObjects (ctx.lastActionVar?.getD ⟨0⟩), ctx)
  if l == "each chosen creature" || l == "each chosen permanent" || l == "those chosen cards" then
    let expr := ctx.lastSubject?.getD (if ctx.slots.size > 0 then .target (ctx.lastTargetSlot?.getD 0) else .allTargets)
    return some (expr, ctx)
  -- `"all creatures that aren't of the chosen type"` / `"creature that isn't of the chosen type"` (`Raise the Palisade`, `Kindred Judgment`)
  if l == "all creatures that aren't of the chosen type" || l == "creatures that aren't of the chosen type" ||
      l == "creature that isn't of the chosen type" || l == "creature that isn't permanent of the chosen type" ||
      l == "creature not (of the chosen type)" || l == "non-chosen-type creature" then
    let v := ctx.lastActionVar?.getD ⟨0⟩
    return some (.inZones .battlefield (.all #[.hasType .creature, .not (.hasSubtype (.fromStep v))]), ctx)
  -- `"<np> except for <exclNp>"` (`Ajani Unrelenting`: `"each creature except for tokens you control"`)
  if let some (npStr, excStr) := pSplitFirstCI? s " except for " then
    match parseNounPhrase npStr, parseNounPhrase excStr with
    | some np, some excNp =>
      return some (.inZones np.filter.zones (.all #[np.filter.pred, .not excNp.filter.pred]), ctx)
    | _, _ => pure ()
  -- `"<base> matching <pred>"` (`"those cards matching ..."`, `"this permanent matching ..."`, `"that permanent matching ..."`, `"enchanted or equipped permanent matching ..."`, `"target matching ..."`)
  if let some (baseStr, predStr) := pSplitFirstCI? s " matching " then
    let bLow := pLower baseStr
    let baseObj? : Option ObjectExpr :=
      if bLow == "those cards" || bLow == "those objects" then
        some (match ctx.lastActionVar? with | some v => .stepObjects v | none => ctx.lastSubject?.getD .triggerSubject)
      else if DiscourseCtx.isSelfPhrase bLow then some .this
      else if bLow == "target" then some (.target (ctx.lastTargetSlot?.getD 0))
      else ctx.resolveObjectAnaphor? baseStr
    if let some baseObj := baseObj? then
      if let some np := parseNounPhrase predStr then
        let pred' :=
          match ctx.lastPlayer? with
          | some lp =>
            let rec substThatOwner : ObjectPred → ObjectPred
              | .ownedBy { relation := .anyPlayer, pred := .thatPlayer } => .ownedBy (.ofExpr lp)
              | .all ps => .all (ps.map substThatOwner)
              | .any ps => .any (ps.map substThatOwner)
              | .not p => .not (substThatOwner p)
              | p => p
            substThatOwner np.filter.pred
          | none => np.filter.pred
        return some (.filter baseObj pred', ctx)
  -- `"<np> other than those cards/objects"` (`Command the Stage`) — skip target phrases (`Secret Invasion`)
  if !l.contains "target " then
    if let some (npStr, exclStr) := pSplitLastCI? s " other than " then
      if let some exclObj := ctx.resolveObjectAnaphor? exclStr then
        let exclRef : ObjectRef :=
          match exclObj with
          | .this => .this
          | .stepObjects v => .stepVar v
          | .triggerSubject => .triggerSubject
          | .attachedHost => .attachedHost
          | .target i => .target i
          | _ => .this
        if let some np := parseNounPhrase npStr then
          return some (.inZones np.filter.zones (.all #[np.filter.pred, .otherThan exclRef]), ctx)
  -- `"for each opponent, up to one target creature that player controls"` (`Hapatra`, `Celebrate the Mountain-king`)
  if l.startsWith "for each opponent, " || l.startsWith "for each player, " then
    if let some slot := parseTargetSlot s then
      let (_, ctx1) := ctx.pushTargetSlot slot
      return some (.allTargets, ctx1)
  -- Check `"all <X>"` / `"each <X>"` / `"other <X>"` vs anaphora vs targets
  if let some anaph := ctx.resolveObjectAnaphor? s then
    return some (anaph, ctx)
  -- Target phrase (`"target ..."`, `"up to N target ..."`, `"another target ..."`, `"a second target ..."`, `"any number of target ..."`, `"each of one or two target ..."`)
  if l.contains "target " || l.endsWith " targets" then
    let sNoEach := (pDropPrefixCI? s "each of ").getD s
    let (isSecond, slotStr) :=
      match pDropPrefixCI? sNoEach "a second " with
      | some r => (true, r)
      | none =>
        match pDropPrefixCI? sNoEach "second " with
        | some r => (true, r)
        | none => (false, sNoEach)
    if let some slot := parseTargetSlot slotStr then
      let (idx, ctx1) := ctx.pushTargetSlot slot
      let ctx2 :=
        if isSecond && idx > 0 then
          { ctx1 with crossConstraints := ctx1.crossConstraints.push { slots := #[idx - 1, idx], relation := .distinct } }
        else ctx1
      let expr : ObjectExpr :=
        match slot.count with
        | .exact 1 | .upTo 1 => .target idx
        | _ => .allTargets
      return some (expr, ctx2)
  -- Simple object expressions (`"enchanted creature"`, `"equipped creature"`, `"attacking creatures"`, etc.)
  if let some oe := parseSimpleObjectExpr? s then
    return some (oe, ctx)
  -- Noun phrase -> `.inZones np.filter.zones np.filter.pred`
  if let some np := parseNounPhrase s then
    if !np.isTarget then
      let zs0 :=
        match np.filter.zones.owner, ctx.lastPlayer? with
        | .ofPlayer (.triggerPlayer .actor), some lp => { np.filter.zones with owner := .ofPlayer lp }
        | .ofPlayer (.triggerPlayer .actor), none =>
          match ctx.triggerPlayerRole? with
          | some tp => { np.filter.zones with owner := .ofPlayer tp }
          | none => np.filter.zones
        | _, _ => np.filter.zones
      let mentionsTargetPlayer :=
        l.contains "target player controls" || l.contains "target opponent controls" ||
        l.contains "target player's " || l.contains "target opponent's "
      if mentionsTargetPlayer then
        let pf := if l.contains "target opponent" then PlayerFilter.opponent else PlayerFilter.any
        let (idx, c1) := ctx.pushTargetSlot { domain := .player pf }
        let c2 := { c1 with lastPlayer? := some (.target idx) }
        let zs' := if idx > 0 then remapZoneSetTarget0 idx zs0 else zs0
        let pred' := if idx > 0 then remapObjPredTarget0 idx np.filter.pred else np.filter.pred
        return some (.inZones zs' pred', c2)
      let pred0 :=
        if ctx.isSpell then
          match ctx.lastTargetSlot? with
          | some slot =>
            let rec replaceOtherThis : ObjectPred → ObjectPred
              | .otherThan .this => .otherThan (.target slot)
              | .all ps => .all (ps.map replaceOtherThis)
              | .any ps => .any (ps.map replaceOtherThis)
              | .not p => .not (replaceOtherThis p)
              | p => p
            replaceOtherThis np.filter.pred
          | none => np.filter.pred
        else np.filter.pred
      return some (.inZones zs0 pred0, ctx)
  return none

/-- Parse a damage recipient (`"any target"`, `"any other target"`, `"each opponent"`,
`"each creature"`, `"each creature and each player"`, `"target ..."`, `"it"`, etc.). -/
def parseRecipientWithCtx (ctx : DiscourseCtx) (raw : String) :
    Option (RecipientExpr × DiscourseCtx) := Id.run do
  let s := pClean raw
  let l := pLower s
  if l.isEmpty then return none
  if l == "any target" then
    let (idx, ctx') := ctx.pushTargetSlot { domain := .anyTarget }
    return some (.targetSlot idx, ctx')
  if l == "any other target" then
    let (idx, ctx') := ctx.pushTargetSlot { domain := .anyTarget .any }
    return some (.targetSlot idx, ctx')
  if l == "each creature and each player" then
    return some (.both (.inZones .battlefield (.hasType .creature)) .eachPlayer, ctx)
  if l == "each creature and each opponent" then
    return some (.both (.inZones .battlefield (.hasType .creature)) .opponents, ctx)
  if l == "each other creature and each player" then
    return some (.both (.inZones .battlefield (.all #[.hasType .creature, .otherThan .this])) .eachPlayer, ctx)
  if l == "each other creature and each opponent" then
    return some (.both (.inZones .battlefield (.all #[.hasType .creature, .otherThan .this])) .opponents, ctx)
  if l == "each creature you don't control and each opponent" then
    return some (.both (.inZones .battlefield (.all #[.hasType .creature, .not (.controlledBy .you)])) .opponents, ctx)
  if l == "each opponent and each planeswalker they control" then
    return some (.both (.inZones .battlefield (.all #[.hasType .planeswalker, .controlledBy .opponent])) .opponents, ctx)
  -- Compound `"<target1> and <target2>"` (e.g., `"up to one target creature or planeswalker and target player"`)
  if let some (lhs, rhs) := pSplitFirstCI? s " and " then
    if (pLower lhs).contains "target " && (pLower rhs).contains "target " then
      match parseTargetSlot lhs, parseTargetSlot rhs with
      | some s1, some s2 =>
        let (_, ctx1) := ctx.pushTargetSlot s1
        let (_, ctx2) := ctx1.pushTargetSlot s2
        return some (.allTargets, ctx2)
      | _, _ => pure ()
    -- Compound `"<objs> and <players>"` (non-targeted)
    if !(pLower lhs).contains "target " && !(pLower rhs).contains "target " then
      match parseObjWithCtx ctx lhs, parsePlayerWithCtx ctx rhs with
      | some (oe, c1), some (pe, c2) =>
        let _ := c1
        return some (.both oe pe, c2)
      | _, _ =>
        match parsePlayerWithCtx ctx lhs, parseObjWithCtx ctx rhs with
        | some (pe, _), some (oe, c2) => return some (.both oe pe, c2)
        | _, _ => pure ()
  -- Single target slot (`"target creature"`, `"target player"`, `"up to two targets"`, `"target creature or planeswalker"`, etc.)
  if l.contains "target " || l.endsWith " target" || l.endsWith " targets" then
    if let some slot := parseTargetSlot s then
      let (idx, ctx') := ctx.pushTargetSlot slot
      match slot.domain, slot.count with
      | .player _, .exact 1 | .player _, .upTo 1 => return some (.players (.target idx), ctx')
      | _, .exact 1 | _, .upTo 1 => return some (.targetSlot idx, ctx')
      | _, _ => return some (.allTargets, ctx')
  -- Player recipient (`"you"`, `"each opponent"`, `"each player"`, `"its controller"`, `"that player"`, ...)
  if let some (pe, ctx') := parsePlayerWithCtx ctx s then
    return some (.players pe, ctx')
  -- Object recipient (`"each creature"`, `"each attacking creature"`, `"it"`, `"this creature"`, ...)
  if let some (oe, ctx') := parseObjWithCtx ctx s then
    return some (.objects oe, ctx')
  return none

/-! ### `DestZoneSpec`, `MoveMods`, `MoveChoiceSpec` & `GrantPlayPermSpec` Parsers -/

/-- Parse a destination-zone phrase and trailing entry/move modifiers
(`"onto the battlefield [under your/its owner's/its controller's control] [tapped] [and attacking] [transformed] [with N <k> counter(s) on it] [with haste] [with no abilities] [as <type> in addition to its other types] [as a Food token]"`,
`"into your hand"`, `"to its owner's hand"`, `"into exile [linked to this permanent]"`,
`"on top of your library"`, `"on the bottom of its owner's library [in a random order]"`, etc.). -/
def parseDestZoneWithMods? (ctx : DiscourseCtx) (raw : String) :
    Option (DestZoneSpec × MoveMods × DiscourseCtx) := Id.run do
  let mut s := pClean raw
  let mut mods : MoveMods := {}
  let mut ctx' := ctx

  -- Iteratively peel trailing entry/move modifiers (`as a Food token`, `as ... in addition to its other types`,
  -- `with no abilities`, `with <kws>`, `with N <ctr> counters on it`, `tapped`, `attacking`, `transformed`,
  -- `face down`, `goaded`, `linked to this permanent`, `attached to ...`, `then shuffle`)
  let mut progress := true
  while progress do
    progress := false
    if let some b := (pDropSuffixCI? s ", then shuffle").orElse (fun _ => pDropSuffixCI? s " then shuffle") then
      mods := { mods with shuffleAfter := true }; s := b; progress := true
    else if let some b := pDropSuffixCI? s " with no abilities" then
      mods := { mods with enterLoseAllAbilities := true }; s := b; progress := true
    else if let some (b, predefStr) := pSplitLastCI? s " as a " then
      if let some pw := pDropSuffixCI? predefStr " token" then
        if let some pt := parsePredefinedTokenWord? pw then
          mods := { mods with enterAsPredefined? := some pt }; s := b; progress := true
    else if let some (b, tyModStr) := pSplitLastCI? s " as " then
      if let some core := pDropSuffixCI? tyModStr " in addition to its other types" then
        let core := ((pDropPrefixCI? core "a ").orElse fun _ => pDropPrefixCI? core "an ") |>.getD core
        let mut tys : Array CardType := #[]
        let mut subs : Array CardSubtype := #[]
        let mut ok := true
        for w in pWords core do
          if let some t := CardType.ofOracle? (pLower w) then tys := tys.push t
          else if let some sb := CardSubtype.ofOracle? w then subs := subs.push sb
          else ok := false
        if ok && (!tys.isEmpty || !subs.isEmpty) then
          mods := { mods with enterTypeMod? := some { mode := .add, types := tys, subtypes := subs } }
          s := b; progress := true
    else if let some (b, after) := pSplitLastCI? s " with " then
      let ctrClean0 :=
        (pDropSuffixCI? after " on it").orElse (fun _ =>
        (pDropSuffixCI? after " on them").orElse (fun _ => some after)) |>.getD after
      let ctrClean := ctrClean0.replace " additional " " "
      if let some (k, v) := parseCounterSpec? ctrClean then
        mods := { mods with enterCounters := mods.enterCounters.push (k, v) }
        s := b; progress := true
      else if let some kws := parseKeywordList? ctrClean0 then
        mods := { mods with enterKeywords := mods.enterKeywords ++ kws }
        s := b; progress := true
    else if let some b := (pDropSuffixCI? s " tapped and attacking").orElse (fun _ => pDropSuffixCI? s ", tapped and attacking") then
      mods := { mods with tapped := true, attacking := true }; s := b; progress := true
    else if let some b := (pDropSuffixCI? s " tapped").orElse (fun _ => pDropSuffixCI? s ", tapped") then
      mods := { mods with tapped := true }; s := b; progress := true
    else if let some b := (pDropSuffixCI? s " attacking").orElse (fun _ => pDropSuffixCI? s ", attacking") then
      mods := { mods with attacking := true }; s := b; progress := true
    else if let some b := pDropSuffixCI? s " transformed" then
      mods := { mods with mayTransformOnEnter := true }; s := b; progress := true
    else if let some b := pDropSuffixCI? s " face down" then
      mods := { mods with enterFaceDown := true }; s := b; progress := true
    else if let some b := pDropSuffixCI? s " goaded" then
      mods := { mods with goaded := true }; s := b; progress := true
    else if let some b := pDropSuffixCI? s " linked to this permanent" then
      mods := { mods with linkToSource := true }; s := b; progress := true
    if !progress then
      if let some (b, hostStr) := pSplitLastCI? s " attached to " then
        if let some (hostObj, c2) := parseObjWithCtx ctx' hostStr then
          mods := { mods with attachTo? := some hostObj }; ctx' := c2; s := b; progress := true

  let low := pLower s
  -- Battlefield (also handling `"to/onto the battlefield tapped [and attacking] under ... control"`)
  if low == "onto the battlefield" || low == "to the battlefield" then
    return some (.battlefield .controller, mods, ctx')
  if let some (ctrlRest, midTap, midAtk) :=
      ((pDropPrefixCI? s "onto the battlefield tapped and attacking under ").map (·, true, true)).orElse fun _ =>
      ((pDropPrefixCI? s "to the battlefield tapped and attacking under ").map (·, true, true)).orElse fun _ =>
      ((pDropPrefixCI? s "onto the battlefield tapped under ").map (·, true, false)).orElse fun _ =>
      ((pDropPrefixCI? s "to the battlefield tapped under ").map (·, true, false)).orElse fun _ =>
      ((pDropPrefixCI? s "onto the battlefield under ").map (·, false, false)).orElse fun _ =>
      ((pDropPrefixCI? s "to the battlefield under ").map (·, false, false)) then
    mods := { mods with tapped := mods.tapped || midTap, attacking := mods.attacking || midAtk }
    let ctrlCore := (pDropSuffixCI? ctrlRest " control").getD ctrlRest
    let cl := pLower ctrlCore
    if cl == "your" then
      return some (.battlefield .controller, mods, ctx')
    else if cl == "its owner's" || cl == "their owners'" || cl == "their owner's" then
      return some (.battlefield .owner, mods, ctx')
    else if cl == "its controller's" || cl == "their controllers'" || cl == "their controller's" then
      let obj := ctx'.lastSubject?.getD (if ctx'.isTrigger then .triggerSubject else .this)
      return some (.battlefield (.player (.controllerOf obj)), mods, ctx')
    else if let some (p, c2) := parsePossessivePlayerWithCtx ctx' ctrlCore then
      return some (.battlefield (.player p), mods, c2)
    return some (.battlefield .controller, mods, ctx')

  -- Hand
  if low == "into your hand" || low == "to your hand" then
    return some (.hand .controller, mods, ctx')
  if low == "to its owner's hand" || low == "into its owner's hand" ||
      low == "to their owners' hands" || low == "into their owners' hands" ||
      low == "to their owner's hand" then
    return some (.hand .owner, mods, ctx')
  if let some hRest := (pDropPrefixCI? s "into ").orElse (fun _ => pDropPrefixCI? s "to ") then
    if let some whoStr := (pDropSuffixCI? hRest " hand").orElse (fun _ => pDropSuffixCI? hRest " hands") then
      if let some (p, c2) := parsePossessivePlayerWithCtx ctx' whoStr then
        return some (.hand (.player p), mods, c2)

  -- Graveyard / Exile
  if low == "into your graveyard" || low == "into its owner's graveyard" ||
      low == "into their owners' graveyards" || low == "to your graveyard" ||
      low == "into a graveyard" || low == "into the graveyard" || low == "into their graveyard" then
    return some (.graveyard, mods, ctx')
  if low == "into exile" || low == "to exile" || low == "exile" then
    return some (.exile, mods, ctx')

  -- Library (top / bottom / bottom random / offset / shuffle)
  if low.contains "library" || low == "on top" ||
      low.startsWith "second from the top" || low.startsWith "third from the top" then
    if low == "on top" then
      return some (.library .owner .top false, mods, ctx')
    let whose : DestOwnerSpec :=
      if low.contains "your library" || low.contains "its owner's library" ||
          low.contains "their owners' libraries" || low.contains "their owner's library" ||
          low.contains "their library" then .owner
      else .owner
    let orBot := low.contains "or on the bottom" || low.contains "or bottom"
    if low.contains "second from the top" then
      return some (.library whose (.fromTop (.const 1)) orBot, mods, ctx')
    if low.contains "third from the top" then
      return some (.library whose (.fromTop (.const 2)) orBot, mods, ctx')
    if low.contains "top or bottom" || (low.contains "on top" && orBot) then
      return some (.library whose .top true, mods, ctx')
    if low.startsWith "on top of " || low.startsWith "to the top of " then
      return some (.library whose .top false, mods, ctx')
    if low.startsWith "on the bottom of " || low.startsWith "to the bottom of " then
      let pos : LibraryPosSpec :=
        if low.contains "random order" then .bottomRandom else .bottom
      return some (.library whose pos false, mods, ctx')
    if low.startsWith "into " && low.contains "library" then
      return some (.library whose .shuffledIn false, mods, ctx')

  return none

/-- Parse a `GrantPlayPermSpec` (`"[Until ...,] You may cast/play [up to N of] <objs> [now] [until end of turn / until the end of your next turn / for as long as it/this permanent remains exiled] [without paying its/their mana cost(s)], [and mana of any type can be spent to cast it/them]"). -/
def parseGrantPlayPermClause? (ctx : DiscourseCtx) (raw : String) :
    Option (ObjectExpr × GrantPlayPermSpec × DiscourseCtx) := Id.run do
  let mut s := pClean raw
  let mut anyColor := false
  let mut free := false
  let mut castNow := false
  let mut allowLands := false
  let mut asFlashback := false
  let mut payLife := false
  let mut copyAndCast := false
  let mut exileOnResolve := false
  let mut dur : DurationExpr := .untilEndOfTurn
  let mut maxCasts? : Option Nat := none
  let mut maxTotalMv? : Option ValueExpr := none
  let mut cond? : Option Condition := none
  let mut filter? : Option ObjectPred := none

  -- Peel `" (with flashback)"` / `" with flashback"`
  if let some b := (pDropSuffixCI? s " (with flashback)").orElse (fun _ => pDropSuffixCI? s " with flashback") then
    asFlashback := true; s := b

  -- Peel leading duration (`"Until the end of your next turn, you may play ..."`, `"For as long as they remain exiled, ..."`)
  let mut hasDur := false
  if let some r := pDropPrefixCI? s "until the end of your next turn, " then
    dur := .untilEndOfNextTurnOf .you; hasDur := true; s := r
  else if let some r := pDropPrefixCI? s "until your next turn, " then
    dur := .untilNextTurnOf .you; hasDur := true; s := r
  else if let some r := pDropPrefixCI? s "until end of turn, " then
    dur := .untilEndOfTurn; hasDur := true; s := r
  else if let some r := (pDropPrefixCI? s "for as long as it remains exiled, ").orElse
      (fun _ => (pDropPrefixCI? s "for as long as they remain exiled, ").orElse
        (fun _ => pDropPrefixCI? s "for as long as this permanent remains exiled, ")) then
    dur := .indefinite; hasDur := true; s := r

  -- Peel `", and mana of any type can be spent to cast ..."`
  if let some (b, _) := (pSplitFirstCI? s ", and mana of any type can be spent").orElse
      (fun _ => pSplitFirstCI? s " and mana of any type can be spent") then
    anyColor := true
    s := b

  -- Peel `"by paying life equal to their mana value rather than paying their mana cost"` (`Inside Information`)
  if let some (b, _) := (pSplitFirstCI? s " by paying life equal to ").orElse
      (fun _ => pSplitFirstCI? s " paying life equal to ") then
    payLife := true; s := b

  -- Peel trailing `" if <cond>"` (`Flameshape`: `"you may play them if you control a Wizard"`)
  if let some (b, cStr) := pSplitLastCI? s " if " then
    if let some c := parseCondition cStr then
      cond? := some c; s := b

  -- Peel `"without paying its/their mana cost(s)"`
  for sfx in #[
    " without paying its mana cost",
    " without paying their mana costs",
    " without paying their mana cost"
  ] do
    if let some b := pDropSuffixCI? s sfx then
      free := true; s := b
    else if let some (a, b) := pSplitFirstCI? s sfx then
      free := true; s := (a ++ " " ++ b).trimAscii.copy

  -- Peel trailing duration clauses
  if let some b := pDropSuffixCI? s " until the end of your next turn" then
    dur := .untilEndOfNextTurnOf .you; hasDur := true; s := b
  else if let some b := pDropSuffixCI? s " until your next turn" then
    dur := .untilNextTurnOf .you; hasDur := true; s := b
  else if let some b := (pDropSuffixCI? s " until end of turn").orElse
      (fun _ => pDropSuffixCI? s " this turn") then
    dur := .untilEndOfTurn; hasDur := true; s := b
  else if let some b := (pDropSuffixCI? s " for the rest of the game").orElse
      (fun _ => (pDropSuffixCI? s " for as long as it remains exiled").orElse
        (fun _ => (pDropSuffixCI? s " for as long as they remain exiled").orElse
          (fun _ => (pDropSuffixCI? s " for as long as that card remains exiled").orElse
            (fun _ => pDropSuffixCI? s " for as long as this permanent remains exiled")))) then
    dur := if (pLower s).contains "for the rest of the game" then .indefinite else .whileInZone .this .exile
    hasDur := true
    s := b
  else if let some b := pDropSuffixCI? s " now" then
    castNow := true; s := b

  if let some b := pDropSuffixCI? s " now" then
    castNow := true; s := b

  -- Peel `"you may play "` vs `"you may cast "`
  let mut objRaw := ""
  if let some r := pDropPrefixCI? s "you may play " then
    allowLands := true; objRaw := r
  else if let some r := pDropPrefixCI? s "you may cast " then
    objRaw := r
  else
    return none

  -- Peel `"up to N of "` / `"up to N spells "` / `"any number of spells "`
  if let some upRest := pDropPrefixCI? objRaw "up to " then
    let uws := pWords upRest
    if uws.size >= 3 && (pLower uws[1]! == "of" || pLower uws[1]! == "spells" || pLower uws[1]! == "spell") then
      if let some n := parseNatWord? uws[0]! then
        maxCasts? := some n
        objRaw := String.intercalate " " (uws.extract 2 uws.size).toList
  else if let some anyRest := pDropPrefixCI? objRaw "any number of " then
    objRaw := anyRest

  -- Peel `"<pred> [with total mana value <V> or less] from among <objs>"`
  if let some fromAmong := pDropPrefixCI? objRaw "from among " then
    objRaw := fromAmong
  else if let some (predPart0, fromAmong) := pSplitFirstCI? objRaw " from among " then
    let mut predPart := predPart0
    if let some (b, mvPart) := pSplitFirstCI? predPart " with total mana value " then
      let mvStr := (pDropSuffixCI? mvPart " or less").getD mvPart
      if let some mv := parseValueExpr mvStr then
        maxTotalMv? := some mv; predPart := b
    let pCore := ((pDropSuffixCI? predPart " spells").orElse fun _ =>
      (pDropSuffixCI? predPart " spell").orElse fun _ =>
      (pDropSuffixCI? predPart " cards").orElse fun _ =>
      pDropSuffixCI? predPart " card") |>.getD predPart
    if !pCore.isEmpty && pLower pCore != "spells" && pLower pCore != "spell" then
      if let some np := parseNounPhrase pCore then
        filter? := some np.filter.pred
    objRaw := fromAmong

  -- Peel `"with total mana value <V> or less"` / `"with mana value less than or equal to <V>"`
  if let some (b, mvPart) := pSplitFirstCI? objRaw " with total mana value " then
    let mvStr := (pDropSuffixCI? mvPart " or less").getD mvPart
    let mvVal? : Option ValueExpr :=
      if pLower mvStr == "that much" || pLower mvStr == "that damage" then some .eventAmount
      else parseValueExpr mvStr
    if let some mv := mvVal? then
      maxTotalMv? := some mv
      objRaw := b
  else if let some (b, mvPart) := pSplitFirstCI? objRaw " with mana value less than or equal to " then
    let mvVal? : Option ValueExpr :=
      if pLower mvPart == "that damage" || pLower mvPart == "that much" then some .eventAmount
      else parseValueExpr mvPart
    if let some mv := mvVal? then
      maxTotalMv? := some mv
      objRaw := b

  -- Normalize `"<type> spell from your graveyard"` -> `"<type> card in your graveyard"` (`Bilbo`)
  if let some pre := pDropSuffixCI? objRaw " spell from your graveyard" then
    objRaw := pre ++ " card in your graveyard"
    castNow := true

  -- Resolve object expression
  let lObj := pLower objRaw
  if lObj == "the copies" || lObj == "those copies" then
    copyAndCast := true
  if !hasDur && !asFlashback && !copyAndCast then
    castNow := true
  if lObj == "a card that player milled this way" || lObj == "a card that player exiled this way" ||
      lObj == "a card they milled this way" || lObj == "a card they exiled this way" then
    maxCasts? := maxCasts?.orElse (fun _ => some 1)
    let v := ctx.lastActionVar?.getD ⟨0⟩
    let ownerP := ctx.lastPlayer?.getD (.triggerPlayer .actor)
    let filtObj : ObjectExpr := .filter (.stepObjects v) (.ownedBy (.ofExpr ownerP))
    return some (filtObj, {
      duration := dur
      landsAllowed := allowLands
      freeCast := free
      anyManaColor := anyColor
      payLifeInsteadOfMana := payLife
      copyAndCast := copyAndCast
      asFlashback := asFlashback
      castNow := castNow
      exileOnResolveInstead := exileOnResolve
      maxCasts? := maxCasts?
      maxTotalManaValue? := maxTotalMv?
      condition? := cond?
      filter? := filter?
    }, ctx)
  let some (obj0, ctx') :=
    (match parseObjWithCtx ctx objRaw with
    | some res => some res
    | none =>
      if lObj == "the copy" || lObj == "that copy" || lObj == "the copies" || lObj == "those copies" ||
          lObj == "cards exiled this way" || lObj == "a card exiled this way" then
        some (ctx.lastActionVar?.map ObjectExpr.stepObjects |>.getD (if ctx.slots.isEmpty then .costPaidObjects else .triggerSubject), ctx)
      else if lObj == "this card" || lObj == "this permanent" then
        some (.this, ctx)
      else if lObj.startsWith "the exiled " || lObj.startsWith "that " || lObj.startsWith "those " then
        let base :=
          match ctx.lastActionVar? with
          | some v => ObjectExpr.stepObjects v
          | none => ctx.lastSubject?.getD .triggerSubject
        some (base, ctx)
      else none)
    | return none
  let obj : ObjectExpr :=
    match lObj, obj0, ctx.lastRevealUntilPred? with
    | "that card", .stepObjects v, some pred => .filter (.stepObjects v) pred
    | _, _, _ => obj0

  return some (obj, {
    duration := dur
    landsAllowed := allowLands
    freeCast := free
    anyManaColor := anyColor
    payLifeInsteadOfMana := payLife
    copyAndCast
    asFlashback
    castNow
    exileOnResolveInstead := exileOnResolve
    maxCasts?
    maxTotalManaValue? := maxTotalMv?
    condition? := cond?
    filter?
  }, ctx')

/-! ### `SearchLibrarySpec` Parser (CR 701.19) -/

/-- Parse a `"search <zones> for <count> <filter> card(s) ..."` clause (plus optional
following `"If <cond>, untap it."` or `"If you search your library this way, shuffle."`
sentences), returning `(Instruction × consumedSentences × DiscourseCtx)`. -/
def parseSearchLibrarySeq? (ctx : DiscourseCtx) (sents : Array String) (idx : Nat) :
    Option (Instruction × Nat × DiscourseCtx) := Id.run do
  if idx >= sents.size then return none
  let sent := pClean sents[idx]!
  -- Split optional `"<player> searches "` vs `"search "`
  let some (searcher, afterSearch, ctx1) :=
    (match pDropPrefixCI? sent "search " with
    | some r => some (PlayerExpr.you, r, ctx)
    | none =>
      match pSplitFirstCI? sent " searches " with
      | some (whoStr, r) =>
        match parsePlayerWithCtx ctx whoStr with
        | some (who, c1) => some (who, r, c1)
        | none => none
      | none => none)
    | return none

  let some (zonesRaw, restFor) := pSplitFirstCI? afterSearch " for " | return none
  let some (zones, ctx2) := parseZoneSetWithCtx ctx1 zonesRaw | return none

  -- Separate `"<count> <filter> card(s) [with different names]"` from `, reveal ... / , put ... / and put ...`
  let (specPart, afterSpec) :=
    match pSplitFirstCI? restFor ", " with
    | some (a, b) => (a, b)
    | none =>
      match pSplitFirstCI? restFor " and put " with
      | some (a, b) => (a, "put " ++ b)
      | none => (restFor, "")

  let mut specCore := pClean specPart
  let mut gc? : Option GroupTargetConstraint := none
  if let some b := pDropSuffixCI? specCore " with different names" then
    gc? := some .distinctNames; specCore := b
  else if let some b := pDropSuffixCI? specCore " of different card types" then
    gc? := some .distinctCardTypes; specCore := b

  -- Parse count (`up to N`, `up to X`, `up to that many/much`, `a/an`, `N`)
  let (count, filterRaw0) : ExprCountRange × String :=
    if let some r := pDropPrefixCI? specCore "up to " then
      if let some r2 := (pDropPrefixCI? r "that many ").orElse (fun _ => pDropPrefixCI? r "that much ") then
        (.upTo .eventAmount, r2)
      else if let some (vStr, rest) := pSplitFirstCI? r " basic land" then
        let v := (ctx2.resolveStepMetric? vStr).orElse (fun _ => parseCountVal? vStr) |>.getD (.const 1)
        (.upTo v, ("basic land " ++ rest).trimAscii.copy)
      else
        let ws := pWords r
        if ws.size >= 2 then
          match parseCountVal? ws[0]! with
          | some v => (.upTo v, String.intercalate " " (ws.extract 1 ws.size).toList)
          | none => (.upTo (.const 1), r)
        else (.upTo (.const 1), r)
    else if let some r := pDropPrefixCI? specCore "any number of " then
      (.anyNumber, r)
    else if let some r := (pDropPrefixCI? specCore "that many ").orElse (fun _ => pDropPrefixCI? specCore "that much ") then
      (.upTo (ctx2.resolveStepMetric? "that many" |>.getD .eventAmount), r)
    else if let some r := (pDropPrefixCI? specCore "a ").orElse (fun _ => pDropPrefixCI? specCore "an ") then
      (.upTo (.const 1), r)
    else
      let ws := pWords specCore
      if ws.size >= 2 then
        match parseCountVal? ws[0]! with
        | some v => (.upTo v, String.intercalate " " (ws.extract 1 ws.size).toList)
        | none => (.upTo (.const 1), specCore)
      else (.upTo (.const 1), specCore)

  -- Clean trailing `" card"` / `" cards"` / `" card card"` (keeping `"permanent card"` intact)
  let mut filterRaw := filterRaw0.trimAscii.copy
  if pLower filterRaw != "permanent card" && pLower filterRaw != "permanent cards" then
    if let some b := (pDropSuffixCI? filterRaw " cards").orElse (fun _ => pDropSuffixCI? filterRaw " card") then
      filterRaw := b
  -- Parse object predicate (also handling `"basic Plains, Island, or Swamp land"` list)
  let rawFilterPred : ObjectPred :=
    if filterRaw.isEmpty || pLower filterRaw == "any" then .anyObject
    else
      match parseNounPhrase filterRaw with
      | some np => np.filter.pred
      | none =>
        match parseNounPhrase (filterRaw ++ " card") with
        | some np => np.filter.pred
        | none => .anyObject
  let filterPred : ObjectPred :=
    match rawFilterPred with
    | .isKind .card => .anyObject
    | .all ps =>
      let kept := ps.filter (· != .isKind .card)
      match kept.toList with
      | [] => .anyObject
      | [p] => p
      | _ => .all kept
    | other => other

  -- Parse `, [reveal it/them,] [put it/them <dest> [and one <dest2>]], [then shuffle]`
  let mut after := afterSpec
  let mut reveal := false
  let mut shuffle := false
  let mut dest : DestZoneSpec := .hand .controller
  let mut mods : MoveMods := {}
  let mut secondDest? : Option (DestZoneSpec × MoveMods) := none
  let mut ctx3 := ctx2
  let mut consumed : Nat := 1

  if let some r := (pDropPrefixCI? after "reveal it, ").orElse
      (fun _ => (pDropPrefixCI? after "reveal them, ").orElse
        (fun _ => (pDropPrefixCI? after "reveal that card, ").orElse
          (fun _ => pDropPrefixCI? after "reveal those cards, "))) then
    reveal := true; after := r

  -- Special pattern: `"then shuffle and put that card on top"`
  if (pLower after).startsWith "then shuffle and put " && (pLower after).contains "on top" then
    shuffle := true
    dest := .library .owner .top false
  else
    -- Peel trailing `", then shuffle"` / `"then shuffle"`
    if let some b := (pDropSuffixCI? after ", then shuffle").orElse
        (fun _ => (pDropSuffixCI? after ", then shuffle your library").orElse
          (fun _ => pDropSuffixCI? after " then shuffle")) then
      shuffle := true; after := b
    if pLower after == "exile them" || pLower after == "exile it" then
      dest := .exile
      mods := { mods with linkToSource := true }
    else
      -- Parse `"put it/them/that card/one <dest> [and one/the other <dest2>]"`
      let putBody :=
        ((pDropPrefixCI? after "put it ").orElse fun _ =>
         (pDropPrefixCI? after "put them ").orElse fun _ =>
         (pDropPrefixCI? after "put that card ").orElse fun _ =>
         (pDropPrefixCI? after "put those cards ").orElse fun _ =>
         pDropPrefixCI? after "put one ").getD after
      let (d1Raw, d2Raw?) :=
        match (pSplitFirstCI? putBody " and one ").orElse (fun _ => pSplitFirstCI? putBody " and the other ") with
        | some (a, b) => (a, some b)
        | none => (putBody, none)
      if let some (d1, m1, c3) := parseDestZoneWithMods? ctx3 d1Raw then
        dest := d1; mods := m1; ctx3 := c3
      if let some d2Str := d2Raw? then
        if let some (d2, m2, c4) := parseDestZoneWithMods? ctx3 d2Str then
          secondDest? := some (d2, m2); ctx3 := c4

  -- Optional next sentence: `"If you search your library this way, shuffle."` or `"Then shuffle."`
  if idx + consumed < sents.size then
    let nxtLow := pLower (pClean sents[idx + consumed]!)
    if nxtLow == "then shuffle" || nxtLow == "shuffle" ||
        nxtLow == "if you search your library this way, shuffle" ||
        nxtLow == "if you searched your library this way, shuffle" then
      shuffle := true
      consumed := consumed + 1

  -- Optional next sentence: `"If <cond>, untap it."`
  let mut untapIf? : Option Condition := none
  if idx + consumed < sents.size then
    let nxt := pClean sents[idx + consumed]!
    if let some restIf := pDropPrefixCI? nxt "if " then
      if let some (cStr, thenStr) := pSplitFirstCI? restIf ", " then
        let tl := pLower thenStr
        if tl == "untap it" || tl == "untap that land" then
          if let some cond := parseCondition cStr then
            untapIf? := some cond
            consumed := consumed + 1

  return some (.player (.searchLibrary {
    searcher, zones, filter := filterPred, count, groupConstraint? := gc?
    dest, mods, secondDest?, reveal, shuffle, untapIf?
  }), consumed, ctx3)

/-! ### `InspectLibrarySpec` Parser -/

/-- Parse a `"put the rest ..."` / `"shuffle the rest ..."` / `"exile the rest"` sentence into `RestPlacement`. -/
def parseRestPlacement? (raw : String) : Option RestPlacement :=
  let l := pLower (pClean raw)
  if l.contains "bottom" && l.contains "random order" then some .bottomRandom
  else if l.contains "bottom" && l.contains "any order" then some .bottomAnyOrder
  else if l.contains "bottom" then some .bottomRandom
  else if l.contains "graveyard" then some .graveyard
  else if l.startsWith "exile the rest" || l.contains "into exile" then some .exile
  else if l.contains "shuffle" && l.contains "library" then some .shuffleIntoLibrary
  else none

/-- Parse an `InspectLibrarySpec` starting at `sents[idx]`, consuming 1–4 sentences
(`look at the top N ...`, `reveal the top N ...`, `reveal/exile cards from the top of ... until ...`,
`mill N cards. Put ... from among them ...`, `exile all but the bottom card of ...`,
`choose N cards from outside the game. Put ...`). -/
def parseInspectLibrarySeq? (ctx : DiscourseCtx) (sents : Array String) (idx : Nat) :
    Option (Instruction × Nat × DiscourseCtx) := Id.run do
  if idx >= sents.size then return none
  let s0 := pClean sents[idx]!
  let l0 := pLower s0

  -- 1. `"Exile all but the bottom card of <player>'s library"`
  if let some libWho := (pDropPrefixCI? s0 "exile all but the bottom card of ").orElse
      (fun _ => pDropPrefixCI? s0 "exile all cards from ") then
    let whoRaw := (pDropSuffixCI? libWho " library except the bottom card").orElse
      (fun _ => pDropSuffixCI? libWho " library") |>.getD libWho
    if let some (who, ctx1) := parsePossessivePlayerWithCtx ctx whoRaw then
      return some (.player (.inspectLibrary {
        source := .allButBottom who
        action := .moveAll .exile
        rest := .leaveInPlace
      }), 1, ctx1)

  -- 2. `"You may choose/reveal [exactly] N card(s) ... from outside the game"` (`Extrapolate the Impossible`)
  let outsideRest? :=
    (pDropPrefixCI? s0 "you may choose ").orElse fun _ =>
    (pDropPrefixCI? s0 "choose ").orElse fun _ =>
    (pDropPrefixCI? s0 "you may reveal exactly ").orElse fun _ =>
    (pDropPrefixCI? s0 "you may reveal ").orElse fun _ =>
    pDropPrefixCI? s0 "reveal exactly "
  if let some r := outsideRest? then
    if (pLower r).contains "from outside the game" then
      let isOpt := l0.startsWith "you may "
      let ws := pWords r
      let n := (ws[0]?.bind parseNatWord?).getD 1
      let mut action : InspectAction := .none
      let mut consumed : Nat := 1
      let mut ctx1 := ctx
      if idx + consumed < sents.size then
        let s1Low := pLower (pClean sents[idx + consumed]!)
        if s1Low.contains "chooses one of them" then
          consumed := consumed + 1
      if idx + consumed < sents.size then
        let sNext := pClean sents[idx + consumed]!
        let putRest? :=
          (pDropPrefixCI? sNext "you put ").orElse (fun _ => pDropPrefixCI? sNext "put ")
        if let some takeRest := putRest? then
          if let some (whatPart, destPart) := pSplitFirstCI? takeRest " from among them " then
            let (cnt, fRaw0) := (parseExprCountRange? whatPart).getD (.exact (.const 1), whatPart)
            let fRaw := ((pDropSuffixCI? fRaw0 " card(s)").orElse fun _ =>
              (pDropSuffixCI? fRaw0 " cards").orElse fun _ => pDropSuffixCI? fRaw0 " card") |>.getD fRaw0
            let pred :=
              if pLower fRaw == "permanent" || fRaw.isEmpty then .anyObject
              else (parseNounPhrase (fRaw ++ " card")).map (·.filter.pred) |>.getD .anyObject
            if let some (dest, mods, c2) := parseDestZoneWithMods? ctx1 destPart then
              action := .takeMatching pred cnt dest mods
              ctx1 := c2
              consumed := consumed + 1
          else if let some destPart := pDropPrefixCI? takeRest "that card " then
            if let some (dest, mods, c2) := parseDestZoneWithMods? ctx1 destPart then
              action := .takeMatching .anyObject (.exact (.const 1)) dest mods
              ctx1 := c2
              consumed := consumed + 1
      let core : Instruction := .player (.inspectLibrary {
        source := .outsideTheGame .you n
        action
        rest := .leaveInPlace
      })
      return some (if isOpt then .optional .you none core .noop else core, consumed, ctx1)

  -- 3. Parse source sentence: `topCards`, `revealUntil`, or `millCards` (only when followed by `"from among them"`)
  let mut src? : Option InspectSource := none
  let mut inlinePiles? : Option String := none
  let mut ctx1 := ctx

  -- 3a. `"Look at / Reveal the top <N> card(s) of <player>'s library [and exile them face down / and separate them into ...]"`
  let mut inlineAction? : Option String := none
  let mut inlineRest? : Option RestPlacement := none
  let mut inlineMoveAll? : Option (DestZoneSpec × MoveMods) := none
  let topRest? : Option (Bool × String) :=
    match pDropPrefixCI? s0 "look at the top " with
    | some r => some (false, r)
    | none =>
      match pDropPrefixCI? s0 "reveal the top " with
      | some r => some (true, r)
      | none => none
  if let some (rev, r00) := topRest? then
    let (r01, exFaceDown) :=
      match pDropSuffixCI? r00 " and exile them face down" with
      | some a => (a, true)
      | none =>
        match pDropSuffixCI? r00 " and exile it face down" with
        | some a => (a, true)
        | none => (r00, false)
    if exFaceDown then
      inlineMoveAll? := some (.exile, { enterFaceDown := true })
    let (r0, inlAct?) :=
      match pSplitFirstCI? r01 ", put " with
      | some (a, b) =>
        match pSplitFirstCI? b ", then shuffle" with
        | some (b1, _) => (a, some ("put " ++ b1))
        | none => (a, some ("put " ++ b))
      | none => (r01, none)
    if (pLower r01).endsWith ", then shuffle" && inlAct?.isSome then
      inlineRest? := some .shuffleIntoLibrary
    inlineAction? := inlAct?
    let (r, sepPart?) :=
      match pSplitFirstCI? r0 " and separate them into " with
      | some (a, b) => (a, some b)
      | none => (r0, none)
    if let some (cntPart, libPart) := (pSplitFirstCI? r " cards of ").orElse
        (fun _ => pSplitFirstCI? r " card of ") then
      let cnt :=
        if cntPart.isEmpty then .const 1
        else (parseCountVal? cntPart).getD (.const 1)
      let whoRaw := (pDropSuffixCI? libPart " library").getD libPart
      if let some (who, c1) := parsePossessivePlayerWithCtx ctx whoRaw then
        src? := some (.topCards who cnt rev)
        inlinePiles? := sepPart?
        ctx1 := c1
    else if let some libPart := pDropPrefixCI? r "card of " then
      let whoRaw := (pDropSuffixCI? libPart " library").getD libPart
      if let some (who, c1) := parsePossessivePlayerWithCtx ctx whoRaw then
        src? := some (.topCards who (.const 1) rev)
        inlinePiles? := sepPart?
        ctx1 := c1

  -- 3b. `"Reveal/Exile cards from the top of <player>'s library until ..."`
  if src?.isNone then
    let ruInfo? : Option (Bool × Option String × String) :=
      match pDropPrefixCI? s0 "reveal cards from the top of " with
      | some r => some (false, none, r)
      | none =>
        match pDropPrefixCI? s0 "exile cards from the top of " with
        | some r => some (true, none, r)
        | none =>
          match pSplitFirstCI? s0 " exiles cards from the top of " with
          | some (wStr, r) => some (true, some wStr, r)
          | none =>
            match pSplitFirstCI? s0 " reveals cards from the top of " with
            | some (wStr, r) => some (false, some wStr, r)
            | none => none
    if let some (exileWhile, subjWho?, r) := ruInfo? then
      let ctxSubj :=
        match subjWho? with
        | some wStr =>
          match parsePlayerWithCtx ctx wStr with
          | some (p, c) => { c with lastPlayer? := some p }
          | none => ctx
        | none => ctx
      if let some (libPart, untilPart0) := (pSplitFirstCI? r " library until you reveal ").orElse
          (fun _ => (pSplitFirstCI? r " library until you exile ").orElse
            (fun _ => (pSplitFirstCI? r " library until they exile ").orElse
              (fun _ => pSplitFirstCI? r " library until they reveal "))) then
        if let some (who, c1) := parsePossessivePlayerWithCtx ctxSubj libPart then
          -- Peel optional inline `", put ..."` (`Synthetic Destiny`) and `", where X is <V>"` (`Dack Fayden`)
          let (untilPart1, ruInlineAct?) :=
            match pSplitFirstCI? untilPart0 ", put " with
            | some (a, b) => (a, some ("put " ++ b))
            | none => (untilPart0, none)
          if ruInlineAct?.isSome then inlineAction? := ruInlineAct?
          let (untilPart, whereXVal?) : String × Option ValueExpr :=
            match pSplitFirstCI? untilPart1 ", where x is " with
            | some (a, b) => (a, parseValueExpr b)
            | none => (untilPart1, none)
          -- Parse `"<count> <pred> card(s)"`
          let mut uCore := untilPart
          for sfx in #[" card cards", " card card", " cards", " card"] do
            if pLower uCore == "permanent card" then break
            if let some b := pDropSuffixCI? uCore sfx then
              uCore := if (sfx == " card card" || sfx == " card cards") && pLower b == "permanent" then "permanent card" else b
              break
          let (mCnt0, predStr) : ValueExpr × String :=
            if let some rest := (pDropPrefixCI? uCore "a ").orElse (fun _ => pDropPrefixCI? uCore "an ") then
              (.const 1, rest)
            else if let some (vPart, pPart) := pSplitLastCI? uCore " creature" then
              if vPart.isEmpty then (.const 1, uCore)
              else
                let v := (c1.resolveStepMetric? vPart).orElse (fun _ => parseCountVal? vPart) |>.getD (.const 1)
                (v, ("creature " ++ pPart).trimAscii.copy)
            else
              let ws := pWords uCore
              if ws.size >= 2 then
                match parseCountVal? ws[0]! with
                | some v => (v, String.intercalate " " (ws.extract 1 ws.size).toList)
                | none => (.const 1, uCore)
              else (.const 1, uCore)
          let mCnt :=
            match whereXVal?, mCnt0 with
            | some wv, .chosenX => wv
            | _, v => v
          let rawPred :=
            if predStr.isEmpty then .anyObject
            else (parseNounPhrase predStr).map (·.filter.pred)
              |>.orElse (fun _ => (parseNounPhrase (predStr ++ " card")).map (·.filter.pred))
              |>.getD .anyObject
          let pred : ObjectPred :=
            match rawPred with
            | .isKind .card => .anyObject
            | .all ps =>
              let kept := ps.filter (· != .isKind .card)
              match kept.toList with
              | [] => .anyObject
              | [p] => p
              | _ => .all kept
            | other => other
          src? := some (.revealUntil who pred mCnt exileWhile)
          ctx1 := { c1 with lastPlayer? := some who }

  -- 3c. `"Mill N cards"` followed by `"from among them/the milled cards/those cards"`
  if src?.isNone && (l0.startsWith "mill " || l0.contains " mills ") then
    let hasFromAmong (t : String) : Bool :=
      t.contains "from among them" || t.contains "from among the milled cards" ||
      t.contains "from among those cards"
    let hasNextFromAmong :=
      idx + 1 < sents.size && hasFromAmong (pLower sents[idx + 1]!)
    let hasInlineFromAmong := hasFromAmong l0
    if hasNextFromAmong || hasInlineFromAmong then
      let (millHead, millInlineRest?) :=
        match pSplitFirstCI? s0 ", then " with
        | some (a, b) => (a, some b)
        | none => (s0, none)
      let some (who, cntStr, c1) :=
        (match pDropPrefixCI? millHead "mill " with
        | some r => some (PlayerExpr.you, r, ctx)
        | none =>
          match pSplitFirstCI? millHead " mills " with
          | some (wStr, r) =>
            match parsePlayerWithCtx ctx wStr with
            | some (w, c) => some (w, r, c)
            | none => none
          | none => none)
        | return none
      let nStr := ((pDropSuffixCI? cntStr " cards").orElse fun _ => pDropSuffixCI? cntStr " card") |>.getD cntStr
      if let some cnt := parseCountVal? nStr then
        src? := some (.millCards who cnt)
        inlineAction? := millInlineRest?
        ctx1 := c1

  let some src := src? | return none
  let mut consumed : Nat := 1
  let mut action : InspectAction :=
    match inlineMoveAll? with
    | some (d, m) => .moveAll d m
    | none => .none
  let mut restPlace : RestPlacement := inlineRest?.getD .leaveInPlace

  -- Check next-sentence pile split (`Fact or Fiction`: `"An opponent separates those cards into two piles."`)
  if inlinePiles?.isNone && idx + consumed < sents.size then
    let nxtLow := pLower (pClean sents[idx + consumed]!)
    if nxtLow.contains "separates those cards into two piles" || nxtLow.contains "separates them into two piles" then
      inlinePiles? := some (pClean sents[idx + consumed]!)
      consumed := consumed + 1

  -- Handle pile split (`Fact or Fiction` / `Riddles in the Dark`)
  if let some pileDesc := inlinePiles? then
    let isFaceDownUp := (pLower pileDesc).contains "face-down"
    let mut splitter : PlayerExpr := if isFaceDownUp then .you else .opponents
    let mut chooser : PlayerExpr := if isFaceDownUp then .opponents else .you
    let mut d1 : DestZoneSpec := .hand .controller
    let mut d2 : DestZoneSpec := .graveyard
    let mut drawOpt? : Option Nat := none
    if idx + consumed < sents.size then
      let s1 := pClean sents[idx + consumed]!
      if (pLower s1).contains "chooses one of the piles" then
        if (pLower s1).startsWith "an opponent" then
          chooser := .opponents; splitter := .you
        else if (pLower s1).startsWith "you" then
          chooser := .you; splitter := .opponents
        consumed := consumed + 1
    if idx + consumed < sents.size then
      let s2 := pClean sents[idx + consumed]!
      if let some pRest := (pDropPrefixCI? s2 "put that pile ").orElse (fun _ => pDropPrefixCI? s2 "put one pile ") then
        if let some (dest1Str, dest2Str) := pSplitFirstCI? pRest " and the other " then
          if let some (dd1, _, c2) := parseDestZoneWithMods? ctx1 dest1Str then
            d1 := dd1; ctx1 := c2
          if let some (dd2, _, c3) := parseDestZoneWithMods? ctx1 dest2Str then
            d2 := dd2; ctx1 := c3
          consumed := consumed + 1
    if idx + consumed < sents.size then
      if let some rp := parseRestPlacement? sents[idx + consumed]! then
        restPlace := rp
        consumed := consumed + 1
    action := .splitIntoPiles splitter chooser 2 d1 d2 drawOpt?
    return some (.player (.inspectLibrary { source := src, action, rest := restPlace }), consumed, ctx1)

  -- Helper to parse a take/moveAll/distribute sentence (optionally also carrying inline `"and the rest ..."` / `", then shuffle..."` / `"and lose life equal to ... mana value"`)
  let parseActionSent (rawSent : String) (c : DiscourseCtx) : Option (InspectAction × Option RestPlacement × Bool × DiscourseCtx) := Id.run do
    let s0 := pClean rawSent
    -- Strip optional player subject (`"The player puts ..."`, `"You put ..."`)
    let s1 :=
      (pDropPrefixCI? s0 "the player puts ").map ("put " ++ ·)
        |>.orElse (fun _ => (pDropPrefixCI? s0 "that player puts ").map ("put " ++ ·))
        |>.orElse (fun _ => (pDropPrefixCI? s0 "you put ").map ("put " ++ ·))
        |>.getD s0
    -- Split optional inline `" and lose life equal to that permanent's/its mana value"` (`Jhoira`)
    let (s1b, loseMvLife) : String × Bool :=
      match (pSplitFirstCI? s1 " and lose life equal to ").orElse (fun _ => pSplitFirstCI? s1 " and you lose life equal to ") with
      | some (a, b) =>
        if (pLower b).contains "mana value" then (a, true) else (s1, false)
      | none => (s1, false)
    -- Split optional inline rest placement (`" and the rest ..."`, `", then shuffle the rest ..."`, `", then shuffle"`)
    let (s, extraRest?) : String × Option RestPlacement :=
      match pSplitFirstCI? s1b " and the rest " with
      | some (a, b) => (a, parseRestPlacement? ("put the rest " ++ b))
      | none =>
        match pSplitFirstCI? s1b ", then shuffle the rest" with
        | some (a, _) => (a, some .shuffleIntoLibrary)
        | none =>
          match pDropSuffixCI? s1b ", then shuffle" with
          | some a => (a, some .shuffleIntoLibrary)
          | none => (s1b, none)
    let l := pLower s
    -- `"Put one of those cards <dest> for each opponent[ goaded]"`
    if let some r := pDropPrefixCI? s "put one of those cards " then
      if let some (dStr, tail) := pSplitFirstCI? r " for each opponent" then
        if let some (d, m0, c2) := parseDestZoneWithMods? c dStr then
          let m := if (pLower tail).contains "goaded" then { m0 with goaded := true } else m0
          return some (.distributeEachOpponent d m, extraRest?, loseMvLife, c2)
    -- `"Put all of them <dest>"` / `"Put all [creature] cards revealed this way <dest>"` / `"Put that card <dest>"` / `"Put those creature cards <dest>"`
    let moveAllRest? : Option String :=
      (pDropPrefixCI? s "put all of them ").orElse fun _ =>
      (pDropPrefixCI? s "put all revealed cards ").orElse fun _ =>
      (pDropPrefixCI? s "put that card ").orElse fun _ =>
      (pDropPrefixCI? s "put those creature cards ").orElse fun _ =>
      (match pDropPrefixCI? s "put all " with
      | some r =>
        match pSplitFirstCI? r " revealed this way " with
        | some (_, destPart) => some destPart
        | none => none
      | none => none)
    if let some r := moveAllRest? then
      if let some (d, m, c2) := parseDestZoneWithMods? c r then
        return some (.moveAll d m, extraRest?, loseMvLife, c2)
    -- `"You may reveal <pred> card from among them and put it <dest>"` / `"[Reveal it and ]put <count> <pred> card(s) from among them/the milled cards/those cards [at random] <dest>"`
    let mut revTaken := false
    let mut atRand := false
    let mut isMay := false
    let mut work := s
    if let some r := pDropPrefixCI? work "you may " then isMay := true; work := r
    if let some r := (pDropPrefixCI? work "reveal it and ").orElse (fun _ => pDropPrefixCI? work "reveal them and ") then
      revTaken := true; work := r
    if let some r := pDropPrefixCI? work "reveal " then
      if let some (whatPart, putPart) := pSplitFirstCI? r " from among them and put " then
        revTaken := true
        let destPart :=
          (pDropPrefixCI? putPart "it ").orElse (fun _ => pDropPrefixCI? putPart "them ") |>.getD putPart
        let (cnt0, fRaw0) := (parseExprCountRange? whatPart).getD (.upTo (.const 1), whatPart)
        let cnt := if isMay then match cnt0 with | .exact v => .upTo v | other => other else cnt0
        let fRaw :=
          if pLower fRaw0 == "permanent card" || pLower fRaw0 == "permanent cards" ||
              pLower fRaw0 == "permanent card(s)" then "permanent card"
          else ((pDropSuffixCI? fRaw0 " card(s)").orElse fun _ =>
            (pDropSuffixCI? fRaw0 " cards").orElse fun _ => pDropSuffixCI? fRaw0 " card") |>.getD fRaw0
        let rawPred :=
          if fRaw.isEmpty then .anyObject
          else (parseNounPhrase fRaw).map (·.filter.pred)
            |>.orElse (fun _ => (parseNounPhrase (fRaw ++ " card")).map (·.filter.pred))
            |>.getD .anyObject
        let pred : ObjectPred :=
          match rawPred with
          | .isKind .card => .anyObject
          | .all ps =>
            let kept := ps.filter (· != .isKind .card)
            match kept.toList with
            | [] => .anyObject
            | [p] => p
            | _ => .all kept
          | other => other
        if let some (d, m, c2) := parseDestZoneWithMods? c destPart then
          return some (.takeMatching pred cnt d m revTaken false, extraRest?, loseMvLife, c2)
    if let some r := pDropPrefixCI? work "put " then
      let fromSplit? :=
        (pSplitFirstCI? r " from among them").orElse fun _ =>
        (pSplitFirstCI? r " from among the milled cards").orElse fun _ =>
        pSplitFirstCI? r " from among those cards"
      if let some (whatPart0, destPart0) := fromSplit? then
        let mut whatPart := whatPart0
        let mut destPart := destPart0.trimAscii.copy
        if let some d := pDropPrefixCI? destPart "at random " then
          atRand := true; destPart := d
        if let some w := pDropPrefixCI? whatPart "a random " then
          atRand := true; whatPart := "a " ++ w
        let (cnt0, fRaw0) : ExprCountRange × String :=
          if let some rAll := pDropPrefixCI? whatPart "all " then (.anyNumber, rAll)
          else (parseExprCountRange? whatPart).getD (.upTo (.const 1), whatPart)
        let cnt := if isMay then match cnt0 with | .exact v => .upTo v | other => other else cnt0
        let mut fRaw := fRaw0
        for sfx in #[" card card(s)", " card(s)", " cards", " card"] do
          if pLower fRaw == "permanent card" then break
          if let some b := pDropSuffixCI? fRaw sfx then
            fRaw := if (sfx == " card card(s)" || sfx == " card(s)") && pLower b == "permanent" then "permanent card" else b
            break
        let rawPred :=
          if fRaw.isEmpty then .anyObject
          else (parseNounPhrase fRaw).map (·.filter.pred)
            |>.orElse (fun _ => (parseNounPhrase (fRaw ++ " card")).map (·.filter.pred))
            |>.getD .anyObject
        let pred : ObjectPred :=
          match rawPred with
          | .isKind .card => .anyObject
          | .all ps =>
            let kept := ps.filter (· != .isKind .card)
            match kept.toList with
            | [] => .anyObject
            | [p] => p
            | _ => .all kept
          | other => other
        if let some (d, m, c2) := parseDestZoneWithMods? c destPart then
          return some (.takeMatching pred cnt d m revTaken atRand, extraRest?, loseMvLife, c2)
    let _ := l
    return none

  let mut loseLifeMv := false
  -- Check inline action first (`Through the Forest Gate`, `Synthetic Destiny`, mill inline)
  if let some inlineTake := inlineAction? then
    if let some (act, er?, lmv, c2) := parseActionSent inlineTake ctx1 then
      action := act; ctx1 := c2; loseLifeMv := loseLifeMv || lmv
      if let some er := er? then restPlace := er
  else if inlineMoveAll?.isNone && idx + consumed < sents.size then
    if let some (act, er?, lmv, c2) := parseActionSent sents[idx + consumed]! ctx1 then
      action := act; ctx1 := c2; consumed := consumed + 1; loseLifeMv := loseLifeMv || lmv
      if let some er := er? then restPlace := er

  -- Check optional `"If it's a double-faced card, you may transform it."` (`Nick Fury`)
  if idx + consumed < sents.size then
    let nxtLow := pLower (pClean sents[idx + consumed]!)
    if nxtLow == "if it's a double-faced card, you may transform it" ||
        nxtLow == "if it is a double-faced card, you may transform it" then
      match action with
      | .takeMatching pred cnt d m rev rand =>
        action := .takeMatching pred cnt d { m with mayTransformOnEnter := true } rev rand
        consumed := consumed + 1
      | .moveAll d m =>
        action := .moveAll d { m with mayTransformOnEnter := true }
        consumed := consumed + 1
      | _ => pure ()

  -- Check optional `"They're goaded for the rest of the game. For each of those permanents, choose a different opponent. Each opponent gains control ..."` (`Dack Fayden`)
  if idx + consumed < sents.size then
    let nxtLow := pLower (pClean sents[idx + consumed]!)
    if nxtLow.contains "goaded for the rest of the game" then
      let mut goaded := true
      let mut adv := 1
      if idx + consumed + adv < sents.size && (pLower sents[idx + consumed + adv]!).contains "choose a different opponent" then
        adv := adv + 1
      if idx + consumed + adv < sents.size && (pLower sents[idx + consumed + adv]!).contains "gains control of the permanent for which they were chosen" then
        adv := adv + 1
        match action with
        | .moveAll d m =>
          action := .distributeEachOpponent d { m with goaded }
          consumed := consumed + adv
        | _ => pure ()

  -- Check optional `"If <cond>, <altTake> instead."` (`Earth's Mightiest Heroes`)
  let mut altCondAction? : Option (Condition × InspectAction) := none
  if idx + consumed < sents.size then
    let nxt := pClean sents[idx + consumed]!
    if let some ifRest := pDropPrefixCI? nxt "if " then
      if let some (cStr, body0) := pSplitFirstCI? ifRest ", " then
        if let some body := pDropSuffixCI? body0 " instead" then
          match parseCondition cStr, parseActionSent body ctx1 with
          | some cond, some (altAct, _, _, c2) =>
            altCondAction? := some (cond, altAct)
            ctx1 := c2
            consumed := consumed + 1
          | _, _ => pure ()

  -- Check optional `"Put the rest ..."` / `"Shuffle the rest ..."` sentence
  if idx + consumed < sents.size then
    if let some rp := parseRestPlacement? sents[idx + consumed]! then
      restPlace := rp
      consumed := consumed + 1

  let wrapLoseMv (baseI : Instruction) (cIn : DiscourseCtx) : Instruction × DiscourseCtx :=
    if !loseLifeMv then (baseI, cIn)
    else
      let (v, cOut) := cIn.allocVar
      (.bind v baseI (.life (.lose .you (.aggregate .sum (.stat .manaValue) (.stepObjects v)))), cOut)

  match altCondAction? with
  | some (cond, altAct) =>
    let baseI := Instruction.ifCond cond
      (.player (.inspectLibrary { source := src, action := altAct, rest := restPlace }))
      (.player (.inspectLibrary { source := src, action, rest := restPlace }))
    let (resI, ctxOut) := wrapLoseMv baseI ctx1
    return some (resI, consumed, ctxOut)
  | none =>
    let baseI := Instruction.player (.inspectLibrary { source := src, action, rest := restPlace })
    let (resI, ctxOut) := wrapLoseMv baseI ctx1
    return some (resI, consumed, ctxOut)

/-! ### `ContinuousModification` & `DelayedTriggerSpec` Parsers for `InstallEffectOp` -/

/-- Parse a single continuous modification clause on a permanent/creature
(`"gets +2/+2"`, `"gains flying and lifelink"`, `"gains \"...\""`, `"loses all abilities"`,
`"has base power and toughness 4/4"`, `"becomes a 4/4 red Dragon creature ..."`,
`"becomes a copy of <obj>[, except ...]"`, `"can't be blocked"`, `"can't block"`). -/
partial def parseContinuousModAtom? (qp : QuotedAbilityParsers) (ctx : DiscourseCtx)
    (raw : String) : Option (ContinuousModification × DiscourseCtx) := Id.run do
  let s := pClean raw
  let l := pLower s
  -- `"loses all abilities"` / `"lose all abilities"`
  if l == "loses all abilities" || l == "lose all abilities" then
    return some (.loseAllAbilities, ctx)
  -- `"has all creature types"` / `"have all creature types"` / `"is all creature types"`
  if l == "has all creature types" || l == "have all creature types" || l == "is all creature types" ||
      l == "are all creature types" then
    return some (.addAllCreatureTypes, ctx)
  -- `"can't be blocked"` / `"can't block"` / `"can't attack"` / `"can't attack or block"` / `"can't become untapped"` / `"doesn't untap..."`
  if l == "can't be blocked" then
    return some (.applyRule (.combat (.cantBeBlocked .self)), ctx)
  if l == "can't block" then
    return some (.applyRule (.combat (.cantBlock .self none)), ctx)
  if l == "can't attack" then
    return some (.applyRule (.combat (.cantAttack .self)), ctx)
  if l == "can't attack or block" then
    return some (.applyRule (.all #[.combat (.cantAttack .self), .combat (.cantBlock .self none)]), ctx)
  if l == "can't become untapped" then
    return some (.applyRule (.game (.cantBecomeUntapped .self)), ctx)
  if l == "doesn't untap during its controller's untap step" ||
      l == "doesn't untap during your untap step" ||
      l == "don't untap during their controllers' untap steps" then
    return some (.applyRule (.game (.doesntUntapDuringUntapStep .self none)), ctx)
  if let some bpStr := (pDropPrefixCI? s "can't be blocked until end of turn except by ").orElse
      (fun _ => (pDropPrefixCI? s "can't be blocked this turn except by ").orElse
        (fun _ => pDropPrefixCI? s "can't be blocked except by ")) then
    if let some np := parseNounPhrase bpStr then
      return some (.applyRule (.combat (.cantBeBlockedBy .self (.not np.filter.pred))), ctx)
  if let some bpStr := (pDropPrefixCI? s "can't be blocked until end of turn by ").orElse
      (fun _ => (pDropPrefixCI? s "can't be blocked this turn by ").orElse
        (fun _ => pDropPrefixCI? s "can't be blocked by ")) then
    if let some np := parseNounPhrase bpStr then
      return some (.applyRule (.combat (.cantBeBlockedBy .self np.filter.pred)), ctx)
  -- `"gets +P/+T"` / `"get +P/+T"` (including `"+<V>/+<V>"` and `"+P/+T for each ..."`)
  if let some ptRest0 := (pDropPrefixCI? s "gets ").orElse (fun _ => pDropPrefixCI? s "get ") then
    let ptRest := (pDropPrefixCI? ptRest0 "until end of turn ").getD ptRest0
    if let some (pv, tv) := parsePTDeltaExpr? ptRest then
      return some (.modifyPT pv tv, ctx)
    -- `"+P/+T [until end of turn] for each <X>"` / `"+P/+T for the number of <X>"`
    let ptClean := ptRest.replace " until end of turn " " "
    if let some (ptStr, eachStr) := (pSplitFirstCI? ptClean " for each ").orElse
        (fun _ => pSplitFirstCI? ptClean " for the number of ") then
      if let some (p, t) := parsePTDeltaInt? ptStr then
        let cnt? : Option ValueExpr :=
          if (pLower eachStr).startsWith "card looked at while scrying" ||
              (pLower eachStr).startsWith "card looked at while surveiling" then
            some .eventAmount
          else (parseNounPhrase eachStr).map fun np =>
            ValueExpr.aggregate .count .one (.inZones np.filter.zones np.filter.pred)
        if let some cnt := cnt? then
          let pv := if p == 0 then .const 0 else if p == 1 then cnt else .binary .mul (.const p) cnt
          let tv := if t == 0 then .const 0 else if t == 1 then cnt else .binary .mul (.const t) cnt
          return some (.modifyPT pv tv, ctx)
  -- `"has/have base power and toughness P/T"` / `"base power and toughness become(s) P/T"`
  if let some ptRest := (pDropPrefixCI? s "has base power and toughness ").orElse fun _ =>
      (pDropPrefixCI? s "have base power and toughness ").orElse fun _ =>
      (pDropPrefixCI? s "base power and toughness become ").orElse fun _ =>
      pDropPrefixCI? s "base power and toughness becomes " then
    let parts := ptRest.splitOn "/"
    if parts.length == 2 then
      match parseCountVal? parts[0]!, parseCountVal? parts[1]! with
      | some pv, some tv => return some (.setBasePT (some pv) (some tv), ctx)
      | _, _ => pure ()
  if let some pRest := (pDropPrefixCI? s "has base power ").orElse (fun _ => pDropPrefixCI? s "have base power ") then
    if let some pv := (parseCountVal? pRest).orElse (fun _ => parseValueExpr pRest) then
      return some (.setBasePT (some pv) none, ctx)
  if let some tRest := (pDropPrefixCI? s "has base toughness ").orElse (fun _ => pDropPrefixCI? s "have base toughness ") then
    if let some tv := (parseCountVal? tRest).orElse (fun _ => parseValueExpr tRest) then
      return some (.setBasePT none (some tv), ctx)
  -- `"gains/gain/has/have <keywords and/or quoted abilities>"`
  if let some gRest := (pDropPrefixCI? s "gains ").orElse fun _ =>
      (pDropPrefixCI? s "gain ").orElse fun _ =>
      (pDropPrefixCI? s "has ").orElse fun _ => pDropPrefixCI? s "have " then
    let items := splitTopLevelList gRest
    if !items.isEmpty then
      let mut mods : Array ContinuousModification := #[]
      let mut kws : Array KeywordAbility := #[]
      let mut ok := true
      for it in items do
        let itT := it.trimAscii.copy
        if itT.startsWith "\"" then
          let inner := (itT.replace "\"" "").trimAscii.copy
          match parseGrantedAbility? qp inner ctx.cardName with
          | some (.activated ab) => mods := mods.push (.grantActivated #[ab])
          | some (.triggered ab) => mods := mods.push (.grantTriggered #[ab])
          | some (.static sa) => mods := mods.push (.grantStatic #[sa])
          | some (.keyword k) => kws := kws.push k
          | none => ok := false; break
        else if let some kw := parseKeywordAbility itT then
          kws := kws.push kw
        else
          ok := false; break
      if ok then
        if !kws.isEmpty then
          let kwsSorted := kws.qsort (fun a b => a.displayOrder < b.displayOrder)
          mods := #[.grantKeywords kwsSorted] ++ mods
        match mods.toList with
        | [m] => return some (m, ctx)
        | _ :: _ => return some (.all mods, ctx)
        | [] => pure ()
  -- `"loses/lose <keywords>"`
  if let some lRest := (pDropPrefixCI? s "loses ").orElse (fun _ => pDropPrefixCI? s "lose ") then
    if let some kws := parseKeywordList? lRest then
      return some (.loseKeywords kws, ctx)
  -- `"becomes a copy of <obj>[ until end of turn][, except <mods>]"`
  if let some cRest := (pDropPrefixCI? s "becomes a copy of ").orElse
      (fun _ => pDropPrefixCI? s "become copies of ") then
    let (refStr0, excStr?) :=
      match pSplitFirstCI? cRest ", except " with
      | some (a, b) => (a, some b)
      | none => (cRest, none)
    let refStr :=
      (pDropSuffixCI? refStr0 " until end of turn").orElse (fun _ =>
      pDropSuffixCI? refStr0 " until your next turn") |>.getD refStr0
    if let some (refObj, ctx1) := parseObjWithCtx ctx refStr then
      let cMods? :=
        match excStr? with
        | none => some #[]
        | some ex => parseCopyModifications? qp ex ctx.cardName
      if let some cMods := cMods? then
        return some (.becomeCopyOf refObj cMods, ctx1)
  -- `"becomes/is/are a(n) [P/T] [<colors>] [<subtypes>] [<types>] [with base power and toughness P/T] [with <kws/abilities>] [in addition to its other types]"`
  if let some bRest := (pDropPrefixCI? s "becomes ").orElse fun _ =>
      (pDropPrefixCI? s "become ").orElse fun _ =>
      (pDropPrefixCI? s "is ").orElse fun _ => pDropPrefixCI? s "are " then
    let (inAdd, core1) :=
      match (pDropSuffixCI? bRest " in addition to its other types").orElse
          (fun _ => pDropSuffixCI? bRest " in addition to their other types") with
      | some c => (true, c)
      | none => (false, bRest)
    let (core2, ptPair?) :=
      match pSplitFirstCI? core1 " with base power and toughness " with
      | some (a, b) =>
        let pts := b.splitOn "/"
        if pts.length == 2 then
          match parseCountVal? pts[0]!, parseCountVal? pts[1]! with
          | some pv, some tv => (a, some (pv, tv))
          | _, _ => (core1, none)
        else (core1, none)
      | none => (core1, none)
    let (core2b, extraWithMods) : String × Array ContinuousModification :=
      match pSplitFirstCI? core2 " with " with
      | some (a, b) =>
        match parseContinuousModAtom? qp ctx s!"gains {b}" with
        | some (.all ms, _) => (a, ms)
        | some (m, _) => (a, #[m])
        | none => (core2, #[])
      | none => (core2, #[])
    let core3 := (pDropPrefixCI? core2b "an ").orElse (fun _ => pDropPrefixCI? core2b "a ") |>.getD core2b
    let ws := pWords core3
    if !ws.isEmpty then
      let mut sups : Array Supertype := #[]
      let mut tys : Array CardType := #[]
      let mut subs : Array CardSubtype := #[]
      let mut cols := ColorSet.empty
      let mut inlinePt? : Option (ValueExpr × ValueExpr) := ptPair?
      let mut ok := true
      for w in ws do
        let wl := pLower w
        if wl == "and" || wl == "colorless" then pure ()
        else if w.contains '/' then
          let pts := w.splitOn "/"
          if pts.length == 2 then
            match parseCountVal? pts[0]!, parseCountVal? pts[1]! with
            | some pv, some tv => inlinePt? := some (pv, tv)
            | _, _ => ok := false; break
          else ok := false; break
        else if wl == "legendary" then sups := sups.push .legendary
        else if wl == "snow" then sups := sups.push .snow
        else if wl == "basic" then sups := sups.push .basic
        else if let some col := parseColorWord? w then cols := cols.insert col
        else if let some ty :=
            match wl with
            | "artifact" | "artifacts" => some CardType.artifact
            | "creature" | "creatures" => some .creature
            | "enchantment" | "enchantments" => some .enchantment
            | "land" | "lands" => some .land
            | "planeswalker" | "planeswalkers" => some .planeswalker
            | _ => none then
          tys := tys.push ty
        else if let some sub := CardSubtype.ofOracle? w then subs := subs.push sub
        else ok := false; break
      let (inAddCol, core1b) :=
        match (pDropSuffixCI? core1 " in addition to its other colors").orElse
            (fun _ => pDropSuffixCI? core1 " in addition to their other colors") with
        | some c => (true, c)
        | none => (false, core1)
      let _ := inAddCol
      let _ := core1b
      if ok && (!tys.isEmpty || !subs.isEmpty || !sups.isEmpty) then
        let tm : TypeSetMod := {
          mode := if inAdd then .add else .set
          supertypes := sups
          types := tys
          subtypes := subs
        }
        let mut ms : Array ContinuousModification := #[.modifyTypes tm]
        if let some (pv, tv) := inlinePt? then
          ms := ms.push (.setBasePT (some pv) (some tv))
        if !cols.isColorless then
          ms := ms.push (.modifyColors { mode := if inAdd then .add else .set, colors := cols })
        ms := ms ++ extraWithMods
        match ms.toList with
        | [m] => return some (m, ctx)
        | _ => return some (.all ms, ctx)
      else if ok && !cols.isColorless then
        return some (.modifyColors { mode := if inAdd || inAddCol then .add else .set, colors := cols }, ctx)
      else if pLower core3 == "colorless" then
        return some (.modifyColors { mode := .set, colors := ColorSet.empty }, ctx)
  return none

/-- Parse a compound continuous modification clause joined by `", "` / `" and "`
(`"gets +2/+2 and gains flying and lifelink"`). -/
partial def parseContinuousMod? (qp : QuotedAbilityParsers) (ctx : DiscourseCtx) (raw : String) :
    Option (ContinuousModification × DiscourseCtx) := Id.run do
  if let some res := parseContinuousModAtom? qp ctx raw then
    return some res
  -- Split on `" and "` / `", "` before verb phrases
  let verbSeps := #[
    " and gains ", " and gain ", " and has ", " and have ", " and gets ", " and get ",
    " and loses ", " and lose ", " and becomes ", " and become ", " and is ", " and are ",
    " and can't ", " and doesn't ", " and don't ",
    ", and gains ", ", and has ", ", and gets ", ", and becomes ", ", and is ", ", and can't ", ", and doesn't ",
    ", gains ", ", has ", ", gets ", ", loses ", ", becomes ", ", is ", ", can't ", ", doesn't "
  ]
  for sep in verbSeps do
    if let some (lhs, rhs) := pSplitFirstCI? raw sep then
      let verbWord :=
        ((pDropPrefixCI? sep ", and ").orElse fun _ =>
         (pDropPrefixCI? sep " and ").orElse fun _ =>
         pDropPrefixCI? sep ", ").getD sep
      let rhsFull := verbWord ++ " " ++ rhs
      match parseContinuousModAtom? qp ctx lhs, parseContinuousMod? qp ctx rhsFull with
      | some (m1, c1), some (m2, c2) =>
        let _ := c1
        let flat :=
          match m1, m2 with
          | .all a, .all b => .all (a ++ b)
          | .all a, b => .all (a.push b)
          | a, .all b => .all (#[a] ++ b)
          | a, b => .all #[a, b]
        return some (flat, c2)
      | _, _ => pure ()
  return none

end Mtg.Engine.Parser
