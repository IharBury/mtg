import Mtg.Engine.Card.Ability
import Mtg.Engine.Card.Parser.Lexer
import Mtg.Engine.Card.Parser.SubGrammars

/-!
# Stage-5 Discourse & Anaphora Binder (CR 608.2c, 603.12, 614.6)

Tracks cross-sentence discourse context (`DiscourseCtx`) across multi-sentence
one-shot `Instruction` sequences:
- Resolves object anaphora (`"it"`, `"them"`, `"that creature"`, `"those cards"`,
  `"the exiled card"`, etc.) to `.target slot`, `.stepObjects var`, `.attachedHost`,
  `.triggerSubject`, or `.this`.
- Resolves player anaphora (`"its controller"`, `"its owner"`, `"that player"`,
  `"they"`) to `.controllerOf ...`, `.ownerOf ...`, `.target slot`, or
  `.triggerPlayer ...`.
- Resolves post-replacement step references (`"<noun>s exiled/destroyed/milled/created/
  sacrificed/discarded/returned this way"`, `"that many"`, `"excess damage dealt this way"`)
  by wrapping the antecedent step in `Instruction.bind v step cont` (CR 614.6).
- Binds trailing `"where X is <ValueExpr>"` clauses by substituting `ValueExpr.chosenX`.
- Folds `"You may <action>. If you do, <consequence>.[ Otherwise, <alt>.]"` into
  `Instruction.optional` and `"You may <action>. When you do, <reflexive>."` into
  `Instruction.optional` + `Instruction.queueReflexiveTrigger` (CR 603.12).
-/

namespace Mtg.Engine.Parser

open Mtg.Engine
open Mtg.Engine.OracleNorm

/-- Cross-sentence discourse state threaded through Stage-4/5 instruction parsing. -/
structure DiscourseCtx where
  cardName : String := ""
  slots : Array TargetSlot := #[]
  crossConstraints : Array CrossSlotConstraint := #[]
  lastTargetSlot? : Option Nat := none
  lastSubject? : Option ObjectExpr := none
  lastPlayer? : Option PlayerExpr := none
  lastActionVar? : Option VarId := none
  nextVarIdx : Nat := 0
  boundX? : Option ValueExpr := none
  isTrigger : Bool := false
  isSelfTrigger : Bool := false
  isSpell : Bool := false
  attachedHostCtx : Bool := false
  triggerPlayerRole? : Option PlayerExpr := none
  lastRevealUntilPred? : Option ObjectPred := none
  lastActionWasLife : Bool := false
  lastCounterKind? : Option CounterKind := none
deriving Repr, Inhabited

namespace DiscourseCtx

/-- Append a new `TargetSlot` and record it as the most recent discourse antecedent. -/
def pushTargetSlot (ctx : DiscourseCtx) (slot : TargetSlot) : Nat × DiscourseCtx :=
  let idx := ctx.slots.size
  let isPlayer :=
    match slot.domain with
    | .player _ => true
    | _ => false
  let objExpr : ObjectExpr :=
    match slot.count with
    | .exact 1 | .upTo 1 => .target idx
    | _ => .allTargets
  let ctx' : DiscourseCtx := {
    ctx with
    slots := ctx.slots.push slot
    lastTargetSlot? := some idx
    lastSubject? := if isPlayer then ctx.lastSubject? else some objExpr
    lastPlayer? := if isPlayer then some (.target idx) else ctx.lastPlayer?
  }
  (idx, ctx')

/-- Allocate a fresh lexical `VarId` for an antecedent step that a later sentence
may reference via `"this way"` / `"that many"` / `"those cards"`. -/
def allocVar (ctx : DiscourseCtx) : VarId × DiscourseCtx :=
  let v : VarId := ⟨ctx.nextVarIdx⟩
  (v, { ctx with lastActionVar? := some v, lastRevealUntilPred? := none, lastActionWasLife := false, nextVarIdx := ctx.nextVarIdx + 1 })

/-- Allocate a fresh lexical `VarId` for a `forEach` loop variable without overwriting
`lastActionVar?` from an earlier antecedent step (e.g. *Worlds Within Worlds*). -/
def allocLoopVar (ctx : DiscourseCtx) : VarId × DiscourseCtx :=
  let v : VarId := ⟨ctx.nextVarIdx⟩
  (v, { ctx with nextVarIdx := ctx.nextVarIdx + 1 })

/-- Final `TargetSpec` collected from the discourse context. -/
def toTargetSpec (ctx : DiscourseCtx) : TargetSpec :=
  { slots := ctx.slots, crossSlotConstraints := ctx.crossConstraints }

private def cleanLow (s : String) : String :=
  let s := (collapseWs (normalizeTypography s)).trimAscii.copy
  let s := if s.endsWith "." || s.endsWith "," then (s.dropEnd 1).trimAscii.copy else s
  lowerAscii s

/-- True when `phrase` is a self-reference to the source object. -/
def isSelfPhrase (phrase : String) : Bool :=
  match cleanLow phrase with
  | "this" | "this permanent" | "this creature" | "this artifact" | "this enchantment"
  | "this equipment" | "this aura" | "this land" | "this planeswalker" | "this card"
  | "this spell" | "this saga" | "this token" | "this tokens" | "this vehicle"
  | "this spacecraft" | "this emblem" => true
  | _ => false

/-- Resolve an object anaphor (`"it"`, `"them"`, `"that creature"`, `"those cards"`,
`"this permanent"`, `"equipped creature"`, `"the cards exiled this way"`, etc.)
against the current `DiscourseCtx`. -/
def resolveObjectAnaphor? (ctx : DiscourseCtx) (phrase : String) : Option ObjectExpr :=
  let l := cleanLow phrase
  if isSelfPhrase l then
    some .this
  else if l == "enchanted creature" || l == "enchanted permanent" || l == "equipped creature" ||
      l == "enchanted or equipped permanent" || l == "equipped or enchanted permanent" then
    some .attachedHost
  else if l.startsWith "the objects from step " then
    let nStr := (l.drop "the objects from step ".length).trimAscii.copy
    if !nStr.isEmpty && nStr.all Char.isDigit then
      some (.stepObjects ⟨nStr.toNat!⟩)
    else none
  else if l == "those exiled cards" then
    match ctx.lastActionVar? with
    | some v => some (.stepObjects v)
    | none => some .costPaidObjects
  else if l.endsWith " this way" then
    match ctx.lastActionVar? with
    | some v => some (.stepObjects v)
    | none =>
      if ctx.isTrigger then some .triggerSubject
      else ctx.lastSubject?
  else if l == "he" || l == "she" || l == "him" || l == "her" then
    some .this
  else if l == "those cards" || l == "those creatures" || l == "those permanents" ||
      l == "those tokens" || l == "those objects" || l == "the exiled cards" ||
      l == "the exiled card" || l == "the chosen card" || l == "the chosen cards" ||
      l == "the chosen creature" || l == "the chosen permanent" || l == "the amassed army" ||
      l == "that token" || l == "that card" || l == "those lands" then
    match ctx.lastActionVar? with
    | some v => some (.stepObjects v)
    | none =>
      match ctx.lastSubject? with
      | some subj => some subj
      | none => if ctx.isTrigger then some .triggerSubject else none
  else if ((l == "that permanent" || ((l == "that land" || l == "that object") && !ctx.isSelfTrigger)) &&
        ctx.isTrigger && ctx.lastSubject?.isNone) ||
      ((l == "that permanent" || l == "that creature" || l == "that artifact" ||
        l == "that enchantment" || l == "that land" || l == "that spell" || l == "that object") &&
        ctx.isTrigger && !ctx.isSelfTrigger && !ctx.attachedHostCtx && ctx.lastSubject? == some .this) then
    some .triggerSubject
  else if l == "it" || l == "them" || l == "they" ||
      l == "that object" || l == "that creature" || l == "that permanent" ||
      l == "that artifact" || l == "that enchantment" ||
      l == "that spell" || l == "that land" || l == "that planeswalker" ||
      l == "that target" || l == "those targets" || l == "that nonland permanent" then
    match ctx.lastSubject? with
    | some subj => some subj
    | none =>
      match ctx.lastActionVar? with
      | some v => some (.stepObjects v)
      | none =>
        if ctx.attachedHostCtx then some .attachedHost
        else if ctx.isSelfTrigger then some .this
        else if ctx.isTrigger then some .triggerSubject
        else some .this
  else
    none

/-- Resolve a player anaphor (`"its controller"`, `"its owner"`, `"that player"`,
`"they"`, `"that creature's controller"`, etc.) against `DiscourseCtx`. -/
def resolvePlayerAnaphor? (ctx : DiscourseCtx) (phrase : String) : Option PlayerExpr :=
  let l := cleanLow phrase
  let lastObj :=
    ctx.lastSubject?.getD (if ctx.isTrigger then .triggerSubject else .this)
  if l.startsWith "the player from step " then
    let nStr := (l.drop "the player from step ".length).trimAscii.copy
    if !nStr.isEmpty && nStr.all Char.isDigit then
      some (.stepPlayers ⟨nStr.toNat!⟩)
    else none
  else if l == "the active player" || l == "active player" then
    some .activePlayer
  else if l == "defending player" || l == "the defending player" then
    some .defendingPlayer
  else if l == "its controller" || l == "their controller" || l == "that creature's controller" ||
      l == "that permanent's controller" || l == "that spell's controller" ||
      l == "that artifact's controller" || l == "that object's controller" then
    some (.controllerOf lastObj)
  else if l == "its owner" || l == "their owner" || l == "that creature's owner" ||
      l == "that permanent's owner" || l == "that card's owner" ||
      l == "that spell's owner" then
    some (.ownerOf lastObj)
  else if l == "enchanted creature's controller" || l == "enchanted permanent's controller" ||
      l == "equipped creature's controller" then
    some (.controllerOf .attachedHost)
  else if l == "that player" || l == "that opponent" || l == "they" || l == "them" then
    match ctx.lastPlayer? with
    | some p => some p
    | none =>
      match ctx.lastSubject? with
      | some (obj@(.target _)) => some (.controllerOf obj)
      | _ =>
        if ctx.isTrigger then some (ctx.triggerPlayerRole?.getD (.triggerPlayer .actor))
        else some (.controllerOf lastObj)
  else
    none

/-- Resolve a `"this way"` / `"that many"` / `"excess damage"` metric phrase into
`ValueExpr.stepMetric` bound to the active antecedent `VarId`. -/
def resolveStepMetric? (ctx : DiscourseCtx) (phrase : String) : Option ValueExpr :=
  let l := cleanLow phrase
  match ctx.lastActionVar? with
  | none =>
    if l == "that many" || l == "that much" then some .eventAmount
    else none
  | some v =>
    if l.contains "excess damage" && l.contains "this way" then
      some (.stepMetric .excessDamage v)
    else if l.contains "damage dealt this way" || l.contains "amount of damage dealt this way" then
      some (.stepMetric .damageDealt v)
    else if l.contains "life lost this way" || l.contains "life gained this way" then
      some (.stepMetric .lifeChanged v)
    else if l.contains "counters removed this way" || l.contains "counters put this way" then
      some (.stepMetric .countersChanged v)
    else if l.contains "tokens created this way" then
      some (.stepMetric .createdCount v)
    else if l.contains "total power" && l.contains "this way" then
      some (.stepMetric .sumPower v)
    else if l.contains "this way" || l == "that many" || l == "that much" then
      some (.stepMetric .movedCount v)
    else
      none

end DiscourseCtx

/-! ### Lexical `VarId` Occurrence Check & `Instruction.bind` Wrapping -/

private partial def valueMentionsVar (v : VarId) : ValueExpr → Bool
  | .stepMetric _ u => u == v
  | .objectStat _ o | .counterCount _ o | .aggregate _ _ o | .basicLandTypeCount o
  | .cardTypeCount o | .subtypeCount _ o | .colorCountAmong o | .manaSymbols _ o
  | .manaSpent o => objExprMentionsVar v o
  | .playerMetric _ p => playerExprMentionsVar v p
  | .maxControlled pf pred => playerFilterMentionsVar v pf || objPredMentionsVar v pred
  | .binary _ a b => valueMentionsVar v a || valueMentionsVar v b
  | _ => false
where
  objExprMentionsVar (v : VarId) : ObjectExpr → Bool
    | .stepObjects u => u == v
    | .targetsOf o | .linkedExile o | .extremum _ _ o => objExprMentionsVar v o
    | .inZones _ pred => objPredMentionsVar v pred
    | .topOfLibrary p c => playerExprMentionsVar v p || valueMentionsVar v c
    | .filter o pred => objExprMentionsVar v o || objPredMentionsVar v pred
    | .union xs => xs.any (objExprMentionsVar v)
    | .diff a b => objExprMentionsVar v a || objExprMentionsVar v b
    | _ => false
  objPredMentionsVar (v : VarId) : ObjectPred → Bool
    | .all xs | .any xs => xs.any (objPredMentionsVar v)
    | .not p => objPredMentionsVar v p
    | .hasSubtype (.fromStep u) | .statParity _ (.fromStep u) => u == v
    | .stat _ _ val | .counterCount _ _ val => valueMentionsVar v val
    | .sameAs (.stepVar u) | .otherThan (.stepVar u) => u == v
    | .controlledBy pf | .ownedBy pf => playerFilterMentionsVar v pf
    | .attachedTo o | .shares _ o => objExprMentionsVar v o
    | .hasAttachment f => objPredMentionsVar v f.pred
    | .targets (.object o) => objExprMentionsVar v o
    | .targets (.player p) => playerExprMentionsVar v p
    | .targets (.either o p) => objExprMentionsVar v o || playerExprMentionsVar v p
    | _ => false
  playerExprMentionsVar (v : VarId) : PlayerExpr → Bool
    | .stepPlayers u => u == v
    | .controllerOf o | .ownerOf o => objExprMentionsVar v o
    | .matching _ pred => playerPredMentionsVar v pred
    | .chosenBy p _ pf => playerExprMentionsVar v p || playerFilterMentionsVar v pf
    | _ => false
  playerFilterMentionsVar (v : VarId) (pf : PlayerFilter) : Bool :=
    playerPredMentionsVar v pf.pred
  playerPredMentionsVar (v : VarId) : PlayerPred → Bool
    | .all xs | .anyOf xs => xs.any (playerPredMentionsVar v)
    | .not p => playerPredMentionsVar v p
    | .metric _ _ val => valueMentionsVar v val
    | .controls f val => objPredMentionsVar v f.pred || valueMentionsVar v val
    | .matchesExpr p => playerExprMentionsVar v p
    | _ => false

private partial def condMentionsVar (v : VarId) : Condition → Bool
  | .cmp _ a b => valueMentionsVar v a || valueMentionsVar v b
  | .exists o => valueMentionsVar.objExprMentionsVar v o
  | .forAll o p => valueMentionsVar.objExprMentionsVar v o || valueMentionsVar.objPredMentionsVar v p
  | .playerPred p pr => valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar.playerPredMentionsVar v pr
  | .stepSucceeded u => u == v
  | .all xs | .any xs => xs.any (condMentionsVar v)
  | .not c => condMentionsVar v c
  | _ => false

private partial def instrMentionsVar (v : VarId) : Instruction → Bool
  | .moveZone o _ _ mods =>
    valueMentionsVar.objExprMentionsVar v o ||
    mods.enterCounters.any (fun (_, c) => valueMentionsVar v c)
  | .create (.tokens p c _ mods) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v c ||
    mods.counters.any (fun (_, val) => valueMentionsVar v val)
  | .create (.emblem p _) => valueMentionsVar.playerExprMentionsVar v p
  | .permanent (.setTapped o _ _) | .permanent (.transform o) | .permanent (.turnFaceUp o)
  | .permanent (.phaseOut o _) | .permanent (.setDesignation o _ _) =>
    valueMentionsVar.objExprMentionsVar v o
  | .permanent (.modifyCounters mode o _) =>
    valueMentionsVar.objExprMentionsVar v o ||
    match mode with
    | .put _ c => valueMentionsVar v c
    | .moveAll src _ | .moveOne src _ | .copyFromLki src | .copyMissingKeywords src =>
      valueMentionsVar.objExprMentionsVar v src
    | _ => false
  | .permanent (.attach a b _) =>
    valueMentionsVar.objExprMentionsVar v a || valueMentionsVar.objExprMentionsVar v b
  | .damage (.deal s to amt _) =>
    valueMentionsVar.objExprMentionsVar v s || valueMentionsVar v amt ||
    match to with
    | .objects o => valueMentionsVar.objExprMentionsVar v o
    | .players p => valueMentionsVar.playerExprMentionsVar v p
    | .both o p => valueMentionsVar.objExprMentionsVar v o || valueMentionsVar.playerExprMentionsVar v p
    | _ => false
  | .damage (.fight a b _) =>
    valueMentionsVar.objExprMentionsVar v a || valueMentionsVar.objExprMentionsVar v b
  | .life (.gain p amt) | .life (.lose p amt) | .life (.set p amt) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v amt
  | .player (.drawCards p amt) | .player (.scry p amt) | .player (.surveil p amt) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v amt
  | .player (.amass p _ amt) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v amt
  | .player (.empowerPlaneswalker _ amt) => valueMentionsVar v amt
  | .player (.proliferate p amt tgt?) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v amt ||
    (tgt?.map (valueMentionsVar.objExprMentionsVar v) |>.getD false)
  | .player (.explore o) | .player (.connive o) => valueMentionsVar.objExprMentionsVar v o
  | .player (.reveal p o _) =>
    valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar.objExprMentionsVar v o
  | .player (.inspectLibrary spec) =>
    match spec.source with
    | .topCards p c _ | .revealUntil p _ c _ | .millCards p c =>
      valueMentionsVar.playerExprMentionsVar v p || valueMentionsVar v c
    | .allButBottom p => valueMentionsVar.playerExprMentionsVar v p
    | .outsideTheGame p _ => valueMentionsVar.playerExprMentionsVar v p
  | .player (.searchLibrary spec) =>
    let countMentions := match spec.count with
      | .exact c | .upTo c => valueMentionsVar v c
      | .between lo hi => valueMentionsVar v lo || valueMentionsVar v hi
      | .anyNumber => false
    valueMentionsVar.playerExprMentionsVar v spec.searcher ||
    valueMentionsVar.objPredMentionsVar v spec.filter ||
    countMentions
  | .stack (.counterStack o _ _) | .stack (.chooseNewTargets o _) | .stack (.mayCastOrPlay o _) =>
    valueMentionsVar.objExprMentionsVar v o
  | .stack (.copyStackObject o c _) =>
    valueMentionsVar.objExprMentionsVar v o || valueMentionsVar v c
  | .installEffect (.applyContinuous _ o mod) =>
    valueMentionsVar.objExprMentionsVar v o ||
    match mod with
    | .modifyPT p t => valueMentionsVar v p || valueMentionsVar v t
    | .setBasePT p? t? =>
      (p?.map (valueMentionsVar v) |>.getD false) || (t?.map (valueMentionsVar v) |>.getD false)
    | _ => false
  | .installEffect (.createDelayedTrigger spec) =>
    instrMentionsVar v spec.effect.body
  | .queueReflexiveTrigger ab => instrMentionsVar v ab.effect.body
  | .seq steps => steps.any (instrMentionsVar v)
  | .bind u s c => instrMentionsVar v s || (u != v && instrMentionsVar v c)
  | .ifCond c t e => condMentionsVar v c || instrMentionsVar v t || instrMentionsVar v e
  | .optional p _ y n _ =>
    valueMentionsVar.playerExprMentionsVar v p || instrMentionsVar v y || instrMentionsVar v n
  | .unlessPays p _ u =>
    valueMentionsVar.playerExprMentionsVar v p || instrMentionsVar v u
  | .forEach _ _ b => instrMentionsVar v b
  | .chooseModes spec => spec.modes.any (fun m => instrMentionsVar v m.body)
  | _ => false

/-- True when `ValueExpr` references `.stepMetric .excessDamage v`. -/
private partial def valueMentionsExcess (v : VarId) : ValueExpr → Bool
  | .stepMetric .excessDamage u => u == v
  | .binary _ a b => valueMentionsExcess v a || valueMentionsExcess v b
  | _ => false

private partial def condMentionsExcess (v : VarId) : Condition → Bool
  | .cmp _ a b => valueMentionsExcess v a || valueMentionsExcess v b
  | .all cs | .any cs => cs.any (condMentionsExcess v)
  | .not c => condMentionsExcess v c
  | _ => false

/-- True when `Instruction` reads `.stepMetric .excessDamage v` (so the antecedent
`DamageOp.deal` must set `trackExcess := true`). -/
private partial def instrMentionsExcess (v : VarId) : Instruction → Bool
  | .damage (.deal _ _ amt _) => valueMentionsExcess v amt
  | .life (.gain _ amt) | .life (.lose _ amt) | .life (.set _ amt) => valueMentionsExcess v amt
  | .player (.drawCards _ amt) | .player (.scry _ amt) | .player (.surveil _ amt)
  | .player (.amass _ _ amt) | .player (.empowerPlaneswalker _ amt)
  | .player (.proliferate _ amt _) => valueMentionsExcess v amt
  | .permanent (.modifyCounters (.put _ amt) _ _) => valueMentionsExcess v amt
  | .create (.tokens _ amt _ _) => valueMentionsExcess v amt
  | .seq steps => steps.any (instrMentionsExcess v)
  | .bind u s c => instrMentionsExcess v s || (u != v && instrMentionsExcess v c)
  | .ifCond c t e =>
    condMentionsExcess v c || instrMentionsExcess v t || instrMentionsExcess v e
  | .optional _ _ y n _ => instrMentionsExcess v y || instrMentionsExcess v n
  | .unlessPays _ _ u => instrMentionsExcess v u
  | .forEach _ _ b => instrMentionsExcess v b
  | .queueReflexiveTrigger ab => instrMentionsExcess v ab.effect.body
  | .installEffect (.createDelayedTrigger spec) => instrMentionsExcess v spec.effect.body
  | _ => false

private def enableTrackExcessIfNeeded (v : VarId) (step cont : Instruction) : Instruction :=
  match step with
  | .damage (.deal src to amt flags) =>
    if !flags.trackExcess && instrMentionsExcess v cont then
      .damage (.deal src to amt { flags with trackExcess := true })
    else step
  | _ => step

/-- Flatten nested `.seq` / `.noop` into a clean instruction sequence. -/
def flattenInstrSeq (xs : Array Instruction) : Instruction :=
  let rec collect (acc : Array Instruction) (i : Instruction) : Array Instruction :=
    match i with
    | .noop => acc
    | .seq sub => sub.attach.foldl (fun a ⟨s, _⟩ => collect a s) acc
    | other => acc.push other
  let flat := xs.foldl collect #[]
  match flat.toList with
  | [] => .noop
  | [x] => x
  | _ => .seq flat

/-- Combine a sequence of `(Option VarId × Instruction)` steps, automatically
inserting `Instruction.bind v step cont` whenever a later step references `v`
(CR 608.2c / 614.6), and flattening plain unreferenced steps into `.seq`. -/
def assembleBoundSteps (steps0 : Array (Option VarId × Instruction)) : Instruction :=
  let rec expandSteps (acc : Array (Option VarId × Instruction)) (s : Instruction) :
      Array (Option VarId × Instruction) :=
    match s with
    | .noop => acc
    | .seq sub => sub.attach.foldl (fun a ⟨x, _⟩ => expandSteps a x) acc
    | other => acc.push (none, other)
  let steps : Array (Option VarId × Instruction) := Id.run do
    let mut acc : Array (Option VarId × Instruction) := #[]
    for i in [:steps0.size] do
      let (v?, s) := steps0[i]!
      match v? with
      | none => acc := expandSteps acc s
      | some v =>
        let usedLater := Id.run do
          let mut used := false
          for j in [i + 1 : steps0.size] do
            if instrMentionsVar v steps0[j]!.2 then used := true
          return used
        if usedLater then
          acc := acc.push (some v, s)
        else
          acc := expandSteps acc s
    return acc
  let rec go (idx : Nat) : Instruction :=
    if idx >= steps.size then .noop
    else
      let (v?, step) := steps[idx]!
      if idx + 1 >= steps.size then step
      else
        let cont := go (idx + 1)
        match v?, step with
        | some v, _ =>
          if instrMentionsVar v cont then
            if idx + 2 < steps.size then
              let (vNext?, nextStep) := steps[idx + 1]!
              let rest := go (idx + 2)
              if !instrMentionsVar v rest && (vNext?.map (fun vn => !instrMentionsVar vn rest) |>.getD true) then
                let step' := enableTrackExcessIfNeeded v step nextStep
                flattenInstrSeq #[.bind v step' nextStep, rest]
              else
                let step' := enableTrackExcessIfNeeded v step cont
                .bind v step' cont
            else
              let step' := enableTrackExcessIfNeeded v step cont
              .bind v step' cont
          else flattenInstrSeq #[step, cont]
        | none, .bind v innerStep innerCont =>
          if instrMentionsVar v cont then
            let fullCont := flattenInstrSeq #[innerCont, cont]
            let innerStep' := enableTrackExcessIfNeeded v innerStep fullCont
            .bind v innerStep' fullCont
          else flattenInstrSeq #[step, cont]
        | none, _ => flattenInstrSeq #[step, cont]
  termination_by steps.size - idx
  go 0

/-! ### `where X is <ValueExpr>` Substitution -/

/-- Replace `ValueExpr.chosenX` with `xVal` inside a `ValueExpr`. -/
partial def substValueX (xVal : ValueExpr) : ValueExpr → ValueExpr
  | .chosenX => xVal
  | .binary op a b => .binary op (substValueX xVal a) (substValueX xVal b)
  | other => other

/-- Replace `ValueExpr.chosenX` with `xVal` inside a `ContinuousModification`. -/
partial def substXContinuousMod (xVal : ValueExpr) : ContinuousModification → ContinuousModification
  | .modifyPT p t => .modifyPT (substValueX xVal p) (substValueX xVal t)
  | .setBasePT p? t? => .setBasePT (p?.map (substValueX xVal)) (t?.map (substValueX xVal))
  | .all ms => .all (ms.map (substXContinuousMod xVal))
  | other => other

/-- Replace `ValueExpr.chosenX` with `xVal` inside a `Condition`. -/
partial def substCondX (xVal : ValueExpr) : Condition → Condition
  | .cmp op a b => .cmp op (substValueX xVal a) (substValueX xVal b)
  | .not c => .not (substCondX xVal c)
  | .all cs => .all (cs.map (substCondX xVal))
  | .any cs => .any (cs.map (substCondX xVal))
  | other => other

/-- Replace `ValueExpr.chosenX` with `xVal` across top-level value slots of an `Instruction`
(used when binding trailing `", where X is <ValueExpr>"` clauses). -/
partial def substInstrX (xVal : ValueExpr) : Instruction → Instruction
  | .damage (.deal src to amt flags) => .damage (.deal src to (substValueX xVal amt) flags)
  | .life (.gain who amt) => .life (.gain who (substValueX xVal amt))
  | .life (.lose who amt) => .life (.lose who (substValueX xVal amt))
  | .life (.set who amt) => .life (.set who (substValueX xVal amt))
  | .player (.drawCards who amt) => .player (.drawCards who (substValueX xVal amt))
  | .player (.scry who amt) => .player (.scry who (substValueX xVal amt))
  | .player (.surveil who amt) => .player (.surveil who (substValueX xVal amt))
  | .player (.amass who sub amt) => .player (.amass who sub (substValueX xVal amt))
  | .player (.empowerPlaneswalker sub amt) => .player (.empowerPlaneswalker sub (substValueX xVal amt))
  | .player (.discover who amt) => .player (.discover who (substValueX xVal amt))
  | .player (.proliferate who amt tgt?) => .player (.proliferate who (substValueX xVal amt) tgt?)
  | .create (.tokens who cnt spec mods) =>
    let spec' :=
      match spec with
      | .custom cs =>
        .custom { cs with
          power? := cs.power?.map (substValueX xVal)
          toughness? := cs.toughness?.map (substValueX xVal) }
      | other => other
    let mods' := { mods with counters := mods.counters.map fun (k, v) => (k, substValueX xVal v) }
    .create (.tokens who (substValueX xVal cnt) spec' mods')
  | .permanent (.modifyCounters (.put k v) o ch?) =>
    .permanent (.modifyCounters (.put k (substValueX xVal v)) o ch?)
  | .permanent (.modifyCounters (.distribute k v) o ch?) =>
    .permanent (.modifyCounters (.distribute k (substValueX xVal v)) o ch?)
  | .moveZone (.topOfLibrary who cnt) dest verb mods =>
    .moveZone (.topOfLibrary who (substValueX xVal cnt)) dest verb mods
  | .stack (.copyStackObject o cnt nt) =>
    .stack (.copyStackObject o (substValueX xVal cnt) nt)
  | .installEffect (.applyContinuous dur aff cm) =>
    .installEffect (.applyContinuous dur aff (substXContinuousMod xVal cm))
  | .seq xs => .seq (xs.map (substInstrX xVal))
  | .bind v s c => .bind v (substInstrX xVal s) (substInstrX xVal c)
  | .ifCond c t e => .ifCond (substCondX xVal c) (substInstrX xVal t) (substInstrX xVal e)
  | .optional w cost? y n m => .optional w cost? (substInstrX xVal y) (substInstrX xVal n) m
  | .unlessPays p cost u => .unlessPays p cost (substInstrX xVal u)
  | .forEach it v b => .forEach it v (substInstrX xVal b)
  | other => other

/-- Build a CR 603.12 reflexive trigger instruction `"When you do, <eff>"`. -/
def mkReflexiveWhenYouDo (eff : Effect) : Instruction :=
  .queueReflexiveTrigger {
    word := .when
    pattern := .thisEnters -- marker pattern; reflexive firing uses `Instruction.queueReflexiveTrigger`
    effect := eff
  }

/-! ### Canonical Bound `VarId` Normalization (α-renaming) -/

private def renameVar (env : List (VarId × VarId)) (v : VarId) : VarId :=
  match env.find? (fun p => p.1 == v) with
  | some (_, v') => v'
  | none => v

private partial def mapValVars (env : List (VarId × VarId)) : ValueExpr → ValueExpr
  | .stepMetric m u => .stepMetric m (renameVar env u)
  | .objectStat k o => .objectStat k (mapObjVars env o)
  | .counterCount k? o => .counterCount k? (mapObjVars env o)
  | .aggregate op m o => .aggregate op m (mapObjVars env o)
  | .basicLandTypeCount o => .basicLandTypeCount (mapObjVars env o)
  | .cardTypeCount o => .cardTypeCount (mapObjVars env o)
  | .subtypeCount cat o => .subtypeCount cat (mapObjVars env o)
  | .colorCountAmong o => .colorCountAmong (mapObjVars env o)
  | .manaSymbols cs o => .manaSymbols cs (mapObjVars env o)
  | .manaSpent o => .manaSpent (mapObjVars env o)
  | .playerMetric m p => .playerMetric m (mapPlVars env p)
  | .maxControlled pf pred => .maxControlled (mapPfVars env pf) (mapPredVars env pred)
  | .binary op a b => .binary op (mapValVars env a) (mapValVars env b)
  | other => other
where
  mapObjVars (env : List (VarId × VarId)) : ObjectExpr → ObjectExpr
    | .stepObjects u => .stepObjects (renameVar env u)
    | .targetsOf o => .targetsOf (mapObjVars env o)
    | .linkedExile o => .linkedExile (mapObjVars env o)
    | .extremum dir m o => .extremum dir m (mapObjVars env o)
    | .inZones zs pred => .inZones (mapZonesVars env zs) (mapPredVars env pred)
    | .topOfLibrary p c => .topOfLibrary (mapPlVars env p) (mapValVars env c)
    | .filter o pred => .filter (mapObjVars env o) (mapPredVars env pred)
    | .union xs => .union (xs.map (mapObjVars env))
    | .diff a b => .diff (mapObjVars env a) (mapObjVars env b)
    | other => other
  mapZonesVars (env : List (VarId × VarId)) (zs : ZoneSetSpec) : ZoneSetSpec :=
    { zs with
      owner := match zs.owner with
        | .ofPlayer p => .ofPlayer (mapPlVars env p)
        | .matching pf => .matching (mapPfVars env pf)
        | other => other }
  mapObjRefVars (env : List (VarId × VarId)) : ObjectRef → ObjectRef
    | .stepVar u => .stepVar (renameVar env u)
    | other => other
  mapPredVars (env : List (VarId × VarId)) : ObjectPred → ObjectPred
    | .all xs => .all (xs.map (mapPredVars env))
    | .any xs => .any (xs.map (mapPredVars env))
    | .not p => .not (mapPredVars env p)
    | .hasSubtype (.fromStep u) => .hasSubtype (.fromStep (renameVar env u))
    | .statParity k (.fromStep u) => .statParity k (.fromStep (renameVar env u))
    | .stat k op val => .stat k op (mapValVars env val)
    | .counterCount k? op val => .counterCount k? op (mapValVars env val)
    | .sameAs r => .sameAs (mapObjRefVars env r)
    | .otherThan r => .otherThan (mapObjRefVars env r)
    | .controlledBy pf => .controlledBy (mapPfVars env pf)
    | .ownedBy pf => .ownedBy (mapPfVars env pf)
    | .attachedTo o => .attachedTo (mapObjVars env o)
    | .shares ch o => .shares ch (mapObjVars env o)
    | .hasAttachment f => .hasAttachment { zones := mapZonesVars env f.zones, pred := mapPredVars env f.pred }
    | .targets (.object o) => .targets (.object (mapObjVars env o))
    | .targets (.player p) => .targets (.player (mapPlVars env p))
    | .targets (.either o p) => .targets (.either (mapObjVars env o) (mapPlVars env p))
    | other => other
  mapPlVars (env : List (VarId × VarId)) : PlayerExpr → PlayerExpr
    | .stepPlayers u => .stepPlayers (renameVar env u)
    | .controllerOf o => .controllerOf (mapObjVars env o)
    | .ownerOf o => .ownerOf (mapObjVars env o)
    | .matching rel pred => .matching rel (mapPpVars env pred)
    | .chosenBy p cnt pf => .chosenBy (mapPlVars env p) cnt (mapPfVars env pf)
    | other => other
  mapPfVars (env : List (VarId × VarId)) (pf : PlayerFilter) : PlayerFilter :=
    { pf with pred := mapPpVars env pf.pred }
  mapPpVars (env : List (VarId × VarId)) : PlayerPred → PlayerPred
    | .all xs => .all (xs.map (mapPpVars env))
    | .anyOf xs => .anyOf (xs.map (mapPpVars env))
    | .not p => .not (mapPpVars env p)
    | .metric m op val => .metric m op (mapValVars env val)
    | .controls f val => .controls { zones := mapZonesVars env f.zones, pred := mapPredVars env f.pred } (mapValVars env val)
    | .matchesExpr p => .matchesExpr (mapPlVars env p)
    | other => other

private partial def mapCondVars (env : List (VarId × VarId)) : Condition → Condition
  | .cmp op a b => .cmp op (mapValVars env a) (mapValVars env b)
  | .exists o => .exists (mapValVars.mapObjVars env o)
  | .forAll o p => .forAll (mapValVars.mapObjVars env o) (mapValVars.mapPredVars env p)
  | .playerPred p pr => .playerPred (mapValVars.mapPlVars env p) (mapValVars.mapPpVars env pr)
  | .stepSucceeded u => .stepSucceeded (renameVar env u)
  | .all xs => .all (xs.map (mapCondVars env))
  | .any xs => .any (xs.map (mapCondVars env))
  | .not c => .not (mapCondVars env c)
  | other => other

private def mapDestOwnerVars (env : List (VarId × VarId)) : DestOwnerSpec → DestOwnerSpec
  | .player p => .player (mapValVars.mapPlVars env p)
  | other => other

private def mapDestZoneVars (env : List (VarId × VarId)) : DestZoneSpec → DestZoneSpec
  | .battlefield u => .battlefield (mapDestOwnerVars env u)
  | .hand u => .hand (mapDestOwnerVars env u)
  | .library u pos opt => .library (mapDestOwnerVars env u) pos opt
  | other => other

private def mapCountRangeVars (env : List (VarId × VarId)) : ExprCountRange → ExprCountRange
  | .exact v => .exact (mapValVars env v)
  | .upTo v => .upTo (mapValVars env v)
  | .between lo hi => .between (mapValVars env lo) (mapValVars env hi)
  | .anyNumber => .anyNumber

private def mapChoiceVars (env : List (VarId × VarId)) (ch : MoveChoiceSpec) : MoveChoiceSpec :=
  { ch with
    chooser := match ch.chooser with | .player p => .player (mapValVars.mapPlVars env p) | other => other
    count := mapCountRangeVars env ch.count
    filter? := ch.filter?.map (mapValVars.mapPredVars env)
    unlessMatching? := ch.unlessMatching?.map (mapValVars.mapPredVars env) }

private def mapGrantPlayVars (env : List (VarId × VarId)) (g : GrantPlayPermSpec) : GrantPlayPermSpec :=
  { g with
    maxTotalManaValue? := g.maxTotalManaValue?.map (mapValVars env)
    condition? := g.condition?.map (mapCondVars env)
    filter? := g.filter?.map (mapValVars.mapPredVars env) }

private def mapMoveModsVars (env : List (VarId × VarId)) (m : MoveMods) : MoveMods :=
  { m with
    attachTo? := m.attachTo?.map (mapValVars.mapObjVars env)
    enterCounters := m.enterCounters.map fun (k, v) => (k, mapValVars env v)
    grantPlayPerm? := m.grantPlayPerm?.map (mapGrantPlayVars env)
    choice? := m.choice?.map (mapChoiceVars env) }

private def mapEnterModsVars (env : List (VarId × VarId)) (m : EnterMods) : EnterMods :=
  { m with
    attachTo? := m.attachTo?.map (mapValVars.mapObjVars env)
    counters := m.counters.map fun (k, v) => (k, mapValVars env v)
    delayedAction? := m.delayedAction?.map fun
      | .sacrificeAtEndStepUnless c => .sacrificeAtEndStepUnless (mapCondVars env c)
      | other => other }

private def mapRuleModVars (env : List (VarId × VarId)) : RuleModification → RuleModification
  | .combat (.cantBeBlockedBy s bp) => .combat (.cantBeBlockedBy s (mapValVars.mapPredVars env bp))
  | .combat (.cantBlock s c?) => .combat (.cantBlock s (c?.map (mapCondVars env)))
  | .combat (.cantAttackUnless s c) => .combat (.cantAttackUnless s (mapCondVars env c))
  | .all rs => .all (rs.map (mapRuleModVars env))
  | other => other

private partial def mapContModVars (env : List (VarId × VarId)) : ContinuousModification → ContinuousModification
  | .modifyPT p t => .modifyPT (mapValVars env p) (mapValVars env t)
  | .setBasePT p? t? => .setBasePT (p?.map (mapValVars env)) (t?.map (mapValVars env))
  | .gainControl p => .gainControl (mapValVars.mapPlVars env p)
  | .exchangeControl o => .exchangeControl (mapValVars.mapObjVars env o)
  | .becomeCopyOf o mods => .becomeCopyOf (mapValVars.mapObjVars env o) mods
  | .applyRule r => .applyRule (mapRuleModVars env r)
  | .all ms => .all (ms.map (mapContModVars env))
  | other => other

private partial def normalizeBoundVarsAux (depth : Nat) (env : List (VarId × VarId)) : Instruction → Instruction
  | .bind v step cont =>
    let step' := normalizeBoundVarsAux depth env step
    let v' : VarId := ⟨depth⟩
    let cont' := normalizeBoundVarsAux (depth + 1) ((v, v') :: env) cont
    .bind v' step' cont'
  | .forEach iter v body =>
    let iter' := match iter with
      | .eachPlayer pf => .eachPlayer (mapValVars.mapPfVars env pf)
      | .eachObject o => .eachObject (mapValVars.mapObjVars env o)
      | .repeatTimes c => .repeatTimes (mapValVars env c)
      | .eachTargetSlot => .eachTargetSlot
    let v' : VarId := ⟨depth⟩
    let body' := normalizeBoundVarsAux (depth + 1) ((v, v') :: env) body
    .forEach iter' v' body'
  | .seq steps => .seq (steps.map (normalizeBoundVarsAux depth env))
  | .ifCond c t e => .ifCond (mapCondVars env c) (normalizeBoundVarsAux depth env t) (normalizeBoundVarsAux depth env e)
  | .optional w cost? y n m =>
    .optional (mapValVars.mapPlVars env w) cost? (normalizeBoundVarsAux depth env y) (normalizeBoundVarsAux depth env n) m
  | .unlessPays p cost u =>
    .unlessPays (mapValVars.mapPlVars env p) cost (normalizeBoundVarsAux depth env u)
  | .chooseModes spec =>
    .chooseModes { spec with modes := spec.modes.map fun m => { m with body := normalizeBoundVarsAux depth env m.body } }
  | .queueReflexiveTrigger ab =>
    .queueReflexiveTrigger { ab with effect := { ab.effect with body := normalizeBoundVarsAux depth env ab.effect.body } }
  | .moveZone o dest verb mods =>
    if env.isEmpty then .moveZone o dest verb mods
    else .moveZone (mapValVars.mapObjVars env o) (mapDestZoneVars env dest) verb (mapMoveModsVars env mods)
  | .create (.tokens p c sp mods) =>
    if env.isEmpty then .create (.tokens p c sp mods)
    else
      let sp' := match sp with
        | .custom cs => .custom { cs with power? := cs.power?.map (mapValVars env), toughness? := cs.toughness?.map (mapValVars env) }
        | .copyOf o ms => .copyOf (mapValVars.mapObjVars env o) ms
        | other => other
      .create (.tokens (mapValVars.mapPlVars env p) (mapValVars env c) sp' (mapEnterModsVars env mods))
  | .create (.emblem p em) =>
    if env.isEmpty then .create (.emblem p em)
    else .create (.emblem (mapValVars.mapPlVars env p) em)
  | .permanent op =>
    if env.isEmpty then .permanent op
    else .permanent (match op with
      | .setTapped o t ch? => .setTapped (mapValVars.mapObjVars env o) t (ch?.map (mapChoiceVars env))
      | .modifyCounters m o ch? =>
        let m' := match m with
          | .put k c => .put k (mapValVars env c)
          | .distribute k c => .distribute k (mapValVars env c)
          | .putAnotherOfChosen => .putAnotherOfChosen
          | .remove k? c => .remove k? (mapCountRangeVars env c)
          | .moveAll s k? => .moveAll (mapValVars.mapObjVars env s) k?
          | .moveOne s k => .moveOne (mapValVars.mapObjVars env s) k
          | .copyFromLki s => .copyFromLki (mapValVars.mapObjVars env s)
          | .copyMissingKeywords s => .copyMissingKeywords (mapValVars.mapObjVars env s)
          | .double k? => .double k?
        .modifyCounters m' (mapValVars.mapObjVars env o) (ch?.map (mapChoiceVars env))
      | .attach a b ch => .attach (mapValVars.mapObjVars env a) (mapValVars.mapObjVars env b) ch
      | .transform o => .transform (mapValVars.mapObjVars env o)
      | .turnFaceUp o => .turnFaceUp (mapValVars.mapObjVars env o)
      | .phaseOut o p? => .phaseOut (mapValVars.mapObjVars env o) (p?.map (mapValVars.mapPlVars env))
      | .setDesignation o tag v => .setDesignation (mapValVars.mapObjVars env o) tag v
      | .assimilate o ch? => .assimilate (mapValVars.mapObjVars env o) (ch?.map (mapChoiceVars env)))
  | .damage op =>
    if env.isEmpty then .damage op
    else .damage (match op with
      | .deal src to amt fl =>
        let to' := match to with
          | .objects o => .objects (mapValVars.mapObjVars env o)
          | .players p => .players (mapValVars.mapPlVars env p)
          | .both o p => .both (mapValVars.mapObjVars env o) (mapValVars.mapPlVars env p)
          | other => other
        .deal (mapValVars.mapObjVars env src) to' (mapValVars env amt) fl
      | .fight a b ow => .fight (mapValVars.mapObjVars env a) (mapValVars.mapObjVars env b) ow)
  | .life op =>
    if env.isEmpty then .life op
    else .life (match op with
      | .gain p v => .gain (mapValVars.mapPlVars env p) (mapValVars env v)
      | .lose p v => .lose (mapValVars.mapPlVars env p) (mapValVars env v)
      | .set p v => .set (mapValVars.mapPlVars env p) (mapValVars env v))
  | .player op =>
    if env.isEmpty then .player op
    else .player (match op with
      | .drawCards p v => .drawCards (mapValVars.mapPlVars env p) (mapValVars env v)
      | .scry p v => .scry (mapValVars.mapPlVars env p) (mapValVars env v)
      | .surveil p v => .surveil (mapValVars.mapPlVars env p) (mapValVars env v)
      | .reveal p o c? => .reveal (mapValVars.mapPlVars env p) (mapValVars.mapObjVars env o) (c?.map (mapCountRangeVars env))
      | .shuffle p => .shuffle (mapValVars.mapPlVars env p)
      | .proliferate p v t? => .proliferate (mapValVars.mapPlVars env p) (mapValVars env v) (t?.map (mapValVars.mapObjVars env))
      | .temptWithRing p => .temptWithRing (mapValVars.mapPlVars env p)
      | .explore o => .explore (mapValVars.mapObjVars env o)
      | .amass p s v => .amass (mapValVars.mapPlVars env p) s (mapValVars env v)
      | .connive o => .connive (mapValVars.mapObjVars env o)
      | .empowerPlaneswalker s v => .empowerPlaneswalker s (mapValVars env v)
      | .discover p v => .discover (mapValVars.mapPlVars env p) (mapValVars env v)
      | .setStatus p k c? => .setStatus (mapValVars.mapPlVars env p) k (c?.map (mapCondVars env))
      | .choose p k => .choose (mapValVars.mapPlVars env p) k
      | .inspectLibrary sp =>
        let src' := match sp.source with
          | .topCards p c rev => .topCards (mapValVars.mapPlVars env p) (mapValVars env c) rev
          | .revealUntil p pr c ex => .revealUntil (mapValVars.mapPlVars env p) (mapValVars.mapPredVars env pr) (mapValVars env c) ex
          | .millCards p c => .millCards (mapValVars.mapPlVars env p) (mapValVars env c)
          | .allButBottom p => .allButBottom (mapValVars.mapPlVars env p)
          | .outsideTheGame p n => .outsideTheGame (mapValVars.mapPlVars env p) n
        .inspectLibrary { sp with source := src' }
      | .searchLibrary sp =>
        .searchLibrary { sp with
          searcher := mapValVars.mapPlVars env sp.searcher
          filter := mapValVars.mapPredVars env sp.filter
          dest := mapDestZoneVars env sp.dest
          mods := mapMoveModsVars env sp.mods }
      | other => other)
  | .stack op =>
    if env.isEmpty then .stack op
    else .stack (match op with
      | .counterStack o ex fc => .counterStack (mapValVars.mapObjVars env o) ex fc
      | .copyStackObject o c nt => .copyStackObject (mapValVars.mapObjVars env o) (mapValVars env c) nt
      | .chooseNewTargets o opt => .chooseNewTargets (mapValVars.mapObjVars env o) opt
      | .mayCastOrPlay o gp => .mayCastOrPlay (mapValVars.mapObjVars env o) (mapGrantPlayVars env gp))
  | .installEffect op =>
    match op with
    | .createDelayedTrigger sp =>
      .installEffect (.createDelayedTrigger { sp with effect := { sp.effect with body := normalizeBoundVarsAux depth env sp.effect.body } })
    | .applyContinuous dur aff mod =>
      if env.isEmpty then .installEffect op
      else .installEffect (.applyContinuous dur (mapValVars.mapObjVars env aff) (mapContModVars env mod))
    | .applyRule dur r =>
      if env.isEmpty then .installEffect op
      else .installEffect (.applyRule dur (mapRuleModVars env r))
    | other => .installEffect other
  | other => other

/-- α-rename bound `VarId`s in `instr` canonically (`0, 1, ...` by nesting depth) so
speculative allocations dropped by `assembleBoundSteps` never leave non-zero gaps. -/
def normalizeBoundVars (instr : Instruction) : Instruction :=
  normalizeBoundVarsAux 0 [] instr

end Mtg.Engine.Parser
