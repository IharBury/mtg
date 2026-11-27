import Mtg.Engine.Card.Effect
import Mtg.Engine.Card.Trigger

/-!
# Triggered abilities: core constructors, targeting, and Oracle rendering (CR 603)

Core generic `TriggeredAbility` constructors (`mkTrigger`, `ofPattern`,
keyword-expansion triggers, and Saga chapters) plus `HasTargeting` and canonical
`ToOracle` / `toNotation` rendering. Test-only named builder tables live under
`Mtg.Engine.Tests.Builders`.
-/

namespace Mtg.Engine

namespace TriggeredAbility

/-- Build a triggered ability from a `TriggerPattern` and a unified `Effect`. -/
def mkTrigger (pattern : TriggerPattern) (effect : Effect)
    (word : TriggerWord := pattern.defaultWord)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit, effect }

/-- Construct a triggered ability directly from a `TriggerPattern` and unified `Instruction`. -/
def ofPattern (pattern : TriggerPattern) (body : Instruction)
    (spec : TargetSpec := .none)
    (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none)
    (activeZones : Array ZoneKind := #[.battlefield])
    (limit : TriggerLimit := .unlimited)
    (word : TriggerWord := pattern.defaultWord) : TriggeredAbility :=
  { word, pattern, grouping, interveningIf?, activeZones, limit,
    effect := { targets := spec, body } }

/-- `"Whenever you gain life, put a +1/+1 counter on this creature."` (CR 603). -/
def onGainLifePlusOne : TriggeredAbility :=
  mkTrigger (.gainLife .you) { body := Instruction.putPlusOne .this 1 }

/-- `"When this permanent enters, you gain N life."` (CR 603). -/
def onEnterGainLife (n : Nat) : TriggeredAbility :=
  mkTrigger .thisEnters (Effect.triggerGainLife n)

/-- Cascade cast trigger (CR 702.85a). -/
def onCastCascade : TriggeredAbility :=
  mkTrigger .thisCast Effect.triggerCascade (activeZones := #[.stack])

/-- Ward trigger (CR 702.21a). -/
def onWard (cost : CostSpec) : TriggeredAbility :=
  ofPattern .thisBecomesTargetByOpponent
    (.unlessPays (.controllerOf .triggerSubject) cost (Instruction.counter .triggerSubject))

/-- Impending end-step time-counter removal trigger (CR 702.176a / 603.4). -/
def impendingEndStep : TriggeredAbility :=
  ofPattern .stepYourEndStep
    (.permanent (.modifyCounters (.remove (some .time) (.exact (.const 1))) .this))
    (interveningIf? := some condImpendingPaidWithTimeCounter)

/-- Build a Saga chapter triggered ability (CR 715.2b). -/
def sagaChapters (chapters : Array Nat) (e : Effect) : TriggeredAbility :=
  { word := .when
    pattern := TriggerPattern.putCountersOnSelf .lore
    grouping := .counterThreshold .lore chapters
    effect := e }

def sagaChapter (n : Nat) (e : Effect) : TriggeredAbility :=
  sagaChapters #[n] e

instance : HasTargeting TriggeredAbility where
  targetSpec ab := ab.effect.targets

/-! ### Oracle Rendering -/

/-- Leading `"When / Whenever / At …"` prefix rendered from `word`, `pattern`,
`grouping`, and `limit`. -/
private def eventPrefixPattern (word : TriggerWord) (grouping : BatchGrouping)
    (limit : TriggerLimit) : TriggerPattern → String
  | .or (.zoneChange (.sameAs .this) (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none)
        (.attacks (.sameAs .this) .any false 1 none false) =>
    "Whenever this creature enters or attacks"
  | .or (.castSpell { relation := .you, pred := .any } (.hasColor (.literal .green)) none none false none none)
        (.zoneChange (.all #[.hasSubtype (.literal .forest), .controlledBy { relation := .you, pred := .any }])
          (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none) =>
    "Whenever you cast a green spell and whenever a Forest you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another {s} you control enters"
  | .zoneChange (.any #[.sameAs .this, .all #[.isToken false, .hasSubtype (.literal s), .controlledBy _]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever this or another nontoken {s} you control enters"
  | .zoneChange (.all #[.otherThan .this, .controlledBy _,
      .any #[.hasSubtype (.literal s), .all #[.hasType .artifact, .hasSubtype (.literal .equipment)]]])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} or Equipment you control enters"
  | .zoneChange (.all #[.otherThan .this, .hasType .creature, .controlledBy _, .stat .power .le (.const n)])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another creature you control with power {n} or less enters"
  | .zoneChange (.all #[.otherThan .this, .hasSubtype (.literal s), .controlledBy _])
      (.notIn .battlefield) (.inZones { zones := #[.battlefield], .. }) none none =>
    s!"Whenever another {s} you control enters"
  | .whenCond inner (.exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)]))) =>
    let base := eventPrefixPattern word grouping limit inner
    s!"{base} while you control a creature with power {n} or greater"
  | .whenCond inner (.all #[.exists .this, .forAll .this (.hasDesignation .harnessed)]) =>
    s!"∞ — {eventPrefixPattern word grouping limit inner}"
  | p =>
    let ctx : PrintCtx :=
      match p with
      | .attacks (.sameAs .this) .. | .blocks (.sameAs .this) | .becomesBlocked (.sameAs .this)
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.inZones { zones := #[.graveyard], .. }) _ _
      | .zoneChange (.sameAs .this) (.inZones { zones := #[.battlefield], .. }) (.notIn .battlefield) _ _ =>
        { selfRef := "this creature", capitalize := false }
      | .damageDealt (.sameAs .this) .. | .damageDealt _ (.object { pred := .sameAs .this, .. }) ..
      | .becomesTapped (.sameAs .this) .. =>
        { selfRef := "this", capitalize := false }
      | .becomesTarget (.object (.sameAs .this)) .. =>
        { selfRef := "this creature", capitalize := false }
      | _ => { selfRef := "this permanent", capitalize := false }
    let w := word.toOracleStr
    s!"{w} {p.renderClause ctx grouping limit}"

/-- Leading `"When / Whenever / At …"` prefix rendered from `ab.word`,
`ab.pattern`, `ab.grouping`, and `ab.limit`. -/
def eventPrefix (ab : TriggeredAbility) : String :=
  eventPrefixPattern ab.word ab.grouping ab.limit ab.pattern

/-- Intervening `"if …"` clause rendered from `ab.interveningIf?`, or empty. -/
def interveningClause (ab : TriggeredAbility) : String :=
  match ab.interveningIf? with
  | none => ""
  | some cond =>
    match cond with
    | .exists (.inZones .battlefield (.all #[.hasType .creature, .controlledBy _, .stat .power .ge (.const n)])) =>
      s!", if you control a creature with power {n} or greater"
    | .cmp .ge (.playerMetric .lifeGainedThisTurn .you) (.const n) =>
      s!", if you gained {n} or more life this turn"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[
        .hasType .land, .controlledBy _]))) (.const 6) =>
      ", if you control six or more lands"
    | .cmp .ge (.aggregate .count .one (.inZones .battlefield (.all #[
        .otherThan .triggerSubject, .hasSubtype (.literal .forest), .controlledBy _]))) (.const 5) =>
      ", if you control at least five other Forests"
    | .any #[
        .turnHistory (.eventOccurredThisTurn _ (.attackedWith (.hasSubtype (.literal sub)) 1)),
        .turnHistory (.eventOccurredThisTurn _ (.permanentEntered (.hasSubtype (.literal _))))] =>
      let a := if sub == .hero then "a Hero" else s!"a {sub}"
      s!", if you attacked with {a} this turn or {a} entered the battlefield under your control this turn"
    | _ =>
      s!", if {ToOracle.toOracle { selfRef := "this permanent", capitalize := false } cond}"

/-- Oracle clause for putting `n` counters of `kind` on `noun`. -/
def counterOn (noun : String) (kind : CounterKind) (n : Nat) : String :=
  match kind with
  | .plusOnePlusOne => s!"put {plusOnePlusOneCountersPhrase n} on {noun}"
  | k => s!"put {k.countersPhrase n} on {noun}"

private def instrObjNoun (noun : String) : ObjectExpr → String
  | .this => "this creature"
  | .attachedHost => "enchanted creature"
  | .triggerSubject => "that creature"
  | .target 0 => if noun.isEmpty then "that creature" else noun
  | .inZones zs pred =>
    let s := ToOracle.toOracle { plural := false, capitalize := false } (ObjectExpr.inZones zs pred)
    let s := if s.startsWith "another " then "other " ++ (s.drop 8).copy else s
    s!"each {s}"
  | o => if noun.isEmpty then ToOracle.toOracle { capitalize := false } o else noun

private def extractSubtypesFromPred : ObjectPred → Option (Array CardSubtype)
  | .hasSubtype (.literal s) => some #[s]
  | .any ps =>
    let ss := ps.filterMap fun | .hasSubtype (.literal s) => some s | _ => none
    if ss.size == ps.size && !ss.isEmpty then some ss else none
  | _ => none

private def extractTypesFromInspectPred : ObjectPred → Option (Array String)
  | .hasType ty => some #[capitalizeAscii ty.oracleWord]
  | .hasSubtype (.literal s) => some #[s.englishName]
  | .isKind .permanentCard => some #["permanent"]
  | .any ps =>
    let xs := ps.filterMap fun
      | .hasType ty => some (capitalizeAscii ty.oracleWord)
      | .hasSubtype (.literal s) => some s.englishName
      | .isKind .permanentCard => some "permanent"
      | _ => none
    if xs.size == ps.size && !xs.isEmpty then some xs else none
  | _ => none

/-- Printed clause for a unified `Instruction` triggered-ability effect. -/
private def withUpToOne (noun : String) : String :=
  if noun.startsWith "up to " then noun else s!"up to one {noun}"

private partial def instrTriggerPhrase (e : Effect) (body : Instruction) (noun : String) : String :=
  match body with
  | .seq #[.permanent (.attach .this (.target 0) _), .ifCond (.exists .this) inner .noop] =>
    s!"attach it to {noun}. {capitalizeAscii (instrTriggerPhrase e inner "that creature")}"
  | .bind ⟨0⟩ (.create (.tokens .you (.const 1) kind _)) (.permanent (.attach .this (.stepObjects ⟨0⟩) _)) =>
    s!"{TokenSpec.createPhrase kind 1}, then attach this Equipment to it"
  | .bind ⟨0⟩ (.create (.tokens .you (.const 1) kind _)) (.permanent (.attach (.stepObjects ⟨0⟩) .this _)) =>
    if kind == .sturdyShield then
      "create a colorless Equipment artifact token named Sturdy Shield with \"Equipped creature gets +1/+2\" and equip {2}. Attach it to this creature"
    else
      s!"{TokenSpec.createPhrase kind 1}. Attach it to this creature"
  | .bind ⟨0⟩ (.player (.amass .you subtype (.const n))) (.permanent (.attach .this (.stepObjects ⟨0⟩) _)) =>
    s!"amass {pluralizeName subtype} {n.toNat}, then attach this Equipment to the amassed Army"
  | .create (.tokens .you (.const n) kind mods) =>
    if kind == .clue && n == 1 && !mods.tapped then "investigate"
    else if kind == .axe && n == 1 && !mods.tapped then
      "create a colorless Equipment artifact token named Axe with \"Equipped creature gets +1/+0\" and equip {2}"
    else if kind == .zabu && n == 1 && !mods.tapped then
      "create Zabu, a legendary 2/2 green Cat creature token with \"Landfall — Whenever a land you control enters, put a +1/+1 counter on Zabu.\""
    else if kind == .redwing && n == 1 && !mods.tapped then
      "create Redwing, a legendary 1/1 blue Bird Scout creature token with flying and \"Whenever Redwing attacks, surveil 1.\""
    else
      let isCopy := match kind with | .copyOf .. => true | _ => false
      let hasExtraMods := mods != {} && mods != { tapped := true }
      if isCopy || hasExtraMods then
        Instruction.toOracleWith { capitalize := false } e.targets body
      else
        TokenSpec.createPhrase kind n.toNat (tapped := mods.tapped)
  | .create (.tokens (.target 0) (.const 1) kind _) =>
    if kind == .theVoid then
      s!"{noun} creates The Void, a legendary 5/5 black Horror Villain creature token with flying, indestructible, and \"The Void attacks each combat if able.\""
    else s!"{noun} creates {kind.oracleNoun}"
  | .create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .opponent]))) .treasure mods) =>
    if mods.tapped then "create X tapped Treasure tokens, where X is the number of artifacts your opponents control"
    else "create a Treasure token for each artifact your opponents control"
  | .bind ⟨0⟩ (.player (.choose .you .creatureType))
      (.create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype (.fromStep ⟨0⟩), .controlledBy .you]))) .treasure _)) =>
    "choose a creature type. Create a Treasure token for each creature you control of that type"
  | .create (.tokens .you (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .creature, .hasSubtype .chosenOnSource, .controlledBy .you]))) .treasure _) =>
    "create a Treasure token for each creature you control of the chosen type"
  | .create (.tokens .you .eventAmount .birdSoldier _) =>
    "create X 1/1 white Bird Soldier creature tokens with flying"
  | .create (.tokens .you .eventAmount .treasure _) =>
    "create that many Treasure tokens"
  | .player (.scry .you (.const n)) => s!"scry {n.toNat}"
  | .player (.surveil .you (.const n)) => s!"surveil {n.toNat}"
  | .player (.empowerPlaneswalker .jace (.const n)) => s!"empower Jace {n.toNat}"
  | .player (.drawCards .you (.const n)) => s!"draw {cardPhrase n.toNat}"
  | .player (.drawCards .you (.playerMetric .one (.matching .anyPlayer (.metric .graveyardSize .ge (.const 7))))) =>
    "draw a card for each graveyard with seven or more cards in it"
  | .player (.amass .you subtype (.const n)) =>
    s!"amass {pluralizeName subtype} {n.toNat}"
  | .player (.amass .you subtype (.objectStat .power .this)) =>
    s!"amass {pluralizeName subtype} X, where X is this creature's power"
  | .player (.connive .this) => "it connives"
  | .player (.connive (.target 0)) => s!"{noun} connives"
  | .player (.temptWithRing .you) => "the Ring tempts you"
  | .player (.addMana .you mp) =>
    let manaSym : ManaType → String
      | .colored c => s!"\{{c.letter}}"
      | .colorless => "{C}"
    let syms :=
      match mp.spec with
      | .sequence pairs =>
        if pairs.all (fun p => p.2.evalConst?.isSome) then
          String.join (pairs.toList.map fun (p : ManaType × ValueExpr) =>
            String.join (List.replicate (p.2.evalConst?.getD 1).toNat (manaSym p.1)))
        else ""
      | _ => ""
    if syms.isEmpty then
      let rawS := mp.toOracleSentence {}
      let noDot := if rawS.endsWith "." then (rawS.dropEnd 1).copy else rawS
      if noDot.startsWith "Add " then "add " ++ (noDot.drop 4).copy else noDot
    else s!"add {syms}"
  | .player (.searchLibrary spec) =>
    if spec.filter == .hasSubtype (.literal .forest) then
      "search your library for a Forest card, put that card onto the battlefield, then shuffle"
    else if spec.filter == .all #[.hasSupertype .basic, .hasType .land] &&
        spec.dest == .hand .controller &&
        spec.count == .upTo (.const 1) &&
        spec.groupConstraint?.isNone then
      searchLibraryToHandPhrase "a basic land card"
    else
      Instruction.toOracleWith { capitalize := false } e.targets body
  | .player (.inspectLibrary spec) =>
    match spec.source, spec.action with
    | .topCards .you (.const n) false, .takeMatching pred (.upTo (.const 1)) (.hand .controller) _ true _ =>
      match extractTypesFromInspectPred pred with
      | some ts =>
        let joined :=
          match ts.toList with
          | [a, b] => s!"a {a} or {b} card"
          | xs => s!"a {String.intercalate " or " xs} card"
        s!"look at the top {n.toNat} cards of your library. You may reveal {joined} from among them and put it into your hand. {restOnBottomRandomPhrase}"
      | none =>
        let rawP := toOracleStr pred { capitalize := false }
        let pS := if rawP.endsWith " card" then (rawP.dropEnd 5).copy else rawP
        let restS := match spec.rest with
          | .bottomRandom => restOnBottomRandomPhrase
          | .bottomAnyOrder => "Put the rest on the bottom of your library in any order"
          | .graveyard => "Put the rest into your graveyard"
          | .exile => "Exile the rest"
          | .shuffleIntoLibrary => "Shuffle the rest into your library"
          | .leaveInPlace => ""
        let tail := if restS.isEmpty then "" else s!". {restS}"
        s!"look at the top {n.toNat} cards of your library. You may reveal {indefinite pS} {pS} card from among them and put it into your hand{tail}"
    | .topCards .you (.const n) true, .takeMatching (.hasType .creature) (.exact (.const 1)) (.battlefield .controller) _ false true =>
      s!"reveal the top {n.toNat} cards of your library. Put a random creature card from among them onto the battlefield. {restOnBottomRandomPhrase}"
    | .millCards .you (.const n), .takeMatching (.hasSubtype (.literal sub)) .anyNumber (.hand .controller) _ _ _ =>
      s!"mill {n.toNat} cards, then put all {sub} cards from among them into your hand"
    | _, _ => Instruction.toOracleWith { capitalize := false } e.targets body
  | .player (.reveal (.target 0) _ (some _)) =>
    s!"{noun} reveals a number of cards from their hand equal to one plus the number of creature cards in your graveyard. You choose one of them. That player discards that card"
  | .seq #[.player (.reveal (.target 0) _ none), .ifCond (.exists .this) (.moveZone (.target 1) .exile .exile _) .noop] =>
    "choose target opponent and up to one target creature they control. They reveal their hand. You may exile a nonland card from their hand or the chosen creature until this leaves the battlefield"
  | .seq #[.player (.drawCards .you (.const 1)),
           .bind ⟨0⟩ (.moveZone (.inZones _ .anyObject) .graveyard .discard _)
             (.ifCond (.exists (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))))
               (.create (.tokens .you (.const 1) .humanSoldier _)) .noop)] =>
    "recruit"
  | .damage (.deal .this .allTargets (.const _) fl) =>
    if fl.divided then
      match e.dividedDamage? with
      | some (amount, maxTargets) =>
        s!"it deals {amount} damage divided as you choose among {dividedAmong maxTargets}"
      | none => "it deals damage divided as you choose"
    else
      Instruction.toOracleWith { capitalize := false } e.targets body
  | .damage (.deal .this (.players (.target 0)) (.const n) _) =>
    s!"this creature deals {n.toNat} damage to {noun}"
  | .damage (.deal .this (.players (.matching .opponent .any)) (.const n) _) =>
    s!"this creature deals {n.toNat} damage to each opponent"
  | .damage (.deal .this (.players _) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal sub), .controlledBy _]))) _) =>
    s!"it deals damage equal to the number of {pluralSubtype sub} you control to each opponent"
  | .damage (.deal .this (.targetSlot 0) (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .treasure), .controlledBy _]))) _) =>
    s!"it deals damage equal to the number of Treasures you control to {noun}"
  | .damage (.deal .this (.objects (.inZones .battlefield (.all #[.hasType .creature, .combatRole (.blockingObject .this)]))) (.const n) _) =>
    s!"it deals {n.toNat} damage to each creature blocking it"
  | .damage (.deal .this (.targetSlot 0) (.objectStat .power .this) _) =>
    s!"it deals damage equal to its power to {noun}"
  | .damage (.deal _ (.objects obj) (.const n) _) =>
    s!"deals {n.toNat} damage to {instrObjNoun noun obj}"
  | .damage (.deal _ (.targetSlot 0) (.const n) _) =>
    if e.allowsZeroTargets then s!"it deals {n.toNat} damage to {withUpToOne noun}"
    else s!"deals {n.toNat} damage to {noun}"
  | .damage (.fight .this (.target 0) false) =>
    s!"this fights {noun}"
  | .life (.gain .you (.const n)) => s!"you gain {n.toNat} life"
  | .life (.lose (.target 0) (.const n)) => s!"{noun} loses {n.toNat} life"
  | .permanent (.attach .this (.target 0) false) =>
    s!"attach it to {noun}"
  | .permanent (.attach (.target 0) (.target 1) false) =>
    Instruction.toOracleWith { capitalize := false } e.targets body
  | .permanent (.modifyCounters (.put kind (.const n)) obj _) =>
    match obj with
    | .inZones .battlefield (.all #[.hasType .creature, .controlledBy _]) =>
      "put a +1/+1 counter on each creature you control"
    | .inZones .battlefield (.all #[.hasSubtype (.literal .equipment), .controlledBy _]) =>
      if kind == .hone then "put a hone counter on each Equipment you control"
      else s!"put a {kind.oracleName} counter on each Equipment you control"
    | .inZones .battlefield (.all #[.hasSubtype (.literal s), .controlledBy _]) =>
      s!"put a +1/+1 counter on each {s} you control"
    | _ =>
      counterOn (instrObjNoun noun obj) kind n.toNat
  | .permanent (.modifyCounters (.put .plusOnePlusOne (.objectStat .manaValue .triggerSubject)) (.target 0) _) =>
    s!"put X +1/+1 counters on {noun}, where X is that spell's mana value"
  | .permanent (.modifyCounters (.copyFromLki .this) (.target 0) _) =>
    "put its counters on up to one target creature you control"
  | .permanent (.setTapped obj true _) =>
    s!"tap {instrObjNoun noun obj}"
  | .permanent (.setTapped obj false _) =>
    s!"untap {instrObjNoun noun obj}"
  | .permanent (.setDesignation obj .prepared true) =>
    s!"{instrObjNoun noun obj} becomes prepared"
  | .ifCond (.playerPred .you (.hasDesignation .citysBlessing))
      (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 2)) _ _))
      (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) _ _)) =>
    "put a +1/+1 counter on each creature you control. If you have the city's blessing, put two +1/+1 counters on each creature you control instead"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.const p) (.const t))) =>
    match obj with
    | .inZones .battlefield (.all #[.hasType .creature, .controlledBy _]) =>
      s!"creatures you control get {signedStat p}/{signedStat t} until end of turn"
    | _ =>
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.objectStat .power _) (.objectStat .toughness _))) =>
    s!"double {instrObjNoun noun obj}'s power and toughness until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.modifyPT (.objectStat .power .this) (.const 0))) =>
    s!"{noun} gets +X/+0 until end of turn, where X is this creature's power"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.objectStat .power obj2) (.const 0))) =>
    if obj == obj2 then s!"double {instrObjNoun noun obj}'s power until end of turn"
    else Instruction.toOracleWith { capitalize := false } e.targets body
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.modifyPT (.aggregate .count .one (.inZones .battlefield (.all #[.hasSubtype (.literal .plains), .controlledBy _]))) _)) =>
    "target creature you control gets +1/+1 until end of turn for each Plains you control"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT .eventAmount .eventAmount)) =>
    "this creature gets +1/+1 until end of turn for each card looked at while scrying this way"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.aggregate .max (.stat .power) _) (.const 0))) =>
    "it gets +X/+0 until end of turn, where X is the greatest power among creatures you control"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.aggregate .count .one (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy _]))) _)) =>
    "it gets +1/+1 until end of turn for each other creature you control"
  | .installEffect (.applyContinuous .untilEndOfTurn (.inZones .battlefield (.all #[.otherThan .this, .hasSubtype (.literal sub), .controlledBy _])) (.modifyPT (.objectStat .toughness .this) (.objectStat .toughness .this))) =>
    s!"each other {sub} you control gets +X/+X until end of turn, where X is this toughness"
  | .installEffect (.applyContinuous .untilEndOfTurn .this (.all #[.modifyTypes { types := #[.creature], .. }, .setBasePT (some (.const p)) (some (.const t))])) =>
    s!"it becomes a {p}/{t} creature until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.setBasePT (some (.objectStat .power .this)) (some (.objectStat .toughness .this)))) =>
    "choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.grantKeywords k)) =>
    s!"{instrObjNoun noun obj} gains {KeywordAbility.joinedAnd k} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.loseKeywords k)) =>
    if k == #[Keyword.indestructible] then
      s!"{instrObjNoun noun obj} loses indestructible until end of turn"
    else
      s!"{instrObjNoun noun obj} loses {KeywordAbility.joinedAnd k} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.setBasePT (some (.const p)) (some (.const t)))) =>
    s!"{instrObjNoun noun obj} has base power and toughness {p}/{t} until end of turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.applyRule (.combat (.cantBeBlocked .self)))) =>
    s!"{instrObjNoun noun obj} can't be blocked this turn"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.modifyTypes { types := #[.artifact], .. }))
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.all #[.modifyTypes { types := #[.artifact], .. }])) =>
    s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types"
  | .installEffect (.applyContinuous .untilEndOfTurn obj (.all #[.modifyTypes { types := #[.artifact], .. }, .grantKeywords k])) =>
    if k == #[Keyword.indestructible] then
      s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types and gains indestructible"
    else
      s!"until end of turn, {instrObjNoun noun obj} becomes an artifact in addition to its other types"
  | .moveZone (.topOfLibrary (.target 0) (.const n)) .graveyard .mill _ =>
    s!"{noun} mills {n.toNat} cards"
  | .moveZone (.topOfLibrary (.triggerPlayer .actor) .eventAmount) .graveyard .mill _ =>
    "that player mills that many cards"
  | .moveZone (.topOfLibrary .you (.const 1)) .exile .exile { grantPlayPerm? := some gp, .. } =>
    if gp == { duration := .untilEndOfNextTurnOf .you, landsAllowed := true } then
      s!"exile the top card of your library. {playThatCardUntilNextTurnPhrase}"
    else Instruction.toOracleWith { capitalize := false } e.targets body
  | .moveZone (.target 0) .exile .exile { grantPlayPerm? := some gp, .. } =>
    if gp == { duration := .untilEndOfNextTurnOf .you, landsAllowed := true } then
      s!"exile {noun}. {playThatCardUntilNextTurnPhrase}"
    else Instruction.toOracleWith { capitalize := false } e.targets body
  | .moveZone (.target 0) .exile .exile { exileUntilSourceLeaves := true, .. } =>
    if e.allowsZeroTargets then
      s!"you may exile {noun} until this leaves the battlefield"
    else s!"exile {noun} until this leaves the battlefield"
  | .moveZone .allTargets .exile .exile { exileUntilSourceLeaves := true, .. } =>
    "for each opponent, exile up to one target nonland permanent that player controls until this leaves the battlefield"
  | .moveZone (.target 0) .exile .exile { linkToSource := true, .. } =>
    if e.allowsZeroTargets then s!"you may exile {noun}" else s!"exile {noun}"
  | .moveZone (.linkedExile .this) (.battlefield .owner) .put _ =>
    "return the exiled card to the battlefield under its owner's control"
  | .moveZone (.target 0) (.battlefield .owner) .put _ =>
    match (e.targets.slots[0]?.map (·.domain) : Option TargetDomain) with
    | some (.object .anyGraveyard (.all #[.not (.hasType .land), .isKind .permanentCard, .stat .manaValue .le (.const mv)])) =>
      s!"put up to one target nonland permanent card with mana value {mv.toNat} or less from a graveyard onto the battlefield under its owner's control"
    | _ => s!"return {noun} to the battlefield under its owner's control"
  | .moveZone (.target 0) (.hand .owner) .returnToHand _ =>
    if e.targets == .permanentCardInYourGraveyard then
      s!"choose {noun.replace " from your graveyard" " in your graveyard"} that was put there from anywhere this turn. Return it to your hand"
    else if e.allowsZeroTargets then
      s!"return {withUpToOne noun} to its owner's hand"
    else s!"return {noun} to its owner's hand"
  | .moveZone (.inZones (.handOf (.target 0)) .anyObject) .graveyard .discard _ =>
    match body with
    | .moveZone _ _ _ { choice? := some { count := .exact (.const n), .. }, .. } =>
      s!"{noun} discards {cardPhrase n.toNat}"
    | _ => s!"{noun} discards a card"
  | .moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy (.ofExpr (.target 0))])) .graveyard .sacrifice _ =>
    s!"{noun} sacrifices a creature of their choice"
  | .moveZone (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .defendingPlayer])) .graveyard .sacrifice _ =>
    "defending player sacrifices a creature with the least power among creatures they control"
  | .forEach (.eachPlayer .opponent) ⟨0⟩ (.moveZone (.inZones (.handOf _) .anyObject) .graveyard .discard _) =>
    "each opponent discards a card"
  | .forEach (.eachPlayer .any) ⟨0⟩ (.moveZone (.inZones .battlefield (.all #[.hasType .creature, _])) .graveyard .sacrifice _) =>
    "each player sacrifices a creature of their choice"
  | .moveZone obj (.library .owner .top false) .put _ =>
    s!"{instrObjNoun noun obj}'s owner puts it on top of their library"
  | .moveZone obj (.library .owner .bottom false) .put _ =>
    s!"{instrObjNoun noun obj}'s owner puts it on the bottom of their library"
  | .moveZone obj .graveyard .destroy _ =>
    s!"destroy {instrObjNoun noun obj}"
  | .moveZone obj .exile .exile m =>
    if m == {} then s!"exile {instrObjNoun noun obj}"
    else Instruction.toOracleWith { capitalize := false } e.targets body
  | .optional .you (some cs) (.player (.drawCards .you (.const n))) .noop _ =>
    if cs == CostSpec.discardCard then
      s!"you may discard a card. If you do, draw {cardPhrase n.toNat}"
    else
      match cs.soleGenericMana? with
      | some k => s!"you may pay \{{k}}. If you do, draw {cardPhrase n.toNat}"
      | none => s!"you may pay {cs.toNotation}. If you do, draw {cardPhrase n.toNat}"
  | .optional .you (some cs) (.seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _), .player (.drawCards .you (.const 1))]) .noop _ =>
    match cs.soleGenericMana? with
    | some k => s!"you may pay \{{k}}. If you do, put a +1/+1 counter on this creature and draw a card"
    | none => s!"you may pay {cs.toNotation}. If you do, put a +1/+1 counter on this creature and draw a card"
  | .optional .you (some cs) (.permanent (.modifyCounters (.put .plusOnePlusOne (.stepMetric .sumPower ⟨0⟩)) .this _)) .noop _ =>
    let _ := cs
    "you may sacrifice another creature. If you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power"
  | .optional .you (some _) (.seq #[.player (.drawCards .you (.const 1)), .create (.tokens .you (.const 1) .treasure _)]) .noop _ =>
    "you may sacrifice another creature or artifact. If you do, draw a card and create a Treasure token"
  | .optional .you (some cs) (.queueReflexiveTrigger ab) .noop _ =>
    if cs == CostSpec.sacrificeAnotherCreature && ab.effect.body == Instruction.destroy (.target 0) then
      "you may sacrifice another creature. When you do, destroy target nonland permanent an opponent controls"
    else if cs == CostSpec.sacrificeArtifactOrDiscardNonland then
      "you may sacrifice an artifact or discard a nonland card. When you do, this deals 2 damage to any target"
    else if cs == CostSpec.tapOnly then
      "you may tap this creature. When you do, another target nonattacking creature you control gains indestructible until end of turn"
    else
      let reflS := Instruction.toOracleWith { capitalize := false } .none (.queueReflexiveTrigger ab)
      s!"you may {cs.toInlinePhrase}. {capitalizeAscii reflS}"
  | .optional .you none (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _) (.player (.drawCards .you (.const n)))) .noop _ =>
    s!"you may discard your hand. If you do, draw {cardPhrase n.toNat}"
  | .optional .you none (.seq #[.player (.drawCards .you (.manaSpent .triggerSubject)), .ifCond _ (.moveZone _ .graveyard .discard { choice? := some { count := .exact (.const n), .. }, .. }) .noop]) .noop _ =>
    let disc := if n == 2 then "two cards" else cardPhrase n.toNat
    s!"you may draw X cards, where X is the amount of mana spent to cast that spell. If you do, discard {disc}"
  | .optional .you none (.installEffect (.applyContinuous .untilEndOfTurn .this (.setBasePT (some (.const p)) (some (.const t))))) .noop _ =>
    s!"you may have this creature's base power and toughness become {p}/{t} until end of turn"
  | .optional .you none (.bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) (.hasType .artifact)) (.battlefield .controller) .put _) _) .noop _ =>
    "you may put an artifact card from your hand onto the battlefield. If it's an Equipment, attach it to this creature"
  | .bind ⟨0⟩ (.moveZone (.target 0) (.hand .owner) .returnToHand _) (.life (.gain .you (.stepMetric .sumPower ⟨0⟩))) =>
    s!"return {noun} to your hand. You gain life equal to that card's power"
  | .bind ⟨0⟩ (.moveZone (.target 0) (.hand .owner) .returnToHand _) (.ifCond (.stepSucceeded ⟨0⟩) (.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _)) .noop) =>
    s!"return {noun} to its owner's hand. If you do, put a +1/+1 counter on this creature"
  | .bind ⟨0⟩ (.moveZone (.inZones .battlefield (.all #[.any #[.hasType .artifact, .hasType .enchantment], .controlledBy .opponent])) .graveyard .destroy _) (.life (.gain .you (.stepMetric .movedCount ⟨0⟩))) =>
    "destroy all artifacts and enchantments your opponents control. You gain 1 life for each permanent destroyed this way"
  | .bind ⟨0⟩ (.moveZone (.target 0) .graveyard .destroy _) (.create (.tokens (.controllerOf (.target 0)) (.const 1) .treasure _)) =>
    s!"destroy {noun}. They create a Treasure token"
  | .bind ⟨0⟩ (.permanent (.setTapped _ true (some _))) (.player (.drawCards .you (.stepMetric .movedCount ⟨0⟩))) =>
    "you may tap any number of untapped Humans you control. Draw a card for each Human tapped this way"
  | .bind ⟨0⟩ (.damage (.deal .this (.targetSlot 0) (.const n) _)) (.ifCond _ (.moveZone (.filter (.stepObjects ⟨0⟩) (.hasSubtype (.literal sub))) .graveyard .destroy _) .noop) =>
    s!"it deals {n.toNat} damage to {noun}. If a {sub} is dealt damage this way, destroy it"
  | .bind ⟨0⟩ (.player (.inspectLibrary { source := .revealUntil .you (.hasType .creature) _, .. })) _ =>
    s!"reveal cards from the top of your library until you reveal a creature card. If its mana value is less than or equal to the number of lands you control, put it onto the battlefield. Otherwise, put it into your hand. {restOnBottomRandomPhrase}"
  | .bind ⟨0⟩ (.moveZone (.topOfLibrary .opponents (.const 2)) .graveyard .mill _) _ =>
    "each opponent mills two cards. When one or more cards are milled this way, exile target enchantment, instant, or sorcery card with equal or lesser mana value than that spell from an opponent's graveyard. Copy the exiled card. You may cast the copy without paying its mana cost"
  | .bind ⟨0⟩ (.moveZone .this .graveyard .sacrifice _) (.ifCond (.stepSucceeded ⟨0⟩) (.queueReflexiveTrigger ab) .noop) =>
    s!"sacrifice it. When you do, {instrTriggerPhrase ab.effect ab.effect.body ab.effect.targets.noun}"
  | .bind ⟨0⟩ (.player (.inspectLibrary { source := .revealUntil .you (.all #[.not (.hasType .land), .stat .manaValue .lt (.objectStat .manaValue .this)]) _ true, .. })) _ =>
    "exile cards from the top of your library until you exile a nonland card that costs less. You may cast it without paying its mana cost"
  | .stack (.mayCastOrPlay (.inZones (.handOf .you) _) { maxTotalManaValue? := some (.binary .mul (.const 2) _), .. }) =>
    "you may cast an instant or sorcery spell with mana value X or less from your hand without paying its mana cost, where X is twice the number of legendary Wizards you control"
  | .stack (.mayCastOrPlay (.inZones (.handOf .you) _) { maxTotalManaValue? := some .eventAmount, .. }) =>
    "you may cast an instant or sorcery spell from your hand with mana value less than or equal to that damage without paying its mana cost"
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, .controlledBy _])) _),
           .life (.gain .you (.aggregate .count .one _))] =>
    "put a +1/+1 counter on each other creature you control. You gain 1 life for each other creature you control"
  | .seq #[.life (.gain .you (.const n)), .player (.searchLibrary _)] =>
    s!"you gain {n.toNat} life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.gainControl .you)),
           .permanent (.setTapped (.target 0) false _),
           .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords _))] =>
    s!"gain control of {noun} until end of turn. Untap it. It gains haste until end of turn"
  | .seq #[.player (.drawCards .you (.const 1)), .ifCond (.not _) (.moveZone (.inZones .yourHand .anyObject) (.library .owner .bottom false) .put _) .noop]
  | .seq #[.player (.drawCards .you (.const 1)), .ifCond (.not _) (.moveZone (.inZones (.handOf .you) .anyObject) (.library .owner .bottom false) .put _) .noop] =>
    "draw a card. Then if you don't control a legendary creature, put a card from your hand on the bottom of your library"
  | .seq #[.bind ⟨0⟩ (.permanent (.modifyCounters (.remove (some .hope) _) .this _)) _, .ifCond _ (.seq #[.moveZone .this .graveyard .sacrifice _, .life (.gain .you (.const 4))]) .noop] =>
    "remove a hope counter from this. If you do, draw a card. Then if this has no hope counters on it, sacrifice it and you gain 4 life"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.inZones .battlefield (.all #[.otherThan .this, .hasType .creature, subPred, .controlledBy _])) (.modifyPT (.const p) (.const t))),
           .installEffect (.applyContinuous .untilEndOfTurn _ (.modifyPT (.const oppP) (.const oppT)))] =>
    match extractSubtypesFromPred subPred with
    | some subtypes =>
      let who :=
        if subtypes == #[.goblin, .orc] then "other Goblins and Orcs you control"
        else s!"other {joinedSubtypes subtypes} you control"
      s!"{who} get {signedStat p}/{signedStat t} until end of turn. Creatures your opponents control get {signedStat oppP}/{signedStat oppT} until end of turn"
    | none => "resolve each step"
  | .seq #[.permanent (.modifyCounters (.put .trample (.const 1)) (.target 0) _),
           .installEffect (.applyContinuous .indefinite (.target 0) (.modifyTypes { subtypes := #[.bear], .. })),
           .ifCond _ (.player (.drawCards .you (.const 2))) .noop] =>
    s!"put a trample counter on {withUpToOne noun}. It becomes a Bear in addition to its other types. Then if you control three or more Bears, draw two cards"
  | .seq #[.permanent (.modifyCounters (.put .quest (.const 1)) .this _), .ifCond _ (.bind ⟨0⟩ (.moveZone .this .graveyard .sacrifice _) _) .noop] =>
    "put a quest counter on this enchantment. If it has six or more quest counters on it, sacrifice it. If you do, search your hand and/or library for a Dragon card and put it onto the battlefield. If you search your library this way, shuffle"
  | .seq #[.player (.drawCards .you (.const 1)), .bind ⟨0⟩ (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard _) (.moveZone (.filter (.stepObjects ⟨0⟩) (.hasType .land)) (.battlefield .controller) .put { tapped := true, .. })] =>
    "draw a card, then discard a card. If you discard a land card this way, put it from your graveyard onto the battlefield tapped"
  | .seq #[.bind ⟨0⟩ (.create (.tokens .you (.const 1) .alien _)) _, .permanent (.modifyCounters (.put .invasion (.const 1)) .this _)] =>
    "create a 1/1 red Alien creature token with haste and \"This token attacks each combat if able.\" Put a +1/+1 counter on it for each invasion counter on this enchantment, then put an invasion counter on this enchantment"
  | .seq #[.permanent (.setTapped _ false _), .turn (.extraPhase .combat true)] =>
    "untap all attacking creatures. After this phase, there is an additional combat phase"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.scry .you (.const n))] =>
    s!"scry {n.toNat} and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.drawCards .you (.const 1)), .moveZone _ .graveyard .discard _] =>
    "draw a card, then discard a card and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .create (.tokens .you (.const 1) .villain21menace _)] =>
    "create a 2/1 black Villain creature token with menace and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .life (.lose _ (.const n)), .life (.gain .you (.const m))] =>
    s!"each opponent loses {n.toNat} life and you gain {m.toNat} life. Put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .player (.drawCards .you (.const 1)), .life (.lose .you (.const 1))] =>
    "you draw a card, lose 1 life, and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .create (.tokens .you (.const 1) .treasure { tapped := true, .. })] =>
    "create a tapped Treasure token and put a plan counter on this enchantment"
  | .seq #[.permanent (.modifyCounters (.put .plan (.const 1)) .this _), .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) (.target 0) _)] =>
    "put a +1/+1 counter on target creature you control and a plan counter on this enchantment"
  | .seq #[.moveZone .this .graveyard .sacrifice _, .player (.drawCards .you (.const 1)), .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) _ _)] =>
    "sacrifice it, draw a card, and put a +1/+1 counter on each creature you control"
  | .seq #[.moveZone .this .graveyard .sacrifice _, .create (.tokens .you (.const n) .robotVillain22 _)] =>
    s!"sacrifice it and create {englishNumber n.toNat} 2/2 colorless Robot Villain artifact creature tokens"
  | .seq #[.permanent (.setTapped (.target 0) true _), .installEffect (.applyContinuous (.whileOnBattlefield .this) (.target 0) (.applyRule (.game (.cantBecomeUntapped .self))))] =>
    s!"tap {noun}. That creature can't become untapped for as long as you control this creature"
  | .seq #[.permanent (.setTapped (.target 0) true _), .ifCond (.exists .this) (.installEffect (.applyContinuous (.whileOnBattlefield .this) (.target 0) .loseAllAbilities)) .noop] =>
    "tap up to one target creature. It loses all abilities for as long as this remains on the battlefield"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords k)),
           .ifCond (.exists (.filter (.target 0) (.hasType .creature))) _ .noop,
           .ifCond (.exists (.filter (.target 0) (.hasType .planeswalker))) _ .noop] =>
    s!"{noun} gains {KeywordAbility.joinedAnd k} until end of turn. Put a +1/+1 counter on it if it's a creature. Put a loyalty counter on it if it's a planeswalker"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn obj (.modifyPT (.const p) (.const t))),
           .installEffect (.applyContinuous .untilEndOfTurn _ (.grantKeywords k))] =>
    if k == #[Keyword.trample] then
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} and gains trample until end of turn"
    else
      s!"{instrObjNoun noun obj} gets {signedStat p}/{signedStat t} and gains {KeywordAbility.joinedAnd k} until end of turn"
  | .seq #[.permanent (.setTapped obj true _), .permanent (.modifyCounters (.put .stun (.const 1)) _ _)] =>
    s!"tap {instrObjNoun noun obj} and put a stun counter on it"
  | _ =>
    Instruction.toOracleWith { capitalize := false } e.targets body

/-- Effect clause rendered from unified `Instruction`, targeting, and divided-damage parameters. -/
def resolutionPhrase (t : Effect) : String :=
  instrTriggerPhrase t t.body t.targets.noun

/-- Sentence whose printed “When/Whenever …” lead-in differs from the generic
`eventPrefix` (a card name, an ability word, or a more specific subject) but
whose effect clause is the shared `resolutionPhrase`. -/
def leadInSentence (ab : TriggeredAbility) (lead : String) : String :=
  s!"{lead}, {resolutionPhrase ab.effect}."

/-- Printed clause when the effect is a pure `Instruction` sequence.
Numbers and the target noun come from the effect, so Oracle refill stays
in step with the printed line. -/
def sequenceClause (e : Effect) : Option String :=
  let noun := e.targetSpec.noun
  match e.body with
  | .seq #[.player (.drawCards .you (.const 1)), .life (.lose .you (.const 1))] =>
    some "you draw a card and lose 1 life"
  | .seq #[.player (.drawCards .you (.const n)),
           .moveZone (.inZones _ .anyObject) .graveyard .discard _] =>
    some s!"draw {cardPhrase n.toNat}, then discard a card"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const p) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.grantKeywords k))] =>
    if k == #[Keyword.trample] then
      some s!"until end of turn, this creature gets {signedStat p}/+0 and creatures you control gain trample"
    else none
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) (.target 0) _),
           .installEffect (.applyContinuous .untilEndOfTurn (.target 0) (.grantKeywords k))] =>
    if k == #[Keyword.lifelink] && n == 1 then
      some s!"put a +1/+1 counter on {noun}. It gains lifelink until end of turn"
    else if k == #[Keyword.vigilance] then
      some s!"put {plusOnePlusOneCountersPhrase n.toNat} on {noun}. It gains vigilance until end of turn"
    else none
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const 1) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn .this (.applyRule (.combat (.cantBeBlocked .self))))] =>
    some "this gets +1/+0 until end of turn and can't be blocked this turn"
  | .seq #[.player (.drawCards .you (.const 1)),
           .permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _)] =>
    some "draw a card and put a +1/+1 counter on this"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.modifyPT (.const p) (.const 0))),
           .installEffect (.applyContinuous .untilEndOfTurn (.inZones _ _) (.grantKeywords k))] =>
    if k == #[Keyword.firstStrike] then
      some s!"creatures you control get {signedStat p}/+0 and gain first strike until end of turn"
    else none
  | .seq #[.permanent (.modifyCounters (.put .plusOnePlusOne (.const 1)) .this _),
           .player (.drawCards .you (.const 1))] =>
    some "put a +1/+1 counter on this and draw a card"
  | .seq #[.installEffect (.applyContinuous .untilEndOfTurn .this (.modifyPT (.const p) (.const t))),
           .damage (.deal .this (.players _) (.const n) _)] =>
    some s!"this gets {signedStat p}/{signedStat t} until end of turn and deals {n} damage to each opponent"
  | .seq #[.permanent (.setTapped (.target 0) false _),
           .ifCond (.exists (.filter (.target 0) (.hasSubtype (.literal subtype))))
             (.permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) (.target 0) _)) .noop] =>
    some s!"untap {noun}. If that creature is a {subtype}, put {plusOnePlusOneCountersPhrase n.toNat} on it"
  | .seq #[.life (.lose .you (.const n)),
           .create (.tokens .you (.const 1) k _)] =>
    some s!"you lose {n} life and {TokenSpec.createPhrase k 1}"
  | .seq #[.moveZone (.target 0) .exile .exile _,
           .life (.lose _ (.const n))] =>
    some s!"exile {withUpToOne noun}. Each opponent loses {n} life"
  | _ => none

private partial def isEnchantedHostInstr : Instruction → Bool
  | .permanent (.setTapped .attachedHost _ _)
  | .permanent (.modifyCounters _ .attachedHost _)
  | .permanent (.setDesignation .attachedHost _ _)
  | .moveZone .attachedHost _ _ _
  | .damage (.deal _ (.objects .attachedHost) _ _)
  | .installEffect (.applyContinuous _ .attachedHost _) => true
  | .seq steps => steps.any isEnchantedHostInstr
  | _ => false

def toNotation (ab : TriggeredAbility) : String :=
  if ab.isSagaChapter then
    s!"When a lore counter is put on this Saga, {resolutionPhrase ab.effect}."
  else if ab.isManaSpentCastScry then
    let n :=
      match ab.effect.body with
      | .player (.scry _ (.const k)) => k.toNat
      | _ => 1
    s!"When that mana is spent to cast a creature spell that shares a creature type with your commander, scry {n}."
  else if ab.isModal then
    let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
    match ab.effect.body with
    | .chooseModes spec =>
      if spec.chooseAtResolution && spec.modes.size == 2 && ab.effect.targets.isEmpty then
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase spec.modes[0]!} or {resolutionPhrase spec.modes[1]!}.{once}"
      else
        let modeTexts := ab.modeEffects.toList.map fun m =>
          let txt := capitalizeAscii (resolutionPhrase m)
          let txt := if txt.endsWith "." then txt else s!"{txt}."
          s!"• {txt}"
        let hdr :=
          match spec.altCountIf? with
          | some (cond, .const 1, .const n) =>
            if n >= 3 then s!"choose one. If {toOracleStr cond { capitalize := false }}, choose one or more instead"
            else s!"choose one. If {toOracleStr cond { capitalize := false }}, you may choose two instead"
          | _ =>
            if spec.minModes == ValueExpr.const 0 && spec.maxModes == ValueExpr.chosenX then "choose up to X"
            else if spec.minModes == ValueExpr.const 0 && spec.maxModes == ValueExpr.eventAmount then "choose up to that many"
            else if spec.minModes == ValueExpr.const 2 && spec.maxModes == ValueExpr.const 2 then "choose two"
            else if spec.unusedThisTurn then "choose one that hasn't been chosen this turn"
            else if spec.unusedEver then "choose one that hasn't been chosen"
            else "choose one"
        s!"{eventPrefix ab}{interveningClause ab}, {hdr} — {" ".intercalate modeTexts}{once}"
    | _ =>
      let modeTexts := ab.modeEffects.toList.map fun m =>
        let txt := capitalizeAscii (resolutionPhrase m)
        let txt := if txt.endsWith "." then txt else s!"{txt}."
        s!"• {txt}"
      s!"{eventPrefix ab}{interveningClause ab}, choose one — {" ".intercalate modeTexts}{once}"
  else
    let p := ab.pattern
    match ab.effect.body with
    | .create (.tokens .you (.const n) k _) =>
      if p == .stepEachUpkeep && ab.interveningIf?.isNone then
        s!"At the beginning of each player's upkeep, you {TokenSpec.createPhrase k n.toNat}."
      else if p == .drawCard .opponent && ab.limit == .nthEachTurn 2 && n == 1 then
        "Whenever an opponent draws their second card each turn, you create a Treasure token."
      else if p == .damageDealt (.all #[.hasSubtype (.literal .dwarf), .controlledBy .you])
          (.playerOrObject .any { zones := .battlefield, pred := .hasType .battle }) (combatOnly := true) && n == 2 then
        leadInSentence ab "Whenever a Dwarf you control deals combat damage to a player or battle"
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        let clause := (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        s!"{eventPrefix ab}{interveningClause ab}, {clause}.{once}"
    | .permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) .this _) =>
      if n == 2 && p == .anotherSubtypeYouControlEnters .wolf then
        "Whenever another Wolf you control enters, put two +1/+1 counters on Chief of the Wilds."
      else if n == 1 && p == .thisDealtDamage then
        "Whenever this is dealt damage, put a +1/+1 counter on it."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .permanent (.attach .this (.target 0) false) =>
      if p == .thisEnters && ab.effect.targets == .creatureYouControl then
        leadInSentence ab "When this Equipment enters"
      else
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.surveil .you (.const n)) =>
      if p == .thisEnters then s!"When this permanent enters, surveil {n.toNat}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.connive .this) =>
      if p == .thisEnters then
        leadInSentence ab "When this creature enters"
      else
        match p with
        | .castSpell { relation := .you, pred := .any } (.hasColor (.literal color))
            (some .hand) .. =>
          s!"Whenever you cast a {color} spell from your hand, this connives."
        | _ =>
          let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
          s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .damage (.deal .this (.players (.target 0)) (.const 3) _) =>
      if p == .youCastColor .red then
        "Whenever you cast a red spell, Aragorn deals 3 damage to target opponent."
      else
        let once := if ab.onceEachTurn then " This ability triggers only once each turn." else ""
        s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}.{once}"
    | .moveZone (.inZones (.handOf (.target 0)) .anyObject) .graveyard .discard { choice? := some { count := .exact (.const n), .. }, .. } =>
      if p == .thisEnters then
        let cards := if n == 2 then "two cards" else cardPhrase n.toNat
        s!"When this enchantment enters, target opponent discards {cards}."
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .player (.inspectLibrary { source := .topCards .you (.const _) true, action := .takeMatching (.hasType .creature) (.exact (.const 1)) (.battlefield .controller) _ false true, .. }) =>
      if p == .thisDies then
        leadInSentence ab "When this artifact is put into a graveyard from the battlefield"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .seq #[.permanent (.setTapped _ false _), .turn (.extraPhase .combat true)] =>
      match p with
      | .attacks _ _ _ _ (some n) _ =>
        leadInSentence ab
          s!"Whenever you attack with creatures with total power {n} or greater for the first time each turn"
      | _ => s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | .seq #[.permanent (.attach .this (.target 0) _), .ifCond (.exists .this) _ .noop] =>
      if p == .thisEnters then leadInSentence ab "When this Equipment enters"
      else s!"{eventPrefix ab}{interveningClause ab}, {resolutionPhrase ab.effect}."
    | body =>
      if p == .thisEnters && isEnchantedHostInstr body then
        leadInSentence ab "When this Aura enters"
      else if p == .equippedAttacksAlone &&
          ab.effect.body == .seq #[Instruction.drawFixed 1, Instruction.loseLifeFixed 1] then
        "Whenever equipped creature attacks alone, you draw a card and you lose 1 life."
      else if p == .landYouControlEnters &&
          ab.effect.body == .seq #[Instruction.drawFixed 1, Instruction.putPlusOne .this 1] then
        "Landfall — Whenever a land you control enters, draw a card and put a +1/+1 counter on Gandalf."
      else if p == .permanentEnters (.all #[
            .otherThan .this, .hasSupertype .legendary,
            .hasSubtype (.literal .elf), .controlledBy .you]) &&
          ab.effect.body == .seq #[Instruction.drawFixed 2, Instruction.discardFixed 1] then
        "Whenever another legendary Elf you control enters, draw two cards, then discard a card."
      else
        let once :=
          if ab.onceEachTurn then " This ability triggers only once each turn."
          else if ab.optionalOnceEachTurn then " Do this only once each turn."
          else ""
        let clause0 :=
          match ab.interveningIf?, ab.effect.body with
          | none, .ifCond cond t .noop =>
            let tS := Instruction.toOracleWith { capitalize := false } ab.effect.targets t
            let cS := ToOracle.toOracle { selfRef := "this permanent", capitalize := false } cond
            if !tS.isEmpty && !tS.contains '.' then s!"{tS} if {cS}"
            else (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
          | _, _ => (sequenceClause ab.effect).getD (resolutionPhrase ab.effect)
        let clause :=
          if ab.activeZones == #[.graveyard] && !(clause0.map Char.toLower).contains "graveyard" then
            clause0.replace "return this permanent " "return this card from your graveyard "
          else clause0
        let inter :=
          if (clause.map Char.toLower).startsWith "if " then ""
          else interveningClause ab
        s!"{eventPrefix ab}{inter}, {clause}.{once}"

instance : ToString TriggeredAbility where
  toString := toNotation

instance : ToOracle TriggeredAbility where
  toOracle _ ab := toNotation ab

end TriggeredAbility

end Mtg.Engine
