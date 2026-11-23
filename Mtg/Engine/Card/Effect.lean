import Mtg.Engine.Card.SpellResolution
import Mtg.Engine.Card.Token

/-!
# Unified one-shot `Effect` & `Instruction` helpers (CR 605 / 608)

Smart constructors, CR 605.1a/b structural predicates (`couldAddMana`,
`movesToOrFromLibrary`), pure computed agent classifiers
(`Effect.classifyForAgent`, `Effect.classifyAbilityForAgent`), and canonical
`ToOracle` rendering for `Instruction` and `Effect`.
-/

namespace Mtg.Engine

namespace Instruction

/-! ### Canonical Smart Constructors -/

def ifThen (cond : Condition) (thenBranch : Instruction) : Instruction :=
  .ifCond cond thenBranch .noop

def may (who : PlayerExpr) (cost? : Option CostSpec) (onYes : Instruction) : Instruction :=
  .optional who cost? onYes .noop

def pump (who : ObjectExpr) (p t : ValueExpr) (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who (.modifyPT p t))

def pumpFixed (who : ObjectExpr) (p t : Int) (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  pump who (.const p) (.const t) dur

def grantKeywords (who : ObjectExpr) (ks : Array KeywordAbility)
    (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who (.grantKeywords ks))

def loseKeywords (who : ObjectExpr) (ks : Array KeywordAbility)
    (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who (.loseKeywords ks))

def loseAllAbilities (who : ObjectExpr) (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who .loseAllAbilities)

def setBasePT (who : ObjectExpr) (p t : ValueExpr)
    (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who (.setBasePT (some p) (some t)))

def setBasePTFixed (who : ObjectExpr) (p t : Int)
    (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  setBasePT who (.const p) (.const t) dur

def cantBeBlocked (who : ObjectExpr) (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who (.applyRule (.combat (.cantBeBlocked .self))))

def doublePT (who : ObjectExpr) (dur : DurationExpr := .untilEndOfTurn) : Instruction :=
  .installEffect (.applyContinuous dur who
    (.modifyPT (.objectStat .power who) (.objectStat .toughness who)))

def pumpAndTrample (who : ObjectExpr) (p t : Int) : Instruction :=
  .seq #[pumpFixed who p t, grantKeywords who #[Keyword.trample]]

def destroy (who : ObjectExpr) (mods : MoveMods := {}) : Instruction :=
  .moveZone who .graveyard .destroy mods

def exile (who : ObjectExpr) (mods : MoveMods := {}) : Instruction :=
  .moveZone who .exile .exile mods

def bounce (who : ObjectExpr) (mods : MoveMods := {}) : Instruction :=
  .moveZone who (.hand .owner) .returnToHand mods

def sacrifice (who : ObjectExpr) (mods : MoveMods := {}) : Instruction :=
  .moveZone who .graveyard .sacrifice mods

def putCounters (who : ObjectExpr) (kind : CounterKind) (n : ValueExpr := .const 1) : Instruction :=
  .permanent (.modifyCounters (.put kind n) who)

def putPlusOne (who : ObjectExpr) (n : Nat := 1) : Instruction :=
  putCounters who .plusOnePlusOne (.const (Int.ofNat n))

def tap (who : ObjectExpr) : Instruction :=
  .permanent (.setTapped who true)

def untap (who : ObjectExpr) : Instruction :=
  .permanent (.setTapped who false)

def tapAndStun (who : ObjectExpr) (n : ValueExpr := .const 1) : Instruction :=
  .seq #[tap who, putCounters who .stun n]

def becomePrepared (who : ObjectExpr) : Instruction :=
  .permanent (.setDesignation who .prepared true)

def becomeArtifactIndestructible (who : ObjectExpr) : Instruction :=
  .installEffect (.applyContinuous .untilEndOfTurn who
    (.all #[.modifyTypes { types := #[.artifact] }, .grantKeywords #[Keyword.indestructible]]))

def putOnLibrary (who : ObjectExpr) (pos : LibraryPosSpec) : Instruction :=
  .moveZone who (.library .owner pos) .put {}

def dealDamage (to : RecipientExpr) (amount : ValueExpr)
    (src : ObjectExpr := .this) (flags : DamageFlags := {}) : Instruction :=
  .damage (.deal src to amount flags)

def dealDamageFixed (to : RecipientExpr) (amount : Nat) (src : ObjectExpr := .this) : Instruction :=
  dealDamage to (.const (Int.ofNat amount)) src

def draw (n : ValueExpr := .const 1) (who : PlayerExpr := .you) : Instruction :=
  .player (.drawCards who n)

def drawFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  draw (.const (Int.ofNat n)) who

def discard (n : ValueExpr := .const 1) (who : PlayerExpr := .you)
    (atRandom : Bool := false) : Instruction :=
  .moveZone (.inZones (.handOf who) .anyObject) .graveyard .discard
    { choice? := some { chooser := .player who, count := .exact n, atRandom } }

def discardFixed (n : Nat) (who : PlayerExpr := .you) (atRandom : Bool := false) : Instruction :=
  discard (.const (Int.ofNat n)) who atRandom

def mill (n : ValueExpr := .const 1) (who : PlayerExpr := .you) : Instruction :=
  .moveZone (.topOfLibrary who n) .graveyard .mill {}

def millFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  mill (.const (Int.ofNat n)) who

def scry (n : ValueExpr := .const 1) (who : PlayerExpr := .you) : Instruction :=
  .player (.scry who n)

def scryFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  scry (.const (Int.ofNat n)) who

def surveil (n : ValueExpr := .const 1) (who : PlayerExpr := .you) : Instruction :=
  .player (.surveil who n)

def surveilFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  surveil (.const (Int.ofNat n)) who

def gainLife (n : ValueExpr) (who : PlayerExpr := .you) : Instruction :=
  .life (.gain who n)

def gainLifeFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  gainLife (.const (Int.ofNat n)) who

def loseLife (n : ValueExpr) (who : PlayerExpr := .you) : Instruction :=
  .life (.lose who n)

def loseLifeFixed (n : Nat) (who : PlayerExpr := .you) : Instruction :=
  loseLife (.const (Int.ofNat n)) who

def createTokens (spec : TokenSpec) (n : ValueExpr := .const 1)
    (who : PlayerExpr := .you) (mods : EnterMods := {}) : Instruction :=
  .create (.tokens who n spec mods)

def createTokensFixed (spec : TokenSpec) (n : Nat)
    (who : PlayerExpr := .you) (tapped : Bool := false) : Instruction :=
  createTokens spec (.const (Int.ofNat n)) who { tapped }

def addMana (spec : ManaProductionSpec) (who : PlayerExpr := .you) : Instruction :=
  .player (.addMana who spec)

def addSimpleMana (types : Array ManaType) (who : PlayerExpr := .you) : Instruction :=
  addMana { spec := .sequence (types.map fun t => (t, .const 1)) } who

/-- Canonical compositional Recruit instruction: draw a card, then discard a card;
if the discarded card isn't a land card, create a 1/1 white Human Soldier creature token. -/
def recruit (who : PlayerExpr := .you) : Instruction :=
  .seq #[
    drawFixed 1 who,
    .bind ⟨0⟩ (discardFixed 1 who)
      (ifThen (.exists (.filter (.stepObjects ⟨0⟩) (.not (.hasType .land))))
        (createTokensFixed .humanSoldier 1 who))
  ]

/-- If the object referred to by `ref` would die this turn, exile it instead. -/
def exileIfDiesThisTurn (ref : ObjectRef := .target 0) : Instruction :=
  .installEffect (.applyReplacement .untilEndOfTurn
    (.exileInsteadOfDying { zones := .battlefield, pred := .sameAs ref } none))

/-- Play an additional land this turn (CR 305.2). -/
def extraLand (who : PlayerFilter := .you) (count : Nat := 1) : Instruction :=
  .installEffect (.applyRule .untilEndOfTurn (.player (.additionalLands who count)))

/-- Counter target spell (or stack objects `objs`). -/
def counter (objs : ObjectExpr := .target 0) (exileInstead : Bool := false)
    (ifPermanentMayCastFree : Bool := false) : Instruction :=
  .stack (.counterStack objs exileInstead ifPermanentMayCastFree)

/-- Empower planeswalker of `subtype` by `amount`. -/
def empower (subtype : CardSubtype := .jace) (amount : ValueExpr) : Instruction :=
  .player (.empowerPlaneswalker subtype amount)

/-- Empower Jace `n`. -/
def empowerJace (n : Nat) : Instruction :=
  empower .jace (.const (Int.ofNat n))

/-- Amass `subtype` `amount`. -/
def amass (amount : ValueExpr) (subtype : CardSubtype := .goblin)
    (who : PlayerExpr := .you) : Instruction :=
  .player (.amass who subtype amount)

/-- Amass `subtype` `n`. -/
def amassFixed (n : Nat) (subtype : CardSubtype := .goblin)
    (who : PlayerExpr := .you) : Instruction :=
  amass (.const (Int.ofNat n)) subtype who

/-! ### Structural Predicates (CR 605.1a / 605.1b / Modal / Mana Inspection) -/

/-- Top-level `ManaProductionSpec` when this instruction is a pure mana production. -/
def manaProduction? : Instruction → Option ManaProductionSpec
  | .player (.addMana _ mp) => some mp
  | _ => none

/-- Top-level `ModalSpec` when this instruction is a modal choice. -/
def modalSpec? : Instruction → Option ModalSpec
  | .chooseModes spec => some spec
  | _ => none

/-- True when executing `i` could add mana to a player's mana pool (CR 605.1a / 605.1b). -/
partial def couldAddMana : Instruction → Bool
  | .player (.addMana _ _) => true
  | .seq steps => steps.any couldAddMana
  | .bind _ s c => couldAddMana s || couldAddMana c
  | .ifCond _ t e => couldAddMana t || couldAddMana e
  | .optional _ _ y n _ => couldAddMana y || couldAddMana n
  | .unlessPays _ _ u => couldAddMana u
  | .chooseModes spec => spec.modes.any fun m => couldAddMana m.body
  | .forEach _ _ b => couldAddMana b
  | .queueReflexiveTrigger ab => couldAddMana ab.effect.body
  | _ => false

/-- True when `obj` references cards in a library. -/
private partial def objExprReadsLibrary : ObjectExpr → Bool
  | .topOfLibrary _ _ => true
  | .inZones zs _ => zs.zones.contains .library
  | .extremum _ _ a | .filter a _ => objExprReadsLibrary a
  | .union xs => xs.any objExprReadsLibrary
  | .diff a b => objExprReadsLibrary a || objExprReadsLibrary b
  | _ => false

/-- True when executing `i` includes instructions to move a card to or from a
library, which disqualifies an activated ability from being a mana ability under
the 25 September 2026 update to CR 605.1a. `.scry` reorders cards within a library
without moving cards to or from it and returns `false`. -/
partial def movesToOrFromLibrary : Instruction → Bool
  | .moveZone objs dest _ _ =>
    let toLib := match dest with | .library .. => true | _ => false
    toLib || objExprReadsLibrary objs
  | .player (.drawCards _ (.const 0)) => false
  | .player (.drawCards _ _) => true
  | .player (.surveil _ _) => true
  | .player (.inspectLibrary spec) =>
    match spec.source with
    | .outsideTheGame _ _ => false
    | _ => true
  | .player (.searchLibrary spec) => spec.zones.zones.contains .library
  | .player (.explore _) => true
  | .player (.connive _) => true
  | .seq steps => steps.any movesToOrFromLibrary
  | .bind _ s c => movesToOrFromLibrary s || movesToOrFromLibrary c
  | .ifCond _ t e => movesToOrFromLibrary t || movesToOrFromLibrary e
  | .optional _ _ y n _ => movesToOrFromLibrary y || movesToOrFromLibrary n
  | .unlessPays _ _ u => movesToOrFromLibrary u
  | .chooseModes spec => spec.modes.any fun m => movesToOrFromLibrary m.body
  | .forEach _ _ b => movesToOrFromLibrary b
  | .queueReflexiveTrigger ab => movesToOrFromLibrary ab.effect.body
  | _ => false

/-- True when `i` is a bare no-op (`.noop`, empty `.seq`, or empty `.chooseModes`). -/
partial def doesNothing : Instruction → Bool
  | .noop => true
  | .seq steps => steps.isEmpty || steps.all doesNothing
  | .chooseModes spec => spec.modes.isEmpty
  | _ => false

private def objMentionsTarget (o : ObjectExpr) : Bool :=
  (ValueExpr.count o).mentionsTarget

private def playerMentionsTarget (p : PlayerExpr) : Bool :=
  (ValueExpr.playerMetric .one p).mentionsTarget

/-- True when any branch of `i` directly references a target slot. -/
partial def mentionsTarget : Instruction → Bool
  | .moveZone objs dest _ _ =>
    objMentionsTarget objs ||
      (match dest with
       | .battlefield (.player p) | .hand (.player p) | .library (.player p) _ _ => playerMentionsTarget p
       | _ => false)
  | .damage (.deal _ (.targetSlot _) _ _) | .damage (.deal _ .allTargets _ _) => true
  | .damage (.deal src (.objects o) _ _) => objMentionsTarget src || objMentionsTarget o
  | .damage (.deal src (.players p) _ _) => objMentionsTarget src || playerMentionsTarget p
  | .damage (.deal src (.both o p) _ _) =>
    objMentionsTarget src || objMentionsTarget o || playerMentionsTarget p
  | .damage (.fight a b _) => objMentionsTarget a || objMentionsTarget b
  | .permanent (.setTapped o _ _) | .permanent (.modifyCounters _ o _)
  | .permanent (.transform o) | .permanent (.turnFaceUp o)
  | .permanent (.phaseOut o _) | .permanent (.setDesignation o _ _) => objMentionsTarget o
  | .permanent (.attach a b _) => objMentionsTarget a || objMentionsTarget b
  | .life (.gain w _) | .life (.lose w _) | .life (.set w _) => playerMentionsTarget w
  | .stack (.counterStack o _ _) | .stack (.copyStackObject o _ _)
  | .stack (.chooseNewTargets o _) | .stack (.mayCastOrPlay o _) =>
    objMentionsTarget o
  | .installEffect (.applyContinuous _ aff _) => objMentionsTarget aff
  | .seq steps => steps.any mentionsTarget
  | .bind _ s c => mentionsTarget s || mentionsTarget c
  | .ifCond c t e => c.mentionsTarget || mentionsTarget t || mentionsTarget e
  | .optional w _ y n _ => playerMentionsTarget w || mentionsTarget y || mentionsTarget n
  | .unlessPays p _ u => playerMentionsTarget p || mentionsTarget u
  | .chooseModes spec => spec.modes.any fun m => !m.targeting.spec.isEmpty || mentionsTarget m.body
  | .forEach _ _ b => mentionsTarget b
  | _ => false

/-! ### Canonical `ToOracle` Rendering -/

private def printObjRef (ctx : PrintCtx) (noun : String) : ObjectExpr → String
  | .this => ctx.selfRef
  | .target 0 => if noun.isEmpty then "target permanent" else noun
  | .target _ => "that permanent"
  | .allTargets => if noun.isEmpty then "those targets" else noun
  | .attachedHost => "enchanted creature"
  | .triggerSubject => "that permanent"
  | .targetsOf s => s!"objects targeted by {printObjRef ctx noun s}"
  | .stepObjects _ => "those cards"
  | .linkedExile _ => s!"a card exiled with {ctx.selfRef}"
  | .costPaidObjects => "those exiled cards"
  | o => toOracleStr o { ctx with capitalize := false }

private def printVal (ctx : PrintCtx) : ValueExpr → String
  | .const n => toString n
  | .chosenX => "X"
  | v => toOracleStr v { ctx with capitalize := false }

private def printCountInt (v : ValueExpr) : Option Nat :=
  match v with
  | .const n => if n >= 0 then some n.toNat else none
  | _ => none

/-- Canonical Oracle rendering of an `Instruction` (used by `ToOracle Instruction`
and as fallback when `Effect.phrase` is empty). -/
partial def toOracle (ctx : PrintCtx) (noun : String := "") : Instruction → String
  | .noop => ""
  | .seq steps =>
    let parts := (steps.toList.map (toOracle { ctx with capitalize := false } noun)).filter (· != "")
    let joined := String.intercalate ". " parts
    if ctx.capitalize then capitalizeAscii joined else joined
  | .bind _ step cont =>
    let a := toOracle { ctx with capitalize := false } noun step
    let b := toOracle { ctx with capitalize := false } noun cont
    let joined := if a.isEmpty then b else if b.isEmpty then a else s!"{a}. {capitalizeAscii b}"
    if ctx.capitalize then capitalizeAscii joined else joined
  | .ifCond cond t e =>
    let condS := toOracleStr cond { ctx with capitalize := false }
    let tS := toOracle { ctx with capitalize := false } noun t
    let base :=
      match e with
      | .noop => s!"if {condS}, {tS}"
      | _ =>
        let eS := toOracle { ctx with capitalize := false } noun e
        s!"if {condS}, {tS}. Otherwise, {eS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .optional who cost? onYes onNo maxTimes =>
    let whoS := match who with | .you => "you" | p => toOracleStr p { ctx with capitalize := false }
    let yesS := toOracle { ctx with capitalize := false } noun onYes
    let timesS := if maxTimes > 1 then s!" up to {englishNumber maxTimes} times" else ""
    let base :=
      match cost? with
      | some cs =>
        let baseYes := s!"{whoS} may pay {cs.toNotation}{timesS}. If {whoS} do, {yesS}"
        match onNo with
        | .noop => baseYes
        | _ => s!"{baseYes}. Otherwise, {toOracle { ctx with capitalize := false } noun onNo}"
      | none =>
        let baseYes := s!"{whoS} may {yesS}"
        match onNo with
        | .noop => baseYes
        | _ => s!"{baseYes}. Otherwise, {toOracle { ctx with capitalize := false } noun onNo}"
    if ctx.capitalize then capitalizeAscii base else base
  | .unlessPays payer cost ifUnpaid =>
    let payerS := match payer with
      | .controllerOf _ => "its controller"
      | .you => "you"
      | p => toOracleStr p { ctx with capitalize := false }
    let uS := toOracle { ctx with capitalize := false } noun ifUnpaid
    let base := s!"{uS} unless {payerS} pays {cost.toNotation}"
    if ctx.capitalize then capitalizeAscii base else base
  | .chooseModes spec =>
    let header :=
      match spec.minModes, spec.maxModes with
      | .const 1, .const 1 => "Choose one —"
      | .const 1, .const 2 => "Choose one or both —"
      | .const 2, .const 2 => "Choose two —"
      | _, _ => "Choose —"
    let modeLines := spec.modes.toList.map fun m =>
      let txt := if !m.phrase.isEmpty then m.phrase else toOracle {} m.targeting.spec.noun m.body
      s!"• {capitalizeAscii txt}"
    String.intercalate "\n" (header :: modeLines)
  | .forEach iter _ body =>
    let pref :=
      match iter with
      | .eachPlayer pf => s!"for each {toOracleStr pf { ctx with capitalize := false }}"
      | .eachObject o => s!"for each {toOracleStr o { ctx with capitalize := false }}"
      | .eachTargetSlot => "for each target"
      | .repeatTimes c => s!"repeat {printVal ctx c} times:"
    let base := s!"{pref}, {toOracle { ctx with capitalize := false } noun body}"
    if ctx.capitalize then capitalizeAscii base else base
  | .moveZone objs dest verb mods =>
    let subj := printObjRef ctx noun objs
    let base :=
      match verb, dest with
      | .destroy, .graveyard => s!"destroy {subj}"
      | .exile, .exile =>
        if mods.exileUntilSourceLeaves then s!"exile {subj} until {ctx.selfRef} leaves the battlefield"
        else s!"exile {subj}"
      | .returnToHand, .hand .owner => s!"return {subj} to its owner's hand"
      | .returnToHand, .hand .controller => s!"return {subj} to your hand"
      | .returnToHand, .hand _ => s!"return {subj} to its owner's hand"
      | .sacrifice, .graveyard => s!"sacrifice {subj}"
      | .discard, .graveyard =>
        match mods.choice? with
        | some ch =>
          match ch.count with
          | .exact v =>
            match printCountInt v with
            | some n => s!"discard {cardPhrase n}"
            | none => s!"discard {printVal ctx v} cards"
          | _ => "discard a card"
        | none => "discard your hand"
      | .mill, .graveyard =>
        match objs with
        | .topOfLibrary _ v =>
          match printCountInt v with
          | some n => s!"mill {cardPhrase n}"
          | none => s!"mill {printVal ctx v} cards"
        | _ => "mill a card"
      | .put, .battlefield _ =>
        let tapS := if mods.tapped then " tapped" else ""
        s!"return {subj} to the battlefield{tapS}"
      | .put, .library _ .top false => s!"{subj}'s owner puts it on top of their library"
      | .put, .library _ .bottom false => s!"{subj}'s owner puts it on the bottom of their library"
      | .put, .library _ .bottomRandom false =>
        s!"put {subj} on the bottom of its owner's library in a random order"
      | .put, .library _ _ true => s!"{subj}'s owner puts it on their choice of the top or bottom of their library"
      | .shuffleIntoLibrary, _ => s!"shuffle {subj} into its owner's library"
      | _, _ => s!"move {subj}"
    if ctx.capitalize then capitalizeAscii base else base
  | .create (.tokens who count spec mods) =>
    let n? := printCountInt count
    let phrase :=
      match n? with
      | some n => spec.createPhrase n mods.tapped
      | none =>
        let tapS := if mods.tapped then "tapped " else ""
        s!"create {printVal ctx count} {tapS}{spec.pluralNoun}"
    let base :=
      match who with
      | .you => phrase
      | p => s!"{toOracleStr p { ctx with capitalize := false }} creates {phrase.drop 7}"
    if ctx.capitalize then capitalizeAscii base else base
  | .create (.emblem _ _) =>
    let base := "you get an emblem"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.setTapped objs true _) =>
    let base := s!"tap {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.setTapped objs false _) =>
    let base := s!"untap {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.modifyCounters (.put k v) objs _) =>
    let subj := printObjRef ctx noun objs
    let cntS :=
      match printCountInt v with
      | some n => k.countersPhrase n
      | none => s!"{printVal ctx v} {k.oracleName} counters"
    let base := s!"put {cntS} on {subj}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.modifyCounters (.remove k? c) objs _) =>
    let subj := printObjRef ctx noun objs
    let kindS := match k? with | some k => s!"{k.oracleName} " | none => ""
    let cntS := match c with
      | .upTo v => s!"up to {printVal ctx v}"
      | .exact v => printVal ctx v
      | _ => "a"
    let base := s!"remove {cntS} {kindS}counter(s) from {subj}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.modifyCounters _ objs _) =>
    let base := s!"modify counters on {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.attach a b _) =>
    let base := s!"attach {printObjRef ctx noun a} to {printObjRef ctx noun b}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.transform objs) =>
    let base := s!"transform {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.turnFaceUp objs) =>
    let base := s!"turn {printObjRef ctx noun objs} face up"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.phaseOut objs _) =>
    let base := s!"{printObjRef ctx noun objs} phases out"
    if ctx.capitalize then capitalizeAscii base else base
  | .permanent (.setDesignation objs tag _) =>
    let subj := printObjRef ctx noun objs
    let base :=
      match tag with
      | .prepared => s!"{subj} becomes prepared"
      | .harnessed => s!"harness {subj}"
      | .goaded => s!"goad {subj}"
      | .ringBearer => s!"{subj} becomes your Ring-bearer"
    if ctx.capitalize then capitalizeAscii base else base
  | .damage (.deal src to amt _) =>
    let toS :=
      match to with
      | .targetSlot 0 => if noun.isEmpty then "any target" else noun
      | .targetSlot _ => "that target"
      | .objects o => printObjRef ctx noun o
      | .players p => toOracleStr p { ctx with capitalize := false }
      | .both o p =>
        s!"{printObjRef ctx noun o} and {toOracleStr p { ctx with capitalize := false }}"
      | .allTargets => if noun.isEmpty then "those targets" else noun
    let srcS := printObjRef ctx noun src
    let base := s!"{srcS} deals {printVal ctx amt} damage to {toS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .damage (.fight a b oneWay) =>
    let aS := printObjRef ctx noun a
    let bS := printObjRef ctx noun b
    let base :=
      if oneWay then s!"{aS} deals damage equal to its power to {bS}"
      else s!"{aS} fights {bS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .life (.gain who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"you gain {amtS} life"
      | p => s!"{toOracleStr p { ctx with capitalize := false }} gains {amtS} life"
    if ctx.capitalize then capitalizeAscii base else base
  | .life (.lose who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"you lose {amtS} life"
      | p => s!"{toOracleStr p { ctx with capitalize := false }} loses {amtS} life"
    if ctx.capitalize then capitalizeAscii base else base
  | .life (.set who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"your life total becomes {amtS}"
      | p => s!"{toOracleStr p { ctx with capitalize := false }}'s life total becomes {amtS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.drawCards who amt) =>
    let cardsS := match printCountInt amt with
      | some n => cardPhrase n
      | none => s!"{printVal ctx amt} cards"
    let base :=
      match who with
      | .you => s!"draw {cardsS}"
      | p => s!"{toOracleStr p { ctx with capitalize := false }} draws {cardsS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.scry _ amt) =>
    let base := s!"scry {printVal ctx amt}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.surveil _ amt) =>
    let base := s!"surveil {printVal ctx amt}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.inspectLibrary _) =>
    let base := "look at the top cards of your library"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.searchLibrary _) =>
    let base := "search your library, then shuffle"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.reveal _ objs _) =>
    let base := s!"reveal {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.shuffle _) =>
    let base := "shuffle"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.addMana _ mp) =>
    mp.toOracleSentence ctx
  | .player (.proliferate _ (.const 1) none) =>
    let base := "proliferate"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.proliferate _ amt _) =>
    let base := s!"proliferate {printVal ctx amt} times"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.temptWithRing _) =>
    let base := "the Ring tempts you"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.explore objs) =>
    let base := s!"{printObjRef ctx noun objs} explores"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.amass _ sub amt) =>
    let base := s!"amass {pluralizeName sub.englishName} {printVal ctx amt}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.connive objs) =>
    let base := s!"{printObjRef ctx noun objs} connives"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.empowerPlaneswalker sub amt) =>
    let base := s!"empower {sub.englishName} {printVal ctx amt}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.setStatus _ .monarch _) =>
    let base := "you become the monarch"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.setStatus _ .winGame _) =>
    let base := "you win the game"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.setStatus _ (.designation .citysBlessing) _) =>
    let base := "you get the city's blessing for the rest of the game"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.setStatus _ (.designation .enduringStory) _) =>
    let base := "you get enduring story for the rest of the game"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.choose _ .creatureType) =>
    let base := "choose a creature type"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.choose _ .oddOrEven) =>
    let base := "choose odd or even"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.choose _ (.keyword ks)) =>
    let base := s!"choose {String.intercalate " or " (KeywordAbility.toOracleList ks)}"
    if ctx.capitalize then capitalizeAscii base else base
  | .player (.choose _ .playerWithMostLife) =>
    let base := "choose a player with the most life or tied for most life"
    if ctx.capitalize then capitalizeAscii base else base
  | .turn (.extraTurn _ _) =>
    let base := "take an extra turn after this one"
    if ctx.capitalize then capitalizeAscii base else base
  | .turn (.extraPhase .combat _) =>
    let base := "there is an additional combat phase after this phase"
    if ctx.capitalize then capitalizeAscii base else base
  | .turn _ =>
    let base := "take an additional phase or step"
    if ctx.capitalize then capitalizeAscii base else base
  | .stack (.counterStack objs _ _) =>
    let base := s!"counter {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .stack (.copyStackObject objs _ _) =>
    let base := s!"copy {printObjRef ctx noun objs}. You may choose new targets for the copy"
    if ctx.capitalize then capitalizeAscii base else base
  | .stack (.chooseNewTargets objs _) =>
    let base := s!"choose new targets for {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .stack (.mayCastOrPlay objs _) =>
    let base := s!"you may play {printObjRef ctx noun objs}"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.applyContinuous dur aff mod) =>
    let subj := printObjRef ctx noun aff
    let durS := toOracleStr dur { ctx with capitalize := false }
    let base :=
      match mod with
      | .modifyPT (.const p) (.const t) =>
        s!"{subj} gets {signedStat p}/{signedStat t} {durS}"
      | .grantKeywords ks =>
        s!"{subj} gains {KeywordAbility.joinedAnd ks} {durS}"
      | .loseKeywords ks =>
        s!"{subj} loses {KeywordAbility.joinedAnd ks} {durS}"
      | .loseAllAbilities =>
        s!"{subj} loses all abilities {durS}"
      | .setBasePT (some (.const p)) (some (.const t)) =>
        s!"{subj} has base power and toughness {p}/{t} {durS}"
      | .gainControl _ =>
        s!"gain control of {subj} {durS}"
      | .exchangeControl _ =>
        s!"exchange control of {subj}"
      | .applyRule (.combat (.cantBeBlocked _)) =>
        s!"{subj} can't be blocked this turn"
      | _ => s!"{subj} is modified {durS}"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.applyRule _ (.player (.additionalLands _ 1))) =>
    let base := "you may play an additional land this turn"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.applyRule _ _) =>
    let base := "apply a rule modification"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.applyReplacement _ (.exileInsteadOfDying _ _)) =>
    let base := "if that creature would die this turn, exile it instead"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.applyReplacement _ _) =>
    let base := "apply a replacement effect"
    if ctx.capitalize then capitalizeAscii base else base
  | .installEffect (.createDelayedTrigger _) =>
    let base := "create a delayed triggered ability"
    if ctx.capitalize then capitalizeAscii base else base
  | .queueReflexiveTrigger ab =>
    let base := s!"when you do, {ab.effect.phrase}"
    if ctx.capitalize then capitalizeAscii base else base

instance : ToOracle Instruction where
  toOracle ctx i := Instruction.toOracle ctx "" i

end Instruction

/-! ### Unified `Effect` Operations & Pure Agent Classification -/

namespace Effect

/-- Whom this effect may target (CR 115.1 / 601.2c). -/
def targetSpec (e : Effect) : TargetSpec :=
  e.targeting.spec

/-- Effective targeting specification incorporating `allowsZeroTargets` /
`maxTargets` bounds for single-slot effects (CR 115.1c / 601.2c). -/
def effectiveTargetSpec (e : Effect) : TargetSpec :=
  e.targeting.spec.withSlotBounds e.allowsZeroTargets e.maxTargets

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (e : Effect) : Nat :=
  e.targeting.targetCount

/-- True when announcing this effect requires choosing a target. -/
def requiresTarget (e : Effect) : Bool :=
  e.targeting.requiresTarget

/-- Upper bound on announced targets. `0` on `maxTargets` means `targetCount`. -/
def maxTargetCount (e : Effect) : Nat :=
  if e.maxTargets == 0 then e.targetCount else e.maxTargets

/-- Top-level `ManaProductionSpec` carried in `e.body`, if any. -/
def manaProduction? (e : Effect) : Option ManaProductionSpec :=
  e.body.manaProduction?

/-- Top-level `ModalSpec` carried in `e.body`, if any. -/
def modalSpec? (e : Effect) : Option ModalSpec :=
  e.body.modalSpec?

/-- True when resolving `e` could add mana to a player's mana pool (CR 605.1a/b). -/
def couldAddMana (e : Effect) : Bool :=
  e.body.couldAddMana

/-- True when resolving `e` moves a card to or from a library (CR 605.1a, 25 Sep 2026). -/
def movesToOrFromLibrary (e : Effect) : Bool :=
  e.body.movesToOrFromLibrary

/-- True when resolving `e` as a spell would do nothing. -/
def doesNothingAsSpell (e : Effect) : Bool :=
  e.body.doesNothing

/-- True when resolving `e` as an activated ability would do nothing. -/
def doesNothingAsActivated (e : Effect) : Bool :=
  e.body.doesNothing

/-- True when resolving `e` as a triggered ability would do nothing. -/
def doesNothingAsTrigger (e : Effect) : Bool :=
  e.body.doesNothing

/-- Helper: true when `TargetSpec`'s primary target requires flying. -/
private def targetsFlyingCreature (spec : TargetSpec) : Bool :=
  spec == .creatureWithFlying ||
    match spec.slots.toList with
    | slot :: _ =>
      match slot.domain with
      | .object _ (.all ps) => ps.contains (.hasKeyword .flying)
      | _ => false
    | [] => false

/-- Helper: true when `TargetSpec` primarily targets artifacts, enchantments, or lands
(not creatures). -/
private def targetsArtifactOrLand (spec : TargetSpec) : Bool :=
  spec == .artifact || spec == .artifactOrLand || spec == .artifactOrEnchantment ||
    spec == .artifactToken || spec == .noncreatureArtifact ||
    spec == .noncreatureArtifactOrEnchantment || spec == .colorlessNonland ||
    spec == .nonland ||
    match spec.slots.toList with
    | slot :: _ =>
      match slot.domain with
      | .object _ (.hasType .artifact) => true
      | .object _ (.hasType .land) => true
      | .object _ (.hasType .enchantment) => true
      | .object _ (.all ps) =>
        (ps.contains (.hasType .artifact) || ps.contains (.hasType .enchantment) ||
         ps.contains (.hasType .land)) && !ps.contains (.hasType .creature)
      | _ => false
    | [] => false

/-- Helper: true when `TargetSpec` targets a player or any target (including players). -/
private def targetsPlayerOrAny (spec : TargetSpec) : Bool :=
  spec == .anyTarget || spec == .opponent || spec == .player ||
    match spec.slots.toList with
    | slot :: _ =>
      match slot.domain with
      | .anyTarget _ | .player _ => true
      | _ => false
    | [] => false

/-- Pure structural classification of a spell `Effect` for the demonstration agent. -/
partial def classifyForAgent (e : Effect) : SpellCastKind :=
  classifyInstr e.targeting.spec e.body
where
  classifyInstr (spec : TargetSpec) : Instruction → SpellCastKind
    | .chooseModes m =>
      match m.modes[0]? with
      | some first => classifyForAgent first
      | none => .extraLand
    | .seq steps =>
      -- Inspect flat steps in priority order so counter/fight/destroy/damage/pump/draw
      -- classify accurately even when followed by scry/surveil/gainLife/exile-if-dies.
      let flat := steps.foldl (fun acc s => acc ++ s.flatten) #[]
      if flat.any (fun | .stack (.counterStack ..) | .unlessPays _ _ (.stack (.counterStack ..)) => true | _ => false) then
        .counter
      else if flat.any (fun | .damage (.fight ..) => true | _ => false) then
        .fight
      else if flat.any (fun | .damage (.deal (.target 0) (.targetSlot 1) ..) => true | _ => false) then
        .fight
      else
        match flat[0]? with
        | some s0 =>
          let k0 := classifyInstr spec s0
          if k0 != .extraLand then k0
          else
            match flat[1]? with
            | some s1 => classifyInstr spec s1
            | none => .extraLand
        | none => .extraLand
    | .bind _ step cont =>
      let ks := classifyInstr spec step
      if ks != .extraLand then ks else classifyInstr spec cont
    | .ifCond _ t f =>
      let kt := classifyInstr spec t
      if kt != .extraLand then kt else classifyInstr spec f
    | .optional _ _ y n _ =>
      let ky := classifyInstr spec y
      if ky != .extraLand then ky else classifyInstr spec n
    | .unlessPays _ _ u => classifyInstr spec u
    | .stack (.counterStack ..) => .counter
    | .stack (.copyStackObject ..) => .creatureDamage
    | .damage (.fight ..) => .fight
    | .damage (.deal (.target 0) (.targetSlot 1) ..) => .fight
    | .damage (.deal _ to _ _) =>
      match to with
      | .targetSlot _ =>
        if targetsFlyingCreature spec then .destroyFlying
        else if targetsPlayerOrAny spec then .burn
        else .creatureDamage
      | .players _ => .burn
      | .objects _ | .both _ _ | .allTargets => .creatureDamage
    | .life (.lose (.matching .opponent _) _) => .burn
    | .moveZone objs dest verb _ =>
      match verb, dest with
      | .destroy, .graveyard =>
        if targetsFlyingCreature spec then .destroyFlying
        else if targetsArtifactOrLand spec then .destroyArtifactOrLand
        else .destroyCreature
      | .exile, .exile =>
        match objs with
        | .topOfLibrary _ _ | .inZones { zones := #[.hand], .. } _
        | .inZones { zones := #[.graveyard], .. } _ => .draw
        | _ =>
          if targetsArtifactOrLand spec then .destroyArtifactOrLand
          else .destroyCreature
      | .returnToHand, .hand .owner =>
        match objs with
        | .target _ | .allTargets =>
          let targetsCreature :=
            spec == .creature || spec == .oppCreature ||
              (match spec.slots.toList with
               | slot :: _ =>
                 match slot.domain with
                 | .object .battlefield (.all ps) => ps.contains (.hasType .creature)
                 | _ => false
               | [] => false)
          if targetsCreature then .destroyCreature else .counter
        | _ => .counter
      | .returnToHand, .hand .controller => .draw
      | .put, .battlefield _ => .draw
      | .put, .library _ _ _ => .counter
      | .sacrifice, .graveyard => .destroyCreature
      | .mill, .graveyard => .draw
      | _, _ => .extraLand
    | .installEffect (.applyContinuous _ aff mod) =>
      match mod with
      | .modifyPT _ _ =>
        match aff with
        | .inZones _ _ => .massPump
        | _ => .pump
      | .setBasePT _ _ =>
        if spec == .creature then .creatureDamage else .pump
      | .grantKeywords _ | .loseKeywords _ | .all _ => .pump
      | .gainControl _ => if spec == .creature then .pump else .counter
      | .exchangeControl _ => .counter
      | .applyRule (.combat (.cantBeBlocked _)) => .pump
      | _ => .extraLand
    | .installEffect (.applyRule _ (.player (.additionalLands _ _))) => .extraLand
    | .installEffect (.applyReplacement _ (.exileInsteadOfDying _ _)) => .creatureDamage
    | .permanent (.modifyCounters (.put .plusOnePlusOne _) _ _) => .pump
    | .permanent (.setTapped _ true _) => .pump
    | .permanent (.phaseOut _ _) => .counter
    | .player (.drawCards _ _) | .player (.scry _ _) | .player (.surveil _ _)
    | .player (.inspectLibrary _) | .player (.searchLibrary _)
    | .player (.addMana _ _) => .draw
    | .player (.amass _ _ _) => .pump
    | .player (.choose _ .creatureType) => .destroyCreature
    | _ => .extraLand

/-- Pure structural classification of an activated-ability mode for the demonstration
agent (`SpellTargets.defaultAbilityMode`). -/
partial def classifyAbilityForAgent (e : Effect) : AbilityCastKind :=
  classifyInstr e.targeting.spec e.body
where
  classifyInstr (spec : TargetSpec) : Instruction → AbilityCastKind
    | .damage (.deal _ _ _ _) => .creatureDamage
    | .moveZone (.target 0) .graveyard .destroy _ =>
      if spec == .colorlessNonland || spec == .artifactOrEnchantment ||
          spec == .permanent || spec == .noncreatureArtifactOrEnchantment then
        .destroyColorless
      else .other
    | .seq steps =>
      match steps[0]? with
      | some s0 => classifyInstr spec s0
      | none => .other
    | _ => .other

/-- Demonstration-agent category for a spell mode (computed purely). -/
def castKind (e : Effect) : SpellCastKind :=
  e.classifyForAgent

/-- Demonstration-agent category for an activated-ability mode (computed purely). -/
def abilityKind (e : Effect) : AbilityCastKind :=
  e.classifyAbilityForAgent

/-- Oracle-style text for this effect. Uses transitional `phrase` when present,
otherwise renders `body` canonically through `ToOracle Instruction`. -/
def toNotation (e : Effect) : String :=
  if !e.phrase.isEmpty then e.phrase
  else Instruction.toOracle {} e.targeting.spec.noun e.body

instance : HasTargeting Effect where
  targeting e := e.targeting

instance : ToString Effect where
  toString := toNotation

end Effect

end Mtg.Engine
