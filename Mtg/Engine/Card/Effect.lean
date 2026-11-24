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
  .installEffect (.applyContinuous .untilEndOfTurn who
    (.all #[.modifyPT (.const p) (.const t), .grantKeywords #[Keyword.trample]]))

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
  | .chooseModes spec => spec.modes.any fun m => !m.targets.isEmpty || mentionsTarget m.body
  | .forEach _ _ b => mentionsTarget b
  | _ => false

/-! ### Canonical `ToOracle` Rendering -/

private def applyCap (ctx : PrintCtx) (s : String) : String :=
  if ctx.capitalize then capitalizeAscii s else s

private def printCountInt (v : ValueExpr) : Option Nat :=
  match v with
  | .const n => if n >= 0 then some n.toNat else none
  | _ => none

private def printVal (ctx : PrintCtx) : ValueExpr → String
  | .const n => toString n
  | .chosenX => "X"
  | .eventAmount => "that much"
  | v => toOracleStr v { ctx with capitalize := false }

private def printSlotRef (targets : TargetSpec) (i : Nat) (fallback : String) : String :=
  let s0 := targets.announcedSlotNoun i
  let s :=
    if !s0.isEmpty && i == 1 &&
        targets.crossSlotConstraints.any (fun c => c.relation == .distinct && c.slots == #[0, 1]) &&
        !(s0.map Char.toLower).startsWith "a second " then
      s!"a second {s0}"
    else s0
  if !s.isEmpty then s else fallback

private partial def printObjRef (ctx : PrintCtx) (targets : TargetSpec) (o : ObjectExpr)
    (anaphor0 : Array Nat := #[]) : String :=
  match o with
  | .this => ctx.selfRef
  | .target i =>
    if anaphor0.contains i then "it"
    else printSlotRef targets i (if i == 0 then "target permanent" else s!"target {i + 1}")
  | .allTargets =>
    if anaphor0.contains 0 then "them"
    else if !targets.isEmpty then targets.noun else "those targets"
  | .attachedHost => "enchanted creature"
  | .triggerSubject => "that permanent"
  | .targetsOf s => s!"objects targeted by {printObjRef ctx targets s anaphor0}"
  | .stepObjects v => if v.idx == 0 then "those cards" else s!"the objects from step {v.idx}"
  | .linkedExile src => s!"a card exiled with {printObjRef ctx targets src anaphor0}"
  | .costPaidObjects => "those exiled cards"
  | .topOfLibrary who n =>
    let whoS :=
      match who with
      | .you => "your"
      | .target i =>
        let pS := if anaphor0.contains i then "that player" else printSlotRef targets i "target player"
        s!"{pS}'s"
      | _ => s!"{toOracleStr who { ctx with capitalize := false }}'s"
    match printCountInt n with
    | some 1 => s!"the top card of {whoS} library"
    | some k => s!"the top {k} cards of {whoS} library"
    | none => s!"the top {printVal ctx n} cards of {whoS} library"
  | .filter objs pred =>
    let base := printObjRef ctx targets objs anaphor0
    let pStr := toOracleStr pred { ctx with capitalize := false }
    s!"{base} matching {pStr}"
  | .extremum dir metric among =>
    let dStr := match dir with | .max => "greatest" | .min => "least"
    let mStr := metric.oracleWord
    s!"the {dStr} {mStr} among {printObjRef ctx targets among anaphor0}"
  | .union xs =>
    String.intercalate " and " (xs.toList.map fun x => printObjRef ctx targets x anaphor0)
  | .diff a b =>
    s!"{printObjRef ctx targets a anaphor0} other than {printObjRef ctx targets b anaphor0}"
  | o => toOracleStr o { ctx with capitalize := false }

private def printEachObj (ctx : PrintCtx) (targets : TargetSpec) (o : ObjectExpr)
    (anaphor0 : Array Nat := #[]) : String :=
  match o with
  | .inZones zs pred =>
    let s := toOracleStr (ObjectExpr.inZones zs pred) { ctx with plural := false, capitalize := false }
    let s := if s.startsWith "another " then "other " ++ (s.drop 8).copy else s
    s!"each {s}"
  | .allTargets =>
    if anaphor0.contains 0 then "each of them"
    else if targets.slots.size == 1 && targets.slots[0]!.count != .exact 1 then
      s!"each of {targets.noun}"
    else printObjRef ctx targets .allTargets anaphor0
  | o => printObjRef ctx targets o anaphor0

private def printPlayerRef (ctx : PrintCtx) (targets : TargetSpec) (p : PlayerExpr)
    (anaphor0 : Array Nat := #[]) : String :=
  match p with
  | .you => "you"
  | .activePlayer => "the active player"
  | .defendingPlayer => "defending player"
  | .monarch => "the monarch"
  | .target i => if anaphor0.contains i then "that player" else printSlotRef targets i "target player"
  | .controllerOf (.target 0) => "its controller"
  | .controllerOf .triggerSubject => "its controller"
  | .controllerOf obj => s!"{printObjRef ctx targets obj anaphor0}'s controller"
  | .ownerOf (.target 0) => "its owner"
  | .ownerOf .triggerSubject => "its owner"
  | .ownerOf obj => s!"{printObjRef ctx targets obj anaphor0}'s owner"
  | .triggerPlayer .giftOpponent => "the opponent who was promised a gift"
  | .triggerPlayer .controllerOfSubject => "its controller"
  | .triggerPlayer .ownerOfSubject => "its owner"
  | .triggerPlayer _ => "that player"
  | .stepPlayers v => if v.idx == 0 then "that player" else s!"the player from step {v.idx}"
  | .matching .opponent .any => "each opponent"
  | .matching .anyPlayer .any => "each player"
  | p => toOracleStr p { ctx with capitalize := false }

private def printPossessivePlayer (ctx : PrintCtx) (targets : TargetSpec) (p : PlayerExpr)
    (anaphor0 : Array Nat := #[]) : String :=
  match p with
  | .you => "your"
  | p => s!"{printPlayerRef ctx targets p anaphor0}'s"

private def printObjectMetric : ObjectMetric → String
  | .one => "count"
  | .stat s => s.oracleWord
  | .counterCount none => "counters"
  | .counterCount (some k) => s!"{k.oracleName} counters"
  | .colorCount => "colors"

private def printExprCount (ctx : PrintCtx) : ExprCountRange → String
  | .exact v =>
    match printCountInt v with
    | some 1 => "a"
    | some n => englishNumber n
    | none => printVal ctx v
  | .upTo v =>
    match printCountInt v with
    | some n => s!"up to {englishNumber n}"
    | none => s!"up to {printVal ctx v}"
  | .between lo hi =>
    s!"{printVal ctx lo} to {printVal ctx hi}"
  | .anyNumber => "any number of"

private def printDestOwner (ctx : PrintCtx) (targets : TargetSpec) : DestOwnerSpec → String
  | .controller => "your"
  | .owner => "its owner's"
  | .player w => printPossessivePlayer ctx targets w

private def printDestZone (ctx : PrintCtx) (targets : TargetSpec) (dest : DestZoneSpec)
    (anaphor0 : Array Nat := #[]) : String :=
  match dest with
  | .battlefield .controller => "onto the battlefield under your control"
  | .battlefield .owner => "onto the battlefield under its owner's control"
  | .battlefield (.player w) => s!"onto the battlefield under {printPossessivePlayer ctx targets w anaphor0} control"
  | .graveyard => "into its owner's graveyard"
  | .hand .controller => "into your hand"
  | .hand .owner => "into its owner's hand"
  | .hand (.player w) => s!"into {printPossessivePlayer ctx targets w anaphor0} hand"
  | .exile => "into exile"
  | .library whose pos opt =>
    let ownerP := printDestOwner ctx targets whose
    if opt then
      match pos with
      | .fromTop (.const 1) => s!"second from the top or on the bottom of {ownerP} library"
      | .fromTop (.const 2) => s!"third from the top or on the bottom of {ownerP} library"
      | _ => s!"on {ownerP} choice of the top or bottom of {ownerP} library"
    else
      match pos with
      | .top => s!"on top of {ownerP} library"
      | .bottom => s!"on the bottom of {ownerP} library"
      | .bottomRandom => s!"on the bottom of {ownerP} library in a random order"
      | .fromTop v => s!"{printVal ctx v} from the top of {ownerP} library"
      | .shuffledIn => s!"into {ownerP} library, then shuffle"

private def printGrantPlayPerm (ctx : PrintCtx) (objStr : String)
    (perm : GrantPlayPermSpec) : String :=
  let durS := toOracleStr perm.duration { ctx with capitalize := false }
  let verb := if perm.landsAllowed then "play" else "cast"
  let noun :=
    match perm.filter? with
    | some p => s!"{toOracleStr p { ctx with capitalize := false }} {if perm.landsAllowed then "cards" else "spells"} from among {objStr}"
    | none => objStr
  let countS :=
    match perm.maxCasts? with
    | some n => s!"up to {englishNumber n} of "
    | none => ""
  let mvS :=
    match perm.maxTotalManaValue? with
    | some v => s!" with total mana value {printVal ctx v} or less"
    | none => ""
  let payS :=
    if perm.freeCast then " without paying their mana costs"
    else if perm.payLifeInsteadOfMana then " by paying life equal to their mana value rather than paying their mana cost"
    else if perm.anyManaColor then ", and mana of any type can be spent to cast them"
    else ""
  let fbS := if perm.asFlashback then " (with flashback)" else ""
  let copyPfx := if perm.copyAndCast then s!"copy {objStr}. " else ""
  let nowS := if perm.castNow then " now" else s!" {durS}"
  let exS := if perm.exileOnResolveInstead then ". If a spell cast this way would be put into a graveyard, exile it instead" else ""
  let condS :=
    match perm.condition? with
    | some c => s!" if {toOracleStr c { ctx with capitalize := false }}"
    | none => ""
  s!"{copyPfx}you may {verb} {countS}{noun}{mvS}{nowS}{payS}{fbS}{condS}{exS}"

private def printTypeSetMod (m : TypeSetMod) : String :=
  let sups := m.supertypes.toList.map Supertype.englishName
  let subs := m.subtypes.toList.map CardSubtype.englishName
  let tys := m.types.toList.map CardType.oracleWord
  let words := String.intercalate " " (sups ++ subs ++ tys)
  match m.mode with
  | .add | .addDedup => s!"{words} in addition to its other types"
  | .set => words
  | .setAndKeepNoncreatureSubtypes => s!"{words} (loses other creature types)"

private def printMoveSuffix (ctx : PrintCtx) (targets : TargetSpec) (mods : MoveMods) : String := Id.run do
  let mut parts : List String := []
  if mods.tapped then parts := parts ++ ["tapped"]
  if mods.attacking then parts := parts ++ ["and attacking"]
  if mods.goaded then parts := parts ++ ["goaded"]
  if mods.enterFaceDown then parts := parts ++ ["face down"]
  if mods.mayTransformOnEnter then parts := parts ++ ["transformed"]
  if let some host := mods.attachTo? then
    parts := parts ++ [s!"attached to {printObjRef ctx targets host}"]
  for (k, v) in mods.enterCounters do
    let cnt := match printCountInt v with | some n => k.countersPhrase n | none => s!"{printVal ctx v} {k.oracleName} counters"
    parts := parts ++ [s!"with {cnt} on it"]
  if let some tm := mods.enterTypeMod? then
    parts := parts ++ [s!"as {printTypeSetMod tm}"]
  if let some pt := mods.enterAsPredefined? then
    parts := parts ++ [s!"as a {pt.oracleNoun}"]
  if !mods.enterKeywords.isEmpty then
    parts := parts ++ [s!"with {KeywordAbility.joinedAnd mods.enterKeywords}"]
  if mods.enterLoseAllAbilities then
    parts := parts ++ ["with no abilities"]
  if mods.exileUntilSourceLeaves then
    parts := parts ++ [s!"until {ctx.selfRef} leaves the battlefield"]
  if mods.linkToSource then
    parts := parts ++ [s!"linked to {ctx.selfRef}"]
  if let some dr := mods.delayedReturn? then
    let drS := match dr with
      | .immediately tap u =>
        s!". Return it {printDestZone ctx targets (.battlefield u)}{if tap then " tapped" else ""}"
      | .atNextEndStep tap u =>
        s!". Return it {printDestZone ctx targets (.battlefield u)}{if tap then " tapped" else ""} at the beginning of the next end step"
      | .returnThenExileAtEndStep tap u =>
        s!". Return it {printDestZone ctx targets (.battlefield u)}{if tap then " tapped" else ""}, then exile it at the beginning of the next end step"
      | .returnIfThenExileAtEndStep cond tap u =>
        s!". If it is {toOracleStr cond { ctx with capitalize := false }}, return it {printDestZone ctx targets (.battlefield u)}{if tap then " tapped" else ""}, then exile it at the beginning of the next end step"
    parts := parts ++ [drS]
  if let some gp := mods.grantPlayPerm? then
    parts := parts ++ [s!". {capitalizeAscii (printGrantPlayPerm ctx "those cards" gp)}"]
  if mods.shuffleAfter then
    parts := parts ++ [", then shuffle"]
  if parts.isEmpty then ""
  else
    let joined := String.intercalate " " parts
    if joined.startsWith "." || joined.startsWith "," then joined else s!" {joined}"

private def printMoveChoice (ctx : PrintCtx) (targets : TargetSpec) (ch : MoveChoiceSpec) : String :=
  let chooserS := match ch.chooser with
    | .controller => ""
    | .owner => "its owner chooses "
    | .player w => s!"{printPlayerRef ctx targets w} chooses "
  let cntS := printExprCount ctx ch.count
  let filterS := match ch.filter? with
    | some p => s!" {toOracleStr p { ctx with capitalize := false }}"
    | none => ""
  let gcS := match ch.groupConstraint? with
    | some (.totalManaValueAtMost cap) => s!" with total mana value {printVal ctx cap} or less"
    | some .distinctControllers => " with different controllers"
    | some .distinctNames => " with different names"
    | some .distinctCardTypes => " of each card type"
    | some (.shareCharacteristic c) => s!" sharing {reprStr c}"
    | none => ""
  let invS := if ch.invertSelection then " (move the rest)" else ""
  let randS := if ch.atRandom then " at random" else ""
  let revS := if ch.revealFirst then " (reveal first)" else ""
  let unlessS := match ch.unlessMatching? with
    | some p => s!" unless you discard {toOracleStr p { ctx with capitalize := false }}"
    | none => ""
  let extS := match ch.extremeMetric? with
    | some (true, m) => s!" with greatest {printObjectMetric m}"
    | some (false, m) => s!" with least {printObjectMetric m}"
    | none => ""
  s!"{chooserS}{cntS}{filterS}{gcS}{extS}{randS}{revS}{invS}{unlessS}"

private def printMoveZone (ctx : PrintCtx) (targets : TargetSpec)
    (objs : ObjectExpr) (dest : DestZoneSpec) (verb : ZoneVerb) (mods : MoveMods)
    (anaphor0 : Array Nat := #[]) : String :=
  let subj := printObjRef ctx targets objs anaphor0
  let sfx := printMoveSuffix ctx targets mods
  let base :=
    match verb, dest with
    | .destroy, .graveyard =>
      match mods.choice? with
      | some ch => s!"destroy {printMoveChoice ctx targets ch} among {subj}{sfx}"
      | none => s!"destroy {subj}{sfx}"
    | .exile, .exile =>
      match mods.choice? with
      | some ch =>
        let revealOppHand? : Option String :=
          if ch.revealFirst then
            match objs with
            | .inZones { zones := #[.hand], owner := .ofPlayer who } pred =>
              if who != .you then
                let pS := toOracleStr pred { ctx with capitalize := false }
                let cardS :=
                  if pred == .anyObject then "a card"
                  else if pS.endsWith " card" then s!"{indefinite pS} {pS}"
                  else s!"{indefinite pS} {pS} card"
                some s!"{printPlayerRef ctx targets who anaphor0} reveals their hand. You choose {cardS} from it. Exile that card{sfx}"
              else none
            | _ => none
          else none
        match revealOppHand? with
        | some s => s
        | none => s!"exile {printMoveChoice ctx targets ch} from {subj}{sfx}"
      | none => s!"exile {subj}{sfx}"
    | .returnToHand, .hand .owner =>
      match mods.choice? with
      | some ch => s!"return {printMoveChoice ctx targets ch} from {subj} to its owner's hand{sfx}"
      | none => s!"return {subj} to its owner's hand{sfx}"
    | .returnToHand, .hand .controller =>
      let altDom? : Option (Condition × TargetDomain) :=
        targets.slots[0]?.bind (·.altDomainIf?)
      match objs, mods.choice?, altDom? with
      | .target 0, none, some (.castPred (.wasKicked .this), .object _ altPred) =>
        let altS := toOracleStr altPred { ctx with plural := true, capitalize := false }
        s!"choose {subj}. If this spell was kicked, instead choose any number of target {altS}. Return it to your hand{sfx}"
      | _, some ch, _ => s!"return {printMoveChoice ctx targets ch} from {subj} to your hand{sfx}"
      | _, none, _ => s!"return {subj} to your hand{sfx}"
    | .returnToHand, .hand (.player w) =>
      s!"return {subj} to {printPossessivePlayer ctx targets w} hand{sfx}"
    | .sacrifice, .graveyard =>
      match mods.choice? with
      | some ch =>
        match ch.chooser with
        | .player w =>
          let whoS := printPlayerRef ctx targets w anaphor0
          let verbS := if w == .you then "sacrifice" else "sacrifices"
          let fS := match ch.filter? with
            | some p => toOracleStr p { ctx with capitalize := false }
            | none => subj
          let extS := match ch.extremeMetric? with
            | some (true, m) => s!" with the greatest {printObjectMetric m}"
            | some (false, m) => s!" with the least {printObjectMetric m}"
            | none => ""
          s!"{whoS} {verbS} {printExprCount ctx ch.count} {fS}{extS}{sfx}"
        | _ => s!"sacrifice {printMoveChoice ctx targets ch} among {subj}{sfx}"
      | none => s!"sacrifice {subj}{sfx}"
    | .discard, .graveyard =>
      match mods.choice? with
      | some ch =>
        let revealOppHand? : Option String :=
          if ch.revealFirst then
            match objs with
            | .inZones { zones := #[.hand], owner := .ofPlayer who } pred =>
              if who != .you then
                let pS := toOracleStr pred { ctx with capitalize := false }
                let cardS :=
                  if pred == .anyObject then "a card"
                  else if pS.endsWith " card" then s!"{indefinite pS} {pS}"
                  else s!"{indefinite pS} {pS} card"
                some s!"{printPlayerRef ctx targets who anaphor0} reveals their hand. You choose {cardS} from it. That player discards that card{sfx}"
              else none
            | _ => none
          else none
        match revealOppHand? with
        | some s => s
        | none =>
          let whoPfx :=
            match ch.chooser with
            | .controller => ""
            | .owner => "its owner "
            | .player .you => ""
            | .player w => s!"{printPlayerRef ctx targets w anaphor0} "
          let discVerb := if whoPfx.isEmpty then "discard" else "discards"
          let cardsS :=
            match ch.count, ch.filter? with
            | .exact v, none =>
              match printCountInt v with
              | some n => cardPhrase n
              | none => s!"{printVal ctx v} cards"
            | _, some p => s!"{printExprCount ctx ch.count} {toOracleStr p { ctx with capitalize := false }} card"
            | _, none => s!"{printExprCount ctx ch.count} cards"
          let randS := if ch.atRandom then " at random" else ""
          let revS := if ch.revealFirst then " (reveal hand)" else ""
          let unlessS := match ch.unlessMatching? with
            | some p =>
              let pS := toOracleStr p { ctx with capitalize := false }
              let cardS := if pS.endsWith " card" then s!"{indefinite pS} {pS}" else s!"{indefinite pS} {pS} card"
              s!" unless you discard {cardS}"
            | none => ""
          s!"{whoPfx}{discVerb} {cardsS}{randS}{revS}{unlessS}{sfx}"
      | none =>
        match objs with
        | .inZones (.handOf .you) .anyObject => s!"discard your hand{sfx}"
        | .inZones (.handOf w) .anyObject => s!"{printPlayerRef ctx targets w anaphor0} discards their hand{sfx}"
        | _ => s!"discard {subj}{sfx}"
    | .mill, .graveyard =>
      match objs with
      | .topOfLibrary w v =>
        let cardsS := match printCountInt v with
          | some n => cardPhrase n
          | none => s!"{printVal ctx v} cards"
        match w with
        | .you => s!"mill {cardsS}{sfx}"
        | _ => s!"{printPlayerRef ctx targets w anaphor0} mills {cardsS}{sfx}"
      | _ => s!"mill {subj}{sfx}"
    | .put, .battlefield _ =>
      let destS := printDestZone ctx targets dest
      let altDom? : Option (Condition × TargetDomain) :=
        targets.slots[0]?.bind (·.altDomainIf?)
      match objs, mods.choice?, altDom? with
      | .target 0, none, some (.castPred (.teamworkPaid .this), altDom) =>
        let altTargets : TargetSpec :=
          { targets with slots := targets.slots.set! 0 { targets.slots[0]! with domain := altDom, altDomainIf? := none } }
        s!"choose {printSlotRef targets 0 "target card"}. If this spell was cast using teamwork, instead choose {printSlotRef altTargets 0 "target card"}. Return the chosen card {destS}{sfx}"
      | _, some ch, _ => s!"put {printMoveChoice ctx targets ch} from {subj} {destS}{sfx}"
      | _, none, _ => s!"return {subj} {destS}{sfx}"
    | .put, .library whose pos opt =>
      let destS := printDestZone ctx targets (.library whose pos opt)
      match mods.choice? with
      | some ch => s!"put {printMoveChoice ctx targets ch} from {subj} {destS}{sfx}"
      | none =>
        if opt && pos == .top then s!"{subj}'s owner puts it on their choice of the top or bottom of their library{sfx}"
        else if opt then s!"{subj}'s owner puts it {destS}{sfx}"
        else s!"put {subj} {destS}{sfx}"
    | .put, .hand _ | .put, .graveyard =>
      let destS := printDestZone ctx targets dest
      match mods.choice?, objs with
      | some { chooser := .controller, count := .exact (.const 1), .. }, .linkedExile _ =>
        s!"put {subj} {destS}{sfx}"
      | some ch, _ => s!"put {printMoveChoice ctx targets ch} from {subj} {destS}{sfx}"
      | none, _ => s!"put {subj} {destS}{sfx}"
    | .shuffleIntoLibrary, _ => s!"shuffle {subj} into its owner's library{sfx}"
    | _, _ => s!"move {subj} {printDestZone ctx targets dest}{sfx}"
  applyCap ctx base

private def printEnterMods (ctx : PrintCtx) (targets : TargetSpec) (mods : EnterMods) : String := Id.run do
  let mut parts : List String := []
  if mods.attacking then parts := parts ++ ["attacking"]
  if mods.goaded then parts := parts ++ ["goaded"]
  if let some host := mods.attachTo? then
    parts := parts ++ [s!"attached to {printObjRef ctx targets host}"]
  for (k, v) in mods.counters do
    let cnt := match printCountInt v with | some n => k.countersPhrase n | none => s!"{printVal ctx v} {k.oracleName} counters"
    parts := parts ++ [s!"with {cnt} on it"]
  if !mods.grantKeywordsUntilEot.isEmpty then
    parts := parts ++ [s!"with {KeywordAbility.joinedAnd mods.grantKeywordsUntilEot} until end of turn"]
  if let some da := mods.delayedAction? then
    let daS := match da with
      | .sacrificeAtEndStep => ". Sacrifice them at the beginning of the next end step"
      | .exileAtEndStep => ". Exile them at the beginning of the next end step"
      | .exileAtEndOfCombat => ". Exile them at end of combat"
      | .sacrificeAtEndStepUnless c =>
        s!". Sacrifice them at the beginning of the next end step unless {toOracleStr c { ctx with capitalize := false }}"
    parts := parts ++ [daS]
  if parts.isEmpty then ""
  else
    let joined := parts.foldl (fun acc p =>
      if acc.isEmpty then p
      else if p.startsWith "." then acc ++ p
      else acc ++ " " ++ p) ""
    if joined.startsWith "." then joined else s!" {joined}"

private def printRuleMod (ctx : PrintCtx) (targets : TargetSpec)
    (dur? : Option DurationExpr := none) (r : RuleModification) (anaphor0 : Array Nat := #[]) : String :=
  match r with
  | .player r =>
    let pRef (pf : PlayerFilter) : String :=
      match pf with
      | { relation := .anyPlayer, pred := .matchesExpr pe } => printPlayerRef ctx targets pe anaphor0
      | _ => toOracleStr pf { ctx with capitalize := false }
    match r with
    | .maxHandSize .you none => "you have no maximum hand size"
    | .maxHandSize .you (some n) => s!"your maximum hand size is {n}"
    | .maxHandSize w none => s!"{pRef w} has no maximum hand size"
    | .maxHandSize w (some n) => s!"{pRef w}'s maximum hand size is {n}"
    | .additionalLands .you 1 => "you may play an additional land this turn"
    | .additionalLands .you n => s!"you may play {englishNumber n} additional lands this turn"
    | .additionalLands w n => s!"{pRef w} may play {englishNumber n} additional land(s)"
    | .cantGainLife w => s!"{pRef w} can't gain life"
    | .cantLoseGame w => s!"{pRef w} can't lose the game"
    | .cantWinGame w => s!"{pRef w} can't win the game"
    | .hexproof w none => s!"{pRef w} has hexproof"
    | .hexproof w (some q) => s!"{pRef w} has hexproof from {toOracleStr q { ctx with capitalize := false }}"
    | .protectionFrom w q => s!"{pRef w} has protection from {toOracleStr q { ctx with capitalize := false }}"
    | .cantCastSpells w p =>
      let wS := if w == .any then "players" else pRef w
      if p == .all #[] || p == .isKind .spell then s!"{wS} can't cast spells"
      else s!"{wS} can't cast {toOracleStr p { ctx with capitalize := false }} spells"
    | .activateAsThoughHaste _ sc => s!"activate abilities of {toOracleStr sc { ctx with capitalize := false }} as though they had haste"
    | .extraAbilityActivation tag sc n =>
      let tagS := match tag with
        | .powerUp => "power-up" | .exhaust => "exhaust" | .boast => "boast"
        | .equip _ => "equip" | .cycling _ => "cycling" | .crew _ => "crew"
      s!"activate {tagS} abilities of {toOracleStr sc { ctx with capitalize := false }} {n} additional time(s)"
    | .lifeTotalCantChange w => s!"{pRef w}'s life total can't change"
    | .forbidAbilityActivation w tag =>
      let tagS := match tag with
        | .powerUp => "power-up" | .exhaust => "exhaust" | .boast => "boast"
        | .equip _ => "equip" | .cycling _ => "cycling" | .crew _ => "crew"
      s!"{pRef w} can't activate {tagS} abilities"
    | .gainDesignation .you .citysBlessing => "you get the city's blessing"
    | .gainDesignation .you .enduringStory => "you get enduring story"
    | .gainDesignation w d => s!"{pRef w} gets {reprStr d}"
    | .controlPlayer w => s!"you control {pRef w} during their next turn"
  | .play r =>
    match r with
    | .lookAtTopOfLibrary _ => "you may look at the top card of your library any time"
    | .mayPlayFrom _ z p lands linked anyC free =>
      s!"you may {if lands then "play" else "cast"} {toOracleStr p { ctx with capitalize := false }} from {z.englishName}{if linked then " exiled with this" else ""}{if anyC then " using mana of any type" else ""}{if free then " without paying their mana costs" else ""}"
    | .castAsThoughFlash _ p ts nth =>
      let nthS := match nth with | some n => s!" (nth={n})" | none => ""
      if ts then "you may cast this spell as though it had flash"
      else s!"you may cast {toOracleStr p { ctx with capitalize := false }} spells as though they had flash{nthS}"
    | .spellCantBeCountered none => "this spell can't be countered"
    | .spellCantBeCountered (some p) => s!"{toOracleStr p { ctx with capitalize := false }} spells can't be countered"
    | .nextSpellCantBeCountered _ p => s!"the next {toOracleStr p { ctx with capitalize := false }} spell you cast can't be countered"
    | .castRestriction c => s!"cast this spell only if {toOracleStr c { ctx with capitalize := false }}"
    | .mayBeginOnBattlefield => "you may begin the game with this card on the battlefield"
    | .canBeCommander => "this card can be your commander"
    | .activateLoyaltyAsInstant _ p => s!"you may activate loyalty abilities of {toOracleStr p { ctx with capitalize := false }} any time you could cast an instant"
  | .combat r =>
    let subjStr : StaticSubject → String
      | .self => ctx.selfRef
      | .matching f => toOracleStr f { ctx with plural := true, capitalize := false }
    match r with
    | .cantAttack s => s!"{subjStr s} can't attack"
    | .cantAttackUnless s c => s!"{subjStr s} can't attack unless {toOracleStr c { ctx with capitalize := false }}"
    | .attackTax ap _ cs => s!"{toOracleStr ap { ctx with capitalize := false }} creatures can't attack you unless their controller pays {cs.toNotation}"
    | .attackPlaneswalkerTax ap pp cs => s!"{toOracleStr ap { ctx with capitalize := false }} can't attack {toOracleStr pp { ctx with capitalize := false }} unless their controller pays {cs.toNotation}"
    | .cantAttackPlayer ap _ none => s!"{toOracleStr ap { ctx with capitalize := false }} can't attack you"
    | .cantAttackPlayer ap _ (some pp) => s!"{toOracleStr ap { ctx with capitalize := false }} can't attack you or {toOracleStr pp { ctx with capitalize := false }}"
    | .attacksEachCombatIfAble s => s!"{subjStr s} attacks each combat if able"
    | .attackDespiteDefender s => s!"{subjStr s} can attack as though it didn't have defender"
    | .maxAttackersPerPermanent s n => s!"no more than {n} creature(s) can attack {subjStr s} each combat"
    | .cantBlock s none => s!"{subjStr s} can't block{if dur? == some .untilEndOfTurn then " this turn" else ""}"
    | .cantBlock s (some c) => s!"{subjStr s} can't block unless {toOracleStr c { ctx with capitalize := false }}"
    | .cantBlockMatching bp ap => s!"{toOracleStr bp { ctx with capitalize := false }} can't block {toOracleStr ap { ctx with capitalize := false }}"
    | .cantBeBlocked s => s!"{subjStr s} can't be blocked"
    | .cantBeBlockedBy s bp => s!"{subjStr s} can't be blocked by {toOracleStr bp { ctx with capitalize := false }}"
    | .minBlockers s n => s!"{subjStr s} can't be blocked except by {englishNumber n} or more creatures"
    | .maxBlockers s n => s!"{subjStr s} can't be blocked by more than {englishNumber n} creature(s)"
    | .assignCombatDamageByToughness sc onlyGt =>
      s!"{toOracleStr sc { ctx with plural := true, capitalize := false }} assign combat damage equal to toughness{if onlyGt then " if greater" else ""}"
    | .assignNegativePowerAsPositive s => s!"{subjStr s} assigns negative power as positive"
  | .trigger r =>
    match r with
    | .extraTrigger sc n => s!"triggered abilities of {toOracleStr sc { ctx with plural := true, capitalize := false }} trigger {n} additional time(s)"
    | .suppressEnteringTriggers sc => s!"{toOracleStr sc { ctx with plural := true, capitalize := false }} entering don't cause abilities to trigger"
  | .game r =>
    let subjStr : StaticSubject → String
      | .self => ctx.selfRef
      | .matching f => toOracleStr f { ctx with plural := true, capitalize := false }
    match r with
    | .doesntUntapDuringUntapStep s none => s!"{subjStr s} doesn't untap during its controller's untap step"
    | .doesntUntapDuringUntapStep s (some c) => s!"{subjStr s} doesn't untap unless {toOracleStr c { ctx with capitalize := false }}"
    | .cantBecomeUntapped s => s!"{subjStr s} can't become untapped"
    | .lockNonManaDuringPhase ph w => s!"during {ph.englishName}, {toOracleStr w { ctx with capitalize := false }} can't cast spells or activate non-mana abilities"
    | .planeswalkersSurviveZeroLoyalty sc => s!"{toOracleStr sc { ctx with plural := true, capitalize := false }} don't die for having 0 loyalty"
    | .cantHaveCountersPutOn sc none => s!"{toOracleStr sc { ctx with plural := true, capitalize := false }} can't have counters put on them"
    | .cantHaveCountersPutOn sc (some k) => s!"{toOracleStr sc { ctx with plural := true, capitalize := false }} can't have {k.oracleName} counters put on them"
    | .legendRuleDisabled _ => "the legend rule doesn't apply to permanents you control"
  | .costMod appliesTo mod nextOnly =>
    let subjS :=
      match appliesTo with
      | .thisSpell => "this spell"
      | .spells _ p nth notFrom _ =>
        let pS :=
          match p with
          | .hasSupertype s => s.oracleWord
          | .hasType t => t.oracleWord
          | .hasColor (.literal c) => c.englishName
          | .hasSubtype (.literal s) => s.englishName
          | .not (.hasType t) => s!"non{t.oracleWord}"
          | _ => toOracleStr p { ctx with capitalize := false }
        let pref := if nextOnly then "the next " else ""
        let nthS := match nth with | some n => s!" (nth={n})" | none => ""
        let nfS := match notFrom with | some z => s!" not from {z.englishName}" | none => ""
        let turnS := if dur? == some DurationExpr.untilEndOfTurn then " this turn" else ""
        s!"{pref}{pS} spells you cast{turnS}{nthS}{nfS}"
      | .abilities _ tag? sc _ nth =>
        let tS := match tag? with | some (.equip _) => "equip" | _ => "activated"
        let nthS := match nth with | some n => s!" (nth={n})" | none => ""
        s!"{tS} abilities of {toOracleStr sc { ctx with capitalize := false }}{nthS}"
    match mod with
    | .reduceGeneric (.const n) => s!"{subjS} cost \{{n.toNat}} less to cast"
    | .reduceGeneric v => s!"{subjS} cost \{{printVal ctx v}} less to cast"
    | .increaseGeneric (.const n) => s!"{subjS} cost \{{n.toNat}} more to cast"
    | .increaseGeneric v => s!"{subjS} cost \{{printVal ctx v}} more to cast"
    | .alternativeFree => s!"{subjS} can be cast without paying its mana cost"
  | .all rs =>
    String.intercalate ". " (rs.attach.toList.map fun ⟨r, _⟩ => printRuleMod ctx targets dur? r)

private def printReplSpec (ctx : PrintCtx) (targets : TargetSpec) : StaticReplacementSpec → String
  | .entersTapped s none =>
    let sStr := match s with | .self => ctx.selfRef | .matching f => toOracleStr f { ctx with capitalize := false }
    s!"{sStr} enters tapped"
  | .entersTapped s (some c) =>
    let sStr := match s with | .self => ctx.selfRef | .matching f => toOracleStr f { ctx with capitalize := false }
    s!"{sStr} enters tapped unless {toOracleStr c { ctx with capitalize := false }}"
  | .entersTappedUnlessPay cs => s!"{ctx.selfRef} enters tapped unless you pay {cs.toNotation}"
  | .entersWithCounters s k v add =>
    let sStr := match s with | .self => ctx.selfRef | .matching f => toOracleStr f { ctx with capitalize := false }
    let cnt := match printCountInt v with | some n => k.countersPhrase n | none => s!"{printVal ctx v} {k.oracleName} counters"
    s!"{sStr} enters with {if add then "additional " else ""}{cnt} on it"
  | .entersWithDesignation tag => s!"{ctx.selfRef} enters {reprStr tag}"
  | .asEntersChoose kind => s!"as {ctx.selfRef} enters, choose {reprStr kind}"
  | .asEntersMayCopy f _ _ => s!"as {ctx.selfRef} enters, you may have it enter as a copy of {toOracleStr f { ctx with capitalize := false }}"
  | .exileInsteadOfDying sc bonus? =>
    let bS := match bonus? with | some tok => s!" and {tok.createPhrase 1}" | none => ""
    if sc == { zones := .battlefield, pred := .sameAs (.target 0) } then
      s!"if that creature would die this turn, exile it instead{bS}"
    else
      s!"if {toOracleStr sc { ctx with capitalize := false }} would die, exile it instead{bS}"
  | .multiplyTokens _ factor => s!"if one or more tokens would be created under your control, {factor} times that many are created instead"
  | .extraTokenWith _ pred tok cnt => s!"when creating {toOracleStr pred { ctx with capitalize := false }} tokens, also {tok.createPhrase cnt}"
  | .replaceTokens _ fromP repl => s!"replace {toOracleStr fromP { ctx with capitalize := false }} tokens with {repl.oracleNoun}"
  | .extraDraw _ n exc => s!"draw {n} cards instead{if exc then " except first draw step" else ""}"
  | .extraDrawOnConnive _ sc n => s!"when {toOracleStr sc { ctx with capitalize := false }} connives, draw {n} extra card(s)"
  | .modifyCountersPut sc k? _ add =>
    let kS := match k? with | some k => s!"{k.oracleName} " | none => ""
    s!"put {add} additional {kS}counter(s) on {toOracleStr sc { ctx with capitalize := false }}"
  | .preventDamage s none =>
    let sStr :=
      match s with
      | .self => ctx.selfRef
      | .matching { pred := .sameAs (.target i), .. } => printObjRef ctx targets (.target i)
      | .matching f => toOracleStr f { ctx with capitalize := false }
    s!"prevent all damage that would be dealt by {sStr}"
  | .preventDamage s (some amt) =>
    let sStr :=
      match s with
      | .self => ctx.selfRef
      | .matching { pred := .sameAs (.target i), .. } => printObjRef ctx targets (.target i)
      | .matching f => toOracleStr f { ctx with capitalize := false }
    s!"prevent the next {printVal ctx amt} damage that would be dealt to {sStr}"
  | .modifyDamage sc noncombat _ mult add =>
    s!"{if noncombat then "noncombat " else ""}damage from {toOracleStr sc { ctx with capitalize := false }} is multiplied by {mult} plus {printVal ctx add}"
  | .healOtherDamageWhenDealt _ => "prevent damage and gain that much life"
  | .unspentManaBecomesColorless _ => "you don't lose unspent mana; it becomes colorless"
  | .exileOnLeaveStack => "if this spell would leave the stack, exile it instead"
  | .entersTappedAndAttackingSameDefender => "enters tapped and attacking the same defender"
  | .all xs =>
    String.intercalate ". " (xs.attach.toList.map fun ⟨x, _⟩ => printReplSpec ctx targets x)

private def printInspectLibrary (ctx : PrintCtx) (targets : TargetSpec) (spec : InspectLibrarySpec) : String :=
  let srcS :=
    match spec.source with
    | .topCards w cnt rev =>
      let verb := if rev then "reveal" else "look at"
      let cntS := match printCountInt cnt with
        | some 1 => "the top card"
        | some n => s!"the top {englishNumber n} cards"
        | none => s!"the top {printVal ctx cnt} cards"
      s!"{verb} {cntS} of {printPossessivePlayer ctx targets w} library"
    | .revealUntil w pred cnt ex =>
      let verb := if ex then "exile" else "reveal"
      let rawP := toOracleStr pred { ctx with capitalize := false }
      let pS := if rawP.endsWith " card" then (rawP.dropEnd 5).copy else rawP
      let cntS := match printCountInt cnt with
        | some 1 =>
          s!"{indefinite pS} {pS} card"
        | some n => s!"{englishNumber n} {pS} cards"
        | none => s!"{printVal ctx cnt} {pS} cards"
      s!"{verb} cards from the top of {printPossessivePlayer ctx targets w} library until you {verb} {cntS}"
    | .millCards w cnt =>
      let cntS := match printCountInt cnt with | some n => cardPhrase n | none => s!"{printVal ctx cnt} cards"
      match w with
      | .you => s!"mill {cntS}"
      | _ => s!"{printPlayerRef ctx targets w} mills {cntS}"
    | .allButBottom w =>
      if spec.action == .moveAll .exile && spec.rest == .leaveInPlace then
        s!"exile all but the bottom card of {printPossessivePlayer ctx targets w} library"
      else
        s!"exile all cards from {printPossessivePlayer ctx targets w} library except the bottom card"
    | .outsideTheGame _ n =>
      s!"choose {englishNumber n} card(s) from outside the game"
  let actS :=
    match spec.action with
    | .takeMatching pred cnt dest mods rev rand =>
      let rawP := toOracleStr pred { ctx with capitalize := false }
      let pS := if rawP.endsWith " card" then (rawP.dropEnd 5).copy else rawP
      let revS := if rev then "reveal it and " else ""
      let randS := if rand then " at random" else ""
      let sfx := printMoveSuffix ctx targets mods
      s!"{revS}put {printExprCount ctx cnt} {pS} card(s) from among them{randS} {printDestZone ctx targets dest}{sfx}"
    | .splitIntoPiles sp ch n d1 d2 drawOpt? =>
      let drawS := match drawOpt? with | some k => s!" (or draw {k})" | none => ""
      let pilesS :=
        if sp == .you && ch == .opponents && n == 2 then
          "a face-down pile and a face-up pile"
        else s!"{englishNumber n} piles"
      let chS :=
        if ch == .opponents then "An opponent"
        else capitalizeAscii (printPlayerRef ctx targets ch)
      let d2S :=
        if d2 == .graveyard && d1 == .hand .controller then "into your graveyard"
        else printDestZone ctx targets d2
      s!"separate them into {pilesS}. {chS} chooses one of the piles{drawS}. Put that pile {printDestZone ctx targets d1} and the other {d2S}"
    | .distributeEachOpponent dest mods =>
      s!"put one of those cards {printDestZone ctx targets dest} for each opponent{printMoveSuffix ctx targets mods}"
    | .moveAll dest mods =>
      match spec.source, dest with
      | .allButBottom _, .exile =>
        if spec.rest == .leaveInPlace && mods == {} then ""
        else s!"put all of them {printDestZone ctx targets dest}{printMoveSuffix ctx targets mods}"
      | _, _ => s!"put all of them {printDestZone ctx targets dest}{printMoveSuffix ctx targets mods}"
    | .none => ""
  let restS :=
    match spec.rest with
    | .leaveInPlace => ""
    | .bottomRandom => "put the rest on the bottom of your library in a random order"
    | .bottomAnyOrder => "put the rest on the bottom of your library in any order"
    | .graveyard => "put the rest into your graveyard"
    | .exile => "exile the rest"
    | .shuffleIntoLibrary => "shuffle the rest into your library"
  let combined :=
    if !srcS.isEmpty && actS.startsWith "separate" then
      let head := s!"{srcS} and {actS}"
      if restS.isEmpty then head else s!"{head}. {capitalizeAscii restS}"
    else
      let parts := ([srcS, actS, restS]).filter (· != "")
      match parts with
      | [] => ""
      | [p] => p
      | first :: rest => String.intercalate ". " (first :: rest.map capitalizeAscii)
  applyCap ctx combined

private def mergeSlots (a b : Array Nat) : Array Nat :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

private partial def predMentionedSlots : ObjectPred → Array Nat
  | .all xs | .any xs => xs.foldl (fun acc p => mergeSlots acc (predMentionedSlots p)) #[]
  | .not p => predMentionedSlots p
  | .controlledBy pf | .ownedBy pf => playerPredMentionedSlots pf.pred
  | .sameAs (.target i) | .otherThan (.target i) => #[i]
  | _ => #[]
where
  playerPredMentionedSlots : PlayerPred → Array Nat
    | .matchesExpr (.target i) => #[i]
    | .all xs | .anyOf xs => xs.foldl (fun acc p => mergeSlots acc (playerPredMentionedSlots p)) #[]
    | .not p => playerPredMentionedSlots p
    | _ => #[]

private partial def objMentionedSlots : ObjectExpr → Array Nat
  | .target i => #[i]
  | .allTargets => #[0]
  | .inZones zs pred =>
    let zSlots := match zs.owner with | .ofPlayer (.target i) => #[i] | _ => #[]
    mergeSlots zSlots (predMentionedSlots pred)
  | .topOfLibrary w _ =>
    match w with | .target i => #[i] | _ => #[]
  | .targetsOf o | .linkedExile o | .filter o _ | .extremum _ _ o => objMentionedSlots o
  | .union xs => xs.foldl (fun acc x => mergeSlots acc (objMentionedSlots x)) #[]
  | .diff a b => mergeSlots (objMentionedSlots a) (objMentionedSlots b)
  | _ => #[]

private def playerMentionedSlots : PlayerExpr → Array Nat
  | .target i => #[i]
  | .controllerOf o | .ownerOf o => objMentionedSlots o
  | _ => #[]

private def printSearchLibrary (ctx : PrintCtx) (targets : TargetSpec) (spec : SearchLibrarySpec)
    (anaphor0 : Array Nat := #[]) : String :=
  let libOwner : PlayerExpr :=
    match spec.zones.owner with
    | .ofPlayer p => p
    | _ => spec.searcher
  let seenSearcher := mergeSlots anaphor0 (playerMentionedSlots spec.searcher)
  let zonesS :=
    if spec.zones == .yourLibrary || spec.zones == .libraryOf .you || spec.zones.zones == #[.library] then
      s!"{printPossessivePlayer ctx targets libOwner seenSearcher} library"
    else
      let zs := String.intercalate " and/or " (spec.zones.zones.toList.map ZoneKind.englishName)
      s!"{printPossessivePlayer ctx targets libOwner seenSearcher} {zs}"
  let isAnyCard := spec.filter == .all #[] || spec.filter == .isKind .card
  let filterS := if isAnyCard then "" else toOracleStr spec.filter { ctx with capitalize := false }
  let isSingle :=
    match spec.count with
    | .upTo (.const 1) | .exact (.const 1) => true
    | _ => false
  let cntS :=
    if isSingle then indefinite (if filterS.isEmpty then "card" else filterS)
    else printExprCount ctx spec.count
  let cardWord := if isSingle then "card" else "cards"
  let pronWord := if isSingle then "it" else "them"
  let filterAndCard := if filterS.isEmpty then cardWord else s!"{filterS} {cardWord}"
  let gcS := match spec.groupConstraint? with
    | some .distinctNames => " with different names"
    | some (.totalManaValueAtMost v) => s!" with total mana value {printVal ctx v} or less"
    | some .distinctCardTypes => " of different card types"
    | some .distinctControllers => " with different controllers"
    | some (.shareCharacteristic c) => s!" sharing {reprStr c}"
    | none => ""
  let revS := if spec.reveal then s!", reveal {pronWord}," else ","
  let destS :=
    if spec.zones == .libraryOf .you || spec.zones == .yourLibrary then
      match spec.dest with
      | .battlefield .controller => "onto the battlefield"
      | .graveyard => "into your graveyard"
      | d => printDestZone ctx targets d seenSearcher
    else printDestZone ctx targets spec.dest seenSearcher
  let sfx := printMoveSuffix ctx targets spec.mods
  let secondS := match spec.secondDest? with
    | some (d2, m2) => s!" and one {printDestZone ctx targets d2}{printMoveSuffix ctx targets m2}"
    | none => ""
  let shufS := if spec.shuffle then ", then shuffle" else ""
  let untapS := match spec.untapIf? with
    | some c => s!". If {toOracleStr c { ctx with capitalize := false }}, untap it"
    | none => ""
  let whoPfx := match spec.searcher with
    | .you => "search"
    | w => s!"{printPlayerRef ctx targets w anaphor0} searches"
  if spec.dest == .library .owner .top false && spec.shuffle && secondS.isEmpty && sfx.isEmpty then
    applyCap ctx s!"{whoPfx} {zonesS} for {cntS} {filterAndCard}{gcS}{revS} then shuffle and put that card on top{untapS}"
  else
    applyCap ctx s!"{whoPfx} {zonesS} for {cntS} {filterAndCard}{gcS}{revS} put {pronWord} {destS}{sfx}{secondS}{shufS}{untapS}"

private def printDividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 2 then "one or two targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

private def ruleModMentionedSlots : RuleModification → Array Nat
  | .player (.maxHandSize w _) | .player (.additionalLands w _) | .player (.cantGainLife w)
  | .player (.cantLoseGame w) | .player (.cantWinGame w) | .player (.hexproof w _)
  | .player (.protectionFrom w _) | .player (.cantCastSpells w _)
  | .player (.lifeTotalCantChange w) | .player (.forbidAbilityActivation w _)
  | .player (.gainDesignation w _) | .player (.controlPlayer w) =>
    predMentionedSlots.playerPredMentionedSlots w.pred
  | _ => #[]

private partial def instrMentionedSlots : Instruction → Array Nat
  | .moveZone o _ _ mods =>
    let base := objMentionedSlots o
    let chSlots := match mods.choice? with
      | some ch => match ch.chooser with | .player p => playerMentionedSlots p | _ => #[]
      | none => #[]
    mergeSlots base chSlots
  | .permanent (.setTapped o _ _) | .permanent (.modifyCounters _ o _)
  | .permanent (.transform o) | .permanent (.turnFaceUp o)
  | .permanent (.phaseOut o _) | .permanent (.setDesignation o _ _) => objMentionedSlots o
  | .permanent (.attach a b _) => mergeSlots (objMentionedSlots a) (objMentionedSlots b)
  | .damage (.deal s to amt _) =>
    let base := objMentionedSlots s
    let _ := amt
    match to with
    | .targetSlot i => mergeSlots base #[i]
    | .objects o => mergeSlots base (objMentionedSlots o)
    | .players p => mergeSlots base (playerMentionedSlots p)
    | .both o p => mergeSlots (mergeSlots base (objMentionedSlots o)) (playerMentionedSlots p)
    | .allTargets => mergeSlots base #[0]
  | .damage (.fight a b _) => mergeSlots (objMentionedSlots a) (objMentionedSlots b)
  | .life (.gain p _) | .life (.lose p _) | .life (.set p _) => playerMentionedSlots p
  | .player (.drawCards p _) | .player (.scry p _) | .player (.surveil p _)
  | .player (.shuffle p) | .player (.setStatus p _ _) => playerMentionedSlots p
  | .player (.searchLibrary spec) =>
    let zSlots := match spec.zones.owner with | .ofPlayer p => playerMentionedSlots p | _ => #[]
    mergeSlots (playerMentionedSlots spec.searcher) zSlots
  | .player (.reveal p o _) => mergeSlots (playerMentionedSlots p) (objMentionedSlots o)
  | .player (.explore o) | .player (.connive o) => objMentionedSlots o
  | .create (.tokens p _ spec _) =>
    let refSlots := match spec with | .copyOf ref _ => objMentionedSlots ref | _ => #[]
    mergeSlots (playerMentionedSlots p) refSlots
  | .stack (.counterStack o _ _) | .stack (.copyStackObject o _ _)
  | .stack (.chooseNewTargets o _) | .stack (.mayCastOrPlay o _) => objMentionedSlots o
  | .installEffect (.applyContinuous _ aff _) => objMentionedSlots aff
  | .installEffect (.applyRule _ r) => ruleModMentionedSlots r
  | .seq steps => steps.foldl (fun acc s => mergeSlots acc (instrMentionedSlots s)) #[]
  | .bind _ s c => mergeSlots (instrMentionedSlots s) (instrMentionedSlots c)
  | .ifCond _ t e => mergeSlots (instrMentionedSlots t) (instrMentionedSlots e)
  | .optional p _ y n _ =>
    mergeSlots (mergeSlots (playerMentionedSlots p) (instrMentionedSlots y)) (instrMentionedSlots n)
  | .unlessPays p _ u => mergeSlots (playerMentionedSlots p) (instrMentionedSlots u)
  | _ => #[]

/-- Canonical Oracle rendering of an `Instruction` with targeting context `targets`. -/
partial def toOracleWith (ctx : PrintCtx) (targets : TargetSpec) (i : Instruction)
    (anaphor0 : Array Nat := #[]) : String :=
  match i with
  | .noop => ""
  | .seq steps =>
    let joined :=
      match steps.toList with
      | [.player (.drawCards .you n),
         .moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard { choice? := some ch, .. }] =>
        let a := toOracleWith { ctx with capitalize := false } targets (.player (.drawCards .you n)) anaphor0
        let b := toOracleWith { ctx with capitalize := false } targets
          (.moveZone (.inZones (.handOf .you) .anyObject) .graveyard .discard { choice? := some ch }) anaphor0
        if ch.unlessMatching?.isSome then s!"{a}. Then {b}"
        else s!"{a}, then {b}"
      | [.player (.drawCards who n), .life (.lose who2 m)] =>
        if who == who2 then
          let cardsS := match printCountInt n with | some k => cardPhrase k | none => s!"{printVal ctx n} cards"
          match who with
          | .you => s!"you draw {cardsS} and lose {printVal ctx m} life"
          | p => s!"{printPlayerRef ctx targets p anaphor0} draws {cardsS} and loses {printVal ctx m} life"
        else
          let a := toOracleWith { ctx with capitalize := false } targets (.player (.drawCards who n)) anaphor0
          let seen1 := mergeSlots anaphor0 (playerMentionedSlots who)
          let b := toOracleWith { ctx with capitalize := false } targets (.life (.lose who2 m)) seen1
          s!"{a}. {capitalizeAscii b}"
      | [.player (.drawCards who n), .life (.gain who2 m)] =>
        if who == who2 then
          let cardsS := match printCountInt n with | some k => cardPhrase k | none => s!"{printVal ctx n} cards"
          match who with
          | .you => s!"you draw {cardsS} and gain {printVal ctx m} life"
          | p => s!"{printPlayerRef ctx targets p anaphor0} draws {cardsS} and gains {printVal ctx m} life"
        else
          let a := toOracleWith { ctx with capitalize := false } targets (.player (.drawCards who n)) anaphor0
          let seen1 := mergeSlots anaphor0 (playerMentionedSlots who)
          let b := toOracleWith { ctx with capitalize := false } targets (.life (.gain who2 m)) seen1
          s!"{a}. {capitalizeAscii b}"
      | [.installEffect (.applyContinuous dur1 aff1 m1),
         .installEffect (.applyContinuous dur2 aff2 m2)] =>
        if dur1 == dur2 && aff1 == aff2 then
          toOracleWith { ctx with capitalize := false } targets
            (.installEffect (.applyContinuous dur1 aff1 (.all #[m1, m2]))) anaphor0
        else
          let a := toOracleWith { ctx with capitalize := false } targets (.installEffect (.applyContinuous dur1 aff1 m1)) anaphor0
          let seen1 := mergeSlots anaphor0 (objMentionedSlots aff1)
          let b := toOracleWith { ctx with capitalize := false } targets (.installEffect (.applyContinuous dur2 aff2 m2)) seen1
          s!"{a}. {capitalizeAscii b}"
      | _ =>
        let parts : List String := Id.run do
          let mut out : List String := []
          let mut seen := anaphor0
          for st in steps do
            let s := toOracleWith { ctx with capitalize := false } targets st seen
            if !s.isEmpty then out := out ++ [s]
            seen := mergeSlots seen (instrMentionedSlots st)
          return out
        match parts with
        | [] => ""
        | [p] => p
        | first :: rest =>
          String.intercalate ". " (first :: rest.map capitalizeAscii)
    applyCap ctx joined
  | .bind _ step cont =>
    let a := toOracleWith { ctx with capitalize := false } targets step anaphor0
    let seen1 := mergeSlots anaphor0 (instrMentionedSlots step)
    let b := toOracleWith { ctx with capitalize := false } targets cont seen1
    let joined := if a.isEmpty then b else if b.isEmpty then a else s!"{a}. {capitalizeAscii b}"
    applyCap ctx joined
  | .ifCond cond t e =>
    let condS := toOracleStr cond { ctx with capitalize := false }
    let tTargets : TargetSpec :=
      match targets.slots[0]?.bind (·.altDomainIf?) with
      | some (altC, altDom) =>
        if altC == cond then
          { targets with slots := targets.slots.set! 0 { targets.slots[0]! with domain := altDom, altDomainIf? := none } }
        else targets
      | none => targets
    let rec renderScoped (tgts : TargetSpec) (instr : Instruction) (seen : Array Nat) : String :=
      match instr with
      | .seq xs =>
        if xs.size >= 2 then
          let parts : List String := Id.run do
            let mut out : List String := []
            let mut s := seen
            for st in xs do
              let str := renderScoped tgts st s
              if !str.isEmpty then out := out ++ [str]
              s := mergeSlots s (instrMentionedSlots st)
            return out
          String.intercalate "; " parts
        else if xs.size == 1 then renderScoped tgts xs[0]! seen
        else ""
      | .bind _ st c =>
        let a := renderScoped tgts st seen
        let s1 := mergeSlots seen (instrMentionedSlots st)
        let b := renderScoped tgts c s1
        if a.isEmpty then b else if b.isEmpty then a else s!"{a}; {b}"
      | .queueReflexiveTrigger ab =>
        s!"when you do, {renderScoped ab.effect.targets ab.effect.body #[]}"
      | _ => toOracleWith { ctx with capitalize := false } tgts instr seen
    let base :=
      match e with
      | .noop =>
        let tS := renderScoped tTargets t anaphor0
        s!"if {condS}, {tS}"
      | _ =>
        match cond with
        | .castPred _ =>
          let eS := renderScoped targets e anaphor0
          let hasAltDom :=
            match targets.slots[0]?.bind (·.altDomainIf?) with
            | some (altC, _) => altC == cond
            | none => false
          let seenAfterE := if hasAltDom then anaphor0 else mergeSlots anaphor0 (instrMentionedSlots e)
          let tS := renderScoped tTargets t seenAfterE
          s!"{eS}. If {condS}, {tS} instead"
        | _ =>
          let tS := renderScoped tTargets t anaphor0
          let seenAfterT := mergeSlots anaphor0 (instrMentionedSlots t)
          let eS := renderScoped targets e seenAfterT
          s!"if {condS}, {tS}. Otherwise, {eS}"
    applyCap ctx base
  | .optional who cost? onYes onNo maxTimes =>
    let choosePfx :=
      match who with
      | .ownerOf (.target 0) =>
        if anaphor0.contains 0 then ""
        else s!"choose {printSlotRef targets 0 "target permanent"}. "
      | _ => ""
    let anaphEff := if choosePfx.isEmpty then anaphor0 else mergeSlots anaphor0 #[0]
    let whoS := printPlayerRef ctx targets who anaphEff
    let seenWho := mergeSlots anaphEff (playerMentionedSlots who)
    let doS := if who == .you then "do" else "does"
    let timesS := if maxTimes > 1 then s!" up to {englishNumber maxTimes} times" else ""
    let rec renderScopedOpt (tgts : TargetSpec) (instr : Instruction) (seen : Array Nat) : String :=
      match instr with
      | .seq xs =>
        if xs.size >= 2 then
          let parts : List String := Id.run do
            let mut out : List String := []
            let mut s := seen
            for st in xs do
              let str := renderScopedOpt tgts st s
              if !str.isEmpty then out := out ++ [str]
              s := mergeSlots s (instrMentionedSlots st)
            return out
          String.intercalate "; " parts
        else if xs.size == 1 then renderScopedOpt tgts xs[0]! seen
        else ""
      | .bind _ st c =>
        let a := renderScopedOpt tgts st seen
        let s1 := mergeSlots seen (instrMentionedSlots st)
        let b := renderScopedOpt tgts c s1
        if a.isEmpty then b else if b.isEmpty then a else s!"{a}; {b}"
      | .queueReflexiveTrigger ab =>
        s!"when you do, {renderScopedOpt ab.effect.targets ab.effect.body #[]}"
      | .player (.searchLibrary spec) =>
        if spec.searcher == who && who != .you then
          let s := printSearchLibrary { ctx with capitalize := false } tgts spec seen
          let pfx := s!"{printPlayerRef ctx tgts who seen} searches "
          if s.startsWith pfx then "search " ++ (s.drop pfx.length).copy else s
        else toOracleWith { ctx with capitalize := false } tgts instr seen
      | _ => toOracleWith { ctx with capitalize := false } tgts instr seen
    let base :=
      match cost? with
      | some cs =>
        let costPhrase :=
          match cs.items.toList with
          | [.mana _] => s!"pay {cs.toInlinePhrase}"
          | _ =>
            let s := cs.toInlinePhrase
            if s.startsWith "{" then s!"pay {s}" else s
        let yesS := renderScopedOpt targets onYes seenWho
        if yesS.isEmpty then
          match onNo with
          | .noop => s!"{whoS} may {costPhrase}{timesS}"
          | _ =>
            let dontS := if who == .you then "don't" else "doesn't"
            s!"{whoS} may {costPhrase}{timesS}. If {whoS} {dontS}, {renderScopedOpt targets onNo seenWho}"
        else
          let baseYes := s!"{whoS} may {costPhrase}{timesS}. If {whoS} {doS}, {yesS}"
          match onNo with
          | .noop => baseYes
          | _ => s!"{baseYes}. Otherwise, {renderScopedOpt targets onNo seenWho}"
      | none =>
        let baseYes :=
          match onYes with
          | .seq steps =>
            if steps.size >= 2 then
              let first := toOracleWith { ctx with capitalize := false } targets steps[0]! seenWho
              let seen1 := mergeSlots seenWho (instrMentionedSlots steps[0]!)
              let rest := renderScopedOpt targets (.seq (steps.extract 1 steps.size)) seen1
              if rest.isEmpty then s!"{whoS} may {first}{timesS}"
              else s!"{whoS} may {first}{timesS}. If {whoS} {doS}, {rest}"
            else
              s!"{whoS} may {renderScopedOpt targets onYes seenWho}{timesS}"
          | .bind _ step cont =>
            let first := toOracleWith { ctx with capitalize := false } targets step seenWho
            let seen1 := mergeSlots seenWho (instrMentionedSlots step)
            let rest := renderScopedOpt targets cont seen1
            if rest.isEmpty then s!"{whoS} may {first}{timesS}"
            else s!"{whoS} may {first}{timesS}. If {whoS} {doS}, {rest}"
          | _ =>
            s!"{whoS} may {renderScopedOpt targets onYes seenWho}{timesS}"
        match onNo with
        | .noop => baseYes
        | _ => s!"{baseYes}. Otherwise, {renderScopedOpt targets onNo seenWho}"
    let fullBase := if choosePfx.isEmpty then base else s!"{choosePfx}{capitalizeAscii base}"
    applyCap ctx fullBase
  | .unlessPays payer cost ifUnpaid =>
    let payerS := printPlayerRef ctx targets payer anaphor0
    let uS := toOracleWith { ctx with capitalize := false } targets ifUnpaid anaphor0
    let base := s!"{uS} unless {payerS} pays {cost.toNotation}"
    applyCap ctx base
  | .chooseModes spec =>
    let header :=
      match spec.altCountIf? with
      | some (.castPred (.teamworkPaid .this), _, _) =>
        "Choose one. If this spell was cast using teamwork, choose both instead —"
      | some (.playerPred .you (.controls { zones := .battlefield, pred := .hasSubtype (.literal sub) } (.const 1)), _, _)
      | some (.exists (.inZones { zones := #[.battlefield], .. } (.all #[.hasSubtype (.literal sub), .controlledBy _])), _, _) =>
        s!"Choose one. If you control a {sub}, you may choose two instead —"
      | some (cond, _, .const 2) =>
        s!"Choose one. If {toOracleStr cond { ctx with capitalize := false }}, you may choose two instead —"
      | _ =>
        if spec.minModes == .const 0 && spec.maxModes == .chosenX then
          "Choose up to X —"
        else if spec.unusedThisTurn then
          "Choose one that hasn't been chosen this turn —"
        else if spec.unusedEver then
          "Choose one that hasn't been chosen —"
        else
          match spec.minModes, spec.maxModes with
          | .const 1, .const 1 => "Choose one —"
          | .const 1, .const 2 => "Choose one or both —"
          | .const 2, .const 2 => "Choose two —"
          | .const 0, .eventAmount => "Choose up to that many —"
          | _, _ =>
            s!"Choose {printVal ctx spec.minModes} to {printVal ctx spec.maxModes} —"
    let modeLines := spec.modes.toList.map fun m =>
      let txt := toOracleWith { ctx with capitalize := true } m.targets m.body
      let txt := if txt.endsWith "." then txt else s!"{txt}."
      s!"• {txt}"
    String.intercalate " " (header :: modeLines)
  | .forEach iter _ body =>
    let pref :=
      match iter with
      | .eachPlayer pf => s!"for each {toOracleStr pf { ctx with capitalize := false }}"
      | .eachObject o => s!"for each {printObjRef ctx targets o anaphor0}"
      | .eachTargetSlot => "for each target"
      | .repeatTimes c => s!"repeat {printVal ctx c} times"
    applyCap ctx s!"{pref}, {toOracleWith { ctx with capitalize := false } targets body anaphor0}"
  | .moveZone objs dest verb mods =>
    printMoveZone ctx targets objs dest verb mods anaphor0
  | .create (.tokens who count spec mods) =>
    let n? := printCountInt count
    let tapS := if mods.tapped then "tapped " else ""
    let phrase :=
      match spec with
      | .copyOf ref copyMods =>
        let refS := printObjRef ctx targets ref anaphor0
        let modParts := copyMods.toList.filterMap CopyModification.toOraclePhrase?
        let exceptS :=
          if modParts.isEmpty then ""
          else s!", except {String.intercalate ", " modParts}"
        match n? with
        | some 1 => s!"create a {tapS}token that's a copy of {refS}{exceptS}"
        | some n => s!"create {englishNumber n} {tapS}tokens that are copies of {refS}{exceptS}"
        | none => s!"create {printVal ctx count} {tapS}tokens that are copies of {refS}{exceptS}"
      | _ =>
        match n? with
        | some n => spec.createPhrase n mods.tapped
        | none => s!"create {printVal ctx count} {tapS}{spec.pluralNoun}"
    let enterSfx := printEnterMods ctx targets mods
    let base :=
      match who with
      | .you => s!"{phrase}{enterSfx}"
      | p => s!"{printPlayerRef ctx targets p anaphor0} creates {phrase.drop 7}{enterSfx}"
    applyCap ctx base
  | .create (.emblem who emb) =>
    let parts : List String :=
      (emb.staticAbilities.toList.map fun ab =>
        match ab with
        | .continuous _ _ (.all #[.modifyPT (.const p) (.const t), .grantKeywords ks]) =>
          s!"Creatures you control get {signedStat p}/{signedStat t} and have {KeywordAbility.joinedAnd ks}."
        | .continuous _ _ (.modifyPT (.const p) (.const t)) =>
          s!"Creatures you control get {signedStat p}/{signedStat t}."
        | _ => "static ability") ++
      (emb.triggeredAbilities.toList.map fun ab =>
        s!"{toOracleStr ab.pattern { ctx with capitalize := true }}, {toOracleWith { ctx with capitalize := false } ab.effect.targets ab.effect.body}.") ++
      (emb.activatedAbilities.toList.map fun ab =>
        s!"{ab.cost.toNotation}: {toOracleWith { ctx with capitalize := true } ab.effect.targets ab.effect.body}.")
    let bodyS := if parts.isEmpty then "" else s!" with \"{String.intercalate " " parts}\""
    let whoS := match who with | .you => "you get" | p => s!"{printPlayerRef ctx targets p anaphor0} gets"
    applyCap ctx s!"{whoS} an emblem{bodyS}"
  | .permanent (.setTapped objs tap ch?) =>
    let verb := if tap then "tap" else "untap"
    let base := match ch? with
      | some ch => s!"{verb} {printMoveChoice ctx targets ch} among {printObjRef ctx targets objs anaphor0}"
      | none => s!"{verb} {printObjRef ctx targets objs anaphor0}"
    applyCap ctx base
  | .permanent (.modifyCounters mode objs ch?) =>
    let subj := match ch? with
      | some ch => s!"{printMoveChoice ctx targets ch} among {printObjRef ctx targets objs anaphor0}"
      | none => printEachObj ctx targets objs anaphor0
    let base :=
      match mode with
      | .put k v =>
        match v with
        | .aggregate .count .one (.inZones _ (.all #[.hasType .creature, .controlledBy { relation := .anyPlayer, pred := .matchesExpr (.target i) }])) =>
          s!"put {k.countersPhrase 1} on {subj} for each creature {printPlayerRef ctx targets (.target i) anaphor0} controls"
        | _ =>
          let cntS :=
            match printCountInt v with
            | some n => k.countersPhrase n
            | none => s!"{printVal ctx v} {k.oracleName} counters"
          s!"put {cntS} on {subj}"
      | .remove k? c =>
        let kindS := match k? with | some k => s!"{k.oracleName} " | none => ""
        s!"remove {printExprCount ctx c} {kindS}counter(s) from {subj}"
      | .moveAll fromObj k? =>
        let kindS := match k? with | some k => s!"{k.oracleName} " | none => ""
        s!"move all {kindS}counters from {printObjRef ctx targets fromObj anaphor0} onto {subj}"
      | .moveOne fromObj k =>
        s!"move a {k.oracleName} counter from {printObjRef ctx targets fromObj anaphor0} onto {subj}"
      | .copyFromLki fromObj =>
        s!"put counters matching {printObjRef ctx targets fromObj anaphor0}'s counters on {subj}"
      | .copyMissingKeywords fromObj =>
        s!"put each keyword counter on {subj} for each keyword {printObjRef ctx targets fromObj anaphor0} has"
      | .double k? =>
        let kindS := match k? with | some k => s!"{k.oracleName} " | none => ""
        s!"double the number of {kindS}counters on {subj}"
    applyCap ctx base
  | .permanent (.attach a b chooseFromPool) =>
    let aS := printObjRef ctx targets a anaphor0
    let bS := printObjRef ctx targets b anaphor0
    let base := if chooseFromPool then s!"attach {aS} (chosen) to {bS}" else s!"attach {aS} to {bS}"
    applyCap ctx base
  | .permanent (.transform objs) =>
    applyCap ctx s!"transform {printObjRef ctx targets objs anaphor0}"
  | .permanent (.turnFaceUp objs) =>
    applyCap ctx s!"turn {printObjRef ctx targets objs anaphor0} face up"
  | .permanent (.phaseOut objs untilP?) =>
    let untilS := match untilP? with
      | some p => s!" until {printPossessivePlayer ctx targets p} next turn"
      | none => ""
    applyCap ctx s!"{printObjRef ctx targets objs anaphor0} phases out{untilS}"
  | .permanent (.setDesignation objs tag val) =>
    let subj := printObjRef ctx targets objs anaphor0
    let base :=
      match tag, val with
      | .prepared, true => s!"{subj} becomes prepared"
      | .prepared, false => s!"{subj} becomes unprepared"
      | .harnessed, true => s!"harness {subj}"
      | .harnessed, false => s!"unharness {subj}"
      | .goaded, _ => s!"goad {subj}"
      | .ringBearer, _ => s!"{subj} becomes your Ring-bearer"
    applyCap ctx base
  | .damage (.deal src to amt flags) =>
    let possOf (obj : ObjectExpr) : String :=
      if obj == src then "its" else s!"{printObjRef ctx targets obj anaphor0}'s"
    let amtS :=
      match amt with
      | .objectStat .power obj => s!"damage equal to {possOf obj} power"
      | .binary .mul (.const 2) (.objectStat .power obj) =>
        s!"damage equal to twice {possOf obj} power"
      | .binary .mul (.const k) (.objectStat .power obj) =>
        s!"damage equal to {k} times {possOf obj} power"
      | _ => s!"{printVal ctx amt} damage"
    let divS :=
      if flags.divided then
        let maxT := (targets.dividedDamage?.map Prod.snd).getD (max 1 targets.maxTargetCount)
        s!" divided as you choose among {printDividedAmong maxT}"
      else
        let toS :=
          match to with
          | .targetSlot i =>
            if anaphor0.contains i then "it"
            else printSlotRef targets i (if i == 0 then "any target" else "that target")
          | .objects o => printEachObj ctx targets o anaphor0
          | .players p => printPlayerRef ctx targets p anaphor0
          | .both o p => s!"{printEachObj ctx targets o anaphor0} and {printPlayerRef ctx targets p anaphor0}"
          | .allTargets => if !targets.isEmpty then targets.noun else "those targets"
        s!" to {toS}"
    let cantPrev := if flags.cantBePrevented then ". Damage can't be prevented" else ""
    let base :=
      if src == .this && ctx.selfRef == "this permanent" then
        s!"deals {amtS}{divS}{cantPrev}"
      else
        s!"{printObjRef ctx targets src anaphor0} deals {amtS}{divS}{cantPrev}"
    applyCap ctx base
  | .damage (.fight a b oneWay) =>
    let aS := printObjRef ctx targets a anaphor0
    let bS := printObjRef ctx targets b anaphor0
    let base :=
      if oneWay then s!"{aS} deals damage equal to its power to {bS}"
      else s!"{aS} fights {bS}"
    applyCap ctx base
  | .life (.gain who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"you gain {amtS} life"
      | p => s!"{printPlayerRef ctx targets p anaphor0} gains {amtS} life"
    applyCap ctx base
  | .life (.lose who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"you lose {amtS} life"
      | p => s!"{printPlayerRef ctx targets p anaphor0} loses {amtS} life"
    applyCap ctx base
  | .life (.set who amt) =>
    let amtS := printVal ctx amt
    let base :=
      match who with
      | .you => s!"your life total becomes {amtS}"
      | p => s!"{printPlayerRef ctx targets p anaphor0}'s life total becomes {amtS}"
    applyCap ctx base
  | .player (.drawCards who amt) =>
    let base :=
      match amt with
      | .aggregate .count .one objs =>
        let eachS := toOracleStr objs { ctx with plural := false, capitalize := false }
        match who with
        | .you => s!"draw a card for each {eachS}"
        | p => s!"{printPlayerRef ctx targets p anaphor0} draws a card for each {eachS}"
      | _ =>
        let cardsS := match printCountInt amt with
          | some n => cardPhrase n
          | none => s!"{printVal ctx amt} cards"
        match who with
        | .you => s!"draw {cardsS}"
        | p => s!"{printPlayerRef ctx targets p anaphor0} draws {cardsS}"
    applyCap ctx base
  | .player (.scry who amt) =>
    let base := match who with
      | .you => s!"scry {printVal ctx amt}"
      | p => s!"{printPlayerRef ctx targets p anaphor0} scries {printVal ctx amt}"
    applyCap ctx base
  | .player (.surveil who amt) =>
    let base := match who with
      | .you => s!"surveil {printVal ctx amt}"
      | p => s!"{printPlayerRef ctx targets p anaphor0} surveils {printVal ctx amt}"
    applyCap ctx base
  | .player (.inspectLibrary spec) =>
    printInspectLibrary ctx targets spec
  | .player (.searchLibrary spec) =>
    printSearchLibrary ctx targets spec anaphor0
  | .player (.reveal who objs cnt?) =>
    let cntS := match cnt? with | some c => s!"{printExprCount ctx c} of " | none => ""
    let base := match who with
      | .you => s!"reveal {cntS}{printObjRef ctx targets objs anaphor0}"
      | p => s!"{printPlayerRef ctx targets p anaphor0} reveals {cntS}{printObjRef ctx targets objs anaphor0}"
    applyCap ctx base
  | .player (.shuffle who) =>
    let base := match who with
      | .you => "shuffle"
      | p => s!"{printPlayerRef ctx targets p anaphor0} shuffles"
    applyCap ctx base
  | .player (.addMana _ mp) =>
    mp.toOracleSentence ctx
  | .player (.proliferate _ (.const 1) none) =>
    applyCap ctx "proliferate"
  | .player (.proliferate _ amt tgt?) =>
    let tgtS := match tgt? with | some o => s!" on {printObjRef ctx targets o anaphor0}" | none => ""
    applyCap ctx s!"proliferate {printVal ctx amt} times{tgtS}"
  | .player (.temptWithRing _) =>
    applyCap ctx "the Ring tempts you"
  | .player (.explore objs) =>
    applyCap ctx s!"{printObjRef ctx targets objs anaphor0} explores"
  | .player (.amass who sub amt) =>
    let base := match who with
      | .you => s!"amass {pluralizeName sub.englishName} {printVal ctx amt}"
      | p => s!"{printPlayerRef ctx targets p anaphor0} amasses {pluralizeName sub.englishName} {printVal ctx amt}"
    applyCap ctx base
  | .player (.connive objs) =>
    applyCap ctx s!"{printObjRef ctx targets objs anaphor0} connives"
  | .player (.empowerPlaneswalker sub amt) =>
    applyCap ctx s!"empower {sub.englishName} {printVal ctx amt}"
  | .player (.setStatus who kind cond?) =>
    let condPfx := match cond? with
      | some c => s!"if {toOracleStr c { ctx with capitalize := false }}, "
      | none => ""
    let whoS := printPlayerRef ctx targets who anaphor0
    let base :=
      match kind with
      | .monarch => s!"{condPfx}{whoS} {if who == .you then "become" else "becomes"} the monarch"
      | .winGame => s!"{condPfx}{whoS} {if who == .you then "win" else "wins"} the game"
      | .designation .citysBlessing => s!"{condPfx}{whoS} {if who == .you then "get" else "gets"} the city's blessing for the rest of the game"
      | .designation .enduringStory => s!"{condPfx}{whoS} {if who == .you then "get" else "gets"} enduring story for the rest of the game"
    applyCap ctx base
  | .player (.choose _ .creatureType) => applyCap ctx "choose a creature type"
  | .player (.choose _ .oddOrEven) => applyCap ctx "choose odd or even"
  | .player (.choose _ (.keyword ks)) =>
    let kwNames := ks.toList.map fun k => KeywordAbility.toOracleStr { capitalize := false } k
    applyCap ctx s!"it gains your choice of {String.intercalate " or " kwNames} until end of turn"
  | .player (.choose _ .playerWithMostLife) =>
    applyCap ctx "choose a player with the most life or tied for most life"
  | .turn (.extraTurn who rule?) =>
    let whoS := match who with | .you => "take" | p => s!"{printPlayerRef ctx targets p anaphor0} takes"
    let rS := match rule? with
      | some r => s!" ({printRuleMod ctx targets none r})"
      | none => ""
    applyCap ctx s!"{whoS} an extra turn after this one{rS}"
  | .turn (.extraPhase .combat afterCur) =>
    applyCap ctx s!"{if afterCur then "after this phase, " else ""}there is an additional combat phase"
  | .turn (.extraPhase ph afterCur) =>
    applyCap ctx s!"{if afterCur then "after this phase, " else ""}there is an additional {ph.englishName} phase"
  | .turn (.extraStep st afterCur) =>
    applyCap ctx s!"{if afterCur then "after this step, " else ""}there is an additional {reprStr st} step"
  | .stack (.counterStack objs exileInstead ifPermCastFree) =>
    let exS := if exileInstead then ". If that spell is countered this way, exile it instead of putting it into its owner's graveyard" else ""
    let castS := if ifPermCastFree then ". If it's a permanent card, you may cast it without paying its mana cost" else ""
    applyCap ctx s!"counter {printObjRef ctx targets objs anaphor0}{exS}{castS}"
  | .stack (.copyStackObject objs copies mayRetarget) =>
    let subj := match objs with | .triggerSubject => "that spell" | _ => printObjRef ctx targets objs anaphor0
    let cntS := match printCountInt copies with
      | some 1 => ""
      | some n => s!" {englishNumber n} times"
      | none => s!" {printVal ctx copies} times"
    let retS := if mayRetarget then ". You may choose new targets for the copy" else ""
    applyCap ctx s!"copy {subj}{cntS}{retS}"
  | .stack (.chooseNewTargets objs opt) =>
    let mayS := if opt then "you may " else ""
    applyCap ctx s!"{mayS}choose new targets for {printObjRef ctx targets objs anaphor0}"
  | .stack (.mayCastOrPlay objs perm) =>
    applyCap ctx (printGrantPlayPerm ctx (printObjRef ctx targets objs anaphor0) perm)
  | .installEffect (.applyContinuous dur aff mod) =>
    let isPlural := match aff with | .inZones _ _ | .union _ => true | _ => false
    let subj :=
      if aff == .inZones .battlefield (.hasType .creature) then "all creatures"
      else if isPlural then printObjRef { ctx with plural := true } targets aff anaphor0
      else printObjRef ctx targets aff anaphor0
    let durS := toOracleStr dur { ctx with capitalize := false }
    let durSp := if durS.isEmpty then "" else s!" {durS}"
    let vGet := if isPlural then "get" else "gets"
    let vGain := if isPlural then "gain" else "gains"
    let vLose := if isPlural then "lose" else "loses"
    let vHave := if isPlural then "have" else "has"
    let vBecome := if isPlural then "become" else "becomes"
    let rec renderMod : ContinuousModification → String
      | .modifyPT (.const p) (.const t) => s!"{vGet} {signedStat p}/{signedStat t}"
      | .modifyPT p t => s!"{vGet} +{printVal ctx p}/+{printVal ctx t}"
      | .grantKeywords ks => s!"{vGain} {KeywordAbility.joinedAnd ks}"
      | .loseKeywords ks => s!"{vLose} {KeywordAbility.joinedAnd ks}"
      | .grantActivated abs =>
        let parts := abs.toList.map fun ab =>
          s!"\"{ab.cost.toNotation}: {toOracleWith { ctx with capitalize := true } ab.effect.targets ab.effect.body}.\""
        s!"{vGain} {String.intercalate " and " parts}"
      | .grantTriggered trs =>
        let parts := trs.toList.map fun ab =>
          s!"\"{toOracleStr ab.pattern { ctx with capitalize := true }}, {toOracleWith { ctx with capitalize := false } ab.effect.targets ab.effect.body}.\""
        s!"{vGain} {String.intercalate " and " parts}"
      | .grantStatic sas =>
        let renderGrantedStatic : StaticAbility → String
          | .characteristicDefining (.setPT (some p) (some t)) =>
            if p == t then s!"\"This creature's power and toughness are each equal to {printVal ctx p}.\""
            else s!"\"This creature's power is equal to {printVal ctx p} and its toughness is equal to {printVal ctx t}.\""
          | .characteristicDefining (.setPT (some p) none) =>
            s!"\"This creature's power is equal to {printVal ctx p}.\""
          | .characteristicDefining (.setPT none (some t)) =>
            s!"\"This creature's toughness is equal to {printVal ctx t}.\""
          | .continuous (some .isYourTurn) _ (.grantKeywords ks) =>
            s!"\"During your turn, this creature has {KeywordAbility.joinedAnd ks}.\""
          | .continuous none _ (.modifyPT p t) =>
            if p == t then s!"\"This creature gets +{printVal ctx p}/+{printVal ctx t}.\""
            else s!"\"This creature gets +{printVal ctx p}/+{printVal ctx t}.\""
          | .continuous (some c) _ (.grantKeywords ks) =>
            s!"\"As long as {toOracleStr c { ctx with capitalize := false }}, this creature has {KeywordAbility.joinedAnd ks}.\""
          | _ => "\"static ability\""
        let parts := sas.toList.map renderGrantedStatic
        s!"{vGain} {String.intercalate " and " parts}"
      | .copyActivatedFrom src => s!"{vHave} all activated abilities of {toOracleStr src { ctx with capitalize := false }}"
      | .loseAllAbilities => s!"{vLose} all abilities"
      | .setBasePT (some p) (some t) => s!"{vHave} base power and toughness {printVal ctx p}/{printVal ctx t}"
      | .setBasePT (some p) none => s!"{vHave} base power {printVal ctx p}"
      | .setBasePT none (some t) => s!"{vHave} base toughness {printVal ctx t}"
      | .setBasePT none none => "keeps base power and toughness"
      | .modifyTypes tm => s!"{vBecome} {printTypeSetMod tm}"
      | .addAllCreatureTypes => s!"{vHave} all creature types"
      | .modifyColors cm =>
        let cols := cm.colors.toList.map Color.englishName
        let colStr := if cols.isEmpty then "colorless" else String.intercalate " and " cols
        if cm.mode == .add then s!"{vBecome} {colStr} in addition to its other colors"
        else s!"{vBecome} {colStr}"
      | .gainControl w =>
        match w with
        | .you => s!"gain control of {subj}"
        | p => s!"{printPlayerRef ctx targets p anaphor0} gains control of {subj}"
      | .exchangeControl other => s!"exchange control of {subj} and {printObjRef ctx targets other anaphor0}"
      | .becomeCopyOf src mods =>
        let modParts := mods.toList.filterMap CopyModification.toOraclePhrase?
        let mS := if modParts.isEmpty then "" else s!", except {String.intercalate ", " modParts}"
        s!"{vBecome} a copy of {printObjRef ctx targets src anaphor0}{mS}"
      | .applyRule r => printRuleMod ctx targets (some dur) r
      | .all ms => String.intercalate " and " (ms.toList.map renderMod)
    let base :=
      match dur, mod with
      | .untilEndOfTurn, .all ms =>
        match ms.toList with
        | .modifyTypes tm :: .setBasePT (some p) (some t) :: rest =>
          let sups := tm.supertypes.toList.map Supertype.englishName
          let subs := tm.subtypes.toList.map CardSubtype.englishName
          let tys := tm.types.toList.map CardType.oracleWord
          let words := String.intercalate " " (sups ++ subs ++ tys)
          let tailS :=
            if rest.isEmpty then ""
            else " and " ++ String.intercalate " and " (rest.map renderMod)
          let addS := if tm.mode == .add || tm.mode == .addDedup then " in addition to its other types" else ""
          s!"until end of turn, {subj} {vBecome} {indefinite words} {words} with base power and toughness {printVal ctx p}/{printVal ctx t}{addS}{tailS}"
        | _ => s!"{subj} {renderMod mod}{durSp}"
      | _, .gainControl _ | _, .exchangeControl _ => s!"{renderMod mod}{durSp}"
      | _, .applyRule (.combat (.cantBeBlocked .self)) => s!"{subj} can't be blocked this turn"
      | _, .applyRule (.combat (.cantBlock .self none)) => s!"{subj} can't block this turn"
      | _, .applyRule (.combat (.cantBeBlockedBy .self bp)) =>
        s!"{subj} can't be blocked{durSp} by {toOracleStr bp { ctx with capitalize := false }}"
      | _, .applyRule (.game (.cantBecomeUntapped .self)) =>
        s!"{subj} can't become untapped{durSp}"
      | _, .applyRule (.game (.doesntUntapDuringUntapStep .self none)) =>
        s!"{subj} doesn't untap during its controller's untap step{durSp}"
      | _, _ => s!"{subj} {renderMod mod}{durSp}"
    applyCap ctx base
  | .installEffect (.applyRule dur rule) =>
    let rS := printRuleMod ctx targets (some dur) rule anaphor0
    let seenAfterRule := mergeSlots anaphor0 (ruleModMentionedSlots rule)
    let durS : String :=
      match dur with
      | .untilNextTurnOf p => s!"until {printPossessivePlayer ctx targets p seenAfterRule} next turn"
      | .untilEndOfNextTurnOf p => s!"until the end of {printPossessivePlayer ctx targets p seenAfterRule} next turn"
      | _ => toOracleStr dur { ctx with capitalize := false }
    let base :=
      if durS.isEmpty || rS.contains durS || (dur == .untilEndOfTurn && rS.contains "this turn") ||
          (match rule with | .player (.controlPlayer ..) => true | _ => false) then rS
      else s!"{rS} {durS}"
    applyCap ctx base
  | .installEffect (.applyReplacement dur spec) =>
    let sS := printReplSpec ctx targets spec
    let durS := toOracleStr dur { ctx with capitalize := false }
    let base :=
      if durS.isEmpty || sS.contains durS || (dur == .untilEndOfTurn && sS.contains "this turn") then sS
      else s!"{sS} {durS}"
    applyCap ctx base
  | .installEffect (.createDelayedTrigger spec) =>
    let clauseS := spec.pattern.renderClause { ctx with capitalize := false } spec.grouping
    let patS := s!"{spec.pattern.defaultWord.toOracleStr} {clauseS}"
    let durS := toOracleStr spec.duration { ctx with capitalize := false }
    let effTargets := if spec.effect.targets.isEmpty then targets else spec.effect.targets
    let effAnaphor := if spec.effect.targets.isEmpty then anaphor0 else #[]
    let effS := toOracleWith { ctx with capitalize := false } effTargets spec.effect.body effAnaphor
    let base :=
      if spec.oneShot && clauseS.startsWith "you " then
        let dur := if spec.duration == .untilEndOfTurn then " this turn"
                   else if durS.isEmpty then "" else s!" {durS}"
        s!"when you next {clauseS.drop 4}{dur}, {effS}"
      else if spec.oneShot && spec.pattern == .stepBegins .end (.player .any) then
        s!"at the beginning of the next end step, {effS}"
      else if spec.oneShot && spec.pattern == .stepBegins .upkeep (.player .any) then
        s!"at the beginning of the next upkeep, {effS}"
      else if spec.duration == .untilEndOfTurn then
        s!"until end of turn, {patS}, {effS}"
      else if durS.isEmpty then s!"{patS}, {effS}"
      else s!"{patS} {durS}, {effS}"
    applyCap ctx base
  | .queueReflexiveTrigger ab =>
    let rec renderRefl (tgts : TargetSpec) (instr : Instruction) (seen : Array Nat) : String :=
      match instr with
      | .seq xs =>
        if xs.size >= 2 then
          let parts : List String := Id.run do
            let mut out : List String := []
            let mut s := seen
            for st in xs do
              let str := renderRefl tgts st s
              if !str.isEmpty then out := out ++ [str]
              s := mergeSlots s (instrMentionedSlots st)
            return out
          String.intercalate "; " parts
        else if xs.size == 1 then renderRefl tgts xs[0]! seen
        else ""
      | .bind _ st c =>
        let a := renderRefl tgts st seen
        let s1 := mergeSlots seen (instrMentionedSlots st)
        let b := renderRefl tgts c s1
        if a.isEmpty then b else if b.isEmpty then a else s!"{a}; {b}"
      | _ => toOracleWith { ctx with capitalize := false } tgts instr seen
    let effS := renderRefl ab.effect.targets ab.effect.body #[]
    applyCap ctx s!"when you do, {effS}"

/-- Canonical Oracle rendering of an `Instruction` with an optional single-target noun. -/
def toOracle (ctx : PrintCtx) (noun : String := "") (i : Instruction) : String :=
  if noun.isEmpty then toOracleWith ctx .none i
  else
    -- Backward-compatible helper when a caller only supplies a plain noun string.
    let s := toOracleWith ctx .none i
    s.replace "target permanent" noun

instance : ToOracle Instruction where
  toOracle ctx i := Instruction.toOracleWith ctx .none i

end Instruction

/-! ### Unified `Effect` Operations & Pure Agent Classification -/

namespace Effect

/-- Whom this effect may target (CR 115.1 / 601.2c). -/
def targetSpec (e : Effect) : TargetSpec :=
  e.targets

/-- Effective targeting specification (CR 115.1c / 601.2c). -/
def effectiveTargetSpec (e : Effect) : TargetSpec :=
  e.targets

/-- How many targets must be announced (CR 601.2c). -/
def targetCount (e : Effect) : Nat :=
  e.targets.targetCount

/-- True when announcing this effect requires choosing a target. -/
def requiresTarget (e : Effect) : Bool :=
  !e.targets.isEmpty

/-- True when every target slot allows choosing zero targets (CR 115.1c). -/
def allowsZeroTargets (e : Effect) : Bool :=
  e.targets.allowsZero

/-- Upper bound on announced targets across all slots. -/
def maxTargetCount (e : Effect) : Nat :=
  e.targets.maxTargetCount

/-- Divided-damage `(amount, maxTargets)` carried on `e.targets`, if any (CR 601.2d). -/
def dividedDamage? (e : Effect) : Option (Nat × Nat) :=
  e.targets.dividedDamage?

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

private partial def beneficialHint : Instruction → Option TargetPreference
  | .installEffect (.applyContinuous _ (.target 0) mod) =>
    match mod with
    | .modifyPT (.const p) (.const t) =>
      if p >= 0 && t >= 0 && (p > 0 || t > 0) then some .own else none
    | .grantKeywords _ => some .own
    | .applyRule (.combat (.cantBeBlocked _)) => some .own
    | _ => none
  | .permanent (.modifyCounters (.put .plusOnePlusOne _) (.target 0) _) => some .own
  | .player (.drawCards (.target 0) _) => some .selfPlayer
  | .life (.gain (.target 0) _) => some .selfPlayer
  | .seq steps =>
    match steps[0]? with
    | some s0 => beneficialHint s0
    | none => none
  | _ => none

/-- Pure structural targeting preference computed from `(e.targets, e.body)` for the
demonstration agent. -/
def targetPreference (e : Effect) : TargetPreference :=
  let spec := e.targets
  if spec.isEmpty then .own
  else (beneficialHint e.body).getD spec.defaultPreference

/-- Helper: true when `spec` is a single slot targeting a creature with power ≥ N. -/
private def isCreaturePowerAtLeastSpec (spec : TargetSpec) : Bool :=
  match spec.slots.toList with
  | [{ domain := .object zs (.all #[.hasType .creature, .stat .power .ge _]), count := .exact 1, .. }] =>
    zs == .battlefield
  | _ => false

/-- Pure structural default-mode hint for modal spells. Prefers targeted removal modes
such as destroy-flying, destroy-big-creature, destroy-and-lose-life, or
negative-P/T-and-exile. -/
def isPreferredDefaultMode (e : Effect) : Bool :=
  match e.body with
  | .moveZone (.target 0) .graveyard .destroy _ =>
    e.targets == .creatureWithFlying || isCreaturePowerAtLeastSpec e.targets
  | .seq #[.moveZone (.target 0) .graveyard .destroy _, .life (.lose (.controllerOf (.target 0)) _)] =>
    true
  | .seq #[.installEffect (.applyContinuous _ (.target 0) (.modifyPT (.const p) (.const t))),
           .installEffect (.applyReplacement _ (.exileInsteadOfDying _ _))] =>
    p < 0 || t < 0
  | _ => false

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
  classifyInstr e.targets e.body
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
  classifyInstr e.targets e.body
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

/-- Canonical Oracle rendering of an `Effect` (computed purely from `targets` and `body`). -/
def toOracle (ctx : PrintCtx) (e : Effect) : String :=
  match e.targets.slots.toList with
  | [slot] =>
    match slot.forEach? with
    | some pf =>
      let who :=
        if pf == PlayerFilter.opponent then "each opponent"
        else if pf == PlayerFilter.any then "each player"
        else s!"each {ToOracle.toOracle { ctx with capitalize := false } pf}"
      let innerDom :=
        if pf == PlayerFilter.opponent then slot.domain.substituteOpponent .thatPlayer
        else slot.domain
      let innerTargets : TargetSpec := {
        e.targets with slots := #[{ slot with domain := innerDom, forEach? := none }]
      }
      let bodyS := Instruction.toOracleWith { ctx with capitalize := false } innerTargets e.body
      let full := s!"for {who}, {bodyS}"
      if ctx.capitalize then capitalizeAscii full else full
    | none => Instruction.toOracleWith ctx e.targets e.body
  | _ => Instruction.toOracleWith ctx e.targets e.body

/-- Canonical Oracle-style text for this effect. -/
def toNotation (e : Effect) : String :=
  e.toOracle {}

instance : ToOracle Effect where
  toOracle := toOracle

instance : HasTargeting Effect where
  targetSpec e := e.targets

instance : ToString Effect where
  toString := toNotation

/-! ### Core Generic Effect Constructors (Card / Game / Catalog) -/

/-- Build a spell-shaped `Effect` from targeting and unified `Instruction` body. -/
def mkSpell (targets : TargetSpec) (body : Instruction) : Effect :=
  { targets, body }

/-- Build an activated-ability `Effect` from targeting and unified `Instruction` body. -/
def mkAbility (targets : TargetSpec) (body : Instruction) : Effect :=
  { targets, body }

/-- True when `i` references `.costPaidObjects` anywhere inside its expressions. -/
def usesCostPaidObjects (i : Instruction) : Bool :=
  instrHasCostPaid i
where
  objHasCostPaid : ObjectExpr → Bool
    | .costPaidObjects => true
    | .filter o _ | .targetsOf o | .linkedExile o | .extremum _ _ o => objHasCostPaid o
    | .union xs => xs.attach.any fun ⟨x, _⟩ => objHasCostPaid x
    | .diff a b => objHasCostPaid a || objHasCostPaid b
    | _ => false
  valHasCostPaid : ValueExpr → Bool
    | .objectStat _ o | .counterCount _ o | .manaSpent o | .colorCountAmong o | .aggregate _ _ o =>
      objHasCostPaid o
    | .binary _ a b => valHasCostPaid a || valHasCostPaid b
    | _ => false
  instrHasCostPaid : Instruction → Bool
    | .player (.drawCards _ v) | .player (.scry _ v) | .player (.surveil _ v) => valHasCostPaid v
    | .life (.gain _ v) | .life (.lose _ v) | .life (.set _ v) => valHasCostPaid v
    | .damage (.deal s _ v _) => objHasCostPaid s || valHasCostPaid v
    | .moveZone o _ _ _ => objHasCostPaid o
    | .seq xs => xs.attach.any fun ⟨x, _⟩ => instrHasCostPaid x
    | .bind _ a b => instrHasCostPaid a || instrHasCostPaid b
    | .ifCond _ a b | .optional _ _ a b _ => instrHasCostPaid a || instrHasCostPaid b
    | .forEach _ _ b => instrHasCostPaid b
    | _ => false

def dealDamage (amount : Nat) : Effect :=
  mkSpell .anyTarget (Instruction.dealDamageFixed (.targetSlot 0) amount)

def pump (power toughness : Int) : Effect :=
  mkSpell .creature (Instruction.pumpFixed (.target 0) power toughness)

def dealDamageToCreature (amount : Nat) : Effect :=
  mkSpell .creature (Instruction.dealDamageFixed (.targetSlot 0) amount)

def draw (n : Nat) : Effect :=
  mkSpell .none (Instruction.drawFixed n)

def gainLife (n : Nat) : Effect :=
  mkAbility .none (Instruction.gainLifeFixed n)

def abilityDraw (n : Nat) : Effect :=
  mkAbility .none (Instruction.drawFixed n)

def searchBasicLandTapped : Effect :=
  mkAbility .none
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := .all #[.hasSupertype .basic, .hasType .land]
      count := .upTo (.const 1)
      dest := .battlefield .controller
      mods := { tapped := true }
      reveal := false
      shuffle := true
    }))

def searchLandTypeFilter (landType : String) : ObjectPred :=
  if landType == "Basic land" || landType == "basic land" then
    .all #[.hasSupertype .basic, .hasType .land]
  else
    match Supertype.ofOracle? landType with
    | some sup => .hasSupertype sup
    | none =>
      match CardType.ofOracle? landType with
      | some ty => .hasType ty
      | none => .hasSubtype (.literal (CardSubtype.ofOracleD landType))

def searchLandTypeToHand (landType : String) : Effect :=
  mkAbility .none
    (.player (.searchLibrary {
      zones := .libraryOf .you
      filter := searchLandTypeFilter landType
      count := .upTo (.const 1)
      dest := .hand .controller
      reveal := true
      shuffle := true
    }))

def attachToTargetCreatureYouControl : Effect :=
  mkAbility .creatureYouControl (.permanent (.attach .this (.target 0)))

def equipEffect (subtype : Option CardSubtype := none) (worthy : Bool := false) : Effect :=
  let spec : TargetSpec :=
    if worthy then .worthyCreatureYouControl
    else match subtype with
      | some s => .creatureYouControlSubtype s
      | none => .creatureYouControl
  mkAbility spec (.permanent (.attach .this (.target 0)))

def sourceGets (power toughness : Int) : Effect :=
  mkAbility .none (Instruction.pumpFixed .this power toughness)

def putPlusOnePlusOneOnSource (n : Nat) : Effect :=
  mkAbility .none (Instruction.putPlusOne .this n)

def targetCantBeBlockedThisTurn : Effect :=
  mkAbility .creature (Instruction.cantBeBlocked (.target 0))

def plusOneX : Effect :=
  mkAbility .none (Instruction.putCounters .this .plusOnePlusOne .chosenX)

def triggerCreateTokens (kind : TokenSpec) (n : Nat) (tapped : Bool := false) : Effect :=
  { body := Instruction.createTokensFixed kind n .you tapped }

def triggerGainLife (n : Nat) : Effect :=
  { body := Instruction.gainLifeFixed n }

def triggerCascade : Effect :=
  let cheaperNonland : ObjectPred :=
    .all #[.not (.hasType .land), .stat .manaValue .lt (.objectStat .manaValue .this)]
  { body := .bind ⟨0⟩ (.player (.inspectLibrary {
        source := .revealUntil .you cheaperNonland (.const 1) (exileWhileRevealing := true)
        action := .none
        rest := .leaveInPlace
      }))
      (.seq #[
        .stack (.mayCastOrPlay (.filter (.stepObjects ⟨0⟩) cheaperNonland) {
          freeCast := true, landsAllowed := false, castNow := true
          maxTotalManaValue? := some (.binary .sub (.objectStat .manaValue .this) (.const 1))
        }),
        .moveZone (.stepObjects ⟨0⟩) (.library .owner .bottomRandom) .put
      ]) }

end Effect

end Mtg.Engine
