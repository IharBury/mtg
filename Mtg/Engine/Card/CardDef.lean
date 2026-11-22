import Mtg.Engine.Card.KeywordExpand

/-!
# Card definitions (CR 108, 109.3, section 2)

Printed Oracle characteristics: `CardDef`, the `AdventureFace` of
adventurer cards, and per-card mana-ability storage.
-/

namespace Mtg.Engine

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
structure AdventureFace where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[.sorcery]
  subtypes : Array Subtype := #["Adventure"]
  spellEffect : Option Effect := none
  /-- Additional casting costs on this Adventure face (CR 118.8 / 601.2b,h). -/
  additionalCosts : Array AdditionalCostSpec := #[]
  /-- Rules lines of this face that are not a modeled spell effect. -/
  extraLines : Array String := #[]
deriving Repr, Inhabited, BEq

set_option maxRecDepth 1024 in
/-- Printed (Oracle) characteristics of a card. -/
structure CardDef where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  power : Option Int := none
  toughness : Option Int := none
  /-- Printed power includes a star added to `power` (CR 208.2).
  A bare `*` leaves `power` empty. `1+*` and `*+1` are `some 1`.
  When that star can't be determined it counts as 0, so the power is
  `power.getD 0`: `*` is 0 and `1+*` is 1 (CR 208.2a). -/
  powerStar : Bool := false
  /-- Printed toughness includes a star added to `toughness` (CR 208.2).
  See `powerStar`. -/
  toughnessStar : Bool := false
  /-- Printed loyalty number (CR 209.1). While this planeswalker is not on
  the battlefield, its loyalty is this number. It enters the battlefield
  with that many loyalty counters. -/
  loyalty : Option Int := none
  /-- Printed defense number (CR 210.1). While this battle is not on
  the battlefield, its defense is this number. It enters the battlefield
  with that many defense counters. -/
  defense : Option Nat := none
  /-- Printed hand modifier (CR 211.1). The lower-left corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting hand size and maximum hand size. -/
  handModifier : Option Int := none
  /-- Printed life modifier (CR 212.1). The lower-right corner of a vanguard:
  a number preceded by a plus sign, a number preceded by a minus sign, or
  zero. It modifies its owner's starting life total. -/
  lifeModifier : Option Int := none
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  /-- Parameterized CR 702 keyword abilities, retaining multiplicity for
  cumulative keywords (Prowess, Cascade, Ward, Toxic, Affinity, Exalted). -/
  keywords : Array KeywordAbility := #[]
  spellEffect : Option Effect := none
  /-- Additional casting costs on this card (CR 118.8 / 601.2b,f,h). -/
  additionalCosts : Array AdditionalCostSpec := #[]
  /-- Transitional modal spell modes (CR 700.2; Phase-8 modal spells store their
  `ModalSpec` directly in `spellEffect.body` as `.chooseModes`, and `CardDef.modalSpec?`
  prefers `spellEffect` with fallback to `spellModes`). -/
  spellModes : Array Effect := #[]
  /-- This object is a token (CR 111). -/
  isToken : Bool := false
  /-- A deck can have any number of cards with this name (CR 100.2a). -/
  anyNumberInDeck : Bool := false
  /-- Printed activated abilities (CR 602), including mana abilities (CR 605.1a)
  and loyalty abilities (CR 606.2). Basic-land intrinsic mana abilities are
  synthesized from Layer 4 basic land types per CR 305.6. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Printed stratified static abilities (CR 604 / 613 / 614–616 / 303.4a). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603), including Saga chapter abilities (CR 714.2)
  and modal triggered abilities (carrying their modes in `effect.body` via
  `Instruction.chooseModes`). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
  /-- Back face of a modal double-faced card that can transform. -/
  otherFace : Option CardDef := none
  /-- Sorcery or instant copied while this permanent is prepared. -/
  prepareFace : Option AdventureFace := none
deriving Repr, Inhabited

namespace CardDef

/-- Append one `KeywordAbility` onto `c.keywords`, preserving cumulative multiplicity. -/
def withKeyword (c : CardDef) (k : KeywordAbility) : CardDef :=
  { c with keywords := KeywordAbility.add c.keywords k }

/-- Merge `ks` onto `c.keywords`, preserving cumulative multiplicity. -/
def withKeywords (c : CardDef) (ks : Array KeywordAbility) : CardDef :=
  { c with keywords := KeywordAbility.merge c.keywords ks }

/-- Pure CR 702.1 expansion of all printed keywords on `c`. -/
def expandedKeywords (c : CardDef) : ExpandedKeyword :=
  KeywordAbility.expandAll c.keywords

/-- True when `c.keywords` contains `.simple s`. -/
@[inline] def hasSimpleKeyword (c : CardDef) (s : SimpleKeyword) : Bool :=
  KeywordAbility.hasSimple c.keywords s

/-- Printed prowess count on `c` (CR 702.108b). -/
def prowessCount (c : CardDef) : Nat :=
  KeywordAbility.prowessCount c.keywords

/-- Printed cascade count on `c` (CR 702.85). -/
def cascadeCount (c : CardDef) : Nat :=
  KeywordAbility.cascadeCount c.keywords

/-- Printed ward `CostSpec`s on `c`, preserving multiplicity (CR 702.21b). -/
def wardCosts (c : CardDef) : Array CostSpec :=
  KeywordAbility.wardCosts c.keywords

/-- Printed Gift variant on `c`, if any (CR 702.174d–i). -/
def giftKind? (c : CardDef) : Option GiftKind :=
  c.keywords.findSome? fun | .gift kind => some kind | _ => none

/-- True when `c` has a Gift keyword ability (CR 702.174). -/
def hasGift (c : CardDef) : Bool :=
  c.giftKind?.isSome

/-- Printed Kicker `CostSpec`, if any (CR 702.33). -/
def kickerCost? (c : CardDef) : Option CostSpec :=
  c.keywords.findSome? fun | .kicker cost => some cost | _ => none

/-- Printed Kicker mana cost, if any (CR 702.33). -/
def kicker (c : CardDef) : Option ManaCost :=
  c.kickerCost?.map CostSpec.manaCost

/-- Printed Teamwork power threshold, if any (CR 702.194). -/
def teamwork (c : CardDef) : Option Nat :=
  c.keywords.findSome? fun | .teamwork n => some n | _ => none

/-- Printed Flashback `CostSpec`, if any (CR 702.34). -/
def flashbackCost? (c : CardDef) : Option CostSpec :=
  c.keywords.findSome? fun | .flashback cost => some cost | _ => none

/-- Printed Flashback mana cost, if any (CR 702.34). -/
def flashback (c : CardDef) : Option ManaCost :=
  c.flashbackCost?.map CostSpec.manaCost

/-- True when Flashback on `c` also requires discarding a card (CR 702.34a). -/
def flashbackDiscard (c : CardDef) : Bool :=
  match c.flashbackCost? with
  | some cs => cs.items.any fun | .discard _ _ => true | _ => false
  | none => false

/-- Printed Crew power threshold, if any (CR 702.122). -/
def crew (c : CardDef) : Option Nat :=
  c.keywords.findSome? fun | .crew n => some n | _ => none

/-- Printed Affinity filters on `c` (CR 702.41). -/
def affinityFilters (c : CardDef) : Array ObjectFilter :=
  c.keywords.filterMap fun | .affinity f => some f | _ => none

/-- Printed Affinity subtype (for subtype-based Affinity, CR 702.41). -/
def affinityForSubtype (c : CardDef) : Option CardSubtype :=
  c.keywords.findSome? fun
    | .affinity f =>
      match f.pred with
      | .hasSubtype (.literal sub) => some sub
      | .all ps =>
        ps.findSome? fun
          | .hasSubtype (.literal sub) => some sub
          | _ => none
      | _ => none
    | _ => none

/-- True when `c` has Daybound (CR 702.145). -/
def daybound (c : CardDef) : Bool :=
  KeywordAbility.hasDaybound c.keywords

/-- Printed Morph turn-face-up `CostSpec`, if any (CR 702.37e). -/
def morphCost? (c : CardDef) : Option CostSpec :=
  c.keywords.findSome? fun | .morph cost => some cost | _ => none

/-- Printed Morph turn-face-up mana cost, if any (CR 702.37e). -/
def morph (c : CardDef) : Option ManaCost :=
  c.morphCost?.map CostSpec.manaCost

/-- Printed Impending `(counters, CostSpec)`, if any (CR 702.176). -/
def impendingSpec? (c : CardDef) : Option (Nat × CostSpec) :=
  c.keywords.findSome? fun | .impending n cost => some (n, cost) | _ => none

/-- Printed Impending `(counters, ManaCost)`, if any (CR 702.176). -/
def impending (c : CardDef) : Option (Nat × ManaCost) :=
  c.impendingSpec?.map fun (n, cs) => (n, cs.manaCost)

/-- Printed Protection qualities on `c` (CR 702.16). -/
def protectionQualities (c : CardDef) : Array ProtectionQuality :=
  c.keywords.filterMap fun | .protection q => some q | _ => none

/-- Colors `c` has printed protection from (CR 702.16). -/
def protectionFromColors (c : CardDef) : Array Color :=
  c.keywords.filterMap fun
    | .protection (.color (.literal col)) => some col
    | _ => none

/-- Printed bare Cycling `CostSpec`, if any (CR 702.29a). -/
def cyclingCost? (c : CardDef) : Option CostSpec :=
  c.keywords.findSome? fun | .cycling none cost => some cost | _ => none

/-- Printed bare Cycling mana cost, if any (CR 702.29a). -/
def cycling (c : CardDef) : Option ManaCost :=
  c.cyclingCost?.map CostSpec.manaCost

/-- Printed Toxic total on `c` (CR 702.164b). -/
def toxic (c : CardDef) : Nat :=
  KeywordAbility.toxicTotal c.keywords

/-- Mandatory additional costs on `c` (CR 118.8 / 601.2b,h). -/
def mandatoryAdditionalCosts (c : CardDef) : Array CostSpec :=
  c.additionalCosts.filterMap fun a => if a.optional then none else some a.cost

/-- If `c` has a mandatory non-choice single-object sacrifice additional cost,
return the predicate matching legal permanents to sacrifice. -/
def mandatorySacrificeFilter? (c : CardDef) : Option ObjectPred :=
  c.mandatoryAdditionalCosts.findSome? fun cs =>
    cs.items.findSome? fun
      | .sacrifice _ (.filter pred) => some pred
      | _ => none

/-- If `c` has a mandatory choice additional cost (`"A or B"` announced at CR 601.2b),
return its branches. -/
def additionalChoiceCost? (c : CardDef) : Option (Array CostSpec) :=
  c.mandatoryAdditionalCosts.findSome? fun cs =>
    cs.items.findSome? fun
      | .or choices => some choices
      | _ => none

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

/-- Commander color identity of this face: mana cost, color indicator, and
basic land types (CR 903.4). Does not look at the other face. -/
def faceColorIdentity (c : CardDef) : ColorSet :=
  let fromCost :=
    match c.colorIndicator with
    | some cs => c.manaCost.colors.union cs
    | none => c.manaCost.colors
  c.subtypes.foldl (fun acc s =>
    match manaForBasicLandType s with
    | some col => acc.insert col
    | none => acc) fromCost

/-- Combined color identity of both faces of a DFC (CR 903.4 / MSH 18). -/
def colorIdentity (c : CardDef) : ColorSet :=
  match c.otherFace with
  | none => c.faceColorIdentity
  | some back => c.faceColorIdentity.union back.faceColorIdentity

/-- True when `t` is among this card's types. -/
def hasType (c : CardDef) (t : CardType) : Bool := c.types.any (· == t)

/-- True when `s` is among this card's subtypes, including CR 702.73a changeling
expansion for creature and kindred cards. -/
def hasSubtype (c : CardDef) (s : CardSubtype) : Bool :=
  c.subtypes.any (· == s.englishName) ||
    (KeywordAbility.hasChangeling c.keywords && (c.hasType .creature || c.hasType .kindred) && !s.isNoncreature)

/-- True when `s` is among this card's supertypes. -/
def hasSupertype (c : CardDef) (s : Supertype) : Bool := c.supertypes.any (· == s)

def isLand (c : CardDef) : Bool := c.hasType .land
def isCreature (c : CardDef) : Bool := c.hasType .creature
def isArtifact (c : CardDef) : Bool := c.hasType .artifact
def isInstant (c : CardDef) : Bool := c.hasType .instant
def isSorcery (c : CardDef) : Bool := c.hasType .sorcery
def isInstantOrSorcery (c : CardDef) : Bool := c.types.any CardType.isInstantOrSorcery
def isEnchantment (c : CardDef) : Bool := c.hasType .enchantment
def isPlaneswalker (c : CardDef) : Bool := c.hasType .planeswalker
def isBattle (c : CardDef) : Bool := c.hasType .battle
def isVanguard (c : CardDef) : Bool := c.hasType .vanguard
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype .aura
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype .equipment

/-- Names a player may choose for “choose a card name”, including an
Adventure face (Gatherer ruling on adventurer cards). -/
def choosableNames (c : CardDef) : Array String :=
  match c.adventure with
  | some adv => #[c.name, adv.name]
  | none => #[c.name]

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !KeywordAbility.hasFlash c.keywords

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || KeywordAbility.hasFlash c.keywords

/-- Extract a fixed Empower Planeswalker count from an `Instruction` tree, if any.
Only inspects top-level instructions and `.seq` steps (not modes inside `.chooseModes`). -/
def extractEmpowerAmount : Instruction → Option Nat
  | .player (.empowerPlaneswalker _ (.const n)) => if n > 0 then some n.toNat else none
  | .seq steps => steps.attach.foldl (fun acc ⟨s, _⟩ => acc <|> extractEmpowerAmount s) none
  | _ => none

/-- Unified `ModalSpec` for a modal spell (CR 700.2). Prefers `spellEffect`'s
`.chooseModes` instruction and falls back to transitional `spellModes`. -/
def modalSpec? (c : CardDef) : Option ModalSpec :=
  match c.spellEffect.bind (·.modalSpec?) with
  | some ms => some ms
  | none => if c.spellModes.isEmpty then none else some { modes := c.spellModes }

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  c.modalSpec?.isSome

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array Effect :=
  match c.modalSpec? with
  | some ms => ms.modes
  | none => #[]

/-- Fixed Empower Planeswalker amount carried directly on `c.spellEffect`, if any. -/
def empowerPlaneswalkerAmount? (c : CardDef) : Option Nat :=
  c.spellEffect.bind (fun e => extractEmpowerAmount e.body)

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.isAura ||
  match c.modalSpec? with
  | some ms => !ms.modes.isEmpty && ms.modes.all (·.requiresTarget)
  | none =>
    match c.spellEffect with
    | some e => e.requiresTarget
    | none => false

/-- True when the printed spell may be announced with zero targets. -/
def allowsZeroTargets (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.allowsZeroTargets
  | none => false

/-- True when the printed effect is classified as `k`. -/
def hasCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellEffect.any (fun e => e.castKind == k)

/-- True when a modal mode is classified as `k`. -/
def hasModeCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.modes.any (fun e => e.castKind == k)

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- Mana types produced by activated abilities gated on this land entering this
turn or controlling a basic land (MSH conditional dual lands). -/
def enteredOrBasicAddMana (c : CardDef) : Array ManaType :=
  c.activatedAbilities.foldl (fun acc ab =>
    if ab.condition? == some ActivatedAbility.condEnteredThisTurnOrControlBasicLand then
      match ab.manaProduction? with
      | some mp => acc ++ mp.spec.staticPossibleTypes
      | none => acc
    else acc) #[]

/-- True when a `{T}: Add` ability requires this land entered this turn or
a basic land you control. -/
def requiresEnteredOrBasicAdd (c : CardDef) : Bool :=
  c.activatedAbilities.any (fun ab =>
    ab.condition? == some ActivatedAbility.condEnteredThisTurnOrControlBasicLand)

/-- All mana types this card's intrinsic basic-land types and printed activated
mana abilities can statically produce (CR 305.6 / 605.1a). -/
def manaAbilities (c : CardDef) : Array ManaType :=
  let basic := if c.isLand then c.basicLandMana.map ManaType.colored else #[]
  let fromActivated := c.activatedAbilities.foldl (fun acc ab =>
    match ab.manaProduction? with
    | some mp => acc ++ mp.spec.staticPossibleTypes
    | none => acc) #[]
  (basic ++ fromActivated).foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]

/-- Lowercase ASCII for comparing Oracle keyword lines to `KeywordAbility.toOracleList`. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- Drop a trailing Oracle reminder parenthetical, e.g. `Menace (This creature...)`. -/
def stripReminderParenthetical (s : String) : String :=
  match s.splitOn "(" with
  | [] => s
  | head :: _ => head.trimAscii.copy

/-- True when `line` restates modeled keywords, e.g. `Haste` or `Reach, deathtouch`.
A line that is only a parenthetical (e.g. basic-land `{T}: Add` reminder text)
is not a keyword restatement. -/
def isKeywordRestatement (k : Array KeywordAbility) (line : String) : Bool :=
  let kw := KeywordAbility.toOracleList k
  let cleaned := stripReminderParenthetical ((line.replace "." "").trimAscii.copy)
  if cleaned.isEmpty then false
  else
    let parts := cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
    !parts.isEmpty && parts.all (fun p => kw.any (fun w => w == lowerAscii p))

/-- Gatherer delimiter between an adventurer card's primary and Adventure faces. -/
def isAdventureDelimiter (line : String) : Bool :=
  line == "//ADV//" || line.startsWith "//ADV//"

/-- Drop a leading `//ADV//` marker. The remainder (Adventure name and mana
cost) is kept so leftover Oracle text does not lose printed mana symbols. -/
def stripAdventureDelimiter (line : String) : Option String :=
  if line == "//ADV//" then none
  else if line.startsWith "//ADV//" then
    let rest := (line.drop "//ADV//".length).trimAscii.copy
    if rest.isEmpty then none else some rest
  else some line

/-- `({T}: Add {R}.)` for each basic land type on a land (CR 305.6). -/
def basicLandReminderLines (c : CardDef) : List String :=
  if !c.isLand then []
  else c.basicLandMana.toList.map fun col => s!"(\{T}: Add \{{col.letter}}.)"

/-- Render an `AdventureFace` / prepare spell's effect and any folded Empower Jace line. -/
private def faceSpellLines (a : AdventureFace) : List String :=
  let effLines :=
    match a.spellEffect with
    | some e => if e.phrase.isEmpty then [] else [e.phrase]
    | none => []
  let empLines :=
    match a.spellEffect.bind (fun e => extractEmpowerAmount e.body) with
    | some n =>
      let already := a.spellEffect.any fun e => (lowerAscii e.phrase).contains "empower jace"
      if already then [] else [s!"Empower Jace {n}."]
    | none => []
  effLines ++ empLines

/-- Adventure name, cost, and spell, without the Gatherer `//ADV//` marker. -/
def adventureLines (c : CardDef) : List String :=
  match c.adventure with
  | none => []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    let extra :=
      a.additionalCosts.toList.map AdditionalCostSpec.toOracleLine ++ faceSpellLines a
    header :: extra ++ a.extraLines.toList

/-- Prepare-spell name, cost, and effect (`"This creature enters prepared."` is
rendered directly from `staticAbilities`). -/
def prepareLines (c : CardDef) : List String :=
  match c.prepareFace with
  | none => []
  | some a =>
    let header :=
      if a.manaCost.symbols.isEmpty then a.name else s!"{a.name} {a.manaCost}"
    [header] ++ faceSpellLines a ++ a.extraLines.toList

/-- Empower Jace printed on this spell when not already present in `spellEffect.phrase`. -/
def empowerLines (c : CardDef) : List String :=
  match c.empowerPlaneswalkerAmount? with
  | some n =>
    let alreadyInPhrase := c.spellEffect.any fun e => (lowerAscii e.phrase).contains "empower jace"
    if alreadyInPhrase then [] else [s!"Empower Jace {n}."]
  | none => []

/-- True when CR 601.2b must announce a choice additional cost (e.g. sacrifice-or-pay,
discard-or-pay, behold-or-pay). -/
def announcesAdditionalCost (c : CardDef) : Bool :=
  c.additionalChoiceCost?.isSome

/-- Additional cost lines printed on `c`. -/
def additionalCostLines (c : CardDef) : List String :=
  c.additionalCosts.toList.map AdditionalCostSpec.toOracleLine

/-- `{T}cycling` and other typecycling, printed as `Mountaincycling {1}`. -/
def activatedNotation (ab : ActivatedAbility) : String :=
  if ab.isFromHand && ab.cost.discardSource then
    match ab.tag? with
    | some (.cycling (some t)) =>
      if t == "Plan" then ab.toNotation else s!"{t}cycling {ab.cost.mana}"
    | _ =>
      match ab.effect.body with
      | .player (.searchLibrary spec) =>
        match spec.filter with
        | .hasSubtype (.literal sub) =>
          if sub.englishName == "Plan" then ab.toNotation else s!"{sub}cycling {ab.cost.mana}"
        | .all #[.hasSupertype .basic, .hasType .land] => s!"Basic landcycling {ab.cost.mana}"
        | _ => ab.toNotation
      | _ => ab.toNotation
  else
    ab.toNotation

/-- Modal header string matching `parseModes` for round-trip Oracle rendering. -/
def modalHeader (ms : ModalSpec) : String :=
  match ms.altCountIf? with
  | some (.castPred (.teamworkPaid .this), _, _) =>
    "Choose one. If this spell was cast using teamwork, choose both instead —"
  | some (.playerPred .you (.controls { zones := .battlefield, pred := .hasSubtype (.literal sub) } (.const 1)), _, _) =>
    s!"Choose one. If you control a {sub}, you may choose two instead —"
  | _ =>
    if ms.minModes == .const 1 && ms.maxModes == .const 2 then
      "Choose one or both —"
    else
      "Choose one —"

/-- Spell effect, or `Choose one —` when the spell is modal. -/
def spellLines (c : CardDef) : List String :=
  match c.modalSpec? with
  | some ms =>
    [s!"{modalHeader ms} • {String.intercalate " • " (ms.modes.toList.map Effect.toNotation)}"]
  | none =>
    match c.spellEffect with
    | some e =>
      let note := Effect.toNotation e
      if note.isEmpty then [] else [note]
    | none => []

/-- Oracle line for a triggered ability; Saga chapter triggers render with
their printed Roman numeral chapter header so `renderFullOracle` round-trips
through `parseChapterHeader`. -/
def triggeredNotation (ab : TriggeredAbility) : String :=
  match ab.chapterNumbers? with
  | some ns =>
    let body := ab.effect.phrase.trimAscii.copy
    let body := if body.endsWith "." then body else s!"{body}."
    s!"{formatChapterRoman ns} — {capitalizeAscii body}"
  | none => ab.toNotation

/-- Basic-land reminders, additional costs, activated (including mana), static,
triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.basicLandReminderLines ++
  c.additionalCostLines ++
  c.activatedAbilities.toList.map activatedNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map triggeredNotation ++
  c.adventureLines ++
  c.prepareLines ++
  c.empowerLines ++
  c.spellLines

/-- Modeled ability lines. Keyword-only lines are omitted; those print with
`KeywordAbility`. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.structuredAbilityLines.filter fun line => !isKeywordRestatement c.keywords line

/-- Abilities to print in the demo, taken from the modeled fields. -/
def abilitiesText (c : CardDef) : String :=
  String.intercalate "; " (structuredAbilityLines c)

/-- Keywords `k` plus leftover Oracle / structured abilities. -/
def keywordsAndAbilitiesOf (c : CardDef) (k : Array KeywordAbility) : String :=
  String.intercalate " "
    ([KeywordAbility.renderSummary k, c.abilitiesText].filter (fun s => !s.isEmpty))

/-- Keywords and abilities shown next to a card in the demo. -/
def keywordsAndAbilities (c : CardDef) : String :=
  c.keywordsAndAbilitiesOf c.keywords

def typeLine (c : CardDef) : String :=
  formatTypeLine c.supertypes c.types c.subtypes

/-- One side of a power/toughness box (CR 208.1 / 208.2).
A star plus constant `k` prints as `k+*` (CR 208.2a writes `1+*`). A bare
star, and `*+0`, print as `*`. -/
def renderPrintedStat (n : Option Int) (star : Bool) : String :=
  if star then
    match n with
    | some k => if k == 0 then "*" else s!"{k}+*"
    | none => "*"
  else
    match n with
    | some k => toString k
    | none => "*"

/-- Printed `power/toughness`, if this object has one.
A creature with neither a number nor a star prints `*/*`. Any other object
with neither prints nothing (CR 208.3). -/
def formatPowerToughness (power toughness : Option Int)
    (powerStar toughnessStar isCreature : Bool) : Option String :=
  if power.isNone && toughness.isNone && !powerStar && !toughnessStar then
    if isCreature then some "*/*" else none
  else
    some s!"{renderPrintedStat power powerStar}/{renderPrintedStat toughness toughnessStar}"

def ptString (c : CardDef) : String :=
  (formatPowerToughness c.power c.toughness c.powerStar c.toughnessStar c.isCreature).getD ""

/-- Name, printed mana cost if any, type line, P/T, then keywords and abilities.
Cards with no mana cost (lands, and other objects whose cost cannot be paid)
omit the cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def summary (c : CardDef) : String :=
  String.intercalate " "
    ([c.name, toString c.manaCost, c.typeLine, c.ptString, c.keywordsAndAbilities].filter
      (fun s => !s.isEmpty))

instance : ToString CardDef where
  toString := summary

/-- True when this card itself has improvise (CR 702.126). -/
def hasImprovise (c : CardDef) : Bool :=
  KeywordAbility.hasImprovise c.keywords

/-- True when this permanent's printed static abilities grant improvise to noncreature spells. -/
def grantsImproviseToNoncreature (c : CardDef) : Bool :=
  c.staticAbilities.any fun
    | .continuous _ sc mod =>
      sc == StaticAbility.scopeNoncreatureSpellsYouControl &&
        mod.flatten.any fun
          | .grantKeywords ks => KeywordAbility.hasImprovise ks
          | _ => false
    | _ => false

/-- True when this permanent has a printed boast activated ability (CR 702.142). -/
def hasBoast (c : CardDef) : Bool :=
  c.activatedAbilities.any (·.isBoast)

/-- Sneak alternative cost, if any (CR 702.190). -/
def sneakCost (c : CardDef) : Option ManaCost :=
  c.keywords.findSome? fun | .sneak cost => some cost.manaCost | _ => none

/-- True when this card's printed static abilities include `"enters prepared"`. -/
def entersPrepared (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyReplacement fun _ spec =>
      match spec with
      | .entersWithDesignation .prepared => true
      | _ => false

/-- True when this card's printed static abilities include `"enters with an indestructible counter"`. -/
def entersWithIndestructibleCounter (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyReplacement fun _ spec =>
      match spec with
      | .entersWithCounters .self .indestructible (.const n) false => n > 0
      | _ => false

/-- True when this card has a printed static ability granting protection from the chosen card type.
Checked at Layer 1 in Layer-4 fast paths to avoid Layer 4↔Layer 6 recursion. -/
def hasProtectionFromChosenCardType (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyRule fun _ r =>
      match r with
      | .player (.protectionFrom _ .chosenCardType) => true
      | _ => false

/-- True when this card has `"As this enters, choose Mardu or Jeskai."` (Layer 1 anchor check). -/
def isMarduOrJeskaiChoice (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyReplacement fun _ spec =>
      match spec with
      | .asEntersChoose (.namedAnchors opts) => opts == #["Mardu", "Jeskai"]
      | _ => false

/-- True when this card has a printed `"This spell can't be countered."` static ability. -/
def cantBeCountered (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyRule fun _ r =>
      match r with
      | .play (.spellCantBeCountered none) => true
      | _ => false

/-- True when this card has `"This planeswalker can be your commander."` (CR 903.3). -/
def canBeCommander (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyRule fun _ r =>
      match r with
      | .play .canBeCommander => true
      | _ => false

/-- True when this card has an `"As this enters, you may have it become a copy ..."` replacement. -/
def hasAsEntersCopy (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyReplacement fun _ spec =>
      match spec with
      | .asEntersMayCopy .. => true
      | _ => false

/-- True when this card has an opening-hand battlefield placement static ability (CR 103.6). -/
def mayBeginOnBattlefield (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyRule fun _ r =>
      match r with
      | .play .mayBeginOnBattlefield => true
      | _ => false

/-- True when this card unconditionally enters tapped. -/
def entersTappedUnconditionally (c : CardDef) : Bool :=
  c.staticAbilities.any fun ab =>
    ab.anyReplacement fun _ spec =>
      match spec with
      | .entersTapped .self none => true
      | _ => false

/-- Equip worthy: legendary non-Villain creature that's red or white. -/
def isWorthy (c : CardDef) : Bool :=
  c.hasSupertype .legendary &&
    !c.hasSubtype .villain &&
    (c.colors.contains .red || c.colors.contains .white)

/-- Equip worthy keyword on this Equipment (MSH). -/
def hasEquipWorthy (c : CardDef) : Bool :=
  c.activatedAbilities.any (·.isEquipWorthy)

/-- True when this face has any printed Saga chapter triggered abilities (CR 714.2). -/
def hasSagaChapters (c : CardDef) : Bool :=
  c.triggeredAbilities.any (·.isSagaChapter)

/-- Printed Saga chapter triggered abilities on this face (CR 714.2). -/
def sagaChapters (c : CardDef) : Array TriggeredAbility :=
  c.triggeredAbilities.filter (·.isSagaChapter)

/-- Printed final chapter number across this face's chapter abilities (CR 714.2d). -/
def finalChapterNumber (c : CardDef) : Nat :=
  TriggeredAbility.finalChapterNumberOf c.triggeredAbilities

/-- Spell, modal, adventure, and prepare effects on this face.
Saga chapters live in `triggeredAbilities` and are validated there via
`Effect.doesNothingAsTrigger`. -/
def spellLikeEffects (c : CardDef) : Array Effect :=
  let modes :=
    match c.modalSpec? with
    | some ms => ms.modes
    | none =>
      match c.spellEffect with
      | some e => #[e]
      | none => #[]
  let adv := match c.adventure with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  let prep := match c.prepareFace with
    | some a => match a.spellEffect with
      | some e => #[e]
      | none => #[]
    | none => #[]
  modes ++ adv ++ prep

/-- Why this face is not fully parsed or its effects are not fully modelled.
Does not look at `otherFace`. -/
def faceModellingError? (c : CardDef) : Option String :=
  let unparsed : Option String :=
    (c.adventure.bind fun a =>
      a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
      <|> (c.prepareFace.bind fun a =>
        a.extraLines[0]?.map fun line => s!"unparsed rules line on {a.name}: {line}")
  let spell : Option String :=
    c.spellLikeEffects.foldl (fun acc e =>
      match acc with
      | some err => some err
      | none =>
        if e.doesNothingAsSpell then
          some s!"{c.name} is not fully modelled: {e.toNotation}"
        else none) none
  let activated : Option String :=
    c.activatedAbilities.foldl (fun acc ab =>
      match acc with
      | some err => some err
      | none =>
        if ab.manaProduction?.isNone && ab.effect.doesNothingAsActivated then
          some s!"{c.name} activated ability is not fully modelled: {ab.effect.toNotation}"
        else none) none
  let triggered : Option String :=
    c.triggeredAbilities.foldl (fun acc ab =>
      match acc with
      | some err => some err
      | none =>
        if ab.activeZones.isEmpty then
          some s!"{c.name} triggered ability has empty activeZones: {ab.toNotation}"
        else
          match ab.modalSpec? with
          | some ms =>
            let minNeeded := match ms.minModes with | .const n => n.toNat | _ => 1
            if ms.modes.size < minNeeded then
              some s!"{c.name} modal triggered ability requires {minNeeded} modes but has {ms.modes.size}: {ab.toNotation}"
            else
              ms.modes.foldl (fun mAcc m =>
                match mAcc with
                | some err => some err
                | none =>
                  if m.doesNothingAsTrigger then
                    some s!"{c.name} modal triggered ability mode is not fully modelled: {m.toNotation}"
                  else none) none
          | none =>
            if ab.effect.doesNothingAsTrigger then
              some s!"{c.name} triggered ability is not fully modelled: {ab.toNotation}"
            else none) none
  unparsed <|> spell <|> activated <|> triggered

/-- Why `c` or its back face is not fully parsed or fully modelled.
`none` when every rules line was recognized and every spell, mode,
adventure, prepare face, Saga chapter, activated ability, and triggered ability
resolves. -/
def modellingError? (c : CardDef) : Option String :=
  c.faceModellingError? <|> (c.otherFace.bind faceModellingError?)

end CardDef

namespace AdventureFace

/-- Fixed Empower Planeswalker amount carried on this alternate face's spell effect. -/
def empowerPlaneswalkerAmount? (a : AdventureFace) : Option Nat :=
  a.spellEffect.bind (fun e => CardDef.extractEmpowerAmount e.body)

/-- Characteristics used while this card is on the stack as an Adventure (CR 715.3b). -/
def toCardDef (a : AdventureFace) : CardDef := {
  name := a.name
  manaCost := a.manaCost
  types := a.types
  subtypes := a.subtypes
  spellEffect := a.spellEffect
  staticAbilities := #[]
  additionalCosts := a.additionalCosts
}

/-- True when this Adventure's effect is classified as `k`. -/
def hasCastKind (a : AdventureFace) (k : SpellCastKind) : Bool :=
  a.spellEffect.any (fun e => e.castKind == k)

end AdventureFace

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.hasSupertype .basic

/-- A land card with the given land type (CR 205.3i / 305.7). -/
def isLandTypeCard (c : CardDef) (landType : CardSubtype) : Bool :=
  c.isLand && c.hasSubtype landType

/-- A card with the Forest land type (CR 205.3i / 305.7). -/
def isForestCard (c : CardDef) : Bool :=
  isLandTypeCard c .forest

end Mtg.Engine
