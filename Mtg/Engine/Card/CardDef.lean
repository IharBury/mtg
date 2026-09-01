import Mtg.Engine.Card.ActivatedAbility
import Mtg.Engine.Card.Saga
import Mtg.Engine.Card.StaticAbility
import Mtg.Engine.Card.TriggeredAbility

/-!
# Card definitions (CR 108, 109.3, section 2)

Printed Oracle characteristics: `CardDef`, the `AdventureFace` of
adventurer cards, and per-card mana-ability storage.
-/

namespace Mtg.Engine

/-- A `{T}: Add {M} for each [subtype] you control` mana ability (CR 106.4 / 605). -/
structure TapAddForEach where
  mana : ManaType
  subtype : String
deriving Repr, Inhabited, BEq

namespace TapAddForEach

def toNotation (a : TapAddForEach) : String :=
  s!"\{T}: Add \{{a.mana.letter}} for each {a.subtype} you control"

instance : ToString TapAddForEach where
  toString := toNotation

end TapAddForEach

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
structure AdventureFace where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[.sorcery]
  subtypes : Array Subtype := #["Adventure"]
  oracleText : String := ""
  spellEffect : Option Effect := none
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
deriving Repr, Inhabited, BEq

/-- Printed (Oracle) characteristics of a card. -/
structure CardDef where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType
  subtypes : Array Subtype := #[]
  supertypes : Array Supertype := #[]
  oracleText : String := ""
  power : Option Int := none
  toughness : Option Int := none
  loyalty : Option Int := none
  /-- Explicit color indicator, if any (CR 107.13 / 202.2). -/
  colorIndicator : Option ColorSet := none
  keywords : Keywords := Keywords.none
  spellEffect : Option Effect := none
  /-- Additional cost: sacrifice an artifact or creature (CR 601.2b / 601.2h), e.g.
  Improvised Club. When `additionalCostOrPayGeneric` is set, that sacrifice
  may be replaced by paying that much generic mana (e.g. Stir Up Trouble).
  The choice is announced at CR 601.2b, before targets. -/
  additionalCostSacrificeArtifactOrCreature : Bool := false
  /-- Alternative additional cost: pay this much generic mana instead of
  sacrificing an artifact or creature (CR 601.2b). -/
  additionalCostOrPayGeneric : Option Nat := none
  /-- Additional cost: discard a card or pay `{n}` (e.g. Titania). -/
  additionalCostDiscardOrPayGeneric : Option Nat := none
  /-- This spell costs this much generic mana less if a creature died this
  turn (e.g. Dreaded Bat-Cloud). -/
  costReductionIfCreatureDied : Nat := 0
  /-- This spell costs this much generic mana less if it targets a creature
  that was dealt damage this turn (e.g. Bitter Downfall). -/
  costReductionIfTargetDamaged : Nat := 0
  /-- This spell costs this much generic mana less if it targets a tapped
  creature (e.g. Magnificent End). -/
  costReductionIfTargetTapped : Nat := 0
  /-- This spell costs this much generic mana less if it targets an attacking
  nontoken creature (e.g. Uneasy Partings). -/
  costReductionIfTargetAttackingNontoken : Nat := 0
  /-- This spell costs this much generic mana less if it targets an attacking
  creature (e.g. Depower). -/
  costReductionIfTargetAttacking : Nat := 0
  /-- This spell costs this much generic mana less if you control a permanent
  of this subtype (e.g. Visions of Villainy, Truck Toss). -/
  costReductionIfYouControl : Option (Nat × String) := none
  /-- This spell costs this much generic mana less if your graveyard has at
  least this many creature cards (e.g. Punishing Punch). -/
  costReductionIfGyCreaturesAtLeast : Option (Nat × Nat) := none
  /-- Modes of a “Choose one” spell (CR 700.2). Nonempty means the spell is modal. -/
  spellModes : Array Effect := #[]
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
  /-- `{T}: Add {M} for each permanent you control with this subtype
  (e.g. Elvish Archdruid). -/
  tapAddManaForEach : Array TapAddForEach := #[]
  /-- `{T}: Add X mana of any one color, where X is this creature's power.
  That mana may be spent only to cast Elf spells and activate abilities of
  Elf sources (e.g. Woodland Weavemaster). -/
  tapAddAnyColorEqualToPower : Bool := false
  /-- `{T}: Add one mana of any color. Spend this mana only to cast an instant
  or sorcery spell (e.g. Pelargir Survivor). -/
  tapAddAnyColorForInstantOrSorcery : Bool := false
  /-- This enchantment enters with a hope counter for each creature you control
  (e.g. Dawn of a New Age). -/
  entersWithHopePerCreature : Bool := false
  /-- This permanent enters tapped (CR 110.5b exception). -/
  entersTapped : Bool := false
  /-- `{T}: Add one of these mana types` as a single choice ability
  (e.g. `{T}: Add {G} or {U}`). -/
  tapAddOneOf : Array ManaType := #[]
  /-- `{T}: Add one of these types. Activate only if this land entered this
  turn or if you control a basic land.` -/
  tapAddOneOfIfEnteredOrBasic : Array ManaType := #[]
  /-- `{T}: Add one mana of any color` with no spending restriction. -/
  tapAddAnyColor : Bool := false
  /-- `{T}, Sacrifice this permanent: Add one mana of any color` (Treasure). -/
  tapSacrificeAddAnyColor : Bool := false
  /-- This object is a token (CR 111). -/
  isToken : Bool := false
  /-- This spell can't be countered. -/
  cantBeCountered : Bool := false
  /-- You may cast this as though it had flash if you control this subtype. -/
  flashIfYouControlSubtype : Option String := none
  /-- Printed ward cost (CR 702.21), e.g. `Ward {3}`. -/
  ward : Option Nat := none
  /-- Flashback cost (CR 702.34). -/
  flashback : Option ManaCost := none
  /-- This permanent enters tapped unless you control a legendary creature. -/
  entersTappedUnlessLegendary : Bool := false
  /-- This permanent enters tapped unless you control an Equipment. -/
  entersTappedUnlessEquipment : Bool := false
  /-- `{T}: Add one mana of any color. Spend this mana only to cast a
  legendary spell, and that spell can't be countered.` -/
  tapAddAnyColorForLegendary : Bool := false
  /-- This spell costs {X} less to cast, where X is the total power of
  creatures you control with flying. -/
  costReductionEqualFlyingPower : Bool := false
  /-- Crew `n` (CR 702.122). -/
  crew : Option Nat := none
  /-- `{T}: Add two mana in any combination of these types`. -/
  tapAddTwoAmong : Array ManaType := #[]
  /-- Modal spell is “Choose one or both” rather than “Choose one”. -/
  chooseOneOrBoth : Bool := false
  /-- “Choose one. If you control a {subtype}, you may choose two instead.” -/
  chooseTwoIfYouControlSubtype : Option String := none
  /-- `{T}: Add one mana of any color among legendary creatures and
  planeswalkers you control`. -/
  tapAddAnyColorAmongLegendaries : Bool := false
  /-- `{T}: Add these mana types. Spend this mana only to cast …`. -/
  tapAddRestricted : Option (Array ManaType × String) := none
  /-- `{T}, Pay n life: Add one of these types`. -/
  tapPayLifeAddOneOf : Option (Nat × Array ManaType) := none
  /-- As this land enters, you may pay `n` life. If you don't, it enters tapped. -/
  entersTappedUnlessPayLife : Option Nat := none
  /-- `{T}: Add one mana of any color in your commander's color identity`. -/
  tapAddCommanderIdentity : Bool := false
  /-- Additional cost: sacrifice a creature. -/
  additionalCostSacrificeCreature : Bool := false
  /-- As this enchantment enters, choose a creature type. -/
  asEntersChooseCreatureType : Bool := false
  /-- Printed Saga chapters (CR 714). -/
  saga : Option SagaDef := none
  /-- Affinity for this subtype (CR 702.40). -/
  affinityForSubtype : Option String := none
  /-- This spell costs {X} less, where X is the greatest number of artifacts
  an opponent controls. -/
  costReductionEqualOppArtifacts : Bool := false
  /-- Gift a Treasure (you may promise an opponent a Treasure). -/
  giftTreasure : Bool := false
  /-- If you would create a Food token, also create a Treasure. -/
  foodAlsoCreatesTreasure : Bool := false
  /-- Other creatures enter with +1/+1 counters equal to this creature's toughness. -/
  othersEnterWithPlusOneEqualToughness : Bool := false
  /-- This gets +N/+0 for each Mountain you control. -/
  powerPerMountain : Nat := 0
  /-- You may play an additional land if you control another of this subtype. -/
  extraLandIfOtherSubtype : Option String := none
  /-- `{T}: Add {C} for each permanent you control of this subtype`. -/
  tapAddColorlessPerSubtype : Option String := none
  /-- Cascade printed `n` times (`Cascade, cascade` when `n = 2`). -/
  cascade : Nat := 0
  /-- Optional kicker cost (CR 702.32). Paid at most once as an additional cost. -/
  kicker : Option ManaCost := none
  /-- If one or more tokens would be created under your control, twice that
  many of those tokens are created instead (e.g. Bard, King of Dale). -/
  tokenDoubling : Bool := false
  /-- If you would draw a card except the first one you draw in each of your
  draw steps, draw two cards instead. -/
  drawTwoExceptFirstDrawStep : Bool := false
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / `tapAddManaForEach` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
  /-- If a creature an opponent controls would die, exile it instead
  (e.g. Head of the Hunt). The original die event never happens (CR 614.6). -/
  exileOppCreaturesInstead : Bool := false
  /-- You may look at the top card of your library any time
  (e.g. Elven Chorus). -/
  mayLookAtTopAnytime : Bool := false
  /-- You may cast creature spells from the top of your library
  (e.g. Elven Chorus). Does not grant flash or change timing. -/
  mayCastCreaturesFromTop : Bool := false
  /-- You may play lands from the top of your library (e.g. Ka-Zar). -/
  mayPlayLandsFromTop : Bool := false
  /-- Creatures you control have `{T}: Add one mana of any color`
  (e.g. Elven Chorus). -/
  grantCreaturesTapAddAnyColor : Bool := false
  /-- The first creature spell you cast each turn costs this much generic
  less (e.g. Radagast of Rhosgobel). -/
  firstCreatureCostsLess : Nat := 0
  /-- The first creature spell you cast each turn can be cast as though it
  had flash (e.g. Radagast of Rhosgobel). -/
  firstCreatureHasFlash : Bool := false
  /-- Hexproof and indestructible while you control this many lore counters
  among Sagas (e.g. Tom Bombadil). -/
  hexproofIndestructibleIfLore : Option Nat := none
  /-- This creature enters with an indestructible counter. -/
  entersWithIndestructibleCounter : Bool := false
  /-- As this permanent enters, choose odd or even (Gollum, Riddle Master). -/
  asEntersChooseOddEven : Bool := false
  /-- Spells you cast from anywhere other than your hand cost this much
  generic mana less (e.g. Bilbo, Thief in the Night). -/
  costReductionNotFromHand : Nat := 0
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
  /-- Teamwork N (CR 702.194): optional additional cost to tap creatures with
  total power N or more. -/
  teamwork : Option Nat := none
  /-- “Choose one. If this spell was cast using teamwork, choose both instead.” -/
  chooseBothIfTeamwork : Bool := false
  /-- This permanent enters with this many shield counters. -/
  entersWithShield : Nat := 0
  /-- Daybound on the front face (CR 702.145). Nick Fury; MSH 191. -/
  daybound : Bool := false
  /-- Back face of a modal double-faced card that can transform. -/
  otherFace : Option CardDef := none
deriving Repr, Inhabited

namespace CardDef

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

/-- True when `s` is among this card's subtypes. -/
def hasSubtype (c : CardDef) (s : Subtype) : Bool := c.subtypes.any (· == s)

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
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.hasSubtype "Aura"
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.hasSubtype "Equipment"

/-- Names a player may choose for “choose a card name”, including an
Adventure face (Gatherer ruling on adventurer cards). -/
def choosableNames (c : CardDef) : Array String :=
  match c.adventure with
  | some adv => #[c.name, adv.name]
  | none => #[c.name]

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !c.keywords.flash

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || c.keywords.flash

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  !c.spellModes.isEmpty

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array Effect :=
  c.spellModes

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.isAura ||
  match c.spellEffect with
  | some e => e.requiresTarget
  | none => !c.spellModes.isEmpty && c.spellModes.all (·.requiresTarget)

/-- True when the printed spell may be announced with zero targets. -/
def allowsZeroTargets (c : CardDef) : Bool :=
  match c.spellEffect with
  | some e => e.allowsZeroTargets
  | none => false

/-- True when the printed effect or a mode is classified as `k`. -/
def hasCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellEffect.any (fun e => e.castKind == k)

/-- True when a modal mode is classified as `k`. -/
def hasModeCastKind (c : CardDef) (k : SpellCastKind) : Bool :=
  c.spellModes.any (fun e => e.castKind == k)

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- `{T}: Add {M}` abilities that produce one mana, from basic land types or
an explicit `tapAddMana` list. -/
def simpleTapAddMana (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

/-- `{T}: Add` types from modeled activated mana abilities. -/
def mshTapAddMana (c : CardDef) : Array ManaType :=
  c.activatedAbilities.foldl (fun acc ab =>
    match ab.effect.resolution with
    | .addMana types => acc ++ types
    | .addBlueCantNonartifact => acc ++ #[.colored .blue]
    | _ => acc) #[]

/-- `{T}: Add` types gated on this land entering this turn or a basic land. -/
def enteredOrBasicAddMana (c : CardDef) : Array ManaType :=
  c.tapAddOneOfIfEnteredOrBasic ++ c.mshTapAddMana

/-- True when a `{T}: Add` ability requires this land entered this turn or
a basic land you control. -/
def requiresEnteredOrBasicAdd (c : CardDef) : Bool :=
  !c.tapAddOneOfIfEnteredOrBasic.isEmpty

/-- True when an activated ability adds any color of mana. -/
def hasAnyColorActivatedAdd (c : CardDef) : Bool :=
  c.activatedAbilities.any (fun ab =>
    match ab.effect.resolution with
    | .addAnyColor | .addAnyColorSpendOnlySubtype _
    | .addAnyColorSpendOnlyArtifactSpell | .addAnyColorEqualToSourcePower
    | .addTwoAnyColorCreatureSources | .addFourAnyCombination
    | .addTwoAnyColorEquipment => true
    | _ => false)

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.simpleTapAddMana ++ c.tapAddOneOf ++ c.tapAddManaForEach.map (·.mana) ++
    c.enteredOrBasicAddMana ++
    (if c.tapAddAnyColorEqualToPower || c.tapAddAnyColorForInstantOrSorcery ||
        c.tapAddAnyColor || c.tapSacrificeAddAnyColor ||
        c.tapAddAnyColorForLegendary || c.tapAddTwoAmong.size >= 2 ||
        c.tapAddAnyColorAmongLegendaries || c.tapAddCommanderIdentity ||
        c.hasAnyColorActivatedAdd then
      (Color.all.map ManaType.colored).toArray
     else #[])

/-- Lowercase ASCII for comparing Oracle keyword lines to `Keywords.toList`. -/
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
def isKeywordRestatement (k : Keywords) (line : String) : Bool :=
  let kw := k.toList
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

/-- Oracle ability lines that are not just restating modeled keywords. The
Gatherer `//ADV//` marker is stored in `oracleText` but is not an ability. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.oracleText.splitOn "\n" |>.map (fun s => s.trimAscii.copy) |>.filterMap (fun line =>
    match stripAdventureDelimiter line with
    | none => none
    | some rest =>
      if rest.isEmpty || isKeywordRestatement c.keywords rest then none else some rest)

/-- `{T}: Add {C}` lines from `simpleTapAddMana`. -/
def simpleTapAddLines (c : CardDef) : List String :=
  c.simpleTapAddMana.toList.map (fun t => s!"\{T}: Add \{{t.letter}}")

/-- `{T}: Add` for each permanent of a listed type. -/
def tapAddForEachLines (c : CardDef) : List String :=
  c.tapAddManaForEach.toList.map TapAddForEach.toNotation

/-- Elf-restricted `{T}: Add` X mana of any color equal to power. -/
def tapAddAnyColorEqualToPowerLine (c : CardDef) : List String :=
  if c.tapAddAnyColorEqualToPower then
    ["{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources."]
  else []

/-- Instant/sorcery-restricted `{T}: Add` one mana of any color. -/
def tapAddAnyColorForInstantOrSorceryLine (c : CardDef) : List String :=
  if c.tapAddAnyColorForInstantOrSorcery then
    ["{T}: Add one mana of any color. Spend this mana only to cast an instant or sorcery spell."]
  else []

/-- True when CR 601.2b must announce a sacrifice-or-pay or discard-or-pay
additional cost. -/
def announcesAdditionalCost (c : CardDef) : Bool :=
  c.additionalCostOrPayGeneric.isSome || c.additionalCostDiscardOrPayGeneric.isSome

/-- Additional cost that sacrifices an artifact or creature (optionally or pay `{n}`). -/
def additionalCostSacrificeArtifactOrCreatureLine (c : CardDef) : List String :=
  if c.additionalCostSacrificeArtifactOrCreature then
    match c.additionalCostOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, sacrifice an artifact or creature or pay \{{n}}"]
    | none =>
      ["As an additional cost to cast this spell, sacrifice an artifact or creature"]
  else
    match c.additionalCostDiscardOrPayGeneric with
    | some n =>
      [s!"As an additional cost to cast this spell, discard a card or pay \{{n}}."]
    | none => []

/-- `{T}: Add` mana abilities, additional costs, activated, static, triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.simpleTapAddLines ++
  c.tapAddForEachLines ++
  c.tapAddAnyColorEqualToPowerLine ++
  c.tapAddAnyColorForInstantOrSorceryLine ++
  c.additionalCostSacrificeArtifactOrCreatureLine ++
  c.activatedAbilities.toList.map ActivatedAbility.toNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  match c.spellEffect with
  | some e => [Effect.toNotation e]
  | none => []

/-- Abilities to print in the demo. Prefer leftover Oracle text so unmodeled
abilities (triggers, extra activations) are visible; fall back to structured
abilities when Oracle is empty or only restates keywords. -/
def abilitiesText (c : CardDef) : String :=
  let fromOracle := leftoverOracleLines c
  if !fromOracle.isEmpty then
    String.intercalate " / " fromOracle
  else
    String.intercalate "; " (structuredAbilityLines c)

/-- Keywords `k` plus leftover Oracle / structured abilities. -/
def keywordsAndAbilitiesOf (c : CardDef) (k : Keywords) : String :=
  String.intercalate " "
    ([toString k, c.abilitiesText].filter (fun s => !s.isEmpty))

/-- Keywords and abilities shown next to a card in the demo. -/
def keywordsAndAbilities (c : CardDef) : String :=
  c.keywordsAndAbilitiesOf c.keywords

def typeLine (c : CardDef) : String :=
  formatTypeLine c.supertypes c.types c.subtypes

def ptString (c : CardDef) : String :=
  match c.power, c.toughness with
  | some p, some t => s!"{p}/{t}"
  | some p, none => s!"{p}/*"
  | none, some t => s!"*/{t}"
  | none, none => if c.isCreature then "*/*" else ""

/-- Name, printed mana cost if any, type line, P/T, then keywords and abilities.
Cards with no mana cost (lands, and other objects whose cost cannot be paid)
omit the cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def summary (c : CardDef) : String :=
  String.intercalate " "
    ([c.name, toString c.manaCost, c.typeLine, c.ptString, c.keywordsAndAbilities].filter
      (fun s => !s.isEmpty))

instance : ToString CardDef where
  toString := summary

/-- True when this card itself has improvise (MSH). -/
def hasImprovise (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .improvise => true
    | _ => false)

/-- True when this permanent grants improvise to noncreature spells you cast. -/
def grantsImproviseToNoncreature (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .noncreatureSpellsHaveImprovise => true
    | _ => false)

/-- True when this permanent has a boast ability (MSH). -/
def hasBoast (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .boast => true
    | _ => false)

/-- Sneak alternative cost, if any (MSH). -/
def sneakCost (c : CardDef) : Option ManaCost :=
  c.staticAbilities.foldl (fun acc ab =>
    match acc, ab with
    | none, .sneak cost => some cost
    | acc, _ => acc) none

/-- Equip worthy: legendary non-Villain creature that's red or white. -/
def isWorthy (c : CardDef) : Bool :=
  c.hasSupertype .legendary &&
    !c.hasSubtype "Villain" &&
    (c.colors.contains .red || c.colors.contains .white)

/-- Equip worthy keyword on this Equipment (MSH). -/
def hasEquipWorthy (c : CardDef) : Bool :=
  c.activatedAbilities.any (·.equipWorthy)

end CardDef

namespace AdventureFace

/-- Characteristics used while this card is on the stack as an Adventure (CR 715.3b). -/
def toCardDef (a : AdventureFace) : CardDef := {
  name := a.name
  manaCost := a.manaCost
  types := a.types
  subtypes := a.subtypes
  oracleText := a.oracleText
  spellEffect := a.spellEffect
}

/-- True when this Adventure's effect is classified as `k`. -/
def hasCastKind (a : AdventureFace) (k : SpellCastKind) : Bool :=
  a.spellEffect.any (fun e => e.castKind == k)

end AdventureFace

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.hasSupertype .basic

/-- A land card with the given land type (CR 205.3i / 305.7). -/
def isLandTypeCard (c : CardDef) (landType : String) : Bool :=
  c.isLand && c.hasSubtype landType

/-- A card with the Forest land type (CR 205.3i / 305.7). -/
def isForestCard (c : CardDef) : Bool :=
  isLandTypeCard c "Forest"

end Mtg.Engine
