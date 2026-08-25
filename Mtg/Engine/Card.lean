import Mtg.Engine.Color
import Mtg.Engine.Mana
import Mtg.Engine.TypeLine

/-!
# Card characteristics (CR 108, 109.3, section 2)

A card’s Oracle characteristics: name, mana cost, color, type line, rules
text, and (when applicable) power, toughness, keywords, and the static,
triggered, activated, and spell abilities we currently model.
-/

namespace Mtg.Engine

/-- Keyword abilities that the engine currently understands. -/
structure Keywords where
  flash : Bool := false
  haste : Bool := false
  flying : Bool := false
  hexproof : Bool := false
  reach : Bool := false
  trample : Bool := false
  deathtouch : Bool := false
  defender : Bool := false
deriving BEq, Repr, Inhabited

namespace Keywords

def none : Keywords := {}

def toList (k : Keywords) : List String :=
  (if k.flash then ["flash"] else []) ++
  (if k.haste then ["haste"] else []) ++
  (if k.flying then ["flying"] else []) ++
  (if k.hexproof then ["hexproof"] else []) ++
  (if k.reach then ["reach"] else []) ++
  (if k.trample then ["trample"] else []) ++
  (if k.deathtouch then ["deathtouch"] else []) ++
  (if k.defender then ["defender"] else [])

instance : ToString Keywords where
  toString k :=
    let ks := k.toList
    if ks.isEmpty then "" else String.intercalate ", " ks

end Keywords

/-- One-shot effect of a spell on resolution. Targeting is stored on the stack object. -/
inductive SpellEffect where
  /-- Deal `amount` damage to the chosen target (player or creature). -/
  | dealDamage (amount : Nat)
  /-- Target creature gets +P/+T until end of turn. -/
  | pump (power toughness : Int)
  /-- Destroy target creature with flying (CR 701.8). -/
  | destroyCreatureWithFlying
  /-- Put a +1/+1 counter on target creature you control. It gains trample and
  hexproof until end of turn. -/
  | plusOnePlusOneTrampleHexproof
deriving Repr, Inhabited, BEq

namespace SpellEffect

def signedStat (n : Int) : String :=
  if n < 0 then toString n else s!"+{n}"

def toNotation : SpellEffect → String
  | .dealDamage n => s!"deals {n} damage to any target"
  | .pump p t => s!"target creature gets {signedStat p}/{signedStat t} until end of turn"
  | .destroyCreatureWithFlying => "destroy target creature with flying"
  | .plusOnePlusOneTrampleHexproof =>
    "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"

instance : ToString SpellEffect where
  toString := toNotation

end SpellEffect

/-- One-shot effect of an activated ability on resolution (CR 602, 608). -/
inductive AbilityEffect where
  /-- Search your library for a basic land card, put it onto the battlefield
  tapped, then shuffle (e.g. Wayfarer's Bauble). -/
  | searchBasicLandTapped
  /-- Exile the top card of your library. You may play it until the end of
  your next turn (e.g. Snowslope Hunter). -/
  | exileTopPlayUntilEndOfNextTurn
deriving Repr, Inhabited, BEq

namespace AbilityEffect

def toNotation : AbilityEffect → String
  | .searchBasicLandTapped =>
    "Search your library for a basic land card, put it onto the battlefield tapped, then shuffle"
  | .exileTopPlayUntilEndOfNextTurn =>
    "Exile the top card of your library. You may play it until the end of your next turn"

instance : ToString AbilityEffect where
  toString := toNotation

end AbilityEffect

/-- Costs of an activated ability besides announcements (CR 602.1). -/
structure ActivationCost where
  mana : ManaCost := ManaCost.empty
  tap : Bool := false
  sacrificeSource : Bool := false
  /-- Sacrifice another creature or artifact you control (CR 701.17). -/
  sacrificeAnotherCreatureOrArtifact : Bool := false
deriving Repr, Inhabited, BEq

namespace ActivationCost

def toNotation (c : ActivationCost) : String :=
  let parts : List String :=
    (if c.mana.symbols.isEmpty then [] else [toString c.mana]) ++
    (if c.tap then ["{T}"] else []) ++
    (if c.sacrificeSource then ["Sacrifice"] else []) ++
    (if c.sacrificeAnotherCreatureOrArtifact then
      ["Sacrifice another creature or artifact"]
     else [])
  String.intercalate ", " parts

instance : ToString ActivationCost where
  toString := toNotation

end ActivationCost

/-- An activated ability printed on a card (CR 602.1). Mana abilities that
are `{T}: Add` are stored separately on `CardDef.tapAddMana` / basic land types. -/
structure ActivatedAbility where
  cost : ActivationCost
  effect : AbilityEffect
  /-- Timing restriction “Activate only as a sorcery” (CR 117.1a). -/
  onlyAsSorcery : Bool := false
  /-- Timing restriction “Activate only during your turn”. -/
  onlyDuringYourTurn : Bool := false
  /-- Frequency restriction “Activate only once each turn”. -/
  onceEachTurn : Bool := false
deriving Repr, Inhabited, BEq

namespace ActivatedAbility

def toNotation (ab : ActivatedAbility) : String :=
  let timing :=
    (if ab.onlyAsSorcery then " (activate only as a sorcery)" else "") ++
    (if ab.onlyDuringYourTurn then " (activate only during your turn)" else "") ++
    (if ab.onceEachTurn then " (activate only once each turn)" else "")
  s!"{ab.cost.toNotation}: {ab.effect.toNotation}{timing}"

instance : ToString ActivatedAbility where
  toString := toNotation

end ActivatedAbility

/-- A static ability the engine currently understands (CR 604). -/
inductive StaticAbility where
  /-- Other creatures you control that have any of these subtypes have trample
  (e.g. Orcish Siegemaster). -/
  | otherCreaturesHaveTrample (subtypes : Array String)
  /-- Enchanted creature gets +P/+T (e.g. Gift of Strands). -/
  | enchantedCreatureGets (power toughness : Int)
deriving Repr, Inhabited, BEq

namespace StaticAbility

/-- English plural used in Oracle-style reminders (`Orc` → `Orcs`). -/
def pluralSubtype (s : String) : String :=
  if s.endsWith "s" then s else s ++ "s"

def toNotation : StaticAbility → String
  | .otherCreaturesHaveTrample subtypes =>
    let who := String.intercalate " and " (subtypes.toList.map pluralSubtype)
    s!"Other {who} you control have trample."
  | .enchantedCreatureGets p t =>
    s!"Enchanted creature gets {SpellEffect.signedStat p}/{SpellEffect.signedStat t}."

instance : ToString StaticAbility where
  toString := toNotation

end StaticAbility

/-- A triggered ability the engine currently understands (CR 603). -/
inductive TriggeredAbility where
  /-- Whenever this creature attacks, it gets +X/+0 until end of turn, where X
  is the greatest power among creatures you control. -/
  | onAttackPumpByGreatestPower
  /-- Whenever this creature becomes blocked, it deals 1 damage to each creature
  blocking it (e.g. Battle-Scarred Goblin). -/
  | onBecomesBlockedDeal1ToBlockers
  /-- When this permanent enters, scry `n` (e.g. Gift of Strands). -/
  | onEnterScry (n : Nat)
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

def toNotation : TriggeredAbility → String
  | .onAttackPumpByGreatestPower =>
    "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
  | .onBecomesBlockedDeal1ToBlockers =>
    "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
  | .onEnterScry n =>
    s!"When this permanent enters, scry {n}."

/-- True for abilities that trigger as this creature is declared as an attacker (CR 508.2). -/
def triggersWhenAttacking : TriggeredAbility → Bool
  | .onAttackPumpByGreatestPower => true
  | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _ => false

/-- True for abilities that trigger as this creature becomes blocked (CR 509.5c). -/
def triggersWhenBecomesBlocked : TriggeredAbility → Bool
  | .onBecomesBlockedDeal1ToBlockers => true
  | .onAttackPumpByGreatestPower | .onEnterScry _ => false

/-- True for abilities that trigger as this permanent enters the battlefield (CR 603.6a). -/
def triggersWhenEntering : TriggeredAbility → Bool
  | .onEnterScry _ => true
  | .onAttackPumpByGreatestPower | .onBecomesBlockedDeal1ToBlockers => false

instance : ToString TriggeredAbility where
  toString := toNotation

end TriggeredAbility

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
  spellEffect : Option SpellEffect := none
  /-- Modes of a “Choose one” spell (CR 700.2). Nonempty means the spell is modal. -/
  spellModes : Array SpellEffect := #[]
  /-- Additional `{T}: Add _` abilities that are not implied by basic land types. -/
  tapAddMana : Array ManaType := #[]
  /-- Non-mana activated abilities (CR 602). `{T}: Add` mana abilities are
  `tapAddMana` / basic land types instead. -/
  activatedAbilities : Array ActivatedAbility := #[]
  /-- Static abilities other than printed keywords (CR 604). -/
  staticAbilities : Array StaticAbility := #[]
  /-- Triggered abilities (CR 603). -/
  triggeredAbilities : Array TriggeredAbility := #[]
deriving Repr, Inhabited

namespace CardDef

/-- Color from color indicator, otherwise from mana cost (CR 202.2). -/
def colors (c : CardDef) : ColorSet :=
  match c.colorIndicator with
  | some cs => cs
  | none => c.manaCost.colors

def isLand (c : CardDef) : Bool := c.types.any (· == .land)
def isCreature (c : CardDef) : Bool := c.types.any (· == .creature)
def isArtifact (c : CardDef) : Bool := c.types.any (· == .artifact)
def isInstant (c : CardDef) : Bool := c.types.any (· == .instant)
def isSorcery (c : CardDef) : Bool := c.types.any (· == .sorcery)
def isEnchantment (c : CardDef) : Bool := c.types.any (· == .enchantment)
def isPermanentCard (c : CardDef) : Bool := c.types.any CardType.isPermanentType
/-- Aura subtype on an Enchantment (CR 303.4). -/
def isAura (c : CardDef) : Bool :=
  c.isEnchantment && c.subtypes.any (· == "Aura")

/-- Timing of a sorcery: also the default for permanent spells without flash (CR 302.1, 307.1). -/
def hasSorcerySpeed (c : CardDef) : Bool :=
  !c.isInstant && !c.isLand && !c.keywords.flash

def hasInstantSpeed (c : CardDef) : Bool :=
  c.isInstant || c.keywords.flash

/-- Modal spell with “Choose one” (CR 700.2). -/
def isModal (c : CardDef) : Bool :=
  !c.spellModes.isEmpty

/-- Modes of a modal spell; empty when the card is not modal. -/
def modes (c : CardDef) : Array SpellEffect :=
  c.spellModes

/-- Whether casting this card requires choosing a target (CR 115.1, 303.4). -/
def requiresTarget (c : CardDef) : Bool :=
  c.spellEffect.isSome || !c.spellModes.isEmpty || c.isAura

def manaValue (c : CardDef) : Nat := c.manaCost.manaValue

/-- Basic land types on this card produce the corresponding mana (CR 305.6). -/
def basicLandMana (c : CardDef) : Array Color :=
  c.subtypes.filterMap manaForBasicLandType

/-- All `{T}: Add` mana types this card can produce. -/
def manaAbilities (c : CardDef) : Array ManaType :=
  c.basicLandMana.map ManaType.colored ++ c.tapAddMana

/-- Lowercase ASCII for comparing Oracle keyword lines to `Keywords.toList`. -/
def lowerAscii (s : String) : String :=
  s.map Char.toLower

/-- True when `line` restates modeled keywords, e.g. `Haste` or `Reach, deathtouch`. -/
def isKeywordRestatement (k : Keywords) (line : String) : Bool :=
  let kw := k.toList
  let cleaned := (line.replace "." "").trimAscii.copy
  if cleaned.isEmpty then true
  else
    let parts := cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
    !parts.isEmpty && parts.all (fun p => kw.any (fun w => w == lowerAscii p))

/-- Oracle ability lines that are not just restating modeled keywords. -/
def leftoverOracleLines (c : CardDef) : List String :=
  c.oracleText.splitOn "\n" |>.map (fun s => s.trimAscii.copy) |>.filter (fun line =>
    !line.isEmpty && !isKeywordRestatement c.keywords line)

/-- `{T}: Add` mana abilities, activated, static, triggered, and spell abilities. -/
def structuredAbilityLines (c : CardDef) : List String :=
  c.manaAbilities.toList.map (fun t => s!"\{T}: Add \{{t.letter}}") ++
  c.activatedAbilities.toList.map ActivatedAbility.toNotation ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  match c.spellEffect with
  | some e => [SpellEffect.toNotation e]
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
  let super := String.intercalate " " (c.supertypes.toList.map toString)
  let types := String.intercalate " " (c.types.toList.map toString)
  let sub := String.intercalate " " c.subtypes.toList
  let head :=
    if super.isEmpty then types else s!"{super} {types}"
  if sub.isEmpty then head else s!"{head} — {sub}"

def ptString (c : CardDef) : String :=
  match c.power, c.toughness with
  | some p, some t => s!"{p}/{t}"
  | _, _ => ""

def summary (c : CardDef) : String :=
  let cost := toString c.manaCost
  let pt := c.ptString
  let extras :=
    [pt, c.keywordsAndAbilities].filter (fun s => !s.isEmpty) |> fun xs =>
      if xs.isEmpty then "" else " " ++ String.intercalate " " xs
  s!"{c.name} {cost} {c.typeLine}{extras}"

instance : ToString CardDef where
  toString := summary

#guard toString ({ Keywords.none with haste := true } : Keywords) == "haste"
#guard toString ({ Keywords.none with flash := true } : Keywords) == "flash"
#guard CardDef.isKeywordRestatement { Keywords.none with haste := true } "Haste"
#guard CardDef.isKeywordRestatement { Keywords.none with flash := true } "Flash"
#guard CardDef.isKeywordRestatement
  { Keywords.none with reach := true, deathtouch := true } "Reach, deathtouch"
#guard !CardDef.isKeywordRestatement { Keywords.none with flying := true } "Flash"
#guard toString ({ Keywords.none with hexproof := true } : Keywords) == "hexproof"
#guard CardDef.isKeywordRestatement { Keywords.none with hexproof := true } "Hexproof"
#guard SpellEffect.toNotation (.dealDamage 3) == "deals 3 damage to any target"
#guard SpellEffect.toNotation (.pump 3 3) == "target creature gets +3/+3 until end of turn"
#guard SpellEffect.toNotation .destroyCreatureWithFlying ==
  "destroy target creature with flying"
#guard SpellEffect.toNotation .plusOnePlusOneTrampleHexproof ==
  "put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn"
#guard (AbilityEffect.toNotation .searchBasicLandTapped).startsWith "Search your library"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := .searchBasicLandTapped
  }
  (toString ab).startsWith "{2}, {T}, Sacrifice:"
#guard StaticAbility.toNotation (.otherCreaturesHaveTrample #["Orc", "Goblin"]) ==
  "Other Orcs and Goblins you control have trample."
#guard StaticAbility.toNotation (.enchantedCreatureGets 3 3) ==
  "Enchanted creature gets +3/+3."
#guard TriggeredAbility.toNotation .onAttackPumpByGreatestPower ==
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
#guard TriggeredAbility.toNotation .onBecomesBlockedDeal1ToBlockers ==
  "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
#guard TriggeredAbility.toNotation (.onEnterScry 2) ==
  "When this permanent enters, scry 2."
#guard TriggeredAbility.triggersWhenAttacking .onAttackPumpByGreatestPower
#guard TriggeredAbility.triggersWhenBecomesBlocked .onBecomesBlockedDeal1ToBlockers
#guard TriggeredAbility.triggersWhenEntering (.onEnterScry 2)
#guard !TriggeredAbility.triggersWhenEntering .onAttackPumpByGreatestPower

end CardDef

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.supertypes.any (· == .basic)

end Mtg.Engine
