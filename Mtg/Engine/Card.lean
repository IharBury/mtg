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
  /-- Deal `amount` damage to target creature (e.g. Spew Flame). -/
  | dealDamageToCreature (amount : Nat)
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
  | .dealDamageToCreature n => s!"deals {n} damage to target creature"

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
  /-- This creature deals `amount` damage to target creature
  (e.g. Goblin Cratermaker). -/
  | dealDamageToTargetCreature (amount : Nat)
  /-- Destroy target colorless nonland permanent (e.g. Goblin Cratermaker). -/
  | destroyTargetColorlessNonland
  /-- Attach this Equipment to target creature you control (CR 702.6a). -/
  | attachToTargetCreatureYouControl
  /-- This enchantment becomes a Bear creature in addition to its other types
  and gains “This creature's power and toughness are each equal to the number
  of lands you control.” The effect does not end (e.g. Beorn's Hospitality). -/
  | becomeBearCreatureWithLandsPT
  /-- This creature gets +P/+T until end of turn (e.g. Goblin Fireleaper). -/
  | sourceGets (power toughness : Int)
deriving Repr, Inhabited, BEq

namespace AbilityEffect

def toNotation : AbilityEffect → String
  | .searchBasicLandTapped =>
    "Search your library for a basic land card, put it onto the battlefield tapped, then shuffle"
  | .exileTopPlayUntilEndOfNextTurn =>
    "Exile the top card of your library. You may play it until the end of your next turn"
  | .dealDamageToTargetCreature n =>
    s!"This creature deals {n} damage to target creature"
  | .destroyTargetColorlessNonland =>
    "Destroy target colorless nonland permanent"
  | .attachToTargetCreatureYouControl =>
    "Attach this Equipment to target creature you control"
  | .becomeBearCreatureWithLandsPT =>
    "This enchantment becomes a Bear creature in addition to its other types and gains \"This creature's power and toughness are each equal to the number of lands you control.\""
  | .sourceGets p t =>
    s!"This creature gets {SpellEffect.signedStat p}/{SpellEffect.signedStat t} until end of turn"

/-- True when announcing this effect requires choosing a target (CR 115.1 / 601.2c). -/
def requiresTarget : AbilityEffect → Bool
  | .dealDamageToTargetCreature _ | .destroyTargetColorlessNonland
  | .attachToTargetCreatureYouControl => true
  | .searchBasicLandTapped | .exileTopPlayUntilEndOfNextTurn
  | .becomeBearCreatureWithLandsPT | .sourceGets _ _ => false

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
  /-- First (or only) mode of this ability. -/
  effect : AbilityEffect
  /-- Additional modes of a modal ability (CR 700.2). Empty means the ability
  is not modal; the player otherwise chooses one mode at CR 601.2b. -/
  otherModes : Array AbilityEffect := #[]
  /-- Timing restriction “Activate only as a sorcery” (CR 117.1a). -/
  onlyAsSorcery : Bool := false
  /-- Timing restriction “Activate only during your turn”. -/
  onlyDuringYourTurn : Bool := false
  /-- Frequency restriction “Activate only once each turn”. -/
  onceEachTurn : Bool := false
deriving Repr, Inhabited, BEq

namespace ActivatedAbility

/-- Every mode of this ability; a non-modal ability is a singleton. -/
def allModes (ab : ActivatedAbility) : Array AbilityEffect :=
  #[ab.effect] ++ ab.otherModes

/-- True when the player must choose among two or more modes (CR 700.2). -/
def isModal (ab : ActivatedAbility) : Bool :=
  !ab.otherModes.isEmpty

def toNotation (ab : ActivatedAbility) : String :=
  let timing :=
    (if ab.onlyAsSorcery then " (activate only as a sorcery)" else "") ++
    (if ab.onlyDuringYourTurn then " (activate only during your turn)" else "") ++
    (if ab.onceEachTurn then " (activate only once each turn)" else "")
  let body :=
    if ab.isModal then
      let modes := ab.allModes.toList.map AbilityEffect.toNotation
      s!"Choose one — {String.intercalate "; " modes}"
    else
      ab.effect.toNotation
  s!"{ab.cost.toNotation}: {body}{timing}"

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
  /-- Equipped creature gets +P/+T (e.g. Ragged Short Spear). -/
  | equippedCreatureGets (power toughness : Int)
  /-- This creature's power and toughness are each equal to the number of lands
  you control (e.g. Mirkwood Pathmaker, animated Beorn's Hospitality). -/
  | powerToughnessEqualLandsYouControl
  /-- This creature can't block unless its controller controls a permanent with
  any of these subtypes (e.g. Olog-hai Crusher). An empty list means it can't
  block at all. The restriction is checked when declaring blockers (CR 509.1b). -/
  | cantBlockUnlessYouControl (subtypes : Array String)
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
  | .equippedCreatureGets p t =>
    s!"Equipped creature gets {SpellEffect.signedStat p}/{SpellEffect.signedStat t}."
  | .powerToughnessEqualLandsYouControl =>
    "This creature's power and toughness are each equal to the number of lands you control."
  | .cantBlockUnlessYouControl subtypes =>
    match subtypes.toList with
    | [] => "This creature can't block."
    | xs =>
      s!"This creature can't block unless you control a {String.intercalate " or " xs}."

instance : ToString StaticAbility where
  toString := toNotation

end StaticAbility

/-- A triggered ability the engine currently understands (CR 603). -/
inductive TriggeredAbility where
  /-- Whenever this creature attacks, it gets +X/+0 until end of turn, where X
  is the greatest power among creatures you control. -/
  | onAttackPumpByGreatestPower
  /-- Whenever this creature attacks, choose up to one other target creature you
  control. Its base power and toughness become equal to this creature's power
  and toughness until end of turn (e.g. Galion, Elvenking's Butler). -/
  | onAttackSetOtherBasePT
  /-- Whenever this creature attacks, another target creature you control gets
  +2/+0 and gains trample until end of turn (e.g. Oliphaunt). -/
  | onAttackOtherGets2AndTrample
  /-- Whenever this creature becomes blocked, it deals 1 damage to each creature
  blocking it (e.g. Battle-Scarred Goblin). -/
  | onBecomesBlockedDeal1ToBlockers
  /-- When this permanent enters, scry `n` (e.g. Gift of Strands). -/
  | onEnterScry (n : Nat)
  /-- When this permanent enters, you may discard a card. If you do, draw `n`
  cards (e.g. Ragged Short Spear). -/
  | onEnterMayDiscardDraw (n : Nat)
  /-- Landfall — Whenever a land you control enters, put a +1/+1 counter on
  target creature you control (e.g. Beorn's Hospitality). -/
  | onLandYouControlEntersPlusOnePlusOne
  /-- When this permanent enters, it deals `amount` damage divided as you
  choose among one to `maxTargets` targets (e.g. Gandalf, Spark Starter). -/
  | onEnterDealDividedDamage (amount maxTargets : Nat)
  /-- Whenever this creature enters or attacks, it deals `amount` damage divided
  as you choose among one to `maxTargets` targets (e.g. Inferno Titan). -/
  | onEnterOrAttackDealDividedDamage (amount maxTargets : Nat)
  /-- When this creature dies, it deals damage equal to its power to target
  creature an opponent controls (e.g. Goblin Fireleaper). -/
  | onDiesDealDamageEqualToPowerToOppCreature
deriving Repr, Inhabited, BEq

namespace TriggeredAbility

/-- English for “divided as you choose among …” (CR 601.2d). -/
def dividedAmong (maxTargets : Nat) : String :=
  if maxTargets == 3 then "one, two, or three targets"
  else if maxTargets == 1 then "one target"
  else s!"up to {maxTargets} targets"

def toNotation : TriggeredAbility → String
  | .onAttackPumpByGreatestPower =>
    "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
  | .onAttackSetOtherBasePT =>
    "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."
  | .onAttackOtherGets2AndTrample =>
    "Whenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn."
  | .onBecomesBlockedDeal1ToBlockers =>
    "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
  | .onEnterScry n =>
    s!"When this permanent enters, scry {n}."
  | .onEnterMayDiscardDraw n =>
    let cards := if n == 1 then "a card" else s!"{n} cards"
    s!"When this permanent enters, you may discard a card. If you do, draw {cards}."
  | .onLandYouControlEntersPlusOnePlusOne =>
    "Whenever a land you control enters, put a +1/+1 counter on target creature you control."
  | .onEnterDealDividedDamage amount maxTargets =>
    s!"When this permanent enters, it deals {amount} damage divided as you choose among {dividedAmong maxTargets}."
  | .onEnterOrAttackDealDividedDamage amount maxTargets =>
    s!"Whenever this creature enters or attacks, it deals {amount} damage divided as you choose among {dividedAmong maxTargets}."
  | .onDiesDealDamageEqualToPowerToOppCreature =>
    "When this creature dies, it deals damage equal to its power to target creature an opponent controls."

/-- Damage amount and maximum number of targets when this ability divides
damage as the controller chooses (CR 601.2d). -/
def dividedDamage? : TriggeredAbility → Option (Nat × Nat)
  | .onEnterDealDividedDamage amount maxTargets
  | .onEnterOrAttackDealDividedDamage amount maxTargets => some (amount, maxTargets)
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT
  | .onAttackOtherGets2AndTrample | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ | .onLandYouControlEntersPlusOnePlusOne
  | .onDiesDealDamageEqualToPowerToOppCreature => none

/-- True for abilities that trigger as this creature is declared as an attacker (CR 508.2). -/
def triggersWhenAttacking : TriggeredAbility → Bool
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT
  | .onAttackOtherGets2AndTrample | .onEnterOrAttackDealDividedDamage _ _ => true
  | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _ | .onEnterMayDiscardDraw _
  | .onLandYouControlEntersPlusOnePlusOne | .onEnterDealDividedDamage _ _
  | .onDiesDealDamageEqualToPowerToOppCreature => false

/-- True for abilities that trigger as this creature becomes blocked (CR 509.5c). -/
def triggersWhenBecomesBlocked : TriggeredAbility → Bool
  | .onBecomesBlockedDeal1ToBlockers => true
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT | .onAttackOtherGets2AndTrample
  | .onEnterScry _ | .onEnterMayDiscardDraw _ | .onLandYouControlEntersPlusOnePlusOne
  | .onEnterDealDividedDamage _ _ | .onEnterOrAttackDealDividedDamage _ _
  | .onDiesDealDamageEqualToPowerToOppCreature => false

/-- True for abilities that trigger as this permanent enters the battlefield (CR 603.6a). -/
def triggersWhenEntering : TriggeredAbility → Bool
  | .onEnterScry _ | .onEnterMayDiscardDraw _ | .onEnterDealDividedDamage _ _
  | .onEnterOrAttackDealDividedDamage _ _ => true
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT | .onAttackOtherGets2AndTrample
  | .onBecomesBlockedDeal1ToBlockers | .onLandYouControlEntersPlusOnePlusOne
  | .onDiesDealDamageEqualToPowerToOppCreature => false

/-- True for abilities that trigger when a land the controller controls enters
(CR 603.6a, landfall). -/
def triggersWhenLandYouControlEnters : TriggeredAbility → Bool
  | .onLandYouControlEntersPlusOnePlusOne => true
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT | .onAttackOtherGets2AndTrample
  | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ | .onEnterDealDividedDamage _ _
  | .onEnterOrAttackDealDividedDamage _ _ | .onDiesDealDamageEqualToPowerToOppCreature => false

/-- True for abilities that trigger when this creature dies (CR 700.4 / 603.6c). -/
def triggersWhenDying : TriggeredAbility → Bool
  | .onDiesDealDamageEqualToPowerToOppCreature => true
  | .onAttackPumpByGreatestPower | .onAttackSetOtherBasePT | .onAttackOtherGets2AndTrample
  | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ | .onLandYouControlEntersPlusOnePlusOne
  | .onEnterDealDividedDamage _ _ | .onEnterOrAttackDealDividedDamage _ _ => false

/-- True when putting this trigger on the stack requires announcing a target
(CR 603.3d / 601.2c). “Up to one” still announces, including choosing zero. -/
def requiresTarget : TriggeredAbility → Bool
  | .onLandYouControlEntersPlusOnePlusOne | .onEnterDealDividedDamage _ _
  | .onEnterOrAttackDealDividedDamage _ _
  | .onDiesDealDamageEqualToPowerToOppCreature | .onAttackSetOtherBasePT
  | .onAttackOtherGets2AndTrample => true
  | .onAttackPumpByGreatestPower | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ => false

/-- True when zero targets is a legal announcement (CR 115.1c / 601.2c), e.g.
“choose up to one”. Such a trigger is never removed for lack of targets. -/
def allowsZeroTargets : TriggeredAbility → Bool
  | .onAttackSetOtherBasePT => true
  | .onAttackPumpByGreatestPower | .onAttackOtherGets2AndTrample
  | .onBecomesBlockedDeal1ToBlockers | .onEnterScry _
  | .onEnterMayDiscardDraw _ | .onLandYouControlEntersPlusOnePlusOne
  | .onEnterDealDividedDamage _ _ | .onEnterOrAttackDealDividedDamage _ _
  | .onDiesDealDamageEqualToPowerToOppCreature => false

instance : ToString TriggeredAbility where
  toString := toNotation

end TriggeredAbility

/-- Alternative characteristics of an adventurer card while it is a spell
cast as an Adventure (CR 715.2). -/
structure AdventureFace where
  name : String
  manaCost : ManaCost := ManaCost.empty
  types : Array CardType := #[.sorcery]
  subtypes : Array Subtype := #["Adventure"]
  oracleText : String := ""
  spellEffect : Option SpellEffect := none
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
  /-- Alternative characteristics used when this card is cast as an Adventure
  (CR 715). -/
  adventure : Option AdventureFace := none
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
/-- Equipment subtype on an Artifact (CR 301.5). -/
def isEquipment (c : CardDef) : Bool :=
  c.isArtifact && c.subtypes.any (· == "Equipment")

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

/-- True when this card has an Adventure (CR 715). -/
def hasAdventure (c : CardDef) : Bool :=
  c.adventure.isSome

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
#guard SpellEffect.toNotation (.dealDamageToCreature 5) ==
  "deals 5 damage to target creature"
#guard (AbilityEffect.toNotation .searchBasicLandTapped).startsWith "Search your library"
#guard AbilityEffect.toNotation (.dealDamageToTargetCreature 2) ==
  "This creature deals 2 damage to target creature"
#guard AbilityEffect.toNotation .destroyTargetColorlessNonland ==
  "Destroy target colorless nonland permanent"
#guard AbilityEffect.toNotation .attachToTargetCreatureYouControl ==
  "Attach this Equipment to target creature you control"
#guard (AbilityEffect.toNotation .becomeBearCreatureWithLandsPT).startsWith
  "This enchantment becomes a Bear creature"
#guard AbilityEffect.toNotation (.sourceGets 1 0) ==
  "This creature gets +1/+0 until end of turn"
#guard AbilityEffect.requiresTarget (.dealDamageToTargetCreature 2)
#guard AbilityEffect.requiresTarget .destroyTargetColorlessNonland
#guard AbilityEffect.requiresTarget .attachToTargetCreatureYouControl
#guard !AbilityEffect.requiresTarget .searchBasicLandTapped
#guard !AbilityEffect.requiresTarget .becomeBearCreatureWithLandsPT
#guard !AbilityEffect.requiresTarget (.sourceGets 1 0)
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true }
    effect := .searchBasicLandTapped
  }
  (toString ab).startsWith "{2}, {T}, Sacrifice:"
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 1, sacrificeSource := true }
    effect := .dealDamageToTargetCreature 2
    otherModes := #[.destroyTargetColorlessNonland]
  }
  ab.isModal &&
    (toString ab).startsWith "{1}, Sacrifice: Choose one —" &&
    ((toString ab).splitOn "target creature").length > 1 &&
    ((toString ab).splitOn "colorless nonland").length > 1
#guard StaticAbility.toNotation (.otherCreaturesHaveTrample #["Orc", "Goblin"]) ==
  "Other Orcs and Goblins you control have trample."
#guard StaticAbility.toNotation (.enchantedCreatureGets 3 3) ==
  "Enchanted creature gets +3/+3."
#guard StaticAbility.toNotation (.equippedCreatureGets 2 0) ==
  "Equipped creature gets +2/+0."
#guard StaticAbility.toNotation .powerToughnessEqualLandsYouControl ==
  "This creature's power and toughness are each equal to the number of lands you control."
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #["Goblin", "Orc"]) ==
  "This creature can't block unless you control a Goblin or Orc."
#guard StaticAbility.toNotation (.cantBlockUnlessYouControl #[]) ==
  "This creature can't block."
#guard TriggeredAbility.toNotation .onAttackPumpByGreatestPower ==
  "Whenever this creature attacks, it gets +X/+0 until end of turn, where X is the greatest power among creatures you control."
#guard TriggeredAbility.toNotation .onAttackSetOtherBasePT ==
  "Whenever this creature attacks, choose up to one other target creature you control. Its base power and toughness become equal to this creature's power and toughness until end of turn."
#guard TriggeredAbility.toNotation .onAttackOtherGets2AndTrample ==
  "Whenever this creature attacks, another target creature you control gets +2/+0 and gains trample until end of turn."
#guard TriggeredAbility.toNotation .onBecomesBlockedDeal1ToBlockers ==
  "Whenever this creature becomes blocked, it deals 1 damage to each creature blocking it."
#guard TriggeredAbility.toNotation (.onEnterScry 2) ==
  "When this permanent enters, scry 2."
#guard TriggeredAbility.toNotation (.onEnterMayDiscardDraw 2) ==
  "When this permanent enters, you may discard a card. If you do, draw 2 cards."
#guard TriggeredAbility.toNotation .onLandYouControlEntersPlusOnePlusOne ==
  "Whenever a land you control enters, put a +1/+1 counter on target creature you control."
#guard TriggeredAbility.toNotation (.onEnterDealDividedDamage 3 3) ==
  "When this permanent enters, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation (.onEnterOrAttackDealDividedDamage 3 3) ==
  "Whenever this creature enters or attacks, it deals 3 damage divided as you choose among one, two, or three targets."
#guard TriggeredAbility.toNotation .onDiesDealDamageEqualToPowerToOppCreature ==
  "When this creature dies, it deals damage equal to its power to target creature an opponent controls."
#guard TriggeredAbility.dividedDamage? (.onEnterDealDividedDamage 3 3) == some (3, 3)
#guard TriggeredAbility.dividedDamage? (.onEnterOrAttackDealDividedDamage 3 3) == some (3, 3)
#guard (TriggeredAbility.dividedDamage? (.onEnterScry 2)).isNone
#guard (TriggeredAbility.dividedDamage? .onDiesDealDamageEqualToPowerToOppCreature).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackSetOtherBasePT).isNone
#guard (TriggeredAbility.dividedDamage? .onAttackOtherGets2AndTrample).isNone
#guard TriggeredAbility.triggersWhenAttacking .onAttackPumpByGreatestPower
#guard TriggeredAbility.triggersWhenAttacking .onAttackSetOtherBasePT
#guard TriggeredAbility.triggersWhenAttacking .onAttackOtherGets2AndTrample
#guard TriggeredAbility.triggersWhenAttacking (.onEnterOrAttackDealDividedDamage 3 3)
#guard !TriggeredAbility.triggersWhenAttacking (.onEnterDealDividedDamage 3 3)
#guard TriggeredAbility.triggersWhenBecomesBlocked .onBecomesBlockedDeal1ToBlockers
#guard TriggeredAbility.triggersWhenEntering (.onEnterScry 2)
#guard TriggeredAbility.triggersWhenEntering (.onEnterMayDiscardDraw 2)
#guard TriggeredAbility.triggersWhenEntering (.onEnterDealDividedDamage 3 3)
#guard TriggeredAbility.triggersWhenEntering (.onEnterOrAttackDealDividedDamage 3 3)
#guard !TriggeredAbility.triggersWhenEntering .onAttackPumpByGreatestPower
#guard
  let ab : ActivatedAbility := {
    cost := { mana := ManaCost.ofGeneric 3 }
    effect := .attachToTargetCreatureYouControl
    onlyAsSorcery := true
  }
  (toString ab).startsWith "{3}: Attach this Equipment" &&
    (toString ab).endsWith "(activate only as a sorcery)"
#guard TriggeredAbility.triggersWhenLandYouControlEnters .onLandYouControlEntersPlusOnePlusOne
#guard !TriggeredAbility.triggersWhenLandYouControlEnters (.onEnterScry 2)
#guard TriggeredAbility.requiresTarget .onLandYouControlEntersPlusOnePlusOne
#guard TriggeredAbility.requiresTarget (.onEnterDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget (.onEnterOrAttackDealDividedDamage 3 3)
#guard TriggeredAbility.requiresTarget .onDiesDealDamageEqualToPowerToOppCreature
#guard TriggeredAbility.requiresTarget .onAttackSetOtherBasePT
#guard TriggeredAbility.requiresTarget .onAttackOtherGets2AndTrample
#guard TriggeredAbility.allowsZeroTargets .onAttackSetOtherBasePT
#guard !TriggeredAbility.allowsZeroTargets .onAttackOtherGets2AndTrample
#guard !TriggeredAbility.allowsZeroTargets .onLandYouControlEntersPlusOnePlusOne
#guard TriggeredAbility.triggersWhenDying .onDiesDealDamageEqualToPowerToOppCreature
#guard !TriggeredAbility.triggersWhenDying (.onEnterScry 2)
#guard !TriggeredAbility.requiresTarget (.onEnterScry 2)

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

end AdventureFace

#guard
  let adv : AdventureFace := {
    name := "Spew Flame"
    manaCost := ManaCost.ofGenericAndColor 4 .red
    oracleText := "Spew Flame deals 5 damage to target creature."
    spellEffect := some (.dealDamageToCreature 5)
  }
  let c := adv.toCardDef
  c.name == "Spew Flame" && c.isSorcery && c.requiresTarget &&
    c.subtypes.any (· == "Adventure")

/-- Constructed-play four-of rule applies to non-basic-land English names (CR 100.2a). -/
def isBasicLandCard (c : CardDef) : Bool :=
  c.isLand && c.supertypes.any (· == .basic)

end Mtg.Engine
