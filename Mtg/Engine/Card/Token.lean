import Mtg.Engine.Card.Keywords
import Mtg.Engine.Card.Text
import Mtg.Engine.Card.Primitives

/-!
# Token specifications (CR 111, 707.9)

Unified, parameterized `TokenSpec` anchored to the 25 September 2026
Comprehensive Rules:
- `PredefinedToken` (CR 111.10a–x)
- `CustomTokenSpec` (CR 111.3 / 111.4 / 111.11)
- `CopyTargetRef` / `CopyModification` (CR 707.9)
-/

namespace Mtg.Engine

/-- Predefined tokens defined directly by CR 111.10a–x (25 September 2026). -/
inductive PredefinedToken where
  /-- CR 111.10a: Colorless Treasure artifact token. -/
  | treasure
  /-- CR 111.10b: Colorless Food artifact token. -/
  | food
  /-- CR 111.10f: Colorless Clue artifact token. -/
  | clue
  /-- CR 111.10i: Transforming colorless Incubator artifact token. -/
  | incubator
  /-- CR 111.10s: Colorless Map artifact token. -/
  | map
  /-- CR 111.10t: Colorless Junk artifact token. -/
  | junk
  /-- CR 111.10u: Colorless Lander artifact token. -/
  | lander
  /-- CR 111.10v: Colorless Mutagen artifact token. -/
  | mutagen
  /-- CR 111.10w: Colorless Vibranium artifact token (indestructible; `{T}: Add {C}`, not for nonartifact spells). -/
  | vibranium
  /-- CR 111.10x: Red and green Heartwood artifact token (`{T}: Add {R} or {G}`). -/
  | heartwood
deriving DecidableEq, Repr, Inhabited, BEq

namespace PredefinedToken

def name : PredefinedToken → String
  | .treasure => "Treasure"
  | .food => "Food"
  | .clue => "Clue"
  | .incubator => "Incubator"
  | .map => "Map"
  | .junk => "Junk"
  | .lander => "Lander"
  | .mutagen => "Mutagen"
  | .vibranium => "Vibranium"
  | .heartwood => "Heartwood"

def oracleNoun (p : PredefinedToken) : String :=
  s!"{p.name} token"

end PredefinedToken

/-- Power or toughness component of a custom token (CR 111.3 / 107.3; generalized
to `ValueExpr` in Phase 2). -/
inductive TokenStat where
  | fixed (n : Int)
  | chosenX
deriving DecidableEq, Repr, Inhabited, BEq

namespace TokenStat

def toOracle : TokenStat → String
  | .fixed n => toString n
  | .chosenX => "X"

def eval (x : Nat := 0) : TokenStat → Int
  | .fixed n => n
  | .chosenX => Int.ofNat x

end TokenStat

/-- Parameterized abilities carried by custom tokens (CR 111.3; generalized to
the full mutual `Ability` AST in Phase 8). -/
inductive TokenAbilitySpec where
  /-- Toxic `n` (CR 702.164). -/
  | toxic (n : Nat)
  /-- This token can't block (CR 509.1b). -/
  | cantBlock
  /-- This token attacks each combat if able (CR 508.1d). -/
  | attacksEachCombatIfAble
  /-- This token can't be blocked by more than `n` creature(s) (CR 509.1b). -/
  | cantBeBlockedByMoreThan (n : Nat)
  /-- Equipped creature gets `+power/+toughness` (CR 301.5). -/
  | equippedCreatureGets (power toughness : Int)
  /-- `Equip {generic}` (CR 702.6a). -/
  | equipGeneric (generic : Nat)
  /-- `{T}, Sacrifice this token: Add <amount> mana of any one color.` -/
  | tapSacrificeAddAnyOneColor (amount : Nat := 1)
  /-- `{generic}, {T}, Sacrifice this token: You gain <life> life.` -/
  | tapSacrificeGainLife (generic life : Nat)
  /-- `{generic}: This token can't be blocked this turn except by creatures with haste.` -/
  | payGenericCantBeBlockedExceptHaste (generic : Nat)
  /-- `[-cost]: Surveil <n>.` (CR 606). -/
  | loyaltyMinusSurveil (cost n : Nat)
  /-- `[-cost]: Draw <n> card(s).` (CR 606). -/
  | loyaltyMinusDraw (cost n : Nat)
  /-- `"Whenever this token attacks, you may mill <n> card(s)."` -/
  | onAttackMayMill (n : Nat)
  /-- `"Whenever this token attacks, scry <n>."` -/
  | onAttackScry (n : Nat)
  /-- `"Whenever this token attacks, destroy target land."` -/
  | onAttackDestroyTargetLand
  /-- `"Whenever you gain life, put <n> +1/+1 counter(s) on this token."` -/
  | onGainLifePutPlusOne (n : Nat := 1)
  /-- `"Whenever a land you control enters, put <n> +1/+1 counter(s) on this token."` -/
  | onLandYouControlEntersPutPlusOne (n : Nat := 1)
deriving DecidableEq, Repr, Inhabited, BEq

namespace TokenAbilitySpec

/-- Quoted rules-text suffix printed inside `CustomTokenSpec.oracleNoun` when
Oracle text writes `with "..."` inline on the token description. -/
def oracleQuote? : TokenAbilitySpec → Option String
  | .tapSacrificeAddAnyOneColor 1 =>
    some "{T}, Sacrifice this token: Add one mana of any color."
  | .onAttackMayMill 1 =>
    some "Whenever this token attacks, you may mill a card."
  | .onGainLifePutPlusOne 1 =>
    some "Whenever you gain life, put a +1/+1 counter on this token."
  | _ => none

end TokenAbilitySpec

/-- Characteristics of a custom token (CR 111.3 / 111.4 / 111.11). -/
structure CustomTokenSpec where
  /-- Explicit name when differing from default CR 111.4 subtype name (e.g.
  `named Stone Boulder`, `named Doombot`, or CR 111.11 `Lotus` / `Gingerbrute`). -/
  name? : Option String := none
  supertypes : Array Supertype := #[]
  types : Array CardType := #[.creature]
  subtypes : Array CardSubtype := #[]
  colors : ColorSet := ColorSet.empty
  power? : Option TokenStat := none
  toughness? : Option TokenStat := none
  loyalty? : Option Int := none
  keywords : Keywords := Keywords.none
  abilities : Array TokenAbilitySpec := #[]
  /-- True for CR 111.11 Oracle-card-named shorthand tokens printed as
  `"<Name> token"` (e.g. `"Lotus token"`, `"Gingerbrute token"`). -/
  useCardNameShorthand : Bool := false
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange CustomTokenSpec where
  applyTextChanges tcs s :=
    if tcs.isEmpty then s
    else
      { s with
        subtypes := HasTextChange.applyTextChanges tcs s.subtypes
        colors := HasTextChange.applyTextChanges tcs s.colors }

/-- Reference to the object being copied by `TokenSpec.copyOf` (CR 707.9;
generalized to `ObjectExpr` in Phase 2). -/
inductive CopyTargetRef where
  | source
  | target
  | triggerSubject
deriving DecidableEq, Repr, Inhabited, BEq

/-- Modification applied while creating a token copy (CR 707.9). -/
inductive CopyModification where
  | setName (name : String)
  | setBasePT (power toughness : Int)
  | addTypes (types : Array CardType)
  | addSubtypes (subtypes : Array CardSubtype)
  | addColors (colors : ColorSet)
  | removeSupertype (supertype : Supertype)
  | addKeywords (keywords : Keywords)
  | addAbilities (abilities : Array TokenAbilitySpec)
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange CopyModification where
  applyTextChanges tcs m :=
    if tcs.isEmpty then m
    else
      match m with
      | .addSubtypes subs => .addSubtypes (HasTextChange.applyTextChanges tcs subs)
      | .addColors cols => .addColors (HasTextChange.applyTextChanges tcs cols)
      | other => other

/-- Unified, parameterized token specification (CR 111, 707.9). -/
inductive TokenSpec where
  /-- A CR 111.10a–x predefined token (Treasure, Food, Clue, Incubator, Map, etc.). -/
  | predefined (kind : PredefinedToken)
  /-- A custom token with explicit characteristics, including CR 111.11 card-named tokens. -/
  | custom (spec : CustomTokenSpec)
  /-- A token copy of a referenced object with optional CR 707.9 exceptions. -/
  | copyOf (ref : CopyTargetRef) (mods : Array CopyModification := #[])
deriving DecidableEq, Repr, Inhabited, BEq

instance : HasTextChange TokenSpec where
  applyTextChanges tcs t :=
    if tcs.isEmpty then t
    else
      match t with
      | .predefined k => .predefined k
      | .custom s => .custom (HasTextChange.applyTextChanges tcs s)
      | .copyOf tgt mods => .copyOf tgt (HasTextChange.applyTextChanges tcs mods)

namespace TokenSpec

-- CR 111.10a–x predefined token shortcuts.
def treasure : TokenSpec := .predefined .treasure
def food : TokenSpec := .predefined .food
def clue : TokenSpec := .predefined .clue
def incubator : TokenSpec := .predefined .incubator
def map : TokenSpec := .predefined .map
def junk : TokenSpec := .predefined .junk
def lander : TokenSpec := .predefined .lander
def mutagen : TokenSpec := .predefined .mutagen
def vibranium : TokenSpec := .predefined .vibranium
def heartwood : TokenSpec := .predefined .heartwood

/-- Helper for standard fixed-P/T custom creature tokens. -/
def creature (subtypes : Array CardSubtype) (power toughness : Int)
    (colors : ColorSet := ColorSet.empty)
    (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature])
    (supertypes : Array Supertype := #[])
    (name? : Option String := none)
    (abilities : Array TokenAbilitySpec := #[]) : TokenSpec :=
  .custom {
    name?, supertypes, types, subtypes, colors
    power? := some (.fixed power)
    toughness? := some (.fixed toughness)
    keywords, abilities
  }

-- Canonical custom token definitions (CR 111.3 / 111.11).
def humanSoldier : TokenSpec :=
  creature #[.human, .soldier] 1 1 (ColorSet.singleton .white)

def wolf : TokenSpec :=
  creature #[.wolf] 2 2 (ColorSet.singleton .green)

def dwarf : TokenSpec :=
  creature #[.dwarf] 2 2 (ColorSet.singleton .red)

def bear : TokenSpec :=
  creature #[.bear] 2 2 (ColorSet.singleton .green)

def elf : TokenSpec :=
  creature #[.elf] 1 1 (ColorSet.singleton .green)

def spirit : TokenSpec :=
  creature #[.spirit] 1 1 (ColorSet.singleton .white) Keyword.flying

def birdSoldier : TokenSpec :=
  creature #[.bird, .soldier] 4 4 (ColorSet.singleton .white) Keyword.flying

def wall : TokenSpec :=
  creature #[.wall] 3 1 ColorSet.empty Keyword.defender
    (types := #[.artifact, .creature]) (name? := some "Stone Boulder")

def dragon : TokenSpec :=
  creature #[.dragon] 6 6 (ColorSet.singleton .red) Keyword.flying

def hero32vigilance : TokenSpec :=
  creature #[.hero] 3 2 (ColorSet.singleton .white) Keyword.vigilance

def villain21menace : TokenSpec :=
  creature #[.villain] 2 1 (ColorSet.singleton .black) Keyword.menace

def robotVillain22 : TokenSpec :=
  creature #[.robot, .villain] 2 2 ColorSet.empty
    (types := #[.artifact, .creature])

def leviathan65hexproof : TokenSpec :=
  creature #[.leviathan] 6 5 (ColorSet.singleton .blue) Keyword.hexproof

def soldier11white : TokenSpec :=
  creature #[.soldier] 1 1 (ColorSet.singleton .white)

def squirrel11green : TokenSpec :=
  creature #[.squirrel] 1 1 (ColorSet.singleton .green)

def wall04defender : TokenSpec :=
  creature #[.wall] 0 4 ColorSet.empty Keyword.defender

def doombot : TokenSpec :=
  creature #[.robot, .villain] 3 3 ColorSet.empty
    (types := #[.artifact, .creature]) (name? := some "Doombot")

def insect11green : TokenSpec :=
  creature #[.insect] 1 1 (ColorSet.singleton .green)

def moloid : TokenSpec :=
  creature #[.minion] 1 1 (ColorSet.singleton .green)
    (name? := some "Moloid") (abilities := #[.onAttackMayMill 1])

def cadet : TokenSpec :=
  creature #[.wizard, .soldier] 2 2 ColorSet.empty (name? := some "Cadet")

def lotus : TokenSpec :=
  .custom {
    name? := some "Lotus"
    types := #[.artifact]
    abilities := #[.tapSacrificeAddAnyOneColor 3]
    useCardNameShorthand := true
  }

def jace : TokenSpec :=
  .custom {
    name? := some "Jace"
    types := #[.planeswalker]
    subtypes := #[.jace]
    colors := ColorSet.singleton .blue
    loyalty? := some 0
    abilities := #[.loyaltyMinusSurveil 1 1, .loyaltyMinusDraw 3 1]
  }

def sculpture : TokenSpec :=
  creature #[.sculpture, .treasure] 1 1 ColorSet.empty
    (types := #[.artifact, .creature]) (abilities := #[.tapSacrificeAddAnyOneColor 1])

def mowu : TokenSpec :=
  creature #[.dog] 3 3 (ColorSet.singleton .green)
    (supertypes := #[.legendary]) (name? := some "Mowu")

def pridemate : TokenSpec :=
  creature #[.cat, .soldier] 2 2 (ColorSet.singleton .white)
    (name? := some "Ajani's Pridemate") (abilities := #[.onGainLifePutPlusOne 1])

def beast44trample : TokenSpec :=
  creature #[.beast] 4 4 (ColorSet.singleton .green) Keyword.trample

def dragon55flying : TokenSpec :=
  creature #[.dragon] 5 5 (ColorSet.singleton .red) Keyword.flying

def forestTentacle : TokenSpec :=
  creature #[.forest, .tentacle] 3 3 (ColorSet.singleton .green)
    (types := #[.land, .creature])

def thopter : TokenSpec :=
  creature #[.thopter] 1 1 ColorSet.empty Keyword.flying
    (types := #[.artifact, .creature])

def angel33blue : TokenSpec :=
  creature #[.angel] 3 3 (ColorSet.singleton .blue) Keyword.flying

def illusion11blue : TokenSpec :=
  creature #[.illusion] 1 1 (ColorSet.singleton .blue)

def leviathan88hexproof : TokenSpec :=
  creature #[.leviathan] 8 8 (ColorSet.singleton .blue) Keyword.hexproof

-- Named and specialized custom tokens.
def axe : TokenSpec :=
  .custom {
    name? := some "Axe"
    types := #[.artifact]
    subtypes := #[.equipment]
    abilities := #[.equippedCreatureGets 1 0, .equipGeneric 2]
  }

def zabu : TokenSpec :=
  creature #[.cat] 2 2 (ColorSet.singleton .green)
    (supertypes := #[.legendary]) (name? := some "Zabu")
    (abilities := #[.onLandYouControlEntersPutPlusOne 1])

def theVoid : TokenSpec :=
  creature #[.horror, .villain] 5 5 (ColorSet.singleton .black)
    (Keyword.flying.merge Keyword.indestructible)
    (supertypes := #[.legendary]) (name? := some "The Void")
    (abilities := #[.attacksEachCombatIfAble])

def redwing : TokenSpec :=
  creature #[.bird, .scout] 1 1 (ColorSet.singleton .blue) Keyword.flying
    (supertypes := #[.legendary]) (name? := some "Redwing")
    (abilities := #[.onAttackScry 1])

def alien : TokenSpec :=
  creature #[.alien] 1 1 (ColorSet.singleton .red) Keyword.haste
    (abilities := #[.attacksEachCombatIfAble])

def sturdyShield : TokenSpec :=
  .custom {
    name? := some "Sturdy Shield"
    types := #[.artifact]
    subtypes := #[.equipment]
    abilities := #[.equippedCreatureGets 1 2, .equipGeneric 2]
  }

def galactus : TokenSpec :=
  creature #[.elder, .alien] 16 16 (ColorSet.singleton .black)
    (Keyword.flying.merge Keyword.trample)
    (supertypes := #[.legendary]) (name? := some "Galactus")
    (abilities := #[.onAttackDestroyTargetLand])

def merfolk : TokenSpec :=
  creature #[.merfolk] 1 1 (ColorSet.singleton .blue)

def tigerGod : TokenSpec :=
  creature #[.cat, .god] 4 4 (ColorSet.singleton .green)
    (supertypes := #[.legendary]) (name? := some "The Tiger God")
    (abilities := #[.cantBeBlockedByMoreThan 1])

-- Additional custom tokens (Commander / special sets).
def citizen : TokenSpec :=
  creature #[.citizen] 1 1 (ColorSet.ofList [.green, .white])

def warrior : TokenSpec :=
  creature #[.warrior] 1 1 (ColorSet.singleton .white)

def insect21flying : TokenSpec :=
  creature #[.insect] 2 1 (ColorSet.singleton .white) Keyword.flying

def myr : TokenSpec :=
  creature #[.myr] 1 1 ColorSet.empty (types := #[.artifact, .creature])

def kobold : TokenSpec :=
  creature #[.kobold] 0 1 (ColorSet.singleton .red)
    (name? := some "Kobolds of Kher Keep")

def mite : TokenSpec :=
  creature #[.phyrexian, .mite] 1 1 ColorSet.empty
    (types := #[.artifact, .creature]) (abilities := #[.toxic 1, .cantBlock])

def sharkX : TokenSpec :=
  .custom {
    types := #[.creature]
    subtypes := #[.shark]
    colors := ColorSet.singleton .blue
    power? := some .chosenX
    toughness? := some .chosenX
    keywords := Keyword.flying
  }

def gingerbrute : TokenSpec :=
  .custom {
    name? := some "Gingerbrute"
    types := #[.artifact, .creature]
    subtypes := #[.food, .golem]
    power? := some (.fixed 1)
    toughness? := some (.fixed 1)
    keywords := Keyword.haste
    abilities := #[.payGenericCantBeBlockedExceptHaste 1, .tapSacrificeGainLife 2 3]
    useCardNameShorthand := true
  }

def angel44white : TokenSpec :=
  creature #[.angel] 4 4 (ColorSet.singleton .white) Keyword.flying

def human11white : TokenSpec :=
  creature #[.human] 1 1 (ColorSet.singleton .white)

def goblin11red : TokenSpec :=
  creature #[.goblin] 1 1 (ColorSet.singleton .red)

def rogue22black : TokenSpec :=
  creature #[.rogue] 2 2 (ColorSet.singleton .black)

private def supertypeLower : Supertype → String
  | .basic => "basic"
  | .legendary => "legendary"
  | .ongoing => "ongoing"
  | .snow => "snow"
  | .world => "world"

private def cardTypeLower : CardType → String
  | .artifact => "artifact"
  | .battle => "battle"
  | .conspiracy => "conspiracy"
  | .creature => "creature"
  | .dungeon => "dungeon"
  | .enchantment => "enchantment"
  | .instant => "instant"
  | .kindred => "kindred"
  | .land => "land"
  | .phenomenon => "phenomenon"
  | .plane => "plane"
  | .planeswalker => "planeswalker"
  | .scheme => "scheme"
  | .sorcery => "sorcery"
  | .vanguard => "vanguard"

/-- Oracle singular noun phrase for a custom token (CR 111.3 / 111.11). -/
def customOracleNoun (s : CustomTokenSpec) : String :=
  if s.useCardNameShorthand then
    match s.name? with
    | some n => s!"{n} token"
    | none => "token"
  else
    let supParts := s.supertypes.toList.map supertypeLower
    let ptParts :=
      match s.power?, s.toughness? with
      | some p, some t => [s!"{p.toOracle}/{t.toOracle}"]
      | _, _ => []
    let colorParts :=
      if s.colors.isColorless then ["colorless"]
      else [String.intercalate " and " (s.colors.toList.map Color.englishName)]
    let subtypeParts := s.subtypes.toList.map CardSubtype.englishName
    let typeParts := s.types.toList.map cardTypeLower
    let kwList := s.keywords.toList
    let kwSuffix :=
      if kwList.isEmpty then []
      else ["with " ++ String.intercalate " and " kwList]
    let defaultName := String.intercalate " " subtypeParts
    let nameSuffix :=
      match s.name? with
      | some n => if n == defaultName then [] else [s!"named {n}"]
      | none => []
    let abilityQuotes := s.abilities.toList.filterMap TokenAbilitySpec.oracleQuote?
    let abilitySuffix :=
      if abilityQuotes.isEmpty then []
      else ["with " ++ String.intercalate " and " (abilityQuotes.map fun q => s!"\"{q}\"")]
    String.intercalate " "
      (supParts ++ ptParts ++ colorParts ++ subtypeParts ++ typeParts ++
        ["token"] ++ kwSuffix ++ nameSuffix ++ abilitySuffix)

/-- Oracle singular noun phrase for `t` (CR 111.3 / 111.10 / 111.11 / 707.9). -/
def oracleNoun : TokenSpec → String
  | .predefined p => p.oracleNoun
  | .custom s => customOracleNoun s
  | .copyOf _ _ => "token that's a copy"

/-- Plural Oracle noun: the singular form with `token` → `tokens`. -/
def pluralNoun (t : TokenSpec) : String :=
  t.oracleNoun.replace "token" "tokens"

/-- Noun phrase for `n` created tokens (`a Treasure token`, `two 2/2 green
Wolf creature tokens`). `createPhrase` and “that player creates …” wordings
share it. -/
def createdTokensPhrase (t : TokenSpec) (n : Nat) (tapped := false) : String :=
  let tappedS := if tapped then "tapped " else ""
  if n == 1 then
    s!"a {tappedS}{t.oracleNoun}"
  else
    s!"{englishNumber n} {tappedS}{t.pluralNoun}"

/-- Oracle “create …” clause for `n` tokens of this spec. -/
def createPhrase (t : TokenSpec) (n : Nat) (tapped := false) : String :=
  s!"create {t.createdTokensPhrase n tapped}"

-- Regression `#guard`s verifying exact Oracle noun fidelity across catalog token specs.
#guard oracleNoun .treasure == "Treasure token"
#guard oracleNoun .food == "Food token"
#guard oracleNoun .humanSoldier == "1/1 white Human Soldier creature token"
#guard oracleNoun .wolf == "2/2 green Wolf creature token"
#guard oracleNoun .dwarf == "2/2 red Dwarf creature token"
#guard oracleNoun .bear == "2/2 green Bear creature token"
#guard oracleNoun .elf == "1/1 green Elf creature token"
#guard oracleNoun .spirit == "1/1 white Spirit creature token with flying"
#guard oracleNoun .birdSoldier == "4/4 white Bird Soldier creature token with flying"
#guard oracleNoun .wall == "3/1 colorless Wall artifact creature token with defender named Stone Boulder"
#guard oracleNoun .dragon == "6/6 red Dragon creature token with flying"
#guard oracleNoun .clue == "Clue token"
#guard oracleNoun .hero32vigilance == "3/2 white Hero creature token with vigilance"
#guard oracleNoun .villain21menace == "2/1 black Villain creature token with menace"
#guard oracleNoun .robotVillain22 == "2/2 colorless Robot Villain artifact creature token"
#guard oracleNoun .leviathan65hexproof == "6/5 blue Leviathan creature token with hexproof"
#guard oracleNoun .soldier11white == "1/1 white Soldier creature token"
#guard oracleNoun .squirrel11green == "1/1 green Squirrel creature token"
#guard oracleNoun .wall04defender == "0/4 colorless Wall creature token with defender"
#guard oracleNoun .doombot == "3/3 colorless Robot Villain artifact creature token named Doombot"
#guard oracleNoun .insect11green == "1/1 green Insect creature token"
#guard oracleNoun .vibranium == "Vibranium token"
#guard oracleNoun .moloid ==
  "1/1 green Minion creature token named Moloid with \"Whenever this token attacks, you may mill a card.\""
#guard oracleNoun .cadet == "2/2 colorless Wizard Soldier creature token named Cadet"
#guard oracleNoun .heartwood == "Heartwood token"
#guard oracleNoun .lotus == "Lotus token"
#guard oracleNoun .jace == "blue Jace planeswalker token"
#guard oracleNoun .sculpture ==
  "1/1 colorless Sculpture Treasure artifact creature token with \"{T}, Sacrifice this token: Add one mana of any color.\""
#guard oracleNoun .mowu == "legendary 3/3 green Dog creature token named Mowu"
#guard oracleNoun .pridemate ==
  "2/2 white Cat Soldier creature token named Ajani's Pridemate with \"Whenever you gain life, put a +1/+1 counter on this token.\""
#guard oracleNoun .beast44trample == "4/4 green Beast creature token with trample"
#guard oracleNoun .dragon55flying == "5/5 red Dragon creature token with flying"
#guard oracleNoun .forestTentacle == "3/3 green Forest Tentacle land creature token"
#guard oracleNoun .thopter == "1/1 colorless Thopter artifact creature token with flying"
#guard oracleNoun .angel33blue == "3/3 blue Angel creature token with flying"
#guard oracleNoun .illusion11blue == "1/1 blue Illusion creature token"
#guard oracleNoun .leviathan88hexproof == "8/8 blue Leviathan creature token with hexproof"
#guard oracleNoun .gingerbrute == "Gingerbrute token"
#guard oracleNoun .incubator == "Incubator token"
#guard oracleNoun .map == "Map token"
#guard pluralNoun .treasure == "Treasure tokens"
#guard pluralNoun .spirit == "1/1 white Spirit creature tokens with flying"
#guard pluralNoun .doombot ==
  "3/3 colorless Robot Villain artifact creature tokens named Doombot"
#guard createPhrase .wolf 2 == "create two 2/2 green Wolf creature tokens"
#guard createPhrase .elf 3 == "create three 1/1 green Elf creature tokens"

end TokenSpec

end Mtg.Engine
