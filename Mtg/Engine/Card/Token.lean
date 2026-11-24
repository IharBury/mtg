import Mtg.Engine.Card.Ability

/-!
# Token specifications & canonical token constructors (CR 111, 707.9)

Smart constructors, `ToOracle` rendering, and regression guards for the unified
`TokenSpec` (`PredefinedToken`, `CustomTokenSpec`, `CopyModification`) defined
in `Mtg/Engine/Card/Ability.lean`, with token abilities represented directly as
mutual `GrantedAbility` values.
-/

namespace Mtg.Engine

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

namespace GrantedAbility

private def tokenEquippedCreatureScope : ObjectFilter :=
  { zones := .battlefield
    pred := .all #[
      .hasType .creature,
      .hasAttachment { zones := .battlefield
                       pred := .all #[.sameAs .this, .hasSubtype (.literal .equipment)] }
    ] }

/-- `Toxic n` (CR 702.164). -/
def toxic (n : Nat) : GrantedAbility :=
  .keyword (.toxic n)

/-- `"This token can't block"` (CR 509.1b). -/
def cantBlock : GrantedAbility :=
  .static (.ruleModifying none (.combat (.cantBlock .self none)))

/-- `"This token attacks each combat if able"` (CR 508.1d). -/
def attacksEachCombatIfAble : GrantedAbility :=
  .static (.ruleModifying none (.combat (.attacksEachCombatIfAble .self)))

/-- `"This token can't be blocked by more than n creature(s)"` (CR 509.1b). -/
def cantBeBlockedByMoreThan (n : Nat) : GrantedAbility :=
  .static (.ruleModifying none (.combat (.maxBlockers .self n)))

/-- `"Equipped creature gets +power/+toughness"` (CR 301.5). -/
def equippedCreatureGets (power toughness : Int) : GrantedAbility :=
  .static (.continuous none tokenEquippedCreatureScope
    (.modifyPT (.const power) (.const toughness)))

/-- `Equip {generic}` (CR 702.6a). -/
def equipGeneric (generic : Nat) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofGeneric generic
    effect := {
      targets := .creatureYouControl
      body := .permanent (.attach .this (.target 0))
    }
    timing := .sorcery
    tag? := some (.equip none)
  }

/-- `"{T}, Sacrifice this token: Add <amount> mana of any one color."` -/
def tapSacrificeAddAnyOneColor (amount : Nat := 1) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self]
    effect := {
      body := .player (.addMana .you { spec := .oneOf .anyColor (.const (Int.ofNat amount)) })
    }
  }

/-- `"{generic}, {T}, Sacrifice this token: You gain <life> life."` -/
def tapSacrificeGainLife (generic life : Nat) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofItems #[.mana (ManaCost.ofGeneric generic), .tapSelf, .sacrifice (.exact 1) .self]
    effect := {
      body := .life (.gain .you (.const (Int.ofNat life)))
    }
  }

/-- `"{generic}: This token can't be blocked this turn except by creatures with haste."` -/
def payGenericCantBeBlockedExceptHaste (generic : Nat) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofGeneric generic
    effect := {
      body := .installEffect (.applyContinuous .untilEndOfTurn .this
        (.applyRule (.combat (.cantBeBlockedBy .self (.not (.hasKeyword .haste))))))
    }
  }

/-- `"[-cost]: Surveil n."` (CR 606). -/
def loyaltyMinusSurveil (cost n : Nat) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofItem (.loyalty (.minus cost))
    timing := .loyalty
    effect := {
      body := .player (.surveil .you (.const (Int.ofNat n)))
    }
  }

/-- `"[-cost]: Draw n card(s)."` (CR 606). -/
def loyaltyMinusDraw (cost n : Nat) : GrantedAbility :=
  .activated {
    cost := CostSpec.ofItem (.loyalty (.minus cost))
    timing := .loyalty
    effect := {
      body := .player (.drawCards .you (.const (Int.ofNat n)))
    }
  }

/-- `"Whenever this token attacks, you may mill n card(s)."` -/
def onAttackMayMill (n : Nat) : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .thisAttacks
    effect := {
      body := .optional .you none
        (.moveZone (.topOfLibrary .you (.const (Int.ofNat n))) .graveyard .mill) .noop
    }
  }

/-- `"Whenever this token attacks, scry n."` -/
def onAttackScry (n : Nat) : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .thisAttacks
    effect := {
      body := .player (.scry .you (.const (Int.ofNat n)))
    }
  }

/-- `"Whenever this token attacks, surveil n."` -/
def onAttackSurveil (n : Nat) : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .thisAttacks
    effect := {
      body := .player (.surveil .you (.const (Int.ofNat n)))
    }
  }

/-- `"Whenever this token attacks, destroy target land."` -/
def onAttackDestroyTargetLand : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .thisAttacks
    effect := {
      targets := .land
      body := .moveZone (.target 0) .graveyard .destroy
    }
  }

/-- `"Whenever you gain life, put n +1/+1 counter(s) on this token."` -/
def onGainLifePutPlusOne (n : Nat := 1) : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .gainLife .you
    effect := {
      body := .permanent (.modifyCounters (.put .plusOnePlusOne (.const (Int.ofNat n))) .this)
    }
  }

/-- `"Whenever a land you control enters, put n +1/+1 counter(s) on this token."` -/
def onLandYouControlEntersPutPlusOne (n : Nat := 1) : GrantedAbility :=
  .triggered {
    word := .whenever
    pattern := .landYouControlEnters
    effect := {
      body := .permanent (.modifyCounters (.put .plusOnePlusOne (.const (Int.ofNat n))) .this)
    }
  }

/-- Quoted rules-text suffix printed inside `CustomTokenSpec.oracleNoun` when
Oracle text writes `with "..."` inline on the token description. -/
def oracleQuote? : GrantedAbility → Option String
  | .activated ab =>
    if ab.cost == CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self] &&
        ab.effect.body == .player (.addMana .you { spec := .oneOf .anyColor (.const 1) }) then
      some "{T}, Sacrifice this token: Add one mana of any color."
    else if ab.cost == CostSpec.ofItems #[.tapSelf, .sacrifice (.exact 1) .self] then
      match ab.effect.body with
      | .player (.addMana .you { spec := .oneOf .anyColor (.const n), .. }) =>
        some s!"\{T}, Sacrifice this token: Add {englishNumber n.toNat} mana of any one color."
      | _ => none
    else if ab.tag? == some (.equip none) then
      some s!"Equip {ab.cost.mana}"
    else none
  | .triggered ab =>
    match ab.pattern, ab.effect.body with
    | .thisAttacks, .optional .you none
        (.moveZone (.topOfLibrary .you (.const n)) .graveyard .mill _) .noop 1 =>
      if n == 1 then some "Whenever this token attacks, you may mill a card."
      else some s!"Whenever this token attacks, you may mill {n.toNat} cards."
    | .thisAttacks, .player (.scry .you (.const n)) =>
      some s!"Whenever this token attacks, scry {n.toNat}."
    | .thisAttacks, .player (.surveil .you (.const n)) =>
      some s!"Whenever this token attacks, surveil {n.toNat}."
    | .thisAttacks, .moveZone (.target 0) .graveyard .destroy _ =>
      if ab.effect.targets == .land then
        some "Whenever this token attacks, destroy target land."
      else none
    | .gainLife .you, .permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) .this none) =>
      if n == 1 then some "Whenever you gain life, put a +1/+1 counter on this token."
      else some s!"Whenever you gain life, put {plusOnePlusOneCountersPhrase n.toNat} on this token."
    | .landYouControlEnters, .permanent (.modifyCounters (.put .plusOnePlusOne (.const n)) .this none) =>
      if n == 1 then some "Whenever a land you control enters, put a +1/+1 counter on this token."
      else some s!"Whenever a land you control enters, put {plusOnePlusOneCountersPhrase n.toNat} on this token."
    | .stepBegins .end (.player .any), .moveZone .this .graveyard .sacrifice _ =>
      match ab.interveningIf? with
      | some c => some s!"At the beginning of the end step, if {toOracleStr c { capitalize := false }}, sacrifice this creature."
      | none => some "At the beginning of the end step, sacrifice this creature."
    | _, _ => none
  | .static sa =>
    match sa with
    | .ruleModifying none (.combat (.cantBlock .self none)) =>
      some "This token can't block."
    | .ruleModifying none (.combat (.attacksEachCombatIfAble .self)) =>
      some "This token attacks each combat if able."
    | .ruleModifying none (.combat (.maxBlockers .self n)) =>
      let w := if n == 1 then "one creature" else s!"{englishNumber n} creatures"
      some s!"This token can't be blocked by more than {w}."
    | .continuous none _ (.modifyPT (.const p) (.const t)) =>
      let ps := if p >= 0 then s!"+{p}" else s!"{p}"
      let ts := if t >= 0 then s!"+{t}" else s!"{t}"
      some s!"Equipped creature gets {ps}/{ts}"
    | _ => none
  | _ => none

end GrantedAbility

namespace CopyModification

/-- Render one `CopyModification` as an Oracle exception phrase (CR 707.9). -/
def toOraclePhrase? : CopyModification → Option String
  | .setName name => some s!"its name is {name}"
  | .setBasePT p t => some s!"it's {p}/{t}"
  | .addSupertypes sups =>
    if sups.isEmpty then none
    else some s!"it's {String.intercalate " " (sups.toList.map Supertype.oracleWord)}"
  | .addTypes tys =>
    if tys.isEmpty then none
    else some s!"it's {String.intercalate " " (tys.toList.map CardType.oracleWord)} in addition to its other types"
  | .addSubtypes subs =>
    if subs.isEmpty then none
    else some s!"it's a {String.intercalate " " (subs.toList.map CardSubtype.englishName)} in addition to its other types"
  | .replaceCreatureSubtypes subs =>
    if subs.isEmpty then none
    else some s!"its creature types are {String.intercalate " " (subs.toList.map CardSubtype.englishName)}"
  | .addColors cols =>
    let cs := cols.toList.map Color.englishName
    if cs.isEmpty then none
    else some s!"it's {String.intercalate " and " cs} in addition to its other colors"
  | .removeSupertype s => some s!"it isn't {s.oracleWord}"
  | .addKeywords kws =>
    if kws.isEmpty then none
    else some s!"it has {KeywordAbility.joinedAnd kws}"
  | .addAbilities abs =>
    let qs := abs.toList.filterMap GrantedAbility.oracleQuote?
    if qs.isEmpty then none
    else some s!"it has {String.intercalate " and " (qs.map fun q => s!"\"{q}\"")}"

end CopyModification

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
    (keywords : Array KeywordAbility := #[])
    (types : Array CardType := #[.creature])
    (supertypes : Array Supertype := #[])
    (name? : Option String := none)
    (abilities : Array GrantedAbility := #[]) : TokenSpec :=
  .custom {
    name?, supertypes, types, subtypes, colors
    power? := some (.const power)
    toughness? := some (.const toughness)
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
  creature #[.spirit] 1 1 (ColorSet.singleton .white) #[Keyword.flying]

def birdSoldier : TokenSpec :=
  creature #[.bird, .soldier] 4 4 (ColorSet.singleton .white) #[Keyword.flying]

def wall : TokenSpec :=
  creature #[.wall] 3 1 ColorSet.empty #[Keyword.defender]
    (types := #[.artifact, .creature]) (name? := some "Stone Boulder")

def dragon : TokenSpec :=
  creature #[.dragon] 6 6 (ColorSet.singleton .red) #[Keyword.flying]

def hero32vigilance : TokenSpec :=
  creature #[.hero] 3 2 (ColorSet.singleton .white) #[Keyword.vigilance]

def villain21menace : TokenSpec :=
  creature #[.villain] 2 1 (ColorSet.singleton .black) #[Keyword.menace]

def robotVillain22 : TokenSpec :=
  creature #[.robot, .villain] 2 2 ColorSet.empty
    (types := #[.artifact, .creature])

def leviathan65hexproof : TokenSpec :=
  creature #[.leviathan] 6 5 (ColorSet.singleton .blue) #[Keyword.hexproof]

def soldier11white : TokenSpec :=
  creature #[.soldier] 1 1 (ColorSet.singleton .white)

def squirrel11green : TokenSpec :=
  creature #[.squirrel] 1 1 (ColorSet.singleton .green)

def wall04defender : TokenSpec :=
  creature #[.wall] 0 4 ColorSet.empty #[Keyword.defender]

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
  creature #[.beast] 4 4 (ColorSet.singleton .green) #[Keyword.trample]

def dragon55flying : TokenSpec :=
  creature #[.dragon] 5 5 (ColorSet.singleton .red) #[Keyword.flying]

def forestTentacle : TokenSpec :=
  creature #[.forest, .tentacle] 3 3 (ColorSet.singleton .green)
    (types := #[.land, .creature])

def thopter : TokenSpec :=
  creature #[.thopter] 1 1 ColorSet.empty #[Keyword.flying]
    (types := #[.artifact, .creature])

def angel33blue : TokenSpec :=
  creature #[.angel] 3 3 (ColorSet.singleton .blue) #[Keyword.flying]

def illusion11blue : TokenSpec :=
  creature #[.illusion] 1 1 (ColorSet.singleton .blue)

def leviathan88hexproof : TokenSpec :=
  creature #[.leviathan] 8 8 (ColorSet.singleton .blue) #[Keyword.hexproof]

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
    #[Keyword.flying, Keyword.indestructible]
    (supertypes := #[.legendary]) (name? := some "The Void")
    (abilities := #[.attacksEachCombatIfAble])

def redwing : TokenSpec :=
  creature #[.bird, .scout] 1 1 (ColorSet.singleton .blue) #[Keyword.flying]
    (supertypes := #[.legendary]) (name? := some "Redwing")
    (abilities := #[.onAttackSurveil 1])

def alien : TokenSpec :=
  creature #[.alien] 1 1 (ColorSet.singleton .red) #[Keyword.haste]
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
    #[Keyword.flying, Keyword.trample]
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
  creature #[.insect] 2 1 (ColorSet.singleton .white) #[Keyword.flying]

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
    keywords := #[Keyword.flying]
  }

def gingerbrute : TokenSpec :=
  .custom {
    name? := some "Gingerbrute"
    types := #[.artifact, .creature]
    subtypes := #[.food, .golem]
    power? := some (.const 1)
    toughness? := some (.const 1)
    keywords := #[Keyword.haste]
    abilities := #[.payGenericCantBeBlockedExceptHaste 1, .tapSacrificeGainLife 2 3]
    useCardNameShorthand := true
  }

def angel44white : TokenSpec :=
  creature #[.angel] 4 4 (ColorSet.singleton .white) #[Keyword.flying]

def human11white : TokenSpec :=
  creature #[.human] 1 1 (ColorSet.singleton .white)

def goblin11red : TokenSpec :=
  creature #[.goblin] 1 1 (ColorSet.singleton .red)

def rogue22black : TokenSpec :=
  creature #[.rogue] 2 2 (ColorSet.singleton .black)

def fish11blue : TokenSpec :=
  creature #[.fish] 1 1 (ColorSet.singleton .blue)

def octopus88blue : TokenSpec :=
  creature #[.octopus] 8 8 (ColorSet.singleton .blue)

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
      | some p, some t => [s!"{toOracleStr p}/{toOracleStr t}"]
      | _, _ => []
    let colorParts :=
      if s.colors.isColorless then ["colorless"]
      else [String.intercalate " and " (s.colors.toList.map Color.englishName)]
    let subtypeParts := s.subtypes.toList.map CardSubtype.englishName
    let typeParts := s.types.toList.map cardTypeLower
    let extraKws := s.abilities.filterMap fun | .keyword k => some k | _ => none
    let kwList := KeywordAbility.toOracleList (s.keywords ++ extraKws)
    let kwSuffix :=
      if kwList.isEmpty then []
      else ["with " ++ String.intercalate " and " kwList]
    let defaultName := String.intercalate " " subtypeParts
    let nameSuffix :=
      match s.name? with
      | some n => if n == defaultName then [] else [s!"named {n}"]
      | none => []
    let abilityQuotes := s.abilities.toList.filterMap GrantedAbility.oracleQuote?
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
  | .copyOf ref mods =>
    let refS := toOracleStr ref { capitalize := false }
    let modParts := mods.toList.filterMap CopyModification.toOraclePhrase?
    if modParts.isEmpty then s!"token that's a copy of {refS}"
    else s!"token that's a copy of {refS}, except {String.intercalate ", " modParts}"

instance : ToOracle TokenSpec where
  toOracle ctx t :=
    let s := if ctx.plural then t.oracleNoun.replace "token" "tokens" else t.oracleNoun
    if ctx.capitalize then capitalizeAscii s else s

/-- Plural Oracle noun: the singular form with `token` → `tokens`. -/
def pluralNoun (t : TokenSpec) : String :=
  t.oracleNoun.replace "token" "tokens"

/-- Noun phrase for `n` created tokens (`a Treasure token`, `two 2/2 green
Wolf creature tokens`). -/
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
