import Std.Data.HashMap
import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.OracleArgs
import Mtg.Engine.Card.OracleCandidates
import Mtg.Engine.Card.OracleNorm

/-!
# Parsing a full Oracle card

`parseOracleCard` reads one card's printed text — name, mana cost, type line,
power and toughness, and rules text — into a `CardDef`. The rules text is
matched to the abilities the engine models. The resulting `CardDef` does not
keep the source text.
-/

namespace Mtg.Engine

open OracleNorm
open OracleActivate
open OracleArgs
open OracleCandidates

/-- Parse `{W}`, `{2}`, `{G/U}`, `{X}`, `{C}` from the front of `s`. -/
def parseManaSymbol (s : String) : Option (ManaSymbol × String) :=
  let s := s.trimAscii.copy
  if !s.startsWith "{" then none
  else
    match (s.drop 1).copy.splitOn "}" with
    | [] => none
    | head :: rest =>
      let sym := head.trimAscii.copy.map Char.toUpper
      let after := (String.intercalate "}" rest).trimAscii.copy
      let color? : String → Option Color
        | "W" => some .white
        | "U" => some .blue
        | "B" => some .black
        | "R" => some .red
        | "G" => some .green
        | _ => none
      if sym == "X" then some (.x, after)
      else if sym == "C" then some (.colorless, after)
      else
        match sym.splitOn "/" with
        | [a, b] =>
          match color? a, color? b with
          | some ca, some cb => some (.hybrid ca cb, after)
          | _, _ => none
        | _ =>
          match color? sym with
          | some c => some (.colored c, after)
          | none =>
            if sym.all Char.isDigit && !sym.isEmpty then
              some (.generic sym.toNat!, after)
            else none

/-- A string that is only mana symbols, such as `{1}{G}`. -/
def parseManaCost (s : String) : Option ManaCost :=
  let s := s.trimAscii.copy
  if s.isEmpty || !s.startsWith "{" then none
  else
    let rec go (left : String) (acc : Array ManaSymbol) : Option ManaCost :=
      if left.isEmpty then some { symbols := acc }
      else
        match parseManaSymbol left with
        | none => none
        | some (sym, rest) =>
          if rest.length < left.length then go rest (acc.push sym) else none
    termination_by left.length
    go s #[]

/-- Name, and a mana cost when the line ends with one (`Allure of Power {1}{B}`). -/
def splitNameCost (line : String) : String × Option ManaCost :=
  let line := line.trimAscii.copy
  let rec go (cs : List Char) (acc : List Char) : String × Option ManaCost :=
    match cs with
    | [] => (line, none)
    | '{' :: rest =>
      let suffix := String.ofList cs
      match parseManaCost suffix with
      | some cost =>
        let name := (String.ofList acc.reverse).trimAscii.copy
        if name.isEmpty then (line, none) else (name, some cost)
      | none => go rest ('{' :: acc)
    | c :: rest => go rest (c :: acc)
  go line.toList []

def parseSupertype (w : String) : Option Supertype :=
  match w with
  | "Basic" => some .basic
  | "Legendary" => some .legendary
  | "Ongoing" => some .ongoing
  | "Snow" => some .snow
  | "World" => some .world
  | _ => none

def parseCardType (w : String) : Option CardType :=
  match w with
  | "Artifact" => some .artifact
  | "Battle" => some .battle
  | "Creature" => some .creature
  | "Enchantment" => some .enchantment
  | "Instant" => some .instant
  | "Land" => some .land
  | "Planeswalker" => some .planeswalker
  | "Sorcery" => some .sorcery
  | "Kindred" => some .kindred
  | "Dungeon" => some .dungeon
  | "Plane" => some .plane
  | "Phenomenon" => some .phenomenon
  | "Vanguard" => some .vanguard
  | "Scheme" => some .scheme
  | "Conspiracy" => some .conspiracy
  | _ => none

/-- `Legendary Creature — Human Wizard`, or `Instant`. -/
def parseTypeLine (line : String) : Except String (Array Supertype × Array CardType × Array Subtype) :=
  let line := line.trimAscii.copy
  let (head, sub) :=
    if (line.splitOn " — ").length > 1 then
      let parts := line.splitOn " — "
      (parts.headD "", String.intercalate " — " parts.tail)
    else if (line.splitOn " - ").length > 1 then
      let parts := line.splitOn " - "
      (parts.headD "", String.intercalate " - " parts.tail)
    else (line, "")
  let words := head.splitOn " " |>.filter (· != "")
  if words.isEmpty then .error s!"empty type line: {line}"
  else Id.run do
    let mut supers : Array Supertype := #[]
    let mut types : Array CardType := #[]
    for w in words do
      match parseSupertype w with
      | some s => supers := supers.push s
      | none =>
        match parseCardType w with
        | some t => types := types.push t
        | none => return .error s!"unknown type-line word '{w}' in: {line}"
    if types.isEmpty then return .error s!"type line has no card type: {line}"
    let subtypes := sub.splitOn " " |>.filter (· != "") |>.toArray
    return .ok (supers, types, subtypes)

def parseStat (tok : String) : Option Int :=
  if tok == "*" then none
  else if tok.startsWith "-" then
    let n := (tok.drop 1).copy
    if n.all Char.isDigit && !n.isEmpty then some (-n.toNat!) else none
  else if tok.all Char.isDigit && !tok.isEmpty then some tok.toNat!
  else none

def isStatToken (tok : String) : Bool :=
  tok == "*" ||
    (tok.startsWith "-" && (tok.drop 1).copy.all Char.isDigit && tok.length > 1) ||
    (tok.all Char.isDigit && !tok.isEmpty)

/-- `2/2`, `*/*`, or `1/*`. -/
def parsePT (line : String) : Option (Option Int × Option Int) :=
  let line := line.trimAscii.copy.replace " " ""
  match line.splitOn "/" with
  | [a, b] =>
    if isStatToken a && isStatToken b then some (parseStat a, parseStat b) else none
  | _ => none

def parseColorName (w : String) : Option Color :=
  match lowerAscii w.trimAscii.copy with
  | "white" | "w" => some .white
  | "blue" | "u" => some .blue
  | "black" | "b" => some .black
  | "red" | "r" => some .red
  | "green" | "g" => some .green
  | _ => none

def parseColorIndicator (line : String) : Option ColorSet :=
  let line := line.trimAscii.copy
  let pref := "Color indicator:"
  if !(line.startsWith pref) then none
  else
    let rest := (line.drop pref.length).trimAscii.copy
    let words := rest.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    let colors := words.filterMap parseColorName
    if colors.isEmpty || colors.length != words.length then none
    else some (colors.foldl (fun acc c => acc.insert c) ColorSet.empty)

/-- Keyword names on one line, such as `Flying, haste`. -/
def keywordTokens (cardName line : String) : Option (List String) :=
  let prepared := prepareLine cardName line
  let cleaned := dropLeadingThis ((prepared.replace "." "").trimAscii.copy)
  let parts := cleaned.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
  let names := Keywords.fields.map (·.name)
  if parts.isEmpty then none
  else if parts.all (fun p => names.any (· == p)) then some parts
  else none

def keywordsFromTokens (toks : List String) : Keywords :=
  toks.foldl (fun acc name =>
    match Keywords.fields.find? (fun f => f.name == name) with
    | some f => f.set acc true
    | none => acc) Keywords.none

def nonEmptyLines (text : String) : List String :=
  text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")

/-- Split a back face introduced by a line that is exactly `//`. -/
def splitBackFace (lines : List String) : List String × Option (List String) :=
  match lines.idxOf? "//" with
  | none => (lines, none)
  | some i =>
    let front := lines.take i
    let back := lines.drop (i + 1)
    (front, some back)

/-- Pull an Adventure block out of the rules lines. -/
def splitAdventure (lines : List String) : List String × Option (List String) :=
  let rec go (acc : List String) : List String → List String × Option (List String)
    | [] => (acc.reverse, none)
    | line :: rest =>
      if line == "//ADV//" then (acc.reverse, some rest)
      else if line.startsWith "//ADV//" then
        let extra := (line.drop "//ADV//".length).trimAscii.copy
        let adv := if extra.isEmpty then rest else extra :: rest
        (acc.reverse, some adv)
      else go (line :: acc) rest
  go [] lines

def romanToken (s : String) : Bool :=
  s.all (fun c => c == 'I' || c == 'V' || c == 'X' || c == ',')

/-- `I — Scry 2.` or `II, III — …`. -/
def parseChapterHeader (line : String) : Option (String × String) :=
  let line := line.trimAscii.copy
  let parts :=
    if (line.splitOn " — ").length > 1 then line.splitOn " — "
    else if line.contains '—' then line.splitOn "—"
    else []
  match parts with
  | roman :: rest =>
    let roman := roman.trimAscii.copy
    let text := (String.intercalate " — " rest).trimAscii.copy
    let bits := roman.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")
    if !bits.isEmpty && bits.all romanToken && !text.isEmpty then some (roman, text)
    else none
  | _ => none

def braceNat (s : String) : Option Nat :=
  match parseManaSymbol s.trimAscii.copy with
  | some (.generic n, rest) => if rest.isEmpty then some n else none
  | _ => none

/-- First `{N}` in `s`. -/
def firstBraceNat (s : String) : Option Nat :=
  let rec go (cs : List Char) : Option Nat :=
    match cs with
    | [] => none
    | '{' :: rest =>
      let digits := rest.takeWhile Char.isDigit
      match rest.dropWhile Char.isDigit with
      | '}' :: _ =>
        if digits.isEmpty then go rest else some (String.ofList digits).toNat!
      | _ => go rest
    | _ :: rest => go rest
  go s.toList

def manaLetters (s : String) : Option (List ManaType) :=
  let rec go (left : String) (acc : List ManaType) : Option (List ManaType) :=
    if left.isEmpty then some acc.reverse
    else if left.startsWith "or " then
      let rest := (left.drop 3).trimAscii.copy
      if rest.length < left.length then go rest acc else none
    else if left.startsWith "and/or " then
      let rest := (left.drop 7).trimAscii.copy
      if rest.length < left.length then go rest acc else none
    else
      match parseManaSymbol left with
      | some (.colored c, rest) =>
        if rest.length < left.length then go rest (.colored c :: acc) else none
      | some (.colorless, rest) =>
        if rest.length < left.length then go rest (.colorless :: acc) else none
      | _ => none
  termination_by left.length
  let s := s.trimAscii.copy
  if s.startsWith "{" then go s [] else none

def isEquipAbility (ab : ActivatedAbility) : Bool :=
  ab.effect == Effect.attachToTargetCreatureYouControl && ab.onlyAsSorcery && !ab.isModal

def typecyclingLand? (ab : ActivatedAbility) : Option String :=
  if ab.activateFromHand && ab.cost.discardSource then
    match ab.effect.resolution with
    | .searchLandTypeToHand t => if t == "Plan" then none else some t
    | _ => none
  else none

/-- Oracle line for one activated ability, matching the wording catalogs store. -/
def printedActivated (ab : ActivatedAbility) : String :=
  if isEquipAbility ab then
    let pay := if ab.cost.payLife != 0 then s!", Pay {ab.cost.payLife} life" else ""
    match ab.equipSubtype with
    | some t => s!"Equip {t} {ab.cost.mana}{pay}"
    | none =>
      if ab.equipWorthy then s!"Equip worthy {ab.cost.mana}{pay}"
      else if pay != "" then s!"Equip—{ab.cost.mana}{pay}"
      else s!"Equip {ab.cost.mana}"
  else
    match typecyclingLand? ab with
    | some t => s!"{t}cycling {ab.cost.mana}"
    | none =>
      let timing :=
        (if ab.costReductionIfYouControlLegendary != 0 then
          s!" This ability costs \{{ab.costReductionIfYouControlLegendary}} less to activate if you control a legendary creature."
         else "") ++
        (if ab.costReductionPerEquipment != 0 then
          s!" This ability costs \{{ab.costReductionPerEquipment}} less to activate for each Equipment you control."
         else "") ++
        (match ab.costReductionIfTargetPowerAtMost with
         | some (n, p) =>
           s!" This ability costs \{{n}} less to activate if it targets a creature with power {p} or less."
         | none => "") ++
        (if ab.onlyAsSorcery then " Activate only as a sorcery." else "") ++
        (if ab.onlyDuringYourTurn && ab.onceEachTurn then
          " Activate only during your turn and only once each turn."
         else
          (if ab.onlyDuringYourTurn then " Activate only during your turn." else "") ++
          (if ab.onceEachTurn then " Activate only once each turn." else "")) ++
        (if ab.onlyIfYouControlLegendary then
          " Activate only if you control a legendary creature." else "") ++
        (if ab.onlyIfYouAttackedWithTwoOrMore then
          " Activate only if you attacked with two or more creatures this turn." else "") ++
        (if ab.onlyIfYouControlCreatureToughnessAtLeast != 0 then
          s!" Activate only if you control a creature with toughness {ab.onlyIfYouControlCreatureToughnessAtLeast} or greater."
         else "") ++
        (if ab.onlyIfGyCreaturesAtLeast != 0 then
          let cards :=
            if ab.onlyIfGyCreaturesAtLeast == 1 then "a creature card"
            else s!"{ab.onlyIfGyCreaturesAtLeast} or more creature cards"
          s!" Activate only if there are {cards} in your graveyard."
         else "")
      let body :=
        if ab.isModal then
          let modes := ab.allModes.toList.map Effect.toNotation
          s!"Choose one — {String.intercalate "; " modes}"
        else ab.effect.toNotation
      s!"{ab.cost.toNotation}: {body}.{timing}"

def spellBody (cardName : String) (e : Effect) : String :=
  let body := e.phrase
  if body.startsWith "deals" || body.startsWith "Deals" then s!"{cardName} {body}" else body

/-- Lines a spell effect contributes, in printed order. -/
def effectLines (cardName : String) (e : Effect) : List String :=
  match e.spellResolution with
  | .tapScryDraw scryN drawN =>
    [s!"Tap target creature. Scry {scryN}.",
      if drawN == 1 then "Draw a card." else s!"Draw {drawN} cards."]
  | .returnSpellDraw =>
    ["Return target spell to its owner's hand.", "Draw a card."]
  | .drawLoseLifeThenAmass n =>
    ["You draw a card and lose 1 life.", s!"Amass Goblins {n}."]
  | .returnCreatureFromGyThenAmass n =>
    ["Return up to one target creature card from your graveyard to your hand.",
      s!"Amass Goblins {n}."]
  | .dealDamageToEachNonDragonThenAddDragonMana n =>
    [s!"{cardName} deals {n} damage to each non-Dragon creature.",
      "Add four mana in any combination of colors. Spend this mana only to cast Dragon spells."]
  | .grantVigilanceUnblockable =>
    ["Target creature gains vigilance until end of turn and can't be blocked this turn.",
      "Draw a card."]
  | .becomeArtifactCreature44Flying =>
    ["Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness 4/4 and gains flying.",
      "Draw a card."]
  | _ =>
    (spellBody cardName e).splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")

inductive ParsedAbility where
  | static (ab : StaticAbility)
  | triggered (ab : TriggeredAbility)
  | activated (ab : ActivatedAbility)
  | spell (e : Effect)
  | modes (es : Array Effect) (oneOrBoth : Bool) (teamwork : Bool) (twoIf : Option String)
deriving Repr

def applyParsed (c : CardDef) (ab : ParsedAbility) : CardDef :=
  match ab with
  | .static ab => { c with staticAbilities := c.staticAbilities.push ab }
  | .triggered ab => { c with triggeredAbilities := c.triggeredAbilities.push ab }
  | .activated ab => { c with activatedAbilities := c.activatedAbilities.push ab }
  | .spell e => { c with spellEffect := some e }
  | .modes es oneOrBoth teamwork twoIf =>
    { c with
      spellModes := es
      chooseOneOrBoth := oneOrBoth
      chooseBothIfTeamwork := teamwork
      chooseTwoIfYouControlSubtype := twoIf }

def pushMana (c : CardDef) (t : ManaType) : CardDef :=
  { c with tapAddMana := c.tapAddMana.push t }

def splitCreatureTypes (s : String) : Array String :=
  let s := s.replace ", or " ", " |>.replace " or " ", "
  (s.splitOn "," |>.map (·.trimAscii.copy) |>.filter (· != "")).toArray

/-- `{2}{G}{U}, {T}, Sacrifice this land: Put two +1/+1 counters on target Elf you control.` -/
def parseSacrificeCounters (line : String) : Option ActivatedAbility :=
  let raw := (stripParentheticals line).trimAscii.copy
  let low := lowerAscii raw
  if !(low.contains "sacrifice this") || !(low.contains "+1/+1 counters on target") then none
  else
    let costText := ((raw.splitOn ":").headD "").splitOn "," |>.headD "" |>.trimAscii.copy
    match parseManaCost costText with
    | none => none
    | some cost =>
      let n :=
        if low.contains "put two " || low.contains "put 2 " then 2 else 1
      let typesText :=
        ((raw.splitOn "on target ").getLastD "").splitOn " you control" |>.headD "" |>.trimAscii.copy
      let types := splitCreatureTypes typesText
      if types.isEmpty then none
      else
        some (activated (Effect.plusOneOnTarget n types) cost
          (tap := low.contains "{t}")
          (sacrificeSource := true)
          (onlyAsSorcery := low.contains "only as a sorcery"))

/-- `Equip {2}`, `Equip Wizard {1}`, `Equip worthy {1}`, `Equip—{2}, Pay 2 life`. -/
def parseEquipLine (line : String) : Option ActivatedAbility :=
  let raw := (stripParentheticals line).trimAscii.copy
  let low := lowerAscii raw
  if !(low.startsWith "equip") then none
  else
    let payLife :=
      if low.contains "pay " && low.contains "life" then
        match (low.splitOn "pay ").getLastD "" |>.takeWhile Char.isDigit with
        | "" => 0
        | d => d.toNat!
      else 0
    let head :=
      if raw.contains ',' then (raw.splitOn ",").headD raw |>.trimAscii.copy else raw
    let afterEquip := (head.drop "Equip".length).trimAscii.copy
    let afterEquip :=
      if afterEquip.startsWith "—" || afterEquip.startsWith "-" then
        (afterEquip.drop 1).trimAscii.copy
      else afterEquip
    let worthy := (lowerAscii afterEquip).startsWith "worthy"
    let costAndType :=
      if worthy then (afterEquip.drop "worthy".length).trimAscii.copy else afterEquip
    let (subtype, cost?) :=
      match parseManaCost costAndType with
      | some cost => (none, some cost)
      | none =>
        match splitNameCost costAndType with
        | (name, some cost) => (some name, some cost)
        | _ => (none, none)
    match cost? with
    | none => none
    | some cost =>
      some (activated (Effect.attachToTargetCreatureYouControl) cost
        (onlyAsSorcery := true) (payLife := payLife)
        (equipSubtype := subtype) (equipWorthy := worthy))

/-- Structural rules that are card fields rather than an ability value. -/
def parseStructural (c : CardDef) (line : String) : Option CardDef :=
  let raw := unwrapOuterParens line.trimAscii.copy
  let low := lowerAscii (stripParentheticals raw).trimAscii.copy
  let named := collapseWs (prepareLine c.name raw)
  let n := firstBraceNat raw
  if low.contains "sacrifice this land" && low.contains "create x treasure tokens" then
    let head := (raw.splitOn ",").headD "" |>.trimAscii.copy
    match parseManaCost head with
    | some cost =>
      let ab :=
        activated (Effect.abilityCreateTokensX .treasure) cost
          (tap := low.contains "{t}") (sacrificeSource := true)
      some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none => none
  else if low.startsWith "this spell costs {x} less to cast, where x is the total power of creatures you control with flying" then
    some { c with costReductionEqualFlyingPower := true }
  else if low.startsWith "this spell costs {x} less to cast, where x is the greatest number of artifacts an opponent controls" then
    some { c with costReductionEqualOppArtifacts := true }
  else if low.startsWith "this spell costs " && low.contains "less to cast if a creature died this turn" then
    n.map fun k => { c with costReductionIfCreatureDied := k }
  else if low.startsWith "this spell costs " && low.contains "dealt damage this turn" then
    n.map fun k => { c with costReductionIfTargetDamaged := k }
  else if low.startsWith "this spell costs " && low.contains "tapped creature" then
    n.map fun k => { c with costReductionIfTargetTapped := k }
  else if low.startsWith "this spell costs " && low.contains "attacking nontoken" then
    n.map fun k => { c with costReductionIfTargetAttackingNontoken := k }
  else if low.startsWith "this spell costs " && low.contains "attacking creature" then
    n.map fun k => { c with costReductionIfTargetAttacking := k }
  else if low.startsWith "this spell costs " && low.contains "if you control a " then
    match n with
    | none => none
    | some k =>
      let after := (low.splitOn "if you control a ").getLastD ""
      let subtype := (after.splitOn ".").headD "" |>.trimAscii.copy
      if subtype.isEmpty then none
      else
        let printed :=
          (raw.splitOn "if you control a ").getLastD ""
            |>.splitOn "." |>.headD "" |>.trimAscii.copy
        some { c with costReductionIfYouControl := some (k, printed) }
  else if low.startsWith "this spell costs " && low.contains "creature card" && low.contains "graveyard" then
    match n with
    | none => none
    | some k =>
      let min :=
        if low.contains "a creature card" then 1
        else
          match (replaceNumberWords low |>.splitOn " or more creature").headD "" |>.splitOn " " |>.getLast? with
          | some w => if w.all Char.isDigit && !w.isEmpty then w.toNat! else 1
          | none => 1
      some { c with costReductionIfGyCreaturesAtLeast := some (min, k) }
  else if low.startsWith "affinity for " then
    let t :=
      ((stripParentheticals ((raw.drop "Affinity for ".length).trimAscii.copy)).trimAscii.copy).replace "." ""
    some { c with affinityForSubtype := some t }
  else if low.contains "cascade" &&
      (((low.replace "," "").splitOn " ").filter (fun w => w != "")).all (fun w => w == "cascade") then
    let n := (low.splitOn "cascade").length - 1
    some { c with cascade := n }
  else if low.startsWith "kicker " then
    let costText :=
      ((stripParentheticals ((raw.drop "Kicker ".length).trimAscii.copy)).trimAscii.copy).replace "." ""
    parseManaCost costText |>.map fun cost => { c with kicker := some cost }
  else if low == "gift a treasure" || low == "gift a treasure." then
    some { c with giftTreasure := true }
  else if low.startsWith "teamwork " then
    let num := (low.drop "teamwork ".length).takeWhile Char.isDigit
    if num.isEmpty then none else some { c with teamwork := some num.toNat! }
  else if low.startsWith "as an additional cost to cast this spell, sacrifice an artifact or creature or pay" then
    n.map fun k => { c with additionalCostSacrificeArtifactOrCreature := true, additionalCostOrPayGeneric := some k }
  else if low.startsWith "as an additional cost to cast this spell, sacrifice an artifact or creature" then
    some { c with additionalCostSacrificeArtifactOrCreature := true }
  else if low.startsWith "as an additional cost to cast this spell, discard a card or pay" then
    n.map fun k => { c with additionalCostDiscardOrPayGeneric := some k }
  else if low.startsWith "as an additional cost to cast this spell, sacrifice a creature" then
    some { c with additionalCostSacrificeCreature := true }
  else if low == "this spell can't be countered" || low == "this spell can't be countered." then
    some { c with cantBeCountered := true }
  else if low.startsWith "you may cast this spell as though it had flash if you control a " then
    let t := (raw.splitOn "if you control a ").getLastD "" |>.replace "." "" |>.trimAscii.copy
    some { c with flashIfYouControlSubtype := some t }
  else if low.startsWith "ward " || low.startsWith "ward{" then
    n.map fun k => { c with ward := some k }
  else if low.startsWith "flashback " then
    let costText :=
      ((stripParentheticals ((raw.drop "Flashback ".length).trimAscii.copy)).trimAscii.copy).replace "." ""
    parseManaCost costText |>.map fun cost => { c with flashback := some cost }
  else if low.startsWith "crew " then
    let num := (low.drop "crew ".length).takeWhile Char.isDigit
    if num.isEmpty then none else some { c with crew := some num.toNat! }
  else if low.contains "enters tapped unless you control a legendary" then
    some { c with entersTappedUnlessLegendary := true }
  else if low.contains "enters tapped unless you control an equipment" then
    some { c with entersTappedUnlessEquipment := true }
  else if low.contains "you may pay" && low.contains "if you don't, it enters tapped" then
    let life :=
      match (low.splitOn "pay ").getLastD "" |>.takeWhile Char.isDigit with
      | "" => none
      | d => some d.toNat!
    life.map fun k => { c with entersTappedUnlessPayLife := some k }
  else if low == "this land enters tapped." || low == "this land enters tapped" ||
      low == "this artifact enters tapped." || low == "this creature enters tapped." ||
      low.endsWith " enters tapped." || low.endsWith " enters tapped" then
    some { c with entersTapped := true }
  else if low.contains "as this enchantment enters, choose a creature type" then
    some { c with asEntersChooseCreatureType := true }
  else if low.contains "enters with a hope counter" then
    some { c with entersWithHopePerCreature := true }
  else if low.contains "enters with" && low.contains "shield counter" then
    let k := if low.contains "counters" then
      match (low.splitOn "enters with ").getLastD "" |>.takeWhile Char.isDigit with
      | "" => 1
      | d => d.toNat!
    else 1
    some { c with entersWithShield := k }
  else if low.contains "if you would create a food token" then
    some { c with foodAlsoCreatesTreasure := true }
  else if low.contains "except the first one you draw in each of your draw steps" then
    some { c with drawTwoExceptFirstDrawStep := true }
  else if low.contains "twice that many of those tokens are created instead" then
    some { c with tokenDoubling := true }
  else if named.contains "additional +1/+1 counters" && named.contains "equal to this toughness" then
    some { c with othersEnterWithPlusOneEqualToughness := true }
  else if low.contains "you may look at the top card of your library any time" then
    some { c with mayLookAtTopAnytime := true }
  else if low.contains "you may cast creature spells from the top of your library" then
    some { c with mayCastCreaturesFromTop := true }
  else if low.contains "you may play lands from the top of your library" then
    some { c with mayPlayLandsFromTop := true }
  else if low.contains "creatures you control have" && low.contains "add one mana of any color" then
    some { c with grantCreaturesTapAddAnyColor := true }
  else if low.contains "the first creature spell you cast each turn costs" then
    match n with
    | none => none
    | some k =>
      some { c with firstCreatureCostsLess := k, firstCreatureHasFlash := low.contains "flash" }
  else if named.contains "as this enters" && named.contains "choose odd or even" then
    some { c with asEntersChooseOddEven := true }
  else if low.contains "from anywhere other than your hand cost" then
    n.map fun k => { c with costReductionNotFromHand := k }
  else if low.contains "enters with an indestructible counter" then
    some { c with entersWithIndestructibleCounter := true }
  else if low.contains "lore counters among sagas you control" && low.contains "hexproof and indestructible" then
    let numbered := replaceNumberWords low
    let k :=
      match (numbered.splitOn "there are ").getLastD "" |>.takeWhile Char.isDigit with
      | "" => 1
      | d => d.toNat!
    some { c with hexproofIndestructibleIfLore := some k }
  else if low.contains "for each mountain you control" then
    let k :=
      match (low.splitOn "gets +").getLastD "" |>.takeWhile Char.isDigit with
      | "" => 1
      | d => d.toNat!
    some { c with powerPerMountain := k }
  else if low.contains "you may play an additional land" && low.contains "as long as you control another" then
    let t := (raw.splitOn "another ").getLastD "" |>.splitOn "," |>.headD "" |>.trimAscii.copy
    some { c with extraLandIfOtherSubtype := some t }
  else if low.contains "sacrifice after" && low.contains "lore counter" then
    let after := (raw.splitOn "Sacrifice after ").getLastD raw
    let roman := (after.takeWhile (fun c => c != '.' && c != ')')).trimAscii.copy
    let s := c.saga.getD { sacrificeAfter := roman, chapters := #[] }
    some { c with saga := some { s with sacrificeAfter := roman } }
  else
    match parseSacrificeCounters raw with
    | some ab => some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none =>
    match parseEquipLine raw with
    | some ab => some { c with activatedAbilities := c.activatedAbilities.push ab }
    | none =>
      if low.startsWith "{t}: add" || low.startsWith "{t}, sacrifice" || low.startsWith "{t}, pay" then
        parseTap c raw low
      else none
where
  parseTap (c : CardDef) (raw low : String) : Option CardDef :=
    if low.contains "where x is this creature's power" then
      some { c with tapAddAnyColorEqualToPower := true }
    else if low.contains "spend this mana only to cast" &&
        !low.contains "legendary spell" && !low.contains "instant or sorcery" then
      let add := (raw.splitOn "Add ").getLastD "" |>.splitOn "." |>.headD ""
      let restriction :=
        ((raw.splitOn "to cast ").getLastD "").replace "." "" |>.trimAscii.copy
      match manaLetters add with
      | some ts => some { c with tapAddRestricted := some (ts.toArray, restriction) }
      | none => none
    else if low.contains "for each" && low.contains "you control" then
      if low.contains "where x is this creature's power" || low.contains "x mana of any" then
        some { c with tapAddAnyColorEqualToPower := true }
      else
        match (low.splitOn "add ").getLastD "" |>.splitOn " for each" with
        | [sym, _] =>
          match manaLetters sym.trimAscii.copy with
          | some [m] =>
            let subtype := (raw.splitOn "for each ").getLastD "" |>.splitOn " you control" |>.headD "" |>.trimAscii.copy
            some { c with tapAddManaForEach := c.tapAddManaForEach.push { mana := m, subtype := subtype } }
          | _ => none
        | _ => none
    else if low.contains "activate only if this land entered this turn" then
      let add := (raw.splitOn "Add ").getLastD "" |>.splitOn "." |>.headD ""
      manaLetters add |>.map fun ts =>
        { c with tapAddOneOfIfEnteredOrBasic := ts.toArray }
    else if low.contains "spend this mana only to cast a legendary spell" then
      some { c with tapAddAnyColorForLegendary := true }
    else if low.contains "spend this mana only to cast an instant or sorcery" then
      some { c with tapAddAnyColorForInstantOrSorcery := true }
    else if low.contains "among legendary creatures and planeswalkers" then
      some { c with tapAddAnyColorAmongLegendaries := true }
    else if low.contains "in your commander's color identity" then
      some { c with tapAddCommanderIdentity := true }
    else if low.contains "sacrifice this artifact: add one mana of any color" ||
        low.contains "sacrifice this token: add one mana of any color" then
      some { c with tapSacrificeAddAnyColor := true }
    else if low.contains "two mana in any combination" then
      let rest := (raw.splitOn "combination of ").getLastD "" |>.replace "." ""
      let parts := rest.splitOn "and/or" |>.flatMap (·.splitOn ",") |>.map (·.trimAscii.copy) |>.filter (· != "")
      let types := parts.filterMap fun p =>
        match manaLetters p with
        | some [t] => some t
        | _ => none
      if types.length >= 2 then some { c with tapAddTwoAmong := types.toArray } else none
    else if low.contains "pay" && low.contains "life: add" then
      let life :=
        match (low.splitOn "pay ").getLastD "" |>.takeWhile Char.isDigit with
        | "" => none
        | d => some d.toNat!
      let add := (raw.splitOn "Add ").getLastD "" |>.replace "." ""
      match life, manaLetters add with
      | some n, some ts => some { c with tapPayLifeAddOneOf := some (n, ts.toArray) }
      | _, _ => none
    else if low.contains " or " then
      let add := (raw.splitOn "Add ").getLastD "" |>.splitOn "." |>.headD ""
      manaLetters add |>.map fun ts => { c with tapAddOneOf := ts.toArray }
    else
      let add := (raw.splitOn "Add ").getLastD "" |>.replace "." "" |>.trimAscii.copy
      match manaLetters add with
      | some [t] =>
        if c.basicLandMana.any (fun col => ManaType.colored col == t) && c.isLand then none
        else some (pushMana c t)
      | _ => none

def normEq (cardName a b : String) : Bool :=
  normalizeUnit cardName a == normalizeUnit cardName b

def linesEq (cardName : String) (printed oracle : List String) : Bool :=
  printed.length == oracle.length &&
    (printed.zip oracle).all fun (p, o) => normEq cardName p o

def skipLine (c : CardDef) (line : String) : Bool :=
  let n := normalizeUnit c.name line
  n.isEmpty || n == "enchant creature" ||
    (c.isLand && c.basicLandMana.any fun col =>
      n == s!"\{t} add \{{lowerAscii col.letter}}")

def matchArgLines (pats : List (List Pat)) (norms : List String) (vals : Array SlotVal) :
    Option (Array SlotVal) :=
  let rec go (pats : List (List Pat)) (norms : List String) (vals : Array SlotVal)
      (seen : List Nat) : Option (Array SlotVal) :=
    match pats with
    | [] => some vals
    | p :: ps =>
      match norms with
      | [] => none
      | line :: rest =>
        match matchPatsSeen p (tokenize line) vals seen with
        | some (vals, seen) => go ps rest vals seen
        | none => none
  go pats norms vals []

/-- Parse `Nat` / `Int` / `String` holes in `proto` from `query` and rebuild `e`. -/
def matchEffectText (cardName proto query : String) (e : Effect) : Option Effect :=
  let args := collectEffect e
  let tryNorm (norm : String → String → String) : Option (Array SlotVal) :=
    matchPats (patsOf (norm cardName proto) args) (tokenize (norm cardName query)) args
  match tryNorm normalizeUnit |>.orElse (fun _ => tryNorm normalizeStructural) with
  | none => none
  | some vals => some (if vals == args then e else refillEffect e vals)

def matchChapter (cardName text : String) : Option Effect :=
  let fromTable := chapterEffects.get.find? fun (stored, _) => normEq cardName stored text
  match fromTable with
  | some (_, e) => some e
  | none =>
    match spellEffects.get.find? fun e =>
        linesEq cardName (effectLines cardName e) [text] with
    | some e => some e
    | none =>
      let fromPattern := chapterEffects.get.foldl (fun acc (stored, e) =>
        match acc with
        | some _ => acc
        | none => matchEffectText cardName stored text e) none
      match fromPattern with
      | some e => some e
      | none =>
        spellEffects.get.foldl (fun acc e =>
          match acc with
          | some _ => acc
          | none =>
            match effectLines cardName e with
            | [line] => matchEffectText cardName line text e
            | _ => none) none

def parseModes (cardName line : String) : Option ParsedAbility :=
  let raw := line.trimAscii.copy
  let low := lowerAscii raw
  if !(low.contains "choose one") then none
  else if raw.contains "{" && ((raw.splitOn "Choose").headD "").contains "{" then none
  else
    let bullets := raw.splitOn "•" |>.map (·.trimAscii.copy) |>.filter (· != "")
    match bullets with
    | [] => none
    | header :: modes =>
      if modes.isEmpty then none
      else
        let effects := modes.filterMap fun m =>
          let m := stripAbilityWord m
          matchChapter cardName m
        if effects.length != modes.length then none
        else
          let oneOrBoth := low.contains "choose one or both"
          let teamwork := low.contains "using teamwork"
          let twoIf :=
            if low.contains "you may choose two instead" then
              let after := (header.splitOn "you control a ").getLastD ""
              let t := (after.splitOn " ").headD "" |>.trimAscii.copy
              if t.isEmpty then none else some t
            else none
          some (.modes effects.toArray oneOrBoth teamwork twoIf)

/-- Name used when indexing printed abilities. `normalizeUnit` rewrites it to `this`,
the same way a real card name is rewritten. -/
private def indexName : String := "CARDNAME"

/-- Lowercase, strip reminders and punctuation, keep the card name. Used to
prefer a literal printed match over a phrase-equivalent one. -/
def lightLine (s : String) : String :=
  collapseWs (keepSignificant (replaceNumberWords (lowerAscii
    (stripParentheticals (unwrapOuterParens (stripAbilityWord s))))))

structure IndexedAbility where
  ability : ParsedAbility
  raw : List String
  norm : List String
  light : List String
  priority : Nat
  args : Array SlotVal
  /-- Holes learned from `normalizeUnit`. -/
  pats : List (List Pat)
  /-- Holes learned before phrase equivalences, so open subtypes stay words. -/
  structPats : List (List Pat)

def collectParsed (ab : ParsedAbility) : Array SlotVal :=
  match ab with
  | .static a => collectStatic a
  | .triggered a => collectTriggered a
  | .activated a => collectActivated a
  | .spell e => collectEffect e
  | .modes .. => #[]

def indexItem (priority : Nat) (ability : ParsedAbility) (lines : List String) : IndexedAbility :=
  let args := collectParsed ability
  let norm := lines.map (normalizeUnit indexName)
  let structNorm := lines.map (normalizeStructural indexName)
  { ability
    raw := lines
    norm
    light := lines.map lightLine
    priority
    args
    pats := patsOfLines norm args
    structPats := patsOfLines structNorm args }

def refillParsed (ab : ParsedAbility) (vals : Array SlotVal) : ParsedAbility :=
  match ab with
  | .static a => .static (refillStatic a vals)
  | .triggered a => .triggered (refillTriggered a vals)
  | .activated a => .activated (refillActivated a vals)
  | .spell e => .spell (refillEffect e vals)
  | .modes es oneOrBoth teamwork twoIf => .modes es oneOrBoth teamwork twoIf

/-- First word, so `other Goblin creatures` still finds the `Elf` prototype. -/
def headWord (s : String) : String :=
  tokenize s |>.headD ""

/-- First token abstracted, so `Forestcycling {2}` finds `Mountaincycling {2}`. -/
def wildcardHead (s : String) : String :=
  match tokenize s with
  | [] => ""
  | t :: rest =>
    let t := if t.endsWith "cycling" then "$cycling" else "$"
    String.intercalate " " (t :: rest)

def mentionsCard (cardName : String) (lines : List String) : Bool :=
  let low := lowerAscii (String.intercalate "\n" lines)
  (nameAliases cardName).any fun a => low.contains (lowerAscii a)

/-- Normalized lines, recomputed when the printed text contains this card's name. -/
def candidateNorm (cardName : String) (item : IndexedAbility) : List String :=
  if mentionsCard cardName item.raw then item.raw.map (normalizeUnit cardName) else item.norm

@[irreducible, noinline] def indexedAbilities : Thunk (Array IndexedAbility) :=
  Thunk.mk fun _ => Id.run do
  let mut out : Array IndexedAbility := #[]
  for e in spellEffects.get do
    -- Ability effects use `abilityCastKind`; filing them as spells steals lines
    -- from the real spell (`Shock` vs `deals N to any target`).
    if e.abilityCastKind == .other then
      out := out.push (indexItem 1 (.spell e) (effectLines indexName e))
  for ab in staticAbilities.get do
    out := out.push (indexItem 2 (.static ab) [StaticAbility.toNotation ab])
  for ab in triggeredAbilities.get do
    let lines := (TriggeredAbility.toNotation ab).splitOn "\n"
      |>.map (·.trimAscii.copy) |>.filter (· != "")
    out := out.push (indexItem 3 (.triggered ab) lines)
  for ab in activatedAbilities.get do
    out := out.push (indexItem 4 (.activated ab) [printedActivated ab])
  out

def pushBucket (m : Std.HashMap String (Array Nat)) (key : String) (i : Nat) :
    Std.HashMap String (Array Nat) :=
  if key.isEmpty then m else m.insert key ((m.getD key #[]).push i)

/-- First-line index so a rules line does not scan every modeled ability. -/
@[irreducible, noinline] def abilityBuckets : Thunk (Std.HashMap String (Array Nat)) :=
  Thunk.mk fun _ => Id.run do
  let mut m : Std.HashMap String (Array Nat) := {}
  let mut i : Nat := 0
  let addKeys (m : Std.HashMap String (Array Nat)) (k : String) (i : Nat) :=
    let m := pushBucket m k i
    let m := (lineKeys k).foldl (fun m sk => pushBucket m sk i) m
    let m := pushBucket m (headWord k) i
    (lineKeys (wildcardHead k)).foldl (fun m sk => pushBucket m sk i) m
  for item in indexedAbilities.get do
    match item.light.head? with
    | some k => m := addKeys m k i
    | none => pure ()
    match item.norm.head? with
    | some k => m := addKeys m k i
    | none => pure ()
    match item.raw.head?.map (normalizeStructural indexName) with
    | some k => m := addKeys m k i
    | none => pure ()
    i := i + 1
  return m

def lookupKeys (cardName line : String) : List String :=
  let lit := lightLine line
  let norm := normalizeUnit cardName line
  let aliased :=
    (nameAliases cardName |>.map lowerAscii).foldl
      (fun acc a => acc.replace a (lowerAscii indexName)) lit
  let base := [lit, aliased, norm, normalizeStructural cardName line].foldl (fun acc k =>
    if k.isEmpty || acc.any (· == k) then acc else acc ++ [k]) []
  let wild := (base.map wildcardHead).flatMap lineKeys
  (base ++ base.flatMap lineKeys ++ base.map headWord ++ wild).foldl
    (fun acc k => if k.isEmpty || acc.any (· == k) then acc else acc ++ [k]) []

def candidatesFor (cardName : String) (units : List String) : Array IndexedAbility :=
  match units with
  | [] => #[]
  | line :: _ =>
    let idxs := (lookupKeys cardName line).foldl (fun acc k =>
      acc ++ ((abilityBuckets.get).getD k #[]).toList) []
    let idxs := idxs.foldl (fun acc i =>
      if acc.any (· == i) then acc else acc ++ [i]) []
    idxs.foldl (fun acc i =>
      match (indexedAbilities.get)[i]? with
      | some item => acc.push item
      | none => acc) #[]

def listPrefix (pre rest : List String) : Bool :=
  match pre, rest with
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && listPrefix as bs

def adaptLight (cardName : String) (lines : List String) : List String :=
  -- `light` is already lowercased, so the sentinel is `cardname`.
  lines.map fun s => s.replace (lowerAscii indexName) (lowerAscii cardName)

def filledAbility (item : IndexedAbility) (norms structNorms : List String) : Option ParsedAbility :=
  let attempt (pats : List (List Pat)) (lines : List String) : Option ParsedAbility :=
    if pats.isEmpty || pats.length > lines.length then none
    else
      match matchArgLines pats lines item.args with
      | none => none
      | some vals =>
        some (if vals == item.args then item.ability else refillParsed item.ability vals)
  (attempt item.pats norms).orElse (fun _ => attempt item.structPats structNorms)

/-- Best modeled ability whose printed lines match `units` at the front.
A literal wording match beats a match that only appears after phrase normalization.
Numeric and text arguments are read from `units` when the line has the same shape. -/
@[irreducible, noinline] def matchModeled (cardName : String) (units : List String) : Option (ParsedAbility × Nat) :=
  let norms := units.map (normalizeUnit cardName)
  let structNorms := units.map (normalizeStructural cardName)
  let lights := units.map lightLine
  let best := (candidatesFor cardName units).foldl (fun acc item =>
    let printed := candidateNorm cardName item
    let n := printed.length
    let literal : Nat :=
      if n == 0 || n > lights.length then 0
      else if listPrefix (adaptLight cardName item.light) lights then 1 else 0
    let filled := filledAbility item norms structNorms
    let exact := n != 0 && n <= norms.length && listPrefix printed norms
    if n == 0 || n > norms.length || (literal == 0 && !exact && filled.isNone) then acc
    else
      let ability := filled.getD item.ability
      match acc with
      | none => some (n, literal, item.priority, ability)
      | some (bn, bl, bp, _) =>
        if n > bn || (n == bn && (literal > bl || (literal == bl && item.priority > bp))) then
          some (n, literal, item.priority, ability)
        else acc) none
  best.map fun (n, _, _, ab) => (ab, n)

partial def parseRules (c : CardDef) (lines : List String) : Except String CardDef :=
  let units := mergeBulletLines lines |>.flatMap splitKeywordWardLine
  let rec go (c : CardDef) (units : List String) : Except String CardDef :=
    match units with
    | [] => .ok c
    | line :: rest =>
      let bare := lowerAscii (stripParentheticals line)
      let c :=
        if bare.contains "a creature an opponent controls would die" &&
            bare.contains "exile it instead" then
          { c with exileOppCreaturesInstead := true }
        else c
      if skipLine c line then go c rest
      else
        match keywordTokens c.name line with
        | some toks => go { c with keywords := c.keywords.merge (keywordsFromTokens toks) } rest
        | none =>
          match parseChapterHeader line with
          | some (roman, text) =>
            let printed :=
              match chapterEffects.get.find? fun (stored, _) => normEq c.name stored text with
              | some (stored, _) => stored
              | none => text
            match matchChapter c.name text with
            | some e =>
              let ch := SagaChapter.of roman printed e
              let s := c.saga.getD { sacrificeAfter := "", chapters := #[] }
              go { c with saga := some { s with chapters := s.chapters.push ch } } rest
            | none => .error s!"unrecognized chapter on {c.name}: {line}"
          | none =>
            match parseStructural c line with
            | some c => go c rest
            | none =>
              match parseModes c.name line with
              | some ab => go (applyParsed c ab) rest
              | none =>
                match matchModeled c.name units with
                | some (ab, n) =>
                  let more := units.drop n
                  if more.length < units.length then go (applyParsed c ab) more
                  else .error s!"unrecognized Oracle line on {c.name}: {line}"
                | none =>
                  .error s!"unrecognized Oracle line on {c.name}: {line}"
  go c units

def parseAdventure (lines : List String) : Except String AdventureFace :=
  match lines with
  | [] => .error "empty Adventure"
  | nameLine :: rest =>
    let (name, costOnName) := splitNameCost nameLine
    let (cost, afterCost) :=
      match costOnName, rest with
      | some cost, rest => (cost, rest)
      | none, line :: rest =>
        match parseManaCost line with
        | some cost => (cost, rest)
        | none => (ManaCost.empty, line :: rest)
      | none, [] => (ManaCost.empty, [])
    match afterCost with
    | [] => .error s!"Adventure {name} is missing a type line"
    | typeLine :: rules =>
      match parseTypeLine typeLine with
      | .error e => .error e
      | .ok (_, types, subtypes) =>
        let base : CardDef := {
          name
          manaCost := cost
          types
          subtypes := if subtypes.isEmpty then #["Adventure"] else subtypes
        }
        match parseRules base rules with
        | .error e => .error e
        | .ok c =>
          .ok {
            name := c.name
            manaCost := c.manaCost
            types := c.types
            subtypes := if c.subtypes.any (· == "Adventure") then c.subtypes else c.subtypes.push "Adventure"
            spellEffect := c.spellEffect
            additionalCostSacrificeCreature := c.additionalCostSacrificeCreature
          }

/-- Parse one face (no `//` back face) into a `CardDef`. -/
def parseFace (lines : List String) : Except String CardDef :=
  let lines := lines.filter (· != "")
  match lines with
  | [] => .error "empty card text"
  | nameLine :: rest =>
    let (name, costOnName) := splitNameCost nameLine
    let (cost, afterCost) :=
      match costOnName, rest with
      | some cost, rest => (cost, rest)
      | none, line :: rest =>
        match parseManaCost line with
        | some cost => (cost, rest)
        | none => (ManaCost.empty, line :: rest)
      | none, [] => (ManaCost.empty, [])
    match afterCost with
    | [] => .error s!"{name} is missing a type line"
    | typeLine :: rest =>
      match parseTypeLine typeLine with
      | .error e => .error e
      | .ok (supers, types, subtypes) =>
        let (pt, rest) :=
          match rest with
          | line :: rest =>
            match parsePT line with
            | some pt => (pt, rest)
            | none => ((none, none), line :: rest)
          | [] => ((none, none), [])
        let rec takeExtras (c : CardDef) : List String → CardDef × List String
          | [] => (c, [])
          | line :: rest =>
            if line == "Token" then takeExtras { c with isToken := true } rest
            else if lowerAscii line == "daybound" then takeExtras { c with daybound := true } rest
            else
              match parseColorIndicator line with
              | some cs => takeExtras { c with colorIndicator := some cs } rest
              | none =>
                if line.startsWith "Loyalty:" then
                  let n := (line.drop "Loyalty:".length).trimAscii.copy
                  if n.all Char.isDigit && !n.isEmpty then
                    takeExtras { c with loyalty := some n.toNat! } rest
                  else (c, line :: rest)
                else (c, line :: rest)
        let base : CardDef := {
          name, manaCost := cost, supertypes := supers, types, subtypes
          power := pt.1, toughness := pt.2
        }
        let (base, rest) := takeExtras base rest
        let (rules, adv) := splitAdventure rest
        match parseRules base rules with
        | .error e => .error e
        | .ok c =>
          match adv with
          | none => .ok c
          | some advLines =>
            match parseAdventure advLines with
            | .error e => .error e
            | .ok a => .ok { c with adventure := some a }

/-- Parse the full printed text of one card.

The text is a name line (mana cost may sit on that line or on the next), a
type line, an optional `power/toughness` line, then rules text. A line that
is exactly `//` starts the back face. An Adventure is introduced by
`//ADV//`. -/
@[irreducible, noinline] def parseOracleCard (text : String) : Except String CardDef :=
  let lines := nonEmptyLines text
  let (front, back) := splitBackFace lines
  match parseFace front with
  | .error e => .error e
  | .ok front =>
    match back with
    | none => .ok front
    | some backLines =>
      match parseFace backLines with
      | .error e => .error e
      | .ok back => .ok { front with otherFace := some back }

/-- `parseOracleCard`, panicking with the line that was not recognized. -/
@[irreducible, noinline] def parseOracleCard! (text : String) : CardDef :=
  match parseOracleCard text with
  | .ok c => c
  | .error e => panic! s!"parseOracleCard: {e}\n---\n{text}"

/-- Keyword line used when a card has no stored rules text. -/
def renderKeywordLine (k : Keywords) : Option String :=
  let names := k.toList.map fun n =>
    match n.toList with
    | [] => n
    | c :: rest => String.ofList (c.toUpper :: rest)
  if names.isEmpty then none else some (String.intercalate ", " names)

def renderColors (cs : ColorSet) : String :=
  String.intercalate ", " (Color.all.filter cs.contains |>.map Color.englishName)

/-- Full printed card: name, mana cost, type line, P/T, color indicator,
`Token`, then `rules`. The rules text is not stored on the parsed `CardDef`. -/
def formatPrintedCard (name : String) (manaCost : ManaCost)
    (supertypes : Array Supertype) (types : Array CardType) (subtypes : Array Subtype)
    (power toughness : Option Int) (colorIndicator : Option ColorSet)
    (isToken : Bool) (rules : String) : String :=
  let cost := if manaCost.symbols.isEmpty then [] else [toString manaCost]
  let isCreature := types.any (· == .creature)
  let pt : List String :=
    match power, toughness with
    | some p, some t => [s!"{p}/{t}"]
    | some p, none => [s!"{p}/*"]
    | none, some t => [s!"*/{t}"]
    | none, none => if isCreature then ["*/*"] else []
  let color :=
    match colorIndicator with
    | some cs => [s!"Color indicator: {renderColors cs}"]
    | none => []
  let token := if isToken then ["Token"] else []
  let rules := if (rules.trimAscii.copy).isEmpty then [] else [rules]
  String.intercalate "\n"
    ([name] ++ cost ++ [formatTypeLine supertypes types subtypes] ++ pt ++ color ++ token ++ rules)

/-- Full printed text reconstructed from modeled fields. -/
partial def renderFullOracle (c : CardDef) : String :=
  let kw := match renderKeywordLine c.keywords with
    | some k => [k]
    | none => []
  let rules := String.intercalate "\n" (kw ++ c.structuredAbilityLines)
  let face :=
    formatPrintedCard c.name c.manaCost c.supertypes c.types c.subtypes
      c.power c.toughness c.colorIndicator c.isToken rules
  let face :=
    match c.loyalty with
    | some n => face ++ s!"\nLoyalty: {n}"
    | none => face
  let face := if c.daybound then face ++ "\nDaybound" else face
  match c.otherFace with
  | none => face
  | some back => face ++ "\n//\n" ++ renderFullOracle back

def firstDiff (a b : String) : String :=
  let rec go : List Char → List Char → Nat → String
    | [], [], _ => "equal"
    | [], _, i => s!"at {i}, parsed ended"
    | _, [], i => s!"at {i}, source ended"
    | x :: xs, y :: ys, i =>
      if x == y then go xs ys (i + 1)
      else
        let preview (cs : List Char) := String.ofList (cs.take 80)
        s!"at {i}: «{preview (x :: xs)}» vs «{preview (y :: ys)}»"
  go a.toList b.toList 0

/-- How `parsed` differs from `source` after forgetting stored Oracle text. -/
def oracleRoundtripDiff (source parsed : CardDef) : Option String :=
  let a := reprStr source
  let b := reprStr parsed
  if a == b then none
  else some s!"{source.name}: {firstDiff a b}"

#guard parseManaCost "{1}{G}" == some (ManaCost.ofGenericAndColor 1 .green)
#guard parseManaCost "{W}" == some (ManaCost.ofColor .white)
#guard parseManaCost "{G/U}" == some (ManaCost.ofHybrid .green .blue)
#guard (parseTypeLine "Legendary Creature — Dwarf Scout").toOption ==
  some (#[.legendary], #[.creature], #["Dwarf", "Scout"])
#guard parsePT "2/2" == some (some 2, some 2)
#guard parsePT "*/*" == some (none, none)
#guard (parseOracleCard "Grizzly Bears\n{1}{G}\nCreature — Bear\n2/2").toOption.map
    (fun c => c.name == "Grizzly Bears" && c.manaCost == ManaCost.ofGenericAndColor 1 .green &&
      c.power == some 2 && c.toughness == some 2 && c.isCreature) == some true
#guard (parseOracleCard "Mountain\nBasic Land — Mountain\n({T}: Add {R}.)").toOption.map
    (fun c => c.isLand && c.hasSupertype .basic && c.hasSubtype "Mountain" &&
      c.tapAddMana.isEmpty) == some true
#guard (parseOracleCard "Shock\n{R}\nInstant\nShock deals 5 damage to any target.").toOption.bind
    (·.spellEffect) == some (Effect.dealDamage 5)
#guard (parseOracleCard "Insight\n{U}\nSorcery\nDraw seven cards.").toOption.bind
    (·.spellEffect) == some (Effect.draw 7)
#guard (parseOracleCard "Wander\n{G}\nInstant\nForestcycling {2}").toOption.bind
    (fun c => c.activatedAbilities[0]?) ==
    some (typecyclingAbility "Forest" (ManaCost.ofGeneric 2))
#guard (parseOracleCard "Sword\n{2}\nArtifact — Equipment\nEquip {5}").toOption.bind
    (fun c => c.activatedAbilities[0]?) == some (equipAbility (ManaCost.ofGeneric 5))
#guard (parseOracleCard "Warren Chief\n{1}{R}\nCreature — Goblin\n2/2\nOther Goblin creatures you control get +2/+2.").toOption.bind
    (fun c => c.staticAbilities[0]?) == some (.otherCreaturesGet #["Goblin"] 2 2)
#guard (parseOracleCard "Test Saga\n{2}{R}\nEnchantment — Saga\nI — Draw seven cards.").toOption.bind
    (fun c => c.saga.bind fun s => (s.chapters[0]?).bind (·.chapterEffect)) ==
    some (Effect.chapterDraw 7)

end Mtg.Engine
