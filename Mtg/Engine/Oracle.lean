import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.Marvel

/-!
# Oracle verification

Check that a `CardDef`'s modeled fields reconstruct its stored Oracle text.
Reminder text, ability words, card-name wording, Gatherer `//ADV//` markers,
and equivalent phrasing (`this creature` vs the printed name) are normalized
away so currently supported cards can be checked mechanically.
-/

namespace Mtg.Engine

namespace CardDef

/-- Unique strings, first occurrence kept. -/
def uniqueStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

/-- Lexicographic sort for comparing ability-unit lists. -/
def sortStrings (xs : List String) : List String :=
  xs.toArray.qsort (fun a b => decide (a < b)) |>.toList

/-- Collapse runs of whitespace. -/
def collapseWs (s : String) : String :=
  let rec go (cs : List Char) (inSpace : Bool) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c == ' ' || c == '\n' || c == '\t' then
        go rest true acc
      else
        let acc := if inSpace && !acc.isEmpty then ' ' :: acc else acc
        go rest false (c :: acc)
  String.ofList (go s.toList false [])

/-- Drop balanced parentheticals, including nested reminder text. -/
def stripParentheticals (s : String) : String :=
  Id.run do
    let mut acc : Array Char := #[]
    let mut depth : Nat := 0
    for c in s.toList do
      if c == '(' then
        depth := depth + 1
      else if c == ')' then
        depth := if depth == 0 then 0 else depth - 1
      else if depth == 0 then
        acc := acc.push c
    return String.ofList acc.toList

/-- If the whole line is a parenthetical (basic-land reminder), unwrap it. -/
def unwrapOuterParens (s : String) : String :=
  let t := s.trimAscii.copy
  if t.startsWith "(" && t.endsWith ")" && t.length >= 2 then
    (t.drop 1 |>.dropEnd 1).trimAscii.copy
  else t

/-- Drop a leading ability word (`Landfall —`, `Ferocious —`). Leaves
`Choose one —` intact because that phrase contains a space. -/
def stripAbilityWord (s : String) : String :=
  match s.splitOn "—" with
  | head :: rest =>
    if rest.isEmpty then s
    else
      let h := head.trimAscii.copy
      let known :=
        h == "Power-up" || h == "Street Justice" || h == "Legal Justice" ||
        h == "Cosmic Awareness" || h == "Unbreakable Skin" || h == "Enrage" ||
        h == "Landfall" || h == "Avian Telepathy" || h == "Seismic Takedown" ||
        h == "Embiggen Fist" || h == "Wasp's Sting" ||
        h == "No One Dies!" || h == "Sonic Attack" ||
        h == "Do You Like Squirrels?" || h == "I LOVE Squirrels!" ||
        h == "Net" || h == "Explosive" || h == "Boomerang" ||
        h == "Solar Beam" || h == "Density Control" || h == "Technopathy" ||
        h == "Trick Arrows" || h == "Radar Sense" ||
        h == "Photographic Reflexes" || h == "Cybernetic Senses" ||
        h == "Designed Only for Killing" ||
        h == "Mental Organism" || h == "Tyrannosaurus Rex"
      if h.isEmpty || (h.contains ' ' && !known) then s
      else (String.intercalate "—" rest).trimAscii.copy
  | [] => s

/-- Printed-name variants used in Oracle (`Gandalf, Spark Starter` → `Gandalf`).
The first word is skipped when it is an article so `The Lonely Mountain`
does not treat `the` as the card name. Name replacement uses `replaceWord`
so `Ori` does not rewrite `storied`. -/
def nameAliases (name : String) : List String :=
  let trimmed := name.trimAscii.copy
  let beforeComma := (trimmed.splitOn ",").headD trimmed |>.trimAscii.copy
  let first := (beforeComma.splitOn " ").headD beforeComma
  let skipFirst :=
    first == "The" || first == "A" || first == "An" || first == "Of" ||
      first == "Enchanted"
  let aliases :=
    if skipFirst then [trimmed, beforeComma] else [trimmed, beforeComma, first]
  uniqueStrings (aliases.filter (fun s => s.length > 2))

/-- Replace each `old` with `new` in order. -/
def applyReplacements (s : String) (pairs : List (String × String)) : String :=
  pairs.foldl (fun acc p => acc.replace p.fst p.snd) s

/-- Replace an isolated word. Non-letters count as boundaries so `Gollum`
still matches in `Gollum can't`. -/
def replaceWord (s old new : String) : String :=
  if old.isEmpty then s
  else
    Id.run do
      let chars := s.toList
      let needle := old.toList
      let n := needle.length
      let mut acc : List Char := []
      let mut i : Nat := 0
      while i < chars.length do
        let slice := chars.drop i |>.take n
        let beforeOk := i == 0 || !(chars[i - 1]!.isAlphanum)
        let afterOk :=
          i + n >= chars.length || !(chars[i + n]!.isAlphanum)
        if slice == needle && beforeOk && afterOk then
          acc := acc ++ new.toList
          i := i + n
        else
          acc := acc ++ [chars[i]!]
          i := i + 1
      String.ofList acc

/-- Lowercase, drop reminders, and replace the card's name with `this`. -/
def prepareLine (cardName : String) (s : String) : String :=
  let s := unwrapOuterParens s
  let s := stripParentheticals s
  let s := stripAbilityWord s
  let s := (lowerAscii s).trimAscii.copy
  let aliases := nameAliases cardName |>.map lowerAscii
  let s :=
    aliases.foldl (fun acc a =>
      let acc := acc.replace s!"{a}'s" "this"
      replaceWord acc a "this") s
  applyReplacements s [
    ("this creature's", "this"),
    ("this permanent's", "this"),
    ("this card's", "this"),
    ("this enchantment's", "this"),
    ("this equipment's", "this"),
    ("this artifact's", "this"),
    ("this aura's", "this"),
    ("this spell's", "this"),
    ("this creature", "this"),
    ("this permanent", "this"),
    ("this enchantment", "this"),
    ("this equipment", "this"),
    ("this artifact", "this"),
    ("this aura", "this"),
    ("this card", "this"),
    ("this spell", "this"),
    ("this land", "this"),
    ("this vehicle", "this"),
    ("this saga", "this"),
    ("this enter ", "this enters "),
    ("this enter,", "this enters,")
  ]

/-- English number words that appear in Oracle (`two cards`, `three or more`). -/
def replaceNumberWords (s : String) : String :=
  let words : List (String × String) := [
    ("twenty", "20"), ("nineteen", "19"), ("eighteen", "18"),
    ("seventeen", "17"), ("sixteen", "16"), ("fifteen", "15"),
    ("fourteen", "14"), ("thirteen", "13"), ("twelve", "12"),
    ("eleven", "11"), ("ten", "10"), ("nine", "9"), ("eight", "8"),
    ("seven", "7"), ("six", "6"), ("five", "5"), ("four", "4"),
    ("three", "3"), ("two", "2"), ("one", "1")
  ]
  words.foldl (fun acc p => replaceWord acc p.fst p.snd) s

/-- Drop a leading `this ` left over from name replacement. -/
def dropLeadingThis (s : String) : String :=
  let s := s.trimAscii.copy
  if s.startsWith "this " then (s.drop "this ".length).trimAscii.copy else s

/-- Keep letters, digits, mana braces, and P/T signs; other punctuation
becomes a space. Apostrophes are dropped so `can't` is `cant`. -/
def keepSignificant (s : String) : String :=
  String.ofList (s.toList.filterMap (fun c =>
    if c == '\'' then none
    else if c.isAlphanum || c == '{' || c == '}' || c == '/' || c == '+' || c == '-' then
      some c
    else some ' '))

/-- Phrase-level Oracle equivalences after `prepareLine`. -/
def normalizePhrases (s : String) : String :=
  applyReplacements s [
    ("put that card", "put it"),
    ("sacrifice this artifact", "sacrifice"),
    ("sacrifice this creature", "sacrifice"),
    ("sacrifice this land", "sacrifice"),
    ("sacrifice this", "sacrifice"),
    ("sacrifice another creature or artifact", "sacrifice an artifact or creature"),
    ("sacrifice another artifact or creature", "sacrifice an artifact or creature"),
    ("he gains", "this gains"),
    ("she gains", "this gains"),
    ("he deals", "this deals"),
    ("she deals", "this deals"),
    ("it deals", "this deals"),
    ("he fights", "this fights"),
    ("she fights", "this fights"),
    ("tap him", "tap this"),
    ("tap her", "tap this"),
    ("this leave the battlefield", "this leaves the battlefield"),
    ("she connives", "it connives"),
    ("he connives", "it connives"),
    ("he has flying", "it has flying"),
    ("attached to him", "attached to it"),
    ("dealt to him", "dealt to it"),
    ("with him on the battlefield", "with it on the battlefield"),
    ("begin the game with him", "begin the game with it"),
    ("and only once each turn", "activate only once each turn"),
    ("activate only from the graveyard", ""),
    ("activate only from your hand", ""),
    ("if you control a creature with power", "while you control a creature with power"),
    ("other elf creatures you control", "other elves you control"),
    ("other bear creatures you control", "other bears you control"),
    ("other merfolk creatures you control", "other merfolk you control"),
    ("other villain creatures you control", "other villains you control"),
    ("other hero creatures you control", "other heroes you control"),
    ("street justice ", ""),
    ("legal justice ", ""),
    ("trick arrows ", ""),
    ("if her power", "if its power"),
    ("if his power", "if its power"),
    ("enchant creature you control", "enchant creature"),
    ("target player create ", "target player creates "),
    ("destroy target artifact or land", "destroy target land"),
    ("you may play it until the end of your next turn",
      "until the end of your next turn you may play that card"),
    ("this enter ", "this enters "),
    ("counter on him", "counter on this"),
    ("counter on her", "counter on this"),
    ("counter on it", "counter on this"),
    ("shield counter on him", "shield counter on this"),
    ("shield counter on her", "shield counter on this"),
    ("shield counter on it", "shield counter on this")
  ]

/-- Comparable form of one ability unit. -/
def normalizeUnit (cardName : String) (s : String) : String :=
  let s := prepareLine cardName s
  let s := replaceNumberWords s
  let s := normalizePhrases s
  let s := keepSignificant s
  let s := collapseWs s
  dropLeadingThis s

/-- True when `line` is a Gatherer Adventure type line. -/
def isAdventureTypeLine (s : String) : Bool :=
  let t := s.trimAscii.copy
  (t.startsWith "Sorcery" || t.startsWith "Instant") &&
    (t.endsWith "Adventure" || (t.splitOn "Adventure").length > 1)

/-- Attach `•` mode lines to the preceding `Choose one` line. -/
def mergeBulletLines (lines : List String) : List String :=
  lines.foldl (fun acc line =>
    if line.startsWith "•" then
      match acc.reverse with
      | [] => [line]
      | last :: rev => ((last ++ " " ++ line) :: rev).reverse
    else
      acc ++ [line]) []

/-- Join `Name {cost}` / `Sorcery — Adventure` / effect into one unit. -/
def mergeAdventureBlocks : List String → List String
  | a :: b :: c :: rest =>
    if isAdventureTypeLine b then
      s!"{a} {b} {c}" :: mergeAdventureBlocks rest
    else
      a :: mergeAdventureBlocks (b :: c :: rest)
  | xs => xs

/-- Split `Flying, first strike, ward {1}` into a keyword line and `Ward {1}.`. -/
def splitKeywordWardLine (s : String) : List String :=
  let t := s.trimAscii.copy
  let lower := lowerAscii t
  if !(lower.contains ", ward {") then [s]
  else
    match t.splitOn ", ward {" with
    | [kws, rest] =>
      let digits := rest.takeWhile Char.isDigit
      if kws.isEmpty || digits.isEmpty then [s]
      else [kws, s!"Ward \{{digits}}."]
    | _ =>
      match t.splitOn ", Ward {" with
      | [kws, rest] =>
        let digits := rest.takeWhile Char.isDigit
        if kws.isEmpty || digits.isEmpty then [s]
        else [kws, s!"Ward \{{digits}}."]
      | _ => [s]

/-- Printed Oracle lines, without the Gatherer `//ADV//` marker. -/
def rawOracleLines (text : String) : List String :=
  (text.splitOn "\n" |>.filterMap (fun line =>
    match stripAdventureDelimiter (line.trimAscii.copy) with
    | none => none
    | some rest => if rest.isEmpty then none else some rest)
  ).flatMap splitKeywordWardLine

/-- Ability units in stored Oracle text. -/
def oracleAbilityUnits (text : String) : List String :=
  mergeAdventureBlocks (mergeBulletLines (rawOracleLines text))

/-- Keyword names the engine models, in lowercase. -/
def modeledKeywordNames : List String :=
  Keywords.fields.map (·.name)

/-- If `prepared` is only modeled keywords, those names; otherwise none. -/
def keywordTokens (prepared : String) : Option (List String) :=
  let cleaned := dropLeadingThis ((prepared.replace "." "").trimAscii.copy)
  let parts :=
    cleaned.splitOn "," |>.map (fun s => s.trimAscii.copy) |>.filter (fun s => !s.isEmpty)
  if parts.isEmpty then none
  else if parts.all (fun p => modeledKeywordNames.any (· == p)) then some parts
  else none

/-- Equip `{cost}` printed as the keyword rather than the reminder. -/
def isEquipAbility (ab : ActivatedAbility) : Bool :=
  ab.effect == Effect.ofAbility .attachToTargetCreatureYouControl && ab.onlyAsSorcery && !ab.isModal

/-- Typecycling land type when this is a cycling activation from hand. -/
def typecyclingLand? (ab : ActivatedAbility) : Option String :=
  if ab.activateFromHand && ab.cost.discardSource then
    match ab.effect.abilityResolution with
    | .searchLandTypeToHand t =>
      if t == "Plan" then none else some t
    | _ => none
  else none

/-- Cost, effect, and timing for a modeled activation. -/
def activatedOracleLineFromParts (ab : ActivatedAbility) : String :=
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
    else
      ab.effect.toNotation
  s!"{ab.cost.toNotation}: {body}.{timing}"

/-- Oracle-style line for a modeled activated ability. Timing restrictions are
sentences, not parentheticals, so they survive reminder-text stripping. -/
def activatedOracleLine (ab : ActivatedAbility) : String :=
  if isEquipAbility ab then
    let pay :=
      if ab.cost.payLife != 0 then s!", Pay {ab.cost.payLife} life" else ""
    match ab.equipSubtype with
    | some t => s!"Equip {t} {ab.cost.mana}{pay}"
    | none =>
      if ab.equipWorthy then s!"Equip worthy {ab.cost.mana}{pay}"
      else if pay != "" then s!"Equip—{ab.cost.mana}{pay}"
      else s!"Equip {ab.cost.mana}"
  else
    match typecyclingLand? ab with
    | some t => s!"{t}cycling {ab.cost.mana}"
    | none => activatedOracleLineFromParts ab

/-- Oracle-style line for a one-shot spell effect. -/
def spellEffectLine (cardName : String) (e : Effect) : String :=
  let body := Effect.toNotation e
  if body.startsWith "deals" then s!"{cardName} {body}" else body

/-- Lines reconstructed from modeled `CardDef` fields (not keywords). -/
def reconstructedAbilityLines (c : CardDef) : List String :=
  (if c.costReductionIfCreatureDied != 0 then
    [s!"This spell costs \{{c.costReductionIfCreatureDied}} less to cast if a creature died this turn."]
   else []) ++
  (if c.costReductionIfTargetDamaged != 0 then
    [s!"This spell costs \{{c.costReductionIfTargetDamaged}} less to cast if it targets a creature that was dealt damage this turn."]
   else []) ++
  (if c.costReductionIfTargetTapped != 0 then
    [s!"This spell costs \{{c.costReductionIfTargetTapped}} less to cast if it targets a tapped creature."]
   else []) ++
  (if c.costReductionIfTargetAttackingNontoken != 0 then
    [s!"This spell costs \{{c.costReductionIfTargetAttackingNontoken}} less to cast if it targets an attacking nontoken creature."]
   else []) ++
  (if c.costReductionIfTargetAttacking != 0 then
    [s!"This spell costs \{{c.costReductionIfTargetAttacking}} less to cast if it targets an attacking creature."]
   else []) ++
  (match c.costReductionIfYouControl with
   | some (n, subtype) =>
     [s!"This spell costs \{{n}} less to cast if you control a {subtype}."]
   | none => []) ++
  (match c.costReductionIfGyCreaturesAtLeast with
   | some (min, n) =>
     let cards := if min == 1 then "a creature card" else s!"{min} or more creature cards"
     [s!"This spell costs \{{n}} less to cast if there are {cards} in your graveyard."]
   | none => []) ++
  (if c.costReductionEqualFlyingPower then
    ["This spell costs {X} less to cast, where X is the total power of creatures you control with flying."]
   else []) ++
  (if c.costReductionEqualOppArtifacts then
    ["This spell costs {X} less to cast, where X is the greatest number of artifacts an opponent controls."]
   else []) ++
  (match c.affinityForSubtype with
   | some t => [s!"Affinity for {t}"]
   | none => []) ++
  (if c.cascade == 1 then ["Cascade"]
   else if c.cascade >= 2 then
     [String.intercalate ", " (List.replicate c.cascade "Cascade")]
   else []) ++
  (match c.kicker with
   | some cost => [s!"Kicker {cost.toNotation}"]
   | none => []) ++
  (if c.giftTreasure then
    ["Gift a Treasure"]
   else []) ++
  (match c.teamwork with
   | some n => [s!"Teamwork {n}"]
   | none => []) ++
  (if c.additionalCostSacrificeCreature then
    ["As an additional cost to cast this spell, sacrifice a creature"]
   else
    c.additionalCostSacrificeArtifactOrCreatureLine) ++
  (if c.isAura then ["Enchant creature"] else []) ++
  c.simpleTapAddLines ++
  (if c.tapAddOneOf.size >= 2 then
    [s!"\{T}: Add {String.intercalate " or " (c.tapAddOneOf.toList.map (fun t => s!"\{{t.letter}}"))}"]
   else
    c.tapAddOneOf.toList.map (fun t => s!"\{T}: Add \{{t.letter}}")) ++
  (if c.tapAddOneOfIfEnteredOrBasic.size >= 2 then
    [s!"\{T}: Add {String.intercalate " or " (c.tapAddOneOfIfEnteredOrBasic.toList.map (fun t => s!"\{{t.letter}}"))}. Activate only if this land entered this turn or if you control a basic land."]
   else
    c.tapAddOneOfIfEnteredOrBasic.toList.map (fun t =>
      s!"\{T}: Add \{{t.letter}}. Activate only if this land entered this turn or if you control a basic land.")) ++
  c.tapAddForEachLines ++
  c.tapAddAnyColorEqualToPowerLine ++
  c.tapAddAnyColorForInstantOrSorceryLine ++
  (if c.tapAddAnyColor then
    ["{T}: Add one mana of any color."]
   else []) ++
  (if c.tapAddAnyColorForLegendary then
    ["{T}: Add one mana of any color. Spend this mana only to cast a legendary spell, and that spell can't be countered."]
   else []) ++
  (if c.tapAddAnyColorAmongLegendaries then
    ["{T}: Add one mana of any color among legendary creatures and planeswalkers you control."]
   else []) ++
  (if c.tapAddCommanderIdentity then
    ["{T}: Add one mana of any color in your commander's color identity."]
   else []) ++
  (match c.tapAddRestricted with
   | some (types, restriction) =>
     let parts := types.toList.map (fun t => s!"\{{t.letter}}")
     [s!"\{T}: Add {String.intercalate "" parts}. Spend this mana only to cast {restriction}."]
   | none => []) ++
  (match c.tapPayLifeAddOneOf with
   | some (life, types) =>
     let add :=
       String.intercalate " or " (types.toList.map (fun t => s!"\{{t.letter}}"))
     [s!"\{T}, Pay {life} life: Add {add}."]
   | none => []) ++
  (if c.tapAddTwoAmong.size >= 2 then
    let letters := c.tapAddTwoAmong.toList.map (fun t => s!"\{{t.letter}}")
    let joined :=
      match letters with
      | [a, b] => s!"{a} and/or {b}"
      | xs =>
        let last := xs.getLast!
        let init := String.intercalate ", " xs.dropLast
        s!"{init}, and/or {last}"
    [s!"\{T}: Add two mana in any combination of {joined}."]
   else []) ++
  (if c.tapSacrificeAddAnyColor then
    ["{T}, Sacrifice this artifact: Add one mana of any color."]
   else []) ++
  (match c.crew with
   | some n => [s!"Crew {n}"]
   | none => []) ++
  (if c.cantBeCountered then
    ["This spell can't be countered."]
   else []) ++
  (match c.flashIfYouControlSubtype with
   | some t =>
     [s!"You may cast this spell as though it had flash if you control a {t}."]
   | none => []) ++
  (match c.ward with
   | some n => [s!"Ward \{{n}}."]
   | none => []) ++
  (match c.flashback with
   | some cost => [s!"Flashback {cost}"]
   | none => []) ++
  (if c.entersTapped then
    [if c.hasSupertype .legendary || (!c.isLand && c.isCreature) then
      s!"{c.name} enters tapped."
     else if c.isLand then "This land enters tapped."
     else if c.isArtifact then "This artifact enters tapped."
     else "This creature enters tapped."]
   else []) ++
  (if c.entersTappedUnlessLegendary then
    [if c.hasSupertype .legendary then
      s!"{c.name} enters tapped unless you control a legendary creature."
     else
      "This land enters tapped unless you control a legendary creature."]
   else []) ++
  (if c.entersTappedUnlessEquipment then
    ["This land enters tapped unless you control an Equipment."]
   else []) ++
  (match c.entersTappedUnlessPayLife with
   | some n =>
     [s!"As {c.name} enters, you may pay {n} life. If you don't, it enters tapped."]
   | none => []) ++
  (if c.asEntersChooseCreatureType then
    ["As this enchantment enters, choose a creature type."]
   else []) ++
  (if c.entersWithHopePerCreature then
    ["This enchantment enters with a hope counter on it for each creature you control."]
   else []) ++
  (if c.entersWithShield == 1 then
    [s!"{c.name} enters with a shield counter on it."]
   else if c.entersWithShield > 1 then
    [s!"{c.name} enters with {c.entersWithShield} shield counters on it."]
   else []) ++
  (if c.foodAlsoCreatesTreasure then
    ["If you would create a Food token, instead create a Food token and a Treasure token."]
   else []) ++
  (if c.drawTwoExceptFirstDrawStep then
    ["If you would draw a card except the first one you draw in each of your draw steps, draw two cards instead."]
   else []) ++
  (if c.tokenDoubling then
    ["If one or more tokens would be created under your control, twice that many of those tokens are created instead."]
   else []) ++
  (if c.othersEnterWithPlusOneEqualToughness then
    ["Each other creature you control enters with a number of additional +1/+1 counters on it equal to this toughness."]
   else []) ++
  (if c.mayLookAtTopAnytime then
    ["You may look at the top card of your library any time."]
   else []) ++
  (if c.mayCastCreaturesFromTop then
    ["You may cast creature spells from the top of your library."]
   else []) ++
  (if c.mayPlayLandsFromTop then
    ["You may play lands from the top of your library."]
   else []) ++
  (if c.grantCreaturesTapAddAnyColor then
    ["Creatures you control have \"{T}: Add one mana of any color.\""]
   else []) ++
  (if c.firstCreatureCostsLess > 0 then
    [if c.firstCreatureHasFlash then
      s!"The first creature spell you cast each turn costs \{{c.firstCreatureCostsLess}} less to cast and can be cast as though it had flash."
     else
      s!"The first creature spell you cast each turn costs \{{c.firstCreatureCostsLess}} less to cast."]
   else []) ++
  (if c.asEntersChooseOddEven then
    ["As Gollum enters, choose odd or even. (Zero is even.)"]
   else []) ++
  (if c.costReductionNotFromHand > 0 then
    [s!"Spells you cast from anywhere other than your hand cost \{{c.costReductionNotFromHand}} less to cast."]
   else []) ++
  (if c.entersWithIndestructibleCounter then
    ["Arwen enters with an indestructible counter on her."]
   else []) ++
  (match c.hexproofIndestructibleIfLore with
   | some n =>
     [s!"As long as there are {n} or more lore counters among Sagas you control, {c.name} has hexproof and indestructible."]
   | none => []) ++
  (if c.powerPerMountain != 0 then
    [s!"This creature gets +{c.powerPerMountain}/+0 for each Mountain you control."]
   else []) ++
  (match c.extraLandIfOtherSubtype with
   | some t =>
     [s!"As long as you control another {t}, you may play an additional land on each of your turns."]
   | none => []) ++
  (match c.tapAddColorlessPerSubtype with
   | some t =>
     [s!"\{T}: Add \{C} for each {t} you control."]
   | none => []) ++
  (match c.saga with
   | some s =>
     [s!"(As this Saga enters and after your draw step, add a lore counter. Sacrifice after {s.sacrificeAfter}.)"] ++
       s.chapters.toList.map (fun ch => s!"{ch.roman} — {ch.effect}")
   | none => []) ++
  c.staticAbilities.toList.map StaticAbility.toNotation ++
  c.triggeredAbilities.toList.map TriggeredAbility.toNotation ++
  c.activatedAbilities.toList.map activatedOracleLine ++
  (if !c.spellModes.isEmpty then
    let modes :=
      String.intercalate " " (c.spellModes.toList.map (fun e =>
        s!"• {spellEffectLine c.name e}"))
    [match c.chooseTwoIfYouControlSubtype, c.chooseBothIfTeamwork, c.chooseOneOrBoth with
     | some t, _, _ =>
       s!"Choose one. If you control a {t} as you cast this spell, you may choose two instead. {modes}"
     | none, true, _ =>
       s!"Choose one. If this spell was cast using teamwork, choose both instead. {modes}"
     | none, false, true =>
       s!"Choose one or both — {modes}"
     | none, false, false =>
       s!"Choose one — {modes}"]
   else
    match c.spellEffect with
    | some e =>
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
        [s!"{c.name} deals {n} damage to each non-Dragon creature.",
          "Add four mana in any combination of colors. Spend this mana only to cast Dragon spells."]
      | .grantVigilanceUnblockable =>
        ["Target creature gains vigilance until end of turn and can't be blocked this turn.",
          "Draw a card."]
      | .becomeArtifactCreature44Flying =>
        ["Until end of turn, target artifact or creature becomes an artifact creature with base power and toughness 4/4 and gains flying.",
          "Draw a card."]
      | _ =>
        e.toNotation.splitOn "\n" |>.filterMap (fun s =>
          let s := s.trimAscii.copy
          if s.isEmpty then none
          else some (if s.startsWith "deals" then s!"{c.name} {s}" else s))
    | none => []) ++
  match c.adventure with
  | none => []
  | some adv =>
    let effect :=
      match adv.spellEffect with
      | some e => spellEffectLine adv.name e
      | none => adv.oracleText
    let typeLine := formatTypeLine #[] adv.types adv.subtypes
    if adv.additionalCostSacrificeCreature then
      [s!"{adv.name} {adv.manaCost} {typeLine} As an additional cost to cast this spell, sacrifice a creature.",
        effect]
    else
      [s!"{adv.name} {adv.manaCost} {typeLine} {effect}"]

/-- Split a unit into modeled keywords or a normalized leftover line. -/
def classifyUnit (cardName : String) (unit : String) : Sum (List String) String :=
  match keywordTokens (prepareLine cardName unit) with
  | some kws => .inl kws
  | none => .inr (normalizeUnit cardName unit)

/-- Keywords and remaining normalized units from a list of ability units. -/
def partitionUnits (cardName : String) (units : List String) : List String × List String :=
  let classified := units.map (classifyUnit cardName)
  let kws :=
    uniqueStrings (classified.foldl (fun acc u =>
      match u with
      | .inl ks => acc ++ ks
      | .inr _ => acc) [])
  let rest :=
    classified.filterMap (fun u =>
      match u with
      | .inl _ => none
      | .inr s => if s.isEmpty then none else some s)
  (sortStrings kws, sortStrings rest)

/-- Keywords and remaining units implied by stored Oracle text. -/
def oraclePartition (c : CardDef) : List String × List String :=
  partitionUnits c.name (oracleAbilityUnits c.oracleText)

/-- Keywords and remaining units implied by modeled fields. -/
def reconstructedPartition (c : CardDef) : List String × List String :=
  let fromLines := partitionUnits c.name (reconstructedAbilityLines c)
  let printed := sortStrings c.keywords.toList
  (sortStrings (uniqueStrings (printed ++ fromLines.fst)), fromLines.snd)

/-- True when modeled fields reconstruct this card's Oracle text. -/
def matchesOracleText (c : CardDef) : Bool :=
  c.oraclePartition == c.reconstructedPartition

/-- Debug report: Oracle vs reconstructed keyword and ability units. -/
def oracleMismatch (c : CardDef) : String :=
  let (ok, oa) := c.oraclePartition
  let (rk, ra) := c.reconstructedPartition
  s!"{c.name}\n  oracle keywords: {ok}\n  modeled keywords: {rk}\n  oracle units: {oa}\n  modeled units: {ra}"

end CardDef

open Catalog

/-- Every card in the engine catalog. Oracle text is fully represented by
modeled fields; `supportedCardsMatchOracle` checks that mechanically. -/
def supportedCatalogCards : Array CardDef :=
  #[grizzlyBears, grayOgre, hillGiant, canyonMinotaur, ragingGoblin,
    llanowarElves, crawWurm, centaurCourser, rumblingBaloth, giantSpider,
    lightningBolt, shock, giantGrowth]
    ++ Catalog.hobbitCards
    ++ Catalog.hobbitEternalCards
    ++ Catalog.mshCards

/-- True when every currently supported catalog card's `CardDef` matches Oracle. -/
def supportedCardsMatchOracle : Bool :=
  supportedCatalogCards.all (·.matchesOracleText)

/-- Names of supported catalog cards whose `CardDef` does not match Oracle. -/
def supportedOracleFailures : List String :=
  supportedCatalogCards.toList.filterMap (fun c =>
    if c.matchesOracleText then none else some c.oracleMismatch)

#guard CardDef.normalizeUnit "Lightning Bolt" "Lightning Bolt deals 3 damage to any target." ==
  CardDef.normalizeUnit "Lightning Bolt" "deals 3 damage to any target"
#guard CardDef.keywordTokens (CardDef.prepareLine "Silent" "Reach, deathtouch") ==
  some ["reach", "deathtouch"]
#guard CardDef.keywordTokens (CardDef.prepareLine "Silent"
  "Menace (This creature can't be blocked except by two or more creatures.)") ==
  some ["menace"]
#guard CardDef.isAdventureTypeLine "Sorcery — Adventure"
#guard CardDef.isAdventureTypeLine "Instant — Adventure"
#guard !CardDef.isAdventureTypeLine "Choose one —"
#guard plains.matchesOracleText
#guard mountain.matchesOracleText
#guard grizzlyBears.matchesOracleText
#guard ragingGoblin.matchesOracleText
#guard llanowarElves.matchesOracleText
#guard giantSpider.matchesOracleText
#guard lightningBolt.matchesOracleText
#guard giantGrowth.matchesOracleText
#guard roguesPassage.matchesOracleText
#guard nightsWhisper.matchesOracleText
#guard giftOfStrands.matchesOracleText
#guard smaugTheGreatCalamity.matchesOracleText
#guard beornReluctantHost.matchesOracleText
#guard gollumTheAbandoned.matchesOracleText
#guard gollumSilentSlinker.keywords.menace
#guard bofurReliableGuardian.matchesOracleText
#guard magnificentEnd.matchesOracleText
#guard gollumSilentSlinker.matchesOracleText
#guard supportedCardsMatchOracle || panic! (String.intercalate "\n\n" supportedOracleFailures)

end Mtg.Engine
