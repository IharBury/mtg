import Mtg.Engine.Card.OracleParse.StaticLines

/-!
# Catalog sentences

Object descriptions and one sentence of a catalog effect.
-/

namespace Mtg.Engine

namespace OracleParts

/-- A word before the noun of an object description: `attacking`, `tapped`,
`legendary`, `nontoken`, or `non<card type>` such as `nonland`. -/
def objectModifier? (w : String) : Option Selector :=
  match w with
  | "attacking" => some (.attacking .all)
  | "tapped" => some .tapped
  | "legendary" => some (.supertype .legendary)
  | "basic" => some (.supertype .basic)
  | "nontoken" => some (.not .token)
  | "untapped" => some (.not .tapped)
  | "nonlegendary" => some (.not (.supertype .legendary))
  | _ => (after? w "non").bind typeOfOracle? |>.map fun t => .not (.cardType t)

/-- Leading modifier words and the words after them. -/
def splitModifiers : List String → List Selector × List String
  | [] => ([], [])
  | w :: rest =>
    match objectModifier? w with
    | some sel =>
      if rest.isEmpty then ([], [w])
      else
        let (mods, core) := splitModifiers rest
        (sel :: mods, core)
    | none => ([], w :: rest)

/-- A subtype printed singular (`Wolf`) or plural (`Goblins`, `Wolves`). -/
def subtypeWord? (w : String) : Option CardSubtype :=
  subtypeOfOracle? w <|> pluralCreatureType? w <|> amassSubtype? w

/-- Subtypes joined by `and`, `or`, or commas: `Goblins and Orcs`. -/
def subtypeWords? (s : String) : Option (List CardSubtype) :=
  let parts := orList ((norm s).replace " and " " or ")
  if parts.isEmpty then none else parts.mapM subtypeWord?

/-- Subtypes that are not creature types (CR 205.3g-205.3m). -/
def nonCreatureSubtypes : List CardSubtype := [
  .adventure, .arcane, .aura, .clue, .equipment, .food, .forest, .gate, .island,
  .mountain, .plains, .plan, .saga, .swamp, .treasure, .vehicle]

/-- The noun of an object description. `permanent` has no type. A card type
list is those types; `creature token` is also a token. A subtype list is
those subtypes, and `withCreature` adds the creature type to a subtype
list. The second result is whether the noun names tokens. -/
def objectNoun? (core : String) (withCreature : Bool) :
    Option (List Selector × Bool) :=
  let core := norm core
  let (core, tokens) :=
    match before? core " tokens" <|> before? core " token" with
    | some rest => (rest, true)
    | none => (core, false)
  if core == "token" || core == "tokens" then some ([], true)
  else if core == "permanent" || core == "permanents" then some ([], tokens)
  else
    match typesInPhrase core with
    | some ts => some ([selectorOfTypes ts], tokens)
    | none =>
      ((subtypeWords? core).map fun sts =>
        let creature := withCreature && !sts.any nonCreatureSubtypes.contains
        ((if creature then [.cardType .creature] else []) ++ [subtypeSelector sts],
          tokens)) <|>
      ((before? core " creatures" <|> before? core " creature").bind subtypeWords? |>.bind fun sts =>
        if sts.any nonCreatureSubtypes.contains then none
        else some ([.cardType .creature, subtypeSelector sts], tokens))

/-- A trailing `with power N or less` or `with power N or greater`, and the
text before it. -/
def splitPowerClause (s : String) : String × List Selector :=
  match split2? s " with power " with
  | some (rest, clause) =>
    match (before? clause " or less").bind natOfDigits?,
        (before? clause " or greater").bind natOfDigits? |>.filter (· != 0) with
    | some k, _ => (rest, [.powerAtMost (Value.int k)])
    | _, some k => (rest, [.powerAtLeast (Value.int k)])
    | none, none => (s, [])
  | none => (s, [])

/-- The controller clause after an object description, and the text before it. -/
def splitControllerClause (s : String) : String × List Selector :=
  match before? s " you control" with
  | some rest => (rest, [youControl])
  | none =>
    match before? s " an opponent controls" <|> before? s " your opponents control" with
    | some rest => (rest, [.controlled (.opponent (.controller .this))])
    | none => (s, [])

/-- A trailing `with <keyword>` or `without <keyword>`, and the text before it. -/
def splitKeywordClause (s : String) : String × List Selector :=
  match split2? s " without " with
  | some (rest, kw) =>
    match keywordOfOracle? kw with
    | some k => (rest, [.not (.keyword k)])
    | none => (s, [])
  | none =>
    match split2? s " with " with
    | some (rest, kw) =>
      match keywordOfOracle? kw with
      | some k => (rest, [.keyword k])
      | none => (s, [])
    | none => (s, [])

/-- The objects matching every selector. One selector is itself. -/
def intersectionOf : List Selector → Selector
  | [one] => one
  | many => .intersection many

/-- A permanent described by `another`, modifiers, a noun, `with` or
`without` a keyword, and a controller: `another nontoken Hero you control`,
`attacking creature tokens you control`, `nonland, nontoken permanent`, or
`noncreature artifact or noncreature enchantment`. `another` and `other`
exclude this object. `withCreature` adds the creature type to a subtype.
Supertypes are last. -/
def parseObjectDesc (s : String) (withCreature : Bool) : Option Selector :=
  let s := norm s
  let (s, other) :=
    match after? s "another " <|> after? s "other " with
    | some rest => (rest, true)
    | none => (s, false)
  let (s, power) := splitPowerClause s
  let (s, controller) := splitControllerClause s
  let (s, keywords) := splitKeywordClause s
  let words := (s.replace ", " " ").splitOn " " |>.map copied |>.filter (· != "")
  let (mods, coreWords) := splitModifiers words
  let modWords := words.take mods.length
  let core := String.intercalate " " coreWords
  let core := modWords.foldl (fun c w => c.replace (" or " ++ w ++ " ") " or ") core
  (objectNoun? core withCreature).map fun (noun, tokens) =>
    let isTokenNeg := fun (sel : Selector) => sel == .not .token
    let isTypeNeg := fun (sel : Selector) =>
      match sel with
      | .not (.cardType _) => true
      | _ => false
    let isSupertype := fun (sel : Selector) =>
      match sel with
      | .supertype _ => true
      | _ => false
    let rest := mods.filter fun m => !isTokenNeg m && !isTypeNeg m && !isSupertype m
    intersectionOf (
      (if other then [.not .this] else []) ++
      mods.filter isTokenNeg ++
      [.zone .battlefield] ++
      mods.filter isTypeNeg ++
      noun ++
      (if tokens then [.token] else []) ++
      rest ++
      keywords ++
      controller ++
      mods.filter isSupertype ++
      power)

/-- `you control a legendary creature`, `you control a Goblin or Orc`: the
object phrase after `you control`, as a condition. -/
def youControlCondition? (obj : String) : Option Condition :=
  (dropArticle? obj).bind (parseObjectDesc · false) |>.map fun sel =>
    .any (andYouControl sel)

/-- A permanent phrase the way a target names it: a subtype is a creature
of that subtype. -/
def parseTargetObject (s : String) : Option Selector :=
  parseObjectDesc s true

/-- `target <object>`, `another target <object>`, `up to one target <object>`,
`up to one other target <object>`, `each of up to two target <object>`,
`any number of target <object>`, or `any target`, as target `n`. Up to N is
zero through N (CR 115.1). `other` excludes this object. `any number` is zero
to unbounded. `any target` is a player or a permanent that can be dealt
damage. -/
def parseTargetDesc (s : String) (n : Nat) : Option Selector :=
  let s := norm s
  if s == "any target" then some (.target n .all)
  else
    let anyNumber :=
      (after? s "any number of target ").bind fun obj =>
        (parseTargetObject obj).map fun sel => .targets n .any sel
    let upTo :=
      (after? s "each of up to " <|> after? s "up to ").bind fun rest =>
        (split2? rest " target ").bind fun (countText, obj) =>
          let (countText, obj) :=
            match before? countText " other" with
            | some c => (c, "other " ++ obj)
            | none => (countText, obj)
          (positiveCount countText).bind fun k =>
            (parseTargetObject obj).map fun sel => .targets n (.range 0 (Value.nat k)) sel
    let another :=
      (after? s "another target ").bind fun obj =>
        (parseTargetObject ("another " ++ obj)).map fun sel => .target n sel
    let plain :=
      (after? s "target ").bind fun obj =>
        (parseTargetObject obj).map fun sel => .target n sel
    anyNumber <|> upTo <|> another <|> plain

/-- A card in your graveyard: `creature card` or `artifact or enchantment card`. -/
def parseGraveyardCard (s : String) : Option Selector :=
  (before? (norm s) " card").bind (fun kind =>
    ((typesInPhrase kind).map selectorOfTypes) <|> ((subtypeOfOracle? kind).map .subtype)) |>.map
    fun k => .intersection [.zone .graveyard, k, .owner (.controller .this)]

/-- The trigger or the spell's controller plays each keyword action: `it`,
`he`, `she`, or this card's name is this object. -/
def selfSubject? (cardName who : String) : Option Selector :=
  if damageSource? cardName who then some (.source .this) else none

/-- Actions from a sentence parser as one action. One action is itself;
several are a sequence, with inner sequences flattened. -/
def combineActions (actions : List CardAction) : Option CardAction :=
  match actions.flatMap flattenAction with
  | [] => none
  | [one] => some one
  | many => some (.sequence many)

/-- Keywords gained by `sel` until end of turn. -/
def gainUntilEnd (sel : Selector) (kws : List Keyword) : Option CardAction :=
  if kws.isEmpty then none
  else some (.continuous (keywordGains sel kws) .endOfTurn)

/-- A subject that gets or gains something: a target (numbered `n`), this
card, `it` (the previous target), `that creature` (the previous target),
`enchanted creature`, `equipped creature`, or permanents such as
`creatures you control`. The number is the next one after the subject. -/
def parseSubject (cardName who : String) (n : Nat) : Option (Selector × Nat) :=
  let who := norm who
  match who with
  | "it" | "that creature" =>
    if n <= 1 then none else some (.targetReference (n - 1), n)
  | "he" | "she" => some (.source .this, n)
  | "enchanted creature" | "equipped creature" => some (.hostOf .this, n)
  | "all creatures" => some (permanentWith [.creature], n)
  | _ =>
    if refersToSelf cardName who then some (.source .this, n)
    else
      match parseTargetDesc who n with
      | some sel => some (sel, n + 1)
      | none => (parseObjectDesc who false).map (·, n)

/-- `<subject> get(s) +P/+T [and gain(s) <keywords>] until end of turn`.
The first effect declares a target in the subject; later ones refer to it.
A zero bonus is omitted. -/
def parseGetsGainsUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " until end of turn").bind fun body =>
    (splitGets? body).bind fun (who, rest) =>
      let (ptText, kws?) :=
        match split2? rest " and gains " <|> split2? rest " and gain " with
        | some (pt, gained) => (pt, parseKeywordPhrase gained)
        | none => (rest, some [])
      match parseSubject cardName who n, parsePowerToughness ptText, kws? with
      | some (sel, n'), some (p, t), some kws =>
        let pt := flatPowerToughness sel p t
        let later := if pt.isEmpty then sel else sel.referenceTargets
        let effects := pt ++ keywordGains later kws
        if pt.isEmpty then none
        else some (.continuous effects .endOfTurn, n')
      | _, _, _ => none

/-- `<subject> gain(s) <keywords> until end of turn [and can't be blocked this turn]`.
The keywords, and the blocking restriction, last until end of turn. -/
def parseGainUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := normSentence sentence
  let (s, unblockable) :=
    match before? s " and can't be blocked this turn" with
    | some rest => (rest, true)
    | none => (s, false)
  (before? s " until end of turn").bind fun body =>
    (split2? body " gains " <|> split2? body " gain ").bind fun (who, gained) =>
      match parseSubject cardName who n, parseKeywordPhrase gained with
      | some (sel, n'), some (k :: ks) =>
        let first := ContinuousEffect.gainAbility sel (.keyword k)
        let later := keywordGains sel.referenceTargets ks
        let block :=
          if unblockable then [ContinuousEffect.forbid (.block .any sel.referenceTargets)]
          else []
        some (.continuous (first :: later ++ block) .endOfTurn, n')
      | _, _ => none

/-- `Put <count> +1/+1 counter(s) on <who>`: a target, `each of up to two target
creatures`, `each other creature you control`, or this card. -/
def parsePutCountersOn (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    let who := norm who
    let onEach :=
      (after? who "each ").bind fun each =>
        if (after? each "of ").isSome then none
        else (parseObjectDesc each false).map fun sel => (.putCounter sel .plusOnePlusOne (.nat k), n)
    let onTarget :=
      (parseTargetDesc ((after? who "each of ").getD who) n).map fun sel =>
        (.putCounter sel .plusOnePlusOne (.nat k), n + 1)
    let onSelf :=
      if refersToSelf cardName who || who == "it" then
        some (.putCounter (.source .this) .plusOnePlusOne (.nat k), n)
      else none
    onSelf <|> onEach <|> onTarget

/-- `create <count> [tapped] <P>/<T> <color> <subtypes> creature token(s)
[with <keywords>]`. One token uses the singular noun; more than one uses the
plural. `X` is the value of X (CR 107.3) and uses the plural. A tapped token
enters tapped (CR 110.5). The token is a creature of that power, toughness,
color, and subtypes, with those keywords. The color may be `colorless`, and
the type `artifact creature`. -/
def parseCreateCreatureTokens (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "create ").bind fun rest =>
    let (rest, kws?) :=
      match split2? rest " with " with
      | some (head, kwText) => (head, parseKeywordPhrase kwText)
      | none => (rest, some [])
    let words := rest.splitOn " " |>.map copied |>.filter (· != "")
    match words with
    | countText :: more =>
      let (tapped, more) :=
        match more with
        | "tapped" :: after => (true, after)
        | _ => (false, more)
      match more with
      | pt :: colorText :: typeWords =>
        match typeWords.reverse with
        | tokenWord :: "creature" :: subtypeWordsRev =>
          let plural := tokenWord == "tokens"
          let count? : Option Value :=
            if countText == "x" then (if plural then some .x else none)
            else (nounCount? countText plural).map Value.nat
          let (types, subtypeWordsRev) : List CardType × List String :=
            match subtypeWordsRev with
            | "artifact" :: more => ([.artifact, .creature], more)
            | _ => ([.creature], subtypeWordsRev)
          let colors? : Option (List Color) :=
            if colorText == "colorless" then some [] else (colorName? colorText).map ([·])
          if tokenWord != "token" && !plural then none
          else
            match count?, parseUnsignedPT pt, colors?,
                subtypeWordsRev.reverse.mapM subtypeOfOracle?, kws? with
            | some k, some (p, t), some cs, some (st :: sts), some kws =>
              some (.createTokens (.controller .this) k
                (types.map CardPart.type ++ (st :: sts).map CardPart.subtype ++
                  [.colorIndicator cs, .power p, .toughness t] ++
                  kws.map fun kw => .ability (.keyword kw))
                (if tapped then [.tapped] else []))
            | _, _, _, _, _ => none
        | _ => none
      | _ => none
    | [] => none

/-- `Create a Treasure token`, `create two Treasure tokens`, `create X
Treasure tokens`, `create a Food token`, or `create a Food token or a
Treasure token`. Food and Treasure are predefined tokens (CR 111.10). `X`
takes the plural noun and is the X of the cost (CR 107.3). With `or`, the
player chooses one to create. -/
def parseCreatePredefinedTokens (sentence : String) : Option CardAction :=
  let one (s : String) : Option CardAction :=
    (after? (norm s) "create ").bind fun rest =>
      let (countText, noun) :=
        match rest.splitOn " " with
        | c :: more => (copied c, copied (String.intercalate " " more))
        | [] => ("", rest)
      let named :=
        (before? noun " tokens").map (true, ·) <|> (before? noun " token").map (false, ·)
      named.bind fun (plural, kind) =>
        let count? : Option Value :=
          if countText == "x" then (if plural then some .x else none)
          else (nounCount? countText plural).map Value.nat
        count?.bind fun k =>
          let parts? : Option (List CardPart) :=
            match kind with
            | "treasure" => some PredefinedToken.treasureToken
            | "food" => some PredefinedToken.foodToken
            | _ => none
          parts?.map fun parts => .createTokens (.controller .this) k parts
  let s := normSentence sentence
  match split2? s " or a " with
  | some (first, second) =>
    match one first, one ("create a " ++ second) with
    | some a, some b => some (.playerSelectAction (.controller .this) (.range 1 1) [a, b])
    | _, _ => none
  | none => one s

/-- `<this card> deals N damage to <recipient>`: any target, target opponent,
each opponent, or each creature blocking it. The source is this object.
`N` is a positive printed number. -/
def parseDealsDamageTo (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !damageSource? cardName who then none
    else
      (split2? rest " damage to ").bind fun (amt, dest) =>
        (positiveDigits? amt).bind fun amount =>
          let recipient : Option (Selector × Nat) :=
            match dest with
            | "each opponent" => some (.opponent (.controller .this), n)
            | "target opponent" => some (.target n (.opponent (.controller .this)), n + 1)
            | "each creature blocking it" => some (.blocking .this, n)
            | _ => (parseTargetDesc dest n).map (·, n + 1)
          recipient.map fun (sel, n') => (.dealDamage .this sel (.nat amount), n')

/-- `This Saga deals X damage to target opponent, where X is the greatest mana
value among artifacts you control.` The opponent is target `n`. -/
def parseDealsGreatestManaValueDamage (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals x damage to target opponent, where x is the greatest mana value among ").bind
    fun (who, among) =>
      if !damageSource? cardName who then none
      else
        (parseObjectDesc among false).map fun sel =>
          (.dealDamage .this (.target n (.opponent (.controller .this)))
            (.greatestManaValue sel), n + 1)

/-- `It deals damage equal to its power to target creature an opponent controls.`
The source is this object. The recipient is target `n`. -/
def parseSelfDealsDamageEqualToPower (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals damage equal to its power to ").bind
    fun (who, dest) =>
      if !damageSource? cardName who then none
      else
        (parseTargetDesc dest n).map fun sel => (.dealDamageEqualToPower .this sel, n + 1)

/-- `<this card> deals 3 damage divided as you choose among one, two, or three
targets.` Its controller divides the damage (CR 601.2d). The counts are a
positive contiguous range of any targets, numbered `n`. -/
def parseDealsDividedDamage (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " targets").bind fun body =>
    (split2? body " deals ").bind fun (who, rest) =>
      if !damageSource? cardName who then none
      else
        (split2? rest " damage divided as you choose among ").bind fun (amt, counts) =>
          match positiveCount amt, parseContiguousCounts counts with
          | some amount, some (lo, hi) =>
            some (
              .divideDamage (.controller .this) .this
                (.targets n (.range (Value.nat lo) (Value.nat hi)) .all)
                (Value.nat amount),
              n + 1)
          | _, _ => none

/-- `Tap <target>` or `Untap <target>`. `Untap that creature` is the previous
target. -/
def parseTapOrUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let tap := (after? s "tap ").bind fun who => (parseTargetDesc who n).map fun sel => (.tap sel, n + 1)
  let untap :=
    (after? s "untap ").bind fun who =>
      if who == "that creature" then
        if n <= 1 then none else some (.untap (.targetReference (n - 1)), n)
      else (parseTargetDesc who n).map fun sel => (.untap sel, n + 1)
  tap <|> untap

/-- `Destroy <target>`. -/
def parseDestroyTarget (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "destroy ").bind fun who =>
    (parseTargetDesc who n).map fun sel => (.destroy sel, n + 1)

/-- `Return target creature card with mana value 3 or less from your graveyard to the battlefield.`
The card is in your graveyard, and its mana value is at most `N` (CR 202.3).
`N` is a positive printed number. The target is numbered `n`. -/
def parseReturnMvAtMostToBattlefield (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence)
      "return target " " from your graveyard to the battlefield").bind fun obj =>
    (split2? obj " with mana value ").bind fun (card, bound) =>
      (before? bound " or less").bind positiveCount |>.bind fun k =>
        (parseGraveyardCard card).map fun sel =>
          (.putOntoBattlefield
            (.target n (extendIntersection [] sel [.manaValueAtMost (.nat k)])),
           n + 1)

/-- `Return <target card> from your graveyard to your hand`, or
`Return <target> to its owner's hand`. A spell is on the stack. -/
def parseReturnToHand (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let fromGraveyard :=
    (between? s "return target " " from your graveyard to your hand").bind parseGraveyardCard |>.map
      fun sel => (.returnToHand (.target n sel), n + 1)
  let toOwner :=
    (between? s "return " " to its owner's hand").bind fun who =>
      if who == "target spell" then some (.returnToHand (.target n .spell), n + 1)
      else (parseTargetDesc who n).map fun sel => (.returnToHand sel, n + 1)
  fromGraveyard <|> toOwner

/-- `Surveil N`. Does not choose a target. -/
def parseSurveil (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "surveil ").bind positiveCount |>.map fun k =>
    (.surveil (.controller .this) (Value.nat k), n)

/-- `<who> connive(s)`: this object with `it`, `he`, `she`, or its name, or
`up to one target creature you control`. Connive is a keyword action of that
object (CR 701.50). -/
def parseConnive (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  (before? s " connives" <|> before? s " connive").bind fun who =>
    match selfSubject? cardName who with
    | some sel => some (.keyword sel (.connive (.nat 1)), n)
    | none => (parseTargetDesc who n).map fun sel => (.keyword sel (.connive (.nat 1)), n + 1)

/-- `Discard a card.` / `Discard two cards.` The player is this spell's
controller. One card is singular. More than one is plural. -/
def parseDiscardCards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "discard ").bind parseCardCount |>.map fun k =>
    (.discard (.controller .this) (Value.nat k), n)

/-- `Draw <count>`, or `You draw <count> and lose N life`. -/
def parseDrawAndLoseLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let lose :=
    (after? s "you draw ").bind (split2? · " and lose ") |>.bind fun (drawText, lifeText) =>
      match parseCardCount drawText, lifeAmount? ("lose " ++ lifeText) "lose " with
      | some k, some life =>
        some (.sequence [
          .draw (.controller .this) (Value.nat k),
          .loseLife (.controller .this) (Value.nat life)], n)
      | _, _ => none
  lose <|> unchanged (parseDrawCards s) n

/-- `Each opponent loses N life`, `you lose N life`, or
`target opponent loses N life`. The target is numbered `n`. -/
def parseLoseLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  ((parseEachOpponentLosesLife s).map fun k =>
      (.loseLife (.opponent (.controller .this)) (Value.nat k), n)) <|>
    ((lifeAmount? s "you lose ").map fun k =>
      (.loseLife (.controller .this) (Value.nat k), n)) <|>
    ((lifeAmount? s "target opponent loses ").map fun k =>
      (.loseLife (.target n (.opponent (.controller .this))) (Value.nat k), n + 1))

/-- `Target player mills <count>`. The player is target `n`. -/
def parseTargetPlayerMills (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "target player mills ").bind parseCardCount |>.map fun k =>
    (.mill (.target n .player) (Value.nat k), n + 1)

/-- `Each player sacrifices a creature of their choice.` Each player, bound to
variable `n`, chooses one creature they control to sacrifice (CR 701.17a). -/
def parseEachPlayerSacrifices (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "each player sacrifices " " of their choice").bind
    dropArticle? |>.bind typesInPhrase |>.map fun ts =>
      (.forEachVariable n .player [
        .sacrifice
          (.selected (.variable n) (.range 1 1)
            (permanentWith ts [.controlled (.variable n)]))],
       n + 1)

/-- `Search your library for a basic land card, put that card onto the
battlefield tapped, then shuffle`, or `Search your library for a <subtype>
card, reveal it, put it into your hand, then shuffle`. The found card is
variable `n` when it is revealed. -/
def parseSearchLibrary (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let tapped :=
    if s == "search your library for a basic land card, put that card onto the battlefield tapped, then shuffle" then
      parseSearchBasicLandTapped
        "search your library for a basic land card, put it onto the battlefield tapped, then shuffle" n
    else none
  let reveal :=
    (between? s "search your library for " " card, reveal it, put it into your hand, then shuffle").bind
      dropArticle? |>.bind fun kind =>
        if kind == "basic land" then some (searchRevealToHand n basicLandInLibrary)
        else
          (subtypeOfOracle? kind).map fun st =>
            searchRevealToHand n (.intersection [.zone .library, .subtype st])
  tapped <|> reveal

/-- `<who> fights up to one other target creature`. This object fights that
creature (CR 701.12). -/
def parseSelfFights (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " fights ").bind fun (who, dest) =>
    if !damageSource? cardName who then none
    else
      let dest := (dest.replace "one other target" "one target another")
      (after? dest "up to one target ").bind parseTargetObject |>.map fun sel =>
        (.fight .this (.targets n (.range 0 1) sel), n + 1)

/-- `Exile <targets>, then return them to the battlefield tapped under their
owner's control.` Also `return that card … under its owner's control`. The
exile is action `n`. The exiled cards return tapped under their owner's
control. -/
def parseExileThenReturnTapped (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  let parsed :=
    (before? s ", then return them to the battlefield tapped under their owner's control") <|>
      (before? s ", then return that card to the battlefield tapped under its owner's control")
  parsed.bind (after? · "exile ") |>.bind fun who =>
    (parseTargetDesc who n).map fun sel =>
      (.sequence [
        .actionId n (.exile sel),
        .putOntoBattlefieldInState
          (.wasCreatedByAction n)
          [.tapped, .controlled (.owner (.wasCreatedByAction n))]],
       n + 1)

/-- `Exile <targets>, then return that card to the battlefield under its owner's control.`
The exile is action `n`. The card returns untapped under its owner's control. -/
def parseExileThenReturn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  let s := normSentence sentence
  (before? s ", then return that card to the battlefield under its owner's control").bind
    (after? · "exile ") |>.bind fun who =>
      (parseTargetDesc who n).map fun sel =>
        (.sequence [
          .actionId n (.exile sel),
          .putOntoBattlefieldInState
            (.wasCreatedByAction n)
            [.controlled (.owner (.wasCreatedByAction n))]],
         n + 1)

/-- `Creatures without flying can't block this turn.` Only creatures block,
so the blockers are objects without that keyword. -/
def parseWithoutKeywordCantBlock (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "creatures without " " can't block this turn").bind
    keywordOfOracle? |>.map fun k =>
      (.continuous [.forbid (.block (.not (.keyword k)) .all)] .endOfTurn, n)

/-- `Then discard two cards unless you discard an artifact card.` Discarding
an artifact card is the cost that prevents discarding that many cards. -/
def parseDiscardUnlessArtifact (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "discard " " unless you discard an artifact card").bind
    parseCardCount |>.map fun k =>
      (.preventable (.controller .this) [.discard (.cardType .artifact)]
        (.discard (.controller .this) (Value.nat k)), n)

/-- `Artifact spells you cast this turn cost {1} less to cast.` That many
generic mana less until end of turn. -/
def parseSpellsCostLessThisTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " spells you cast this turn cost ").bind fun (kind, rest) =>
    match typeOfOracle? kind, (before? rest " less to cast").bind positiveGeneric? with
    | some t, some k =>
      some (.continuous
        [.reduceCost (.intersection [.spell, .cardType t, youControl]) [.mana [.generic k]]]
        .endOfTurn, n)
    | _, _ => none

/-- `If you control another Hero, you gain 2 life.` or `If you control another
Hero, Human Torch deals 1 damage to target opponent.` `another` excludes this
object. The condition is checked on resolution. -/
def parseIfControlAnotherGainLife (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "if you control another ").bind (split2? · ", ") |>.bind
    fun (stText, effect) =>
      match subtypeOfOracle? stText,
          parseYouGainLife effect n <|> parseDealsDamageTo cardName effect n with
      | some st, some (action, n') => some (.if (.any (anotherSubtypeYouControl st)) [action], n')
      | _, _ => none

/-- `Each opponent discards a card.` Each opponent chooses the card. -/
def parseEachOpponentDiscards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "each opponent discards ").bind parseCardCount |>.map fun k =>
    (.discard (.opponent (.controller .this)) (Value.nat k), n)

/-- `Draw a card if her power is 4 or greater.` The power is this object's,
checked on resolution. -/
def parseDrawIfPowerAtLeast (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " if ").bind fun (draw, cond) =>
    (after? draw "draw ").bind parseCardCount |>.bind fun k =>
      (between? cond "" " or greater").bind (split2? · " power is ") |>.bind fun (who, p) =>
        let who := (before? who "'s").getD
          (match who with
            | "his" | "her" | "its" => "it"
            | _ => "")
        if !damageSource? cardName who then none
        else
          (positiveDigits? p).map fun p =>
            (.if (.any (.intersection [.source .this, .powerAtLeast (Value.int p)]))
              [.draw (.controller .this) (Value.nat k)], n)

/-- `You gain N life for each <objects>.` Each of those objects is variable `n`. -/
def parseGainLifeForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " life for each ").bind fun (gain, each) =>
    match (after? gain "you gain ").bind positiveCount, parseObjectDesc each false with
    | some k, some sel =>
      some (.forEachVariable n sel [.gainLife (.controller .this) (Value.nat k)], n + 1)
    | _, _ => none

/-- `Target player gains 2 life, then searches their library for a basic land
card, puts it onto the battlefield tapped, then shuffles.` The player is target
`n`, and that player searches. -/
def parseTargetGainsThenSearchesBasic (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence) "target player gains "
      " life, then searches their library for a basic land card, puts it onto the battlefield tapped, then shuffles").bind
    positiveCount |>.map fun k =>
      (.sequence [
        .gainLife (.target n .player) (Value.nat k),
        .searchLibraryThenShuffle (.targetReference n) [
          .putOntoBattlefieldInState
            (.selected (.targetReference n) (.range 1 1) basicLandInLibrary)
            [.tapped]]],
       n + 1)

/-- `The owner of target creature an opponent controls puts it into their
library second from the top or on the bottom.` That owner chooses where.
The creature is target `n`. -/
def parseOwnerPutsSecondOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "the owner of "
      " puts it into their library second from the top or on the bottom").bind
    fun who =>
      (parseTargetDesc who n).map fun sel =>
        (.playerSelectAction (.owner (.targetReference n)) (.range 1 1) [
          .putIntoLibraryFromTop sel 2,
          .putOnBottomOfLibrary (.targetReference n)],
         n + 1)

/-- `attach it to <target>`, or `attach <target> to <target>`. `it` or this
card is the attachment. -/
def parseCatalogAttach (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "attach ").bind (fun s =>
      match (s.splitOn " to ").reverse with
      | dest :: whatRev@(_ :: _) =>
        some (copied (String.intercalate " to " whatRev.reverse), copied dest)
      | _ => none) |>.bind fun (what, dest) =>
    if what == "it" || refersToSelf cardName what then
      (parseTargetDesc dest n).map fun sel => (.attach .this sel, n + 1)
    else
      (parseTargetDesc what n).bind fun attached =>
        (parseTargetDesc dest (n + 1)).map fun host => (.attach attached host, n + 2)

/-- `<target> can't be blocked this turn except by creatures with <keyword>.`
Only creatures with that keyword may block it until end of turn. -/
def parseCantBeBlockedExceptBy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " can't be blocked this turn except by creatures with ").bind
    fun (who, kw) =>
      match parseTargetDesc who n, keywordOfOracle? kw with
      | some sel, some k =>
        some (.continuous [.forbid (.block (.not (.keyword k)) sel)] .endOfTurn, n + 1)
      | _, _ => none

/-- `Until end of turn, <subject> gains "<ability>".` The quoted text is a
triggered ability of that object (CR 113.10); `this creature` in it is that
object. -/
def parseGainsQuotedUntilEnd (cardName sentence : String) (n : Nat)
    (quoted : String → Option Ability) : Option (CardAction × Nat) :=
  let s := copied sentence
  let s := (before? s ".").getD s
  (after? (norm s) "until end of turn, ").bind fun _ =>
    (split2? ((s.drop "until end of turn, ".length).copy) " gains \"").bind fun (who, rest) =>
      (before? rest "\"").bind fun text =>
        match parseSubject cardName who n, quoted text with
        | some (sel, n'), some ability => some (.continuous [.gainAbility sel ability] .endOfTurn, n')
        | _, _ => none

/-- Mixed card types and subtypes joined by `or`: `Hero or enchantment`. -/
def typeOrSubtypeList? (s : String) : Option Selector :=
  let parts := orList s
  if parts.isEmpty then none
  else
    (parts.mapM fun w =>
        (if w == "permanent" then some (Selector.zone .battlefield) else none) <|>
        ((typeOfOracle? w).map Selector.cardType) <|> ((subtypeOfOracle? w).map Selector.subtype)) |>.map
      fun
        | [one] => one
        | many => .union many

/-- `Two target players each draw a card.` The players are targets `n`. -/
def parseTwoTargetPlayersEachDraw (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "two target players each draw ").bind parseCardCount |>.map
    fun k => (.draw (.targets n (.range 2 2) .player) (Value.nat k), n + 1)

/-- `create a 3/1 colorless Wall artifact creature token with defender named
Stone Boulder`. The token has that name as printed (CR 111.4). -/
def parseCreateNamedCreatureTokens (sentence : String) : Option CardAction :=
  (split2? (stripTrailingPeriod sentence) " named ").bind fun (head, tokenName) =>
    (parseCreateCreatureTokens head).bind fun
      | .createTokens who k parts states => some (.createTokens who k (.name tokenName :: parts) states)
      | _ => none

/-- A single token to create: `a Treasure token` or `a 1/1 green Elf creature
token`. -/
def createOneToken? (s : String) : Option CardAction :=
  match parseCreatePredefinedTokens s <|> parseCreateCreatureTokens s with
  | some a@(.createTokens _ (.nat 1) _ _) => some a
  | _ => none

/-- `create a Treasure token for each Villain you control`. One token for each
matching object; the object is variable `n`. -/
def parseCreateTokensForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " for each ").bind fun (create, each) =>
    match createOneToken? create, parseObjectDesc each false with
    | some token, some sel => some (.forEachVariable n sel [token], n + 1)
    | _, _ => none

/-- `Look at the top twenty cards of your library, put any number of land cards
from among them onto the battlefield tapped, then shuffle.` The look is action
`n`. The lands are put onto the battlefield from the library before it is
shuffled. -/
def parseLookTopPutLandsShuffle (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "look at the top "
      " cards of your library, put any number of land cards from among them onto the battlefield tapped, then shuffle").bind
    (fun c => (twentyOrSmall? c)) |>.map fun k =>
      (.sequence [
        .actionId n (.lookAt (.topOfLibrary (.controller .this) (Value.nat k))),
        .searchLibraryThenShuffle (.controller .this) [
          .putOntoBattlefieldInState
            (.selected (.controller .this) .any
              (.intersection [.wasObjectOfAction n, .cardType .land]))
            [.tapped]]], n + 1)
where
  twentyOrSmall? (s : String) : Option Nat :=
    if s == "twenty" then some 20 else positiveCount s

/-- `add {R} for each artifact your opponents control`. The mana is added once
for each matching object; the object is variable `n`. -/
def parseAddManaForEach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " for each ").bind fun (add, each) =>
    match (after? add "add ").bind nonemptyMana?, parseObjectDesc each false with
    | some syms, some sel =>
      some (.forEachVariable n sel [.addMana (.controller .this) syms], n + 1)
    | _, _ => none

/-- `add two mana in any combination of {U}, {B}, and/or {R}` (CR 106.4). -/
def parseAddManaInAnyCombination (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " mana in any combination of ").bind fun (add, colors) =>
    match (after? add "add ").bind positiveCount,
        ((colors.replace ", and/or " " ").replace ", " " ").splitOn " " |>.mapM addableSymbol? with
    | some k, some syms@(_ :: _ :: _) =>
      some (.addManaInAnyCombination (.controller .this) syms (Value.nat k), n)
    | _, _ => none

/-- `add {B} or {R}`: the player chooses one listed symbol. -/
def parseAddOneOfSentence (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (parseAddOneOf sentence).map fun actions =>
    (.playerSelectAction (.controller .this) (.range 1 1) actions, n)

/-- `<target> can't be blocked this turn`. The target is `n`. -/
def parseTargetCantBeBlockedThisTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " can't be blocked this turn").bind fun who =>
    (parseTargetDesc who n).map fun sel =>
      (.continuous [.forbid (.block .any sel)] .endOfTurn, n + 1)

/-- `<this> deals damage equal to the number of Dwarves you control to each
opponent`. The source is this object. -/
def parseDealsDamageEqualCountToEachOpponent (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals damage equal to the number of ").bind
    fun (who, rest) =>
      if !damageSource? cardName who then none
      else
        (before? rest " to each opponent").bind (parseObjectDesc · false) |>.map fun among =>
          (.dealDamage .this (.opponent (.controller .this)) (.count among), n)

/-- `put a card from your hand on the bottom of your library`. -/
def parsePutHandCardOnBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "put a card from your hand on the bottom of your library" then
    some (.putOnBottomOfLibrary
      (.selected (.controller .this) (.range 1 1)
        (.intersection [.zone .hand, .owner (.controller .this)])), n)
  else none

/-- `draw cards equal to the greatest toughness among creatures you control`. -/
def parseDrawEqualGreatestToughness (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "draw cards equal to the greatest toughness among ").bind
    (parseObjectDesc · false) |>.map fun among =>
      (.draw (.controller .this) (.greatestToughness among), n)

/-- `put any number of creature cards from your hand onto the battlefield`. -/
def parsePutAnyFromHandOntoBattlefield (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence) "put any number of "
      " cards from your hand onto the battlefield").bind typesInPhrase |>.map fun ts =>
    (.putOntoBattlefield
      (.selected (.controller .this) .any
        (.intersection [.zone .hand, .owner (.controller .this), selectorOfTypes ts])), n)

/-- `it gets +X/+0 until end of turn, where X is the greatest power among
creatures you control`. -/
def parseGetsGreatestPowerUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " gets +x/+0 until end of turn, where x is the greatest power among ").bind
    fun (who, among) =>
      let subject := if who == "it" && n <= 1 then some (.source .this, n) else parseSubject cardName who n
      match subject, parseObjectDesc among false with
      | some (sel, n'), some amongSel =>
        some (.continuous [.addPower sel (.greatestPower amongSel)] .endOfTurn, n')
      | _, _ => none

/-- `each other Hero you control gets +X/+X until end of turn, where X is
<this>'s toughness`, or `another target creature you control gets +X/+0 …,
where X is <this>'s power`. X is this object's current value (CR 608.2h). -/
def parseGetsSelfStatUntilEnd (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let s := normSentence sentence
  let split? (bonus : String) := (split2? s (" gets " ++ bonus ++ " until end of turn, where x is ")).map
    (bonus, ·)
  (split? "+x/+x" <|> split? "+x/+0").bind fun (bonus, who, stat) =>
    let v? : Option Value :=
      match before? stat "'s toughness", before? stat "'s power" with
      | some self, _ => if refersToSelf cardName self then some (.greatestToughness (.source .this)) else none
      | _, some self => if refersToSelf cardName self then some (.greatestPower (.source .this)) else none
      | _, _ => none
    let subject? : Option (Selector × Nat) :=
      match after? who "each " with
      | some rest => (parseObjectDesc rest false).map (·, n)
      | none => (parseTargetDesc who n).map (·, n + 1)
    match v?, subject? with
    | some v, some (sel, n') =>
      let again : Selector :=
        match sel with
        | .target k _ => .targetReference k
        | other => other
      let effects : List ContinuousEffect :=
        if bonus == "+x/+x" then [.addPower sel v, .addToughness again v] else [.addPower sel v]
      some (.continuous effects .endOfTurn, n')
    | _, _ => none

/-- `choose up to two creatures, then destroy the rest`. The chosen creatures
are variable `n` (not targeted, CR 608.2d). -/
def parseChooseUpToDestroyRest (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? (normSentence sentence) "choose up to " ", then destroy the rest").bind
    fun rest =>
      (split2? rest " ").bind fun (countText, noun) =>
        match positiveCount countText, typesInPhrase noun with
        | some k, some ts =>
          let kind := Selector.intersection [.zone .battlefield, selectorOfTypes ts]
          some (.sequence [
            .defineSelectorVariable n (.selected (.controller .this) (.range 0 (Value.nat k)) kind),
            .destroy (.intersection [.zone .battlefield, selectorOfTypes ts, .not (.variable n)])], n + 1)
        | _, _ => none

/-- `Double target creature's power and toughness until end of turn.` It gets
+X/+Y where X is its power and Y is its toughness (CR 701.10b). The creature
is target `n`. -/
def parseDoubleTargetPowerToughness (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (between? s "double " "'s power and toughness until end of turn").bind parseTargetPhrase |>.map
    fun sel =>
      (.continuous [
        .addPower (.target n sel) (.greatestPower (.targetReference n)),
        .addToughness (.targetReference n) (.greatestToughness (.targetReference n))] .endOfTurn,
       n + 1)

/-- `Target creature you control fights target creature an opponent controls.`
The first creature is target `n`; the second is target `n + 1` (CR 701.12). -/
def parseTargetFightsTarget (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? s " fights ").bind fun (a, b) =>
    match parseTargetPhrase a, parseOppControlledTarget b with
    | some src, some dest => some (.fight (.target n src) (.target (n + 1) dest), n + 2)
    | _, _ => none

/-- `Target creature you control deals damage equal to twice its power to
target creature an opponent controls.` The source is target `n`. -/
def parseDealsTwicePower (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (split2? s " deals damage equal to twice its power to ").bind fun (a, b) =>
    match parseTargetPhrase a, parseOppControlledTarget b with
    | some src, some dest =>
      some (.dealDamage (.target n src) (.target (n + 1) dest)
        (.product (.totalPower (.targetReference n)) (.int 2)), n + 2)
    | _, _ => none

/-- `you may put a land card from your hand onto the battlefield tapped`. -/
def parseMayPutFromHand (s : String) (n : Nat) : Option (CardAction × Nat) :=
  let (s, tapped) :=
    match before? s " tapped" with
    | some rest => (rest, true)
    | none => (s, false)
  (between? s "you may put " " card from your hand onto the battlefield").bind dropArticle? |>.bind
    typeOfOracle? |>.map fun t =>
      let card := Selector.selected (.controller .this) (.range 1 1)
        (.intersection [.zone .hand, .owner (.controller .this), .cardType t])
      (.optional (.controller .this)
        (if tapped then .putOntoBattlefieldInState card [.tapped] else .putOntoBattlefield card), n)

/-- `<this> deals damage equal to his power to any other target.` The target
is any target but this object (CR 115.4). -/
def parseSelfDealsPowerToAnyOther (cardName s : String) (n : Nat) : Option (CardAction × Nat) :=
  let ends := [" deals damage equal to his power to any other target",
    " deals damage equal to her power to any other target",
    " deals damage equal to its power to any other target"]
  (ends.findSome? (before? s ·)).bind fun who =>
    if refersToSelf cardName who then
      some (.dealDamageEqualToPower (.source .this) (.target n (.not .this)), n + 1)
    else none

/-- `<this> gains "<ability>" until end of turn.` The quoted text is an
activated ability of this object. -/
def parseGainsQuotedActivatedUntilEnd (cardName sentence : String) (n : Nat)
    (activated : String → Option Ability) : Option (CardAction × Nat) :=
  let s := copied sentence
  (before? s "\" until end of turn").bind (split2? · " gains \"") |>.bind fun (who, text) =>
    if !refersToSelf cardName who then none
    else (activated text).map fun a =>
      (.continuous [.gainAbility (.source .this) a] .endOfTurn, n)

/-- `Draw a card for each card you've discarded this turn.` -/
def parseDrawForEachDiscardedThisTurn (s : String) (n : Nat) : Option (CardAction × Nat) :=
  if s == "draw a card for each card you've discarded this turn" then
    some (.draw (.controller .this)
      (.count (.wasObjectSince (.discard (.controller .this)) .turnStart)), n)
  else none

/-- `Create X 1/1 green Squirrel creature tokens, where X is the number of
Squirrels you control.` -/
def parseCreateXTokensCount (s : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? s "create x ").bind (split2? · ", where x is the number of ") |>.bind
    fun (tokenText, among) =>
      match parseCreateCreatureTokens ("create two " ++ tokenText), parseObjectDesc among false with
      | some (.createTokens who (.nat 2) parts kws), some sel =>
        some (.createTokens who (.count sel) parts kws, n)
      | _, _ => none

/-- `behold an Elf`: behold that subtype (CR 701.4). The article is `a` or `an`. -/
def beholdKeyword? (s : String) : Option Keyword :=
  (after? (norm s) "behold ").bind dropArticle? |>.bind subtypeOfOracle? |>.map
    Keyword.behold

/-- `you may draw <count>`, `you may mill <count>`, `you may create <creature tokens>`,
or `you may behold a <subtype>`. The rest of the sentence is that action. -/
def parseYouMay (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "you may ").bind fun rest =>
    let counted (lead tail : String) (plural : Bool) : Option Nat :=
      (after? rest lead).bind fun afterLead =>
        (before? afterLead tail).bind fun countText =>
          if countText ++ tail == afterLead then nounCount? countText plural else none
    let draw :=
      (counted "draw " " card" false <|> counted "draw " " cards" true).map fun k =>
        .optional (.controller .this) (.draw (.controller .this) (Value.nat k))
    let mill :=
      (counted "mill " " card" false <|> counted "mill " " cards" true).map fun k =>
        .optional (.controller .this) (.mill (.controller .this) (Value.nat k))
    let create :=
      (parseCreateCreatureTokens rest).map fun action =>
        .optional (.controller .this) action
    let behold :=
      (beholdKeyword? rest).map fun k =>
        .optional (.controller .this) (.keyword (.controller .this) k)
    (draw <|> mill <|> create <|> behold).map (·, n)

/-- `Target player draws <count>.` The player is target `n`.
The sentence is that draw and nothing more. -/
def parseTargetPlayerDraws (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "target player draws ").bind fun rest =>
    let counted (tail : String) (plural : Bool) : Option Nat :=
      (before? rest tail).bind fun countText =>
        if countText ++ tail == rest then nounCount? countText plural else none
    (counted " card" false <|> counted " cards" true).map fun k =>
      (.draw (.target n .player) (Value.nat k), n + 1)

/-- `tap enchanted creature and remove all counters from it`. The creature is
this Aura's host. -/
def parseTapEnchantedRemoveCounters (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  if sentenceIs sentence "tap enchanted creature and remove all counters from it" then
    some (.sequence [
      .tap (.hostOf .this),
      .removeAllCounters (.hostOf .this)], n)
  else none

/-- Creating, drawing, and pumping sentences of a catalog effect. -/
private def parseCatalogSentenceCreate (cardName sentence s : String) (n : Nat) :
    Option (CardAction × Nat) :=
  parseTapEnchantedRemoveCounters sentence n <|>
    (parseCreateNamedCreatureTokens sentence).map (·, n) <|>
    parseYouMay sentence n <|>
    parseTargetPlayerDraws sentence n <|>
    parseDoubleTargetPowerToughness s n <|>
    parseGetsSelfStatUntilEnd cardName sentence n <|>
    parseDrawForEachDiscardedThisTurn s n <|>
    parseMayPutFromHand s n <|>
    parseSelfDealsPowerToAnyOther cardName s n <|>
    parseCreateXTokensCount s n <|>
    parseTargetFightsTarget s n <|>
    parseDealsTwicePower s n <|>
    parseTwoTargetPlayersEachDraw s n <|>
    parseCreateTokensForEach s n <|>
    parseLookTopPutLandsShuffle s n <|>
    parseAddManaForEach s n <|>
    parseAddManaInAnyCombination s n <|>
    parseTargetCantBeBlockedThisTurn s n <|>
    parseDealsDamageEqualCountToEachOpponent cardName s n <|>
    parsePutHandCardOnBottom s n <|>
    parseDrawEqualGreatestToughness s n <|>
    parsePutAnyFromHandOntoBattlefield s n <|>
    parseGetsGreatestPowerUntilEnd cardName s n <|>
    parseChooseUpToDestroyRest s n <|>
    parseDrawAndLoseLife s n <|>
    parseDiscardCards s n <|>
    parseCatalogAttach cardName s n <|>
    parseCantBeBlockedExceptBy s n <|>
    parseAddOneManaOfAnyColor s n <|>
    unchanged (parseReturnThisFromGraveyard s) n <|>
    parseTapOrUntap s n <|>
    parseSurveil s n <|>
    parseConnive cardName s n

/-- Damage, destroy, and mana sentences of a catalog effect. -/
private def parseCatalogSentenceResolve (cardName s : String) (n : Nat) :
    Option (CardAction × Nat) :=
  unchanged (parseCreateCreatureTokens s) n <|>
    unchanged (parseCreatePredefinedTokens s) n <|>
    parsePutCountersOn cardName s n <|>
    parseGetsGainsUntilEnd cardName s n <|>
    parseGainUntilEnd cardName s n <|>
    unchanged (parsePumpUntilEndOfTurn s) n <|>
    parseDealsDamageTo cardName s n <|>
    parseDealsGreatestManaValueDamage cardName s n <|>
    parseSelfDealsDamageEqualToPower cardName s n <|>
    parseDealsDividedDamage cardName s n <|>
    parseDestroyTarget s n <|>
    parseReturnMvAtMostToBattlefield s n <|>
    parseReturnToHand s n <|>
    parseTargetPlayerMills s n <|>
    parseLoseLife s n <|>
    parseEachPlayerSacrifices s n <|>
    parseSearchLibrary s n <|>
    parseSelfFights cardName s n <|>
    parseExileThenReturnTapped s n <|>
    parseExileThenReturn s n <|>
    parseWithoutKeywordCantBlock s n <|>
    parseDiscardUnlessArtifact s n <|>
    parseSpellsCostLessThisTurn s n <|>
    parseIfControlAnotherGainLife cardName s n <|>
    parseEachOpponentDiscards s n <|>
    parseDrawIfPowerAtLeast cardName s n <|>
    parseGainLifeForEach s n <|>
    parseTargetGainsThenSearchesBasic s n <|>
    parseOwnerPutsSecondOrBottom s n <|>
    parseAddMana s n <|>
    parseAddOneOfSentence s n <|>
    (parseAttachSelfToTarget cardName s n).bind fun (action, n') =>
      match action with
      | .attach _ (.target _ _) => some (action, n')
      | _ => none

/-- `for each opponent, exile up to one target nonland permanent that player
controls until <this> leaves the battlefield.`
Each opponent is variable `n`. The exile is action `n + 1`, and that
player's permanent is target `n + 1`, from zero through the printed maximum
(CR 115.1). A continuous replacement effect puts the exiled card onto the
battlefield when this ability's source leaves, and the leave still happens
(CR 614). No shorter duration is printed, so the replacement lasts until
the end of the game (CR 611.2a). -/
def parseForEachOpponentExileUntilLeaves (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "for each opponent, exile up to ").bind
    (split2? · " target ") |>.bind fun (countText, rest) =>
      (split2? rest " that player controls until ").bind fun (obj, untilText) =>
        (before? untilText " leaves the battlefield").bind fun who =>
          if !refersToSelf cardName who then none
          else
            match positiveCount countText, parseTargetObject obj with
            | some k, some sel =>
              let controlled :=
                match sel with
                | .intersection parts =>
                  .intersection (parts ++ [.controlled (.variable n)])
                | other => .intersection [other, .controlled (.variable n)]
              some (
                .forEachVariable n (.opponent (.controller .this))
                  [.sequence [
                    .actionId (n + 1)
                      (.exile
                        (.targets (n + 1) (.range 0 (Value.nat k)) controlled)),
                    .continuous
                      [.replace (.leaveBattlefield (.source .this)) [
                        .putOntoBattlefield (.wasCreatedByAction (n + 1)),
                        .keepReplacedAction]]
                      .endOfGame]],
                n + 2)
            | _, _ => none

/-- One sentence of a catalog effect. A leading `Then` is sequencing only.
`You create` is `create`. -/
@[noinline]
def parseCatalogSentenceOnce (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  parseForEachOpponentExileUntilLeaves cardName sentence n <|>
    let s := (after? (normSentence sentence) "then ").getD (normSentence sentence)
    let s := (after? s "you create ").map ("create " ++ ·) |>.getD s
    parseCatalogSentenceCreate cardName sentence s n <|>
      parseCatalogSentenceResolve cardName s n

/-- One sentence, or two clauses joined by `, then` or `and` when the whole
sentence is not one action. Existing sentence templates come first. -/
def parseCatalogSentence (cardName sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  let one (s : String) (n : Nat) :=
    parseSentence cardName s n <|> parseCatalogSentenceOnce cardName s n
  let pair (sep : String) : Option (CardAction × Nat) :=
    (split2? (normSentence sentence) sep).bind fun (a, b) =>
      (one a n).bind fun (first, n1) =>
        (one b n1).map fun (second, n2) => (.sequence [first, second], n2)
  let ifYouDont : Option (CardAction × Nat) :=
    let s := normSentence sentence
    let s := (after? s "then ").getD s
    (after? s "if you don't control ").bind (split2? · ", ") |>.bind fun (obj, effect) =>
      match youControlCondition? obj, one effect n with
      | some cond, some (action, n') => some (.if (.not cond) (flattenAction action), n')
      | _, _ => none
  one sentence n <|> ifYouDont <|> pair ", then " <|> pair " and "

end OracleParts

end Mtg.Engine
