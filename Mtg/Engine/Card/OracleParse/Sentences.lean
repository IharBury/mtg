import Mtg.Engine.Card.OracleParse.Costs

/-!
# One printed sentence

Spell and ability sentences, including a modal “choose one” spell.
The first parser that accepts a sentence wins.
-/

namespace Mtg.Engine

namespace OracleParts

/-- `Tap one or two target creatures.` The target number is `n`. -/
def parseTap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "tap ").bind (split2? · " target ") with
  | some (countText, obj) =>
    match parseCountRange countText, typesInPhrase obj with
    | some r, some ts =>
      some (.tap (.targets n r (permanentWith ts)), n + 1)
    | _, _ => none
  | none => none

/-- `Untap target <permanents> [you control].` The target number is `n`. -/
def parseUntap (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "untap ").bind parseTargetPhrase with
  | some sel => some (.untap (.target n sel), n + 1)
  | none => none

/-- `It gets +P/+T until end of turn.` refers to the last target (`n - 1`). -/
def parseItGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (whoPtUntilEnd? sentence splitGetsOnly?).bind fun (who, p, t) =>
      if who != "it" then none
      else
        (pumpUntilEnd (.targetReference (n - 1)) p t none).map fun action =>
          (action, n)

/-- `If it's a Dwarf, you may attach an Equipment you control to it.`
The previous target (`n - 1`) is the host. -/
def parseIfItsSubtypeMayAttach (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if n <= 1 then none
  else
    (between? (normSentence sentence) "if it's " " you control to it").bind
        (split2? · ", you may attach ") |>.bind fun (hostArt, attachArt) =>
      match dropArticle? hostArt, dropArticle? attachArt with
      | some hostName, some attachName =>
        match subtypeOfOracle? hostName, subtypeOfOracle? attachName with
        | some hostSt, some attachSt =>
          let host := Selector.targetReference (n - 1)
          some (
            .if
              (.anySubtype host hostSt)
              [
                .optional (.controller .this)
                  (.attach
                    (.selected
                      (.controller .this)
                      (.range 1 1)
                      (.intersection [
                        .permanent,
                        .subtype attachSt,
                        youControl]))
                    host)
              ],
            n)
        | _, _ => none
      | _, _ => none

/-- Lands this object's controller controls. -/
def landsYouControl : Selector :=
  permanentWith [.land] [youControl]

/-- `This creature's power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power and toughness are
each a static ability set to the number of lands you control. -/
def powerToughnessEqualLandsAbilities : List Ability := [
  .static (.setPower .this (.count landsYouControl)),
  .static (.setToughness .this (.count landsYouControl))
]

/-- The printed clause after `<this>'s`. -/
def landsCharacteristicSuffix : String :=
  "power and toughness are each equal to the number of lands you control"

def parsePowerToughnessEqualLands (text : String) : Option (List Ability) :=
  if sentenceIs text ("this creature's " ++ landsCharacteristicSuffix) then
    some powerToughnessEqualLandsAbilities
  else none

/-- `a Bear creature in addition to its other types` as that creature subtype. -/
def parseAddedCreatureSubtype (s : String) : Option CardSubtype :=
  (before? (norm s) " creature in addition to its other types").bind dropArticle?
    |>.bind subtypeOfOracle?

/-- `<this> becomes a Bear creature in addition to its other types and gains "…"`.
The subject is this card. No duration is printed, so the effect lasts until
the end of the game (CR 611.2a). The quotation is a static ability this
object gains. -/
def parseBecomeAndGainStatic (cardName : String) (sentence : String) : Option CardAction :=
  (split2? (normSentence sentence) " becomes ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      (split2? rest " and gains \"").bind fun (become, quoted) =>
        (before? quoted "\"").bind fun abilityText =>
          match parseAddedCreatureSubtype become, parsePowerToughnessEqualLands abilityText with
          | some st, some [power, toughness] =>
            some (.continuous
              [.gainType .this .creature,
                .gainSubtype .this st,
                .gainAbility .this power,
                .gainAbility .this toughness]
              .endOfGame)
          | _, _ => none

/-- `Target creature can't be blocked this turn.` The target is `n`.
The restriction lasts until end of turn. -/
def parseTargetCantBeBlocked (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (before? (normSentence sentence) " can't be blocked this turn").bind fun who =>
    (parseBattlefieldTarget who).map fun sel =>
      (.continuous [.forbid (.block .any (.target n sel))] .endOfTurn, n + 1)

/-- `Put two +1/+1 counters on target Elf you control.`
One counter uses the singular noun. A creature type is a creature of those
subtypes. The target is `n`. -/
def parsePutCountersOnTarget (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parseBattlefieldTarget who with
    | some sel =>
      -- A creature type (`Elf`, `Goblin or Orc`), not a card type (`creature`).
      if sel.includedSubtypes.isEmpty then none
      else some (.putCounter (.target n sel) .plusOnePlusOne (.nat k), n + 1)
    | none => none

/-- A basic land card in a library. -/
def basicLandInLibrary : Selector :=
  .intersection [.inLibrary, .cardType .land, .supertype .basic]

/-- Search for one card matching `among`, reveal it, and put it into hand.
The found card is variable `n`. -/
def searchRevealToHand (n : Nat) (among : Selector) : CardAction × Nat :=
  (
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable n
        (.selected (.controller .this) (.range 1 1) among),
      .reveal (.variable n),
      .returnToHand (.variable n)],
    n + 1)

/-- `Search your library for a basic land card, put it onto the battlefield tapped, then shuffle.`
Does not choose a target, so the target number stays `n`. -/
def parseSearchBasicLandTapped (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for a basic land card, put it onto the battlefield tapped, then shuffle" then
    some (
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .putOntoBattlefieldInState
            (.selected (.controller .this) (.range 1 1) basicLandInLibrary)
            [.tapped]],
      n)
  else none

/-- `Search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle.`
Up to two is zero through two (CR 107.1c). The found cards are variable `n`.
One of them enters tapped. Any not put onto the battlefield go to hand. -/
def parseSearchUpToTwoBasics (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for up to two basic land cards, reveal them, put one onto the battlefield tapped and the other into your hand, then shuffle" then
    some (
      .searchLibraryThenShuffle
        (.controller .this)
        [
          .defineSelectorVariable n
            (.selected (.controller .this) (.range 0 2) basicLandInLibrary),
          .reveal (.variable n),
          .putOntoBattlefieldInState
            (.selected (.controller .this) (.range 1 1) (.variable n))
            [.tapped],
          .returnToHand (.variable n)],
      n + 1)
  else none

/-- `Add one mana of any color.` The player chooses one of the five colors
(CR 106.4). Does not choose a target, so the target number stays `n`. -/
def parseAddOneManaOfAnyColor (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "add one mana of any color" then
    some (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1, n)
  else none

/-- `Destroy target permanent.` The target number is `n`. -/
def parseDestroyTargetPermanent (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "destroy target permanent" then
    some (.destroy (.target n .permanent), n + 1)
  else none

/-- This creature's power, including the pronouns a card uses for itself. -/
def selfPowerAmount? (s : String) : Option Value :=
  match norm s with
  | "this creature's power" | "its power" | "her power" | "his power" | "their power" =>
    some (.greatestPower (.source .this))
  | _ => none

/-- `Put X +1/+1 counters on <who>`, or `Put X +1/+1 counters on <who>, where X
is this creature's power`. `X` with no where-clause is the value of X
(CR 107.3). A printed natural count stays in `parsePutPlusOneOn?`. -/
def parsePutVariablePlusOne? (sentence : String) : Option (Value × String) :=
  (after? (normSentence sentence) "put ").bind fun rest =>
    let (body, where?) :=
      match split2? rest ", where x is " with
      | some (body, clause) => (body, some clause)
      | none => (rest, none)
    (split2? body " +1/+1 counters on ").bind fun (countText, who) =>
      if norm countText != "x" then none
      else
        match where? with
        | none => some (.x, who)
        | some clause => (selfPowerAmount? clause).map fun v => (v, who)

/-- `Put X +1/+1 counters on <this>`. The counters go on the source. -/
def parsePutXOnSelf (cardName sentence : String) : Option CardAction :=
  (parsePutVariablePlusOne? sentence).bind fun (amount, who) =>
    if refersToSelf cardName (norm who) || norm who == "it" then
      some (.putCounter (.source .this) .plusOnePlusOne amount)
    else none

/-- A pump, counters, a targeted restriction, a library search, becoming a
creature that gains a static ability, adding one mana of any color, destroying
a permanent, or exiling the top card to play later, optionally followed by an
activation limit. -/
def parseActivatedEffect (cardName : String) (effect : String) (n : Nat) :
    Option (CardAction × ActivateLimit × Nat) :=
  let (body, limit) := splitActivateLimit (sentences effect)
  match body with
  | [one] =>
    let targeted :=
      parseTargetCantBeBlocked one n <|>
        parsePutCountersOnTarget one n <|>
        parseSearchBasicLandTapped one n <|>
        parseSearchUpToTwoBasics one n <|>
        parseDestroyTargetPermanent one n
    let plain :=
      (parsePumpUntilEndOfTurn one <|> parsePutCountersOnThis one <|>
          parseBecomeAndGainStatic cardName one <|>
          parsePutXOnSelf cardName one).map (fun action => (action, n)) <|>
        parseAddOneManaOfAnyColor one n
    (targeted <|> plain).map fun (action, n') => (action, limit, n')
  | _ =>
    (parseExileTopMayPlay body n).map fun (action, n') => (action, limit, n')

/-- `{3}{W}: Creatures you control get +1/+1 until end of turn.`
Also `Pay 2 life: This creature gets +2/+2 until end of turn. Activate only once each turn.`
And `Sacrifice another creature or artifact: Exile the top card of your library. You may play it until the end of your next turn. Activate only during your turn and only once each turn.`
And `{5}{G}{G}: This enchantment becomes a Bear creature in addition to its other types and gains "…"`.
And `{1}, {T}: Add one mana of any color.`
And `{7}, {T}, Sacrifice this artifact: Destroy target permanent.`
And `{1}, {T}, Discard a card: Draw a card.` -/
def parseActivatedAbility (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      match parseActivatedEffect cardName effect n, parseActivationCost cardName costText with
      | some (action, limit, n'), some costs =>
        some (activatedWithCost n costs action limit n')
      | _, _ => none

/-- `{5}{W}, {T}: Harness The Mind Stone.` Harness this permanent
(CR 701.64). Reminder text, such as “Once harnessed, its ∞ ability is
active,” is not rules text. -/
def parseHarness (cardName line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (after? (normSentence effect) "harness ").bind fun who =>
      if !refersToSelf cardName who then none
      else
        (parseActivationCost cardName costText).map fun costs =>
          .ability (.activated costs (.keyword (.source .this) .harness))

/-- Effect of `<word> <this card> <mid> <effect>`.
`word` is `when` or `whenever`. `mid` is the clause boundary, such as
` enters, `. -/
def triggerSelfEffect? (cardName word s mid : String) : Option String :=
  (after? s (word ++ " ")).bind (split2? · mid) |>.bind fun (subject, effect) =>
    if refersToSelf cardName subject then some effect else none

/-- Effect of `when <this card> <mid> <effect>`.
`mid` is the clause boundary, such as ` enters, ` or ` dies, `. -/
def whenSelfEffect? (cardName s mid : String) : Option String :=
  triggerSelfEffect? cardName "when" s mid

/-- `when <this card> <mid> <effect>` as a triggered ability.
`mid` is the clause boundary, such as ` enters, `. -/
def onSelfTrigger (cardName line mid : String) (event : Trigger)
    (effect? : String → Option CardAction) : Option CardPart :=
  onTrigger event ((whenSelfEffect? cardName (normLine line) mid).bind effect?)

/-- Same as `onSelfTrigger`, keeping the target number the effect parser returns. -/
def onSelfTriggerN (cardName line mid : String) (event : Trigger)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onTriggerN event ((whenSelfEffect? cardName (normLine line) mid).bind effect?)

/-- `when <this card> enters, <effect>` as an enters-the-battlefield trigger. -/
def onEnter (cardName line : String) (effect? : String → Option CardAction) : Option CardPart :=
  onSelfTrigger cardName line " enters, " (.enter .this) effect?

/-- `when <this card> dies, <effect>` as a dies trigger. -/
def onDies (cardName line : String) (effect? : String → Option CardAction) : Option CardPart :=
  onSelfTrigger cardName line " dies, " (.die .this) effect?

/-- Same as `onEnter`, keeping the target number the effect parser returns. -/
def onEnterN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " enters, " (.enter .this) effect?

/-- Same as `onDies`, keeping the target number the effect parser returns. -/
def onDiesN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onSelfTriggerN cardName line " dies, " (.die .this) effect?

/-- `whenever <this card> attacks, <effect>` as an attack trigger, keeping the
target number the effect parser returns. -/
def onAttackN (cardName line : String)
    (effect? : String → Option (CardAction × Nat)) : Option (CardPart × Nat) :=
  onTriggerN (.attack .this .all)
    ((triggerSelfEffect? cardName "whenever" (normLine line) " attacks, ").bind effect?)

/-- `<this card> deals 5 damage to target creature.` The source must be this
card. The target number is `n`. -/
def parseDealDamage (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else
      (split2? rest " damage to target ").bind fun (amt, obj) =>
        match positiveDigits? amt, typesInPhrase obj with
        | some amount, some ts =>
          some (.dealDamage .this (.target n (permanentWith ts)) (.nat amount), n + 1)
        | _, _ => none

/-- `Target … gains … until end of turn.` The target number is `n`. -/
def parseGainsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (before? (normSentence sentence) "until end of turn").bind (split2? · " gains ") with
  | some (who, gained) =>
    match parseTargetPhrase who, parseKeywordPhrase gained with
    | some sel, some kws =>
      some (.continuous (gainEffects n sel kws) .endOfTurn, n + 1)
    | _, _ => none
  | none => none

/-- `Target creature gets +2/+2 until end of turn.`
Also `Target creature gets +2/+2 and gains lifelink until end of turn.`
The target number is `n`. A gained keyword refers to that same target. -/
def parseTargetGetsUntilEndOfTurn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (before? (normSentence sentence) " until end of turn").bind splitGetsOnly? |>.bind
    fun (who, rest) =>
      match parseTargetPhrase who, ptAndGains? rest with
      | some sel, some (p, t, kws) => pumpGainsUntilEnd n sel p t kws
      | _, _ => none

/-- `Creatures target player controls get -1 / -1 until end of turn.`
The player is target `n`. `P/T` may be negative. -/
def parseTargetPlayerControlsGet (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    ((before? who " target player controls").bind typesInPhrase).bind fun ts =>
      (pumpUntilEnd (permanentWith ts [.controlled (.target n .player)]) p t none).map
        fun action => (action, n + 1)

/-- `there are two or more creature cards in your graveyard`. -/
def graveyardCountCondition? (s : String) : Option Condition :=
  (between? s "there are " " in your graveyard").bind fun rest =>
    (split2? rest " or more ").bind fun (countText, cards) =>
      match positiveCount countText, (before? cards " cards").bind typeOfOracle? with
      | some k, some t =>
        some (.greaterOrEqual
          (.count (.intersection [.inGraveyard, .cardType t, .owner (.controller .this)]))
          (Value.nat k))
      | _, _ => none

/-- `a card`, `one card`, or `two cards` as how many cards are drawn.
One card is singular. More than one is plural. -/
def parseCardCount (s : String) : Option Nat :=
  let s := norm s
  match before? s " cards" with
  | some countText => nounCount? countText true
  | none =>
    match before? s " card" with
    | some countText => nounCount? countText false
    | none => none

/-- `Target player draws two cards and loses 2 life.`
The player is target `n`. -/
def parseTargetPlayerDrawsLosesLife (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target player draws " " life").bind
      (split2? · " and loses ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, positiveCount lifeText with
    | some cards, some life =>
      some (
        .sequence [
          .draw (.target n .player) (Value.nat cards),
          .loseLife (.targetReference n) (Value.nat life)],
        n + 1)
    | _, _ => none
  | none => none

/-- `When Bilbo Baggins enters, draw a card.` The subject is this card. -/
def parseEnterDraw (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect =>
    (after? effect "draw ").bind parseCardCount |>.map fun k =>
      .draw (.controller .this) (Value.nat k)

/-- `target creature an opponent controls` as the objects a target matches. -/
def parseOppControlledTarget (s : String) : Option Selector :=
  match (between? (norm s) "target " " an opponent controls").bind typesInPhrase with
  | some ts =>
    some (permanentWith ts [.controlled (.opponent (.controller .this))])
  | none => none

/-- `target <permanents> an opponent controls gets P/T until end of turn.`
The target number is `n`. `P/T` may be negative, as in -1 / -1. -/
def parseOppGetsUntilEndOfTurn (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (whoPtUntilEnd? sentence splitGets?).bind fun (who, p, t) =>
    (parseOppControlledTarget who).bind fun sel =>
      (pumpUntilEnd (.target n sel) p t none).map fun action => (action, n + 1)

/-- `When this creature dies, target creature an opponent controls gets -1 / -1 until end of turn.`
The dying object is this card. The target number is `n`. -/
def parseDiesOppGets (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onDiesN cardName line (parseOppGetsUntilEndOfTurn · n)

/-- `put a +1/+1 counter on this creature`. `this`, `this creature`, and `it`
are the source of this ability. -/
def parsePutPlusOneOnThis (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "put a +1/+1 counter on ").bind fun who =>
    if parsePumpWho who == some (.source .this) then
      some (.putCounter (.source .this) .plusOnePlusOne 1)
    else none

/-- `Whenever you draw your second card each turn, put a +1/+1 counter on this creature.` -/
def parseDrawSecondPlusOne (line : String) : Option CardPart :=
  onTrigger (.ordinal 2 .turnStart (.draw (.controller .this) .all))
    ((after? (normLine line) "whenever you draw your second card each turn, ").bind
      parsePutPlusOneOnThis)

/-- `Whenever you draw a card, put a +1/+1 counter on this creature.` -/
def parseYouDrawPlusOne (line : String) : Option CardPart :=
  onTrigger (.draw (.controller .this) .all)
    ((after? (normLine line) "whenever you draw a card, ").bind parsePutPlusOneOnThis)

/-- `Counter target spell unless its controller pays {4}.`
The target number is `n`. -/
def parseCounterUnlessPays (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "counter target ").bind
      (split2? · " unless its controller pays ") with
  | some (obj, costText) =>
    if obj != "spell" then none
    else
      match nonemptyMana? costText with
      | some syms =>
        some (
          .preventable
            (.controller (.targetReference n))
            [.mana syms]
            (.counter (.target n .spell)),
          n + 1)
      | none => none
  | none => none

/-- `Draw two cards, then discard a card.` Does not choose a target. -/
def parseDrawThenDiscard (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match split2? (normSentence sentence) ", then discard " with
  | some (drawPart, discardPart) =>
    match (after? drawPart "draw ").bind parseCardCount, parseCardCount discardPart with
    | some d, some c =>
      some (
        .sequence [
          .draw (.controller .this) (Value.nat d),
          .discard (.controller .this) (Value.nat c)],
        n)
    | _, _ => none
  | none => none

/-- If target `id` would die this turn, exile it instead. -/
def exileIfWouldDie (id : Nat) : ContinuousEffect :=
  .replace (.putToGraveyard (.targetReference id)) [.exile .replacingObject]

/-- `Target creature gets -5 / -5 until end of turn. If that creature would die this turn, exile it instead.`
The pump and the replacement both last until end of turn. Dying is being put
into a graveyard from the battlefield; the replacement exiles that object
instead (CR 614.1). The creature is target `n`. -/
def parsePumpExileIfDies (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [pump, exile] =>
    if !sentenceIs exile "if that creature would die this turn, exile it instead" then none
    else
      match parseTargetGetsUntilEndOfTurn pump n with
      | some (.continuous effects .endOfTurn, n') =>
        match ContinuousEffect.addedPT? effects, ContinuousEffect.targetingSelector? effects with
        | some _, some (.target m (.intersection [.permanent, .cardType .creature])) =>
          some (.continuous (effects ++ [exileIfWouldDie m]) .endOfTurn, n')
        | _, _ => none
      | _ => none
  | _ => none

/-- `Target creature you control deals damage equal to its power to target creature an opponent controls.`
The source is target `n`; the recipient is target `n + 1`. -/
def parseDealsDamageEqualToPower (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match split2? (normSentence sentence) " deals damage equal to its power to " with
  | some (src, dest) =>
    if (before? src " you control").isNone then none
    else
      match parseTargetPhrase src, parseOppControlledTarget dest with
      | some srcSel, some destSel =>
        some (
          .dealDamageEqualToPower
            (.target n srcSel)
            (.target (n + 1) destSel),
          n + 2)
      | _, _ => none
  | none => none

/-- `Put a +1/+1 counter on target creature you control.`
The target is numbered `n`. -/
def parsePutPlusOneOnTarget (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match after? (normSentence sentence) "put a +1/+1 counter on " with
  | some who =>
    (parseTargetPhrase who).map fun sel =>
      (.putCounter (.target n sel) .plusOnePlusOne 1, n + 1)
  | none => none

/-- `It gains trample and hexproof until end of turn.`
The keywords are gained by the target already numbered `targetId`. -/
def parseItGainsKeywords (sentence : String) (targetId : Nat) : Option CardAction :=
  (between? (normSentence sentence) "it gains " " until end of turn").bind
    fun gained =>
      (parseKeywordPhrase gained).map fun kws =>
        .continuous (keywordGains (.targetReference targetId) kws) .endOfTurn

/-- `Put a +1/+1 counter on target creature you control. It gains trample and hexproof until end of turn.`
The counter and the keywords share target `n`. -/
def parsePutPlusOneThenGains (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [put, gains] =>
    match parsePutPlusOneOnTarget put n, parseItGainsKeywords gains n with
    | some (putAction, n'), some gain =>
      some (.sequence [putAction, gain], n')
    | _, _ => none
  | _ => none

/-- `Destroy target creature`, `Destroy target creature with flying`, or
`Destroy target creature with power 4 or greater.`
The target number is `n`. `with` names one keyword the permanent must have,
or `power N or greater`. `N` is a positive printed number. -/
def parseDestroy (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "destroy target ").bind fun rest =>
    let destroyed (ts : List CardType) (tail : List Selector) : CardAction × Nat :=
      (.destroy (.target n (permanentWith ts tail)), n + 1)
    let withPower :=
      (split2? rest " with power ").bind fun (obj, powerText) =>
        (before? powerText " or greater").bind positiveCount |>.bind fun p =>
          (typesInPhrase obj).map fun ts =>
            destroyed ts [.powerAtLeast (Value.int (p : Int))]
    let withKeyword :=
      (split2? rest " with ").bind fun (obj, kwText) =>
        (keywordOfOracle? kwText).bind fun k =>
          (typesInPhrase obj).map fun ts => destroyed ts [.keyword k]
    let plain :=
      (typesInPhrase rest).map fun ts => destroyed ts []
    withPower <|> withKeyword <|> plain

/-- `Destroy target artifact or enchantment. You gain 2 life.`
The destroy chooses target `n`. Gaining life does not. `N` is a positive count. -/
def parseDestroyThenGainLife (text : String) (n : Nat) : Option (CardAction × Nat) :=
  match sentences text with
  | [destroy, gain] =>
    match parseDestroy destroy n, lifeAmount? (normSentence gain) "you gain " with
    | some (destroyed, n'), some k =>
      some (.sequence [destroyed, .gainLife (.controller .this) (Value.nat k)], n')
    | _, _ => none
  | _ => none

/-- `Until end of turn, target creature becomes an artifact in addition to its
other types and gains indestructible.`
The target is `n`. The type and indestructible both last until end of turn.
A reminder parenthetical is not rules text (CR 207.2). -/
def parseBecomeArtifactIndestructible (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normLine sentence) "until end of turn, ").bind fun rest =>
    (split2? rest " becomes ").bind fun (who, become) =>
      (split2? become " and gains ").bind fun (typeText, gained) =>
        if typeText != "an artifact in addition to its other types" then none
        else
          match parseTargetPhrase who, parseKeywordPhrase gained with
          | some sel, some [.indestructible] =>
            if sel != permanentWith [.creature] then none
            else
              some (
                .continuous
                  [.gainType (.target n sel) .artifact,
                    .gainAbility (.targetReference n) (.keyword .indestructible)]
                .endOfTurn,
                n + 1)
          | _, _ => none

/-- Target artifact token, with no further restriction. -/
def artifactTokenPermanent : Selector :=
  .intersection [.permanent, .cardType .artifact, .token]

/-- `Destroy target artifact token.` The token is target `n`. -/
def parseDestroyArtifactToken (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "destroy target artifact token" then
    some (.destroy (.target n artifactTokenPermanent), n + 1)
  else none

/-- `<this card> deals 3 damage to target creature. If that creature would die this turn, exile it instead.`
The creature is target `n`. Dying this turn is replaced by exile. -/
def parseDealDamageExileIfDies (cardName : String) (text : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match sentences text with
  | [damage, exile] =>
    if !sentenceIs exile "if that creature would die this turn, exile it instead" then none
    else
      match parseDealDamage cardName damage n with
      | some (.dealDamage src (.target id among) amount, n') =>
        if src == .this && among == permanentWith [.creature] then
          some (
            .sequence [
              .dealDamage src (.target id among) amount,
              .continuous [exileIfWouldDie id] .endOfTurn],
            n')
        else none
      | _ => none
  | _ => none

/-- `Tap target creature an opponent controls.` The creature is target `n`. -/
def parseTapOppCreature (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "tap " with
  | some rest =>
    (parseOppControlledTarget rest).map fun sel =>
      (.tap (.target n sel), n + 1)
  | none => none

/-- One printed mode of a “Choose one” spell. The first success wins. -/
def parseModeAction (cardName : String) (text : String) (n : Nat) :
    Option (CardAction × Nat) :=
  parseDealDamageExileIfDies cardName text n <|>
    parseDestroyArtifactToken text n <|>
    parseCounterUnlessPays text n <|>
    parseDrawThenDiscard text n <|>
    parsePumpExileIfDies text n <|>
    parseTargetPlayerDrawsLosesLife text n <|>
    parseTargetGetsUntilEndOfTurn text n <|>
    parseTargetPlayerControlsGet text n <|>
    parseDestroyThenGainLife text n <|>
    parseBecomeArtifactIndestructible text n <|>
    parseDestroy text n <|>
    parsePutPlusOneThenGains text n <|>
    (parsePumpUntilEndOfTurn text).map (·, n) <|>
    parseTapOppCreature text n <|>
    parseUntap text n

/-- The text of a `•` mode line, without the bullet. -/
def stripModeBullet (line : String) : Option String :=
  after? (copied line) "•"

/-- `Choose one —` or `Choose one or both —` (CR 700.2).
`true` means one or both. -/
def chooseHeader? (line : String) : Option Bool :=
  if normLine line == "choose one —" then some false
  else if normLine line == "choose one or both —" then some true
  else none

/-- Parts for a modal spell with at least one parsed mode.
`orBoth` is “choose one or both”: the controller selects one or two distinct
modes. “Choose one” selects exactly one. Each mode is chosen at most once
(CR 700.2). No modes makes the parse fail rather than dropping the printed choice. -/
def chooseOneParts (modes : List CardAction) (orBoth : Bool) : Option (List CardPart) :=
  match modes with
  | [] => none
  | modes =>
    some [.actions [
      if orBoth then
        .chooseUniqueModes (.range 1 2) modes
      else
        .chooseUniqueModes (.range 1 1) modes]]

end OracleParts

end Mtg.Engine
