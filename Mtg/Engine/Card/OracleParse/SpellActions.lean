import Mtg.Engine.Card.OracleParse.Sentences

/-!
# Spell text

Static restrictions and the sentences of a spell, joined in printed order.
-/

namespace Mtg.Engine

namespace OracleParts

/-- `<subject> <tail>` as a static restriction, when `subject` is this card. -/
def staticCant (cardName line tail : String) (restriction : Trigger) : Option CardPart :=
  (before? (normLine line) tail).bind fun subject =>
    if subject.isEmpty || !refersToSelf cardName subject then none
    else some (.ability (.static (.forbid restriction)))

/-- `<this card> can't be blocked by tokens.` The subject must be this card. -/
def parseCantBeBlockedByTokens (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked by tokens" (.block .token .this)

/-- `<this card> can't be blocked.` The subject must be this card. -/
def parseCantBeBlocked (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't be blocked" (.block .any .this)

/-- `<this card> can't be blocked by creatures with power 2 or less.`
The subject must be this card. `N` is a positive printed power. -/
def parseCantBeBlockedByPower (cardName : String) (line : String) : Option CardPart :=
  (split2? (normLine line) " can't be blocked by creatures with power ").bind
    fun (subject, rest) =>
      if !refersToSelf cardName subject then none
      else
        (before? rest " or less").bind positiveCount |>.map fun p =>
          .ability (.static (.forbid (.block
            (.intersection [
              .permanent,
              .cardType .creature,
              .powerAtMost (Value.int (p : Int))])
            .this)))

/-- `<this card> can't block.` The subject must be this card. This functions
on the battlefield (CR 604.2 / 509.1b), so it is `static`. -/
def parseCantBlock (cardName : String) (line : String) : Option CardPart :=
  staticCant cardName line " can't block" (.block .this .any)

/-- `Whenever <this card> deals combat damage to a player, draw a card, then
discard a card.` The subject must be this card. The effect is the same
draw-then-discard grammar as a modal spell. -/
def parseCombatDamageLoot (cardName : String) (line : String) : Option CardPart :=
  onTrigger (.combatDamage .this .player)
    ((triggerSelfEffect? cardName "whenever" (normLine line)
        " deals combat damage to a player, ").bind fun effect =>
      actionOf (parseDrawThenDiscard effect 1))

/-- `Exchange control of two target nonland permanents that share a card type.`
The target number is `n`. The noun stays plural, as in the printed template
for a set of permanents. -/
def parseExchangeControlSharingCardType (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  match (between? (normSentence sentence)
      "exchange control of " " that share a card type").bind
      (split2? · " target ") with
  | some (countText, obj) =>
    if obj != "nonland permanents" then none
    else
      match parseCountRange countText with
      | some r =>
        if r == .range 1 1 then none
        else
          some (
            .exchangeControl
              (.targetSet
                n
                r
                (.intersection [.permanent, .not .land])
                [.shareCardType]),
            n + 1)
      | none => none
  | none => none

/-- `Target creature's owner puts it on their choice of the top or bottom of their library.`
The target number is `n`. That creature's owner chooses which library position. -/
def parseOwnerPutsTopOrBottom (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (between? (normSentence sentence) "target "
      "'s owner puts it on their choice of the top or bottom of their library").bind
      typesInPhrase with
  | some ts =>
    let sel := permanentWith ts
    some (
      .playerSelectAction
        (.owner (.targetReference n))
        (.range 1 1)
        [.putOnTopOfLibrary (.target n sel),
          .putOnBottomOfLibrary (.targetReference n)],
      n + 1)
  | none => none

/-- `Put a +1/+1 counter on up to one target creature.`
Up to one target is zero or one (CR 115.1). The targets are numbered `n`. -/
def parsePutPlusOneUpToOne (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match (after? (normSentence sentence) "put a +1/+1 counter on up to one target ").bind
      typesInPhrase with
  | some ts =>
    some (
      .putCounter
        (.targets n (.range 0 1) (permanentWith ts))
        .plusOnePlusOne
        1,
      n + 1)
  | none => none

/-- `Target player gains 2 life.` The player is target `n`. -/
def parseTargetPlayerGainsLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "target player gains ").map fun k =>
    (.gainLife (.target n .player) (Value.nat k), n + 1)

/-- `You gain 2 life.` Does not choose a target, so the target number stays `n`. -/
def parseYouGainLife (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (lifeAmount? (normSentence sentence) "you gain ").map fun k =>
    (.gainLife (.controller .this) (Value.nat k), n)

/-- `Scry 2.` Does not choose a target, so the target number stays `n`. -/
def parseScry (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  match after? (normSentence sentence) "scry " with
  | some count =>
    (positiveCount count).map fun k => (.scry (.controller .this) (Value.nat k), n)
  | none => none

/-- `Whenever one or more other creatures die, scry 1.`
Those creatures die together, so this is one trigger (CR 603.2c).
The effect is `Scry N`. -/
def parseOtherCreaturesDieScry (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (normLine line) "whenever one or more ").bind (split2? · " die, ") |>.bind
    fun (who, effect) =>
      if who != "other creatures" then none
      else
        (parseControlledPhrase who).bind fun among =>
          onTriggerN (.dieSimultaneously among []) (parseScry effect n)

/-- `Counter target spell. If a permanent spell is countered this way, exile
it instead of putting it into its owner's graveyard. You may cast that card
without paying its mana cost for as long as it remains exiled.`
The counter and its target are numbered `n`. The exile that replaces the
graveyard is `n + 1`, and the free cast refers to that exiled card. -/
def parseCounterExilePermanentMayCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, exile, cast] =>
    if !sentenceIs counter "counter target spell" then none
    else if !sentenceIs exile
        "if a permanent spell is countered this way, exile it instead of putting it into its owner's graveyard" then
      none
    else if !sentenceIs cast
        "you may cast that card without paying its mana cost for as long as it remains exiled" then
      none
    else
      let exileId := n + 1
      some (
        [
          .actionId n (.counter (.target n .spell)),
          .continuous
            [.replace
              (.putToGraveyard
                (.intersection [.wasObjectOfAction n, .permanentSpell]))
              [
                .actionId exileId (.exile (.replacingObject)),
                .continuous
                  [.canCastWithoutPayingManaCost
                    (.controller .this)
                    (.wasCreatedByAction exileId)]
                  .endOfGame
              ]]
            .endOfGame
        ],
        exileId)
  | _ => none

/-- `If that spell's mana value was 2 or less, recruit.`
`N` is a positive printed number. Recruit is the effect of that check. -/
def recruitIfSpellMvAtMost? (sentence : String) : Option Nat :=
  (between? (normSentence sentence)
      "if that spell's mana value was " " or less, recruit").bind positiveCount

/-- `Counter target spell. If that spell's mana value was N or less, recruit.`
The spell is target `n`. Before it is countered, value variable `n` records
the greatest mana value of that target, which on the stack includes the
chosen `{X}` (CR 202.3e). Recruit happens only when that variable is less
than or equal to `N`. -/
def parseCounterThenRecruitIfMv (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [counter, cond] =>
    if !sentenceIs counter "counter target spell" then none
    else
      (recruitIfSpellMvAtMost? cond).map fun k =>
        ([
          .defineValueVariable n (.greatestManaValue (.target n .spell)),
          .counter (.targetReference n),
          .if (.lessOrEqual (.variable n) (.nat k))
            [.keyword (.controller .this) .recruit]
        ], n + 1)
  | _ => none

/-- `You may play an additional land this turn.` One extra land play, until end of turn
(CR 305.2b). -/
def parseAdditionalLand (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence "you may play an additional land this turn" then
    some (
      .continuous
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]
        .endOfTurn,
      n)
  else none

/-- `You draw a card and lose 1 life.` One card and 1 life. -/
def parseYouDrawCardLoseLife (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "you draw ").bind (split2? · " and lose ") with
  | some (drawText, lifeText) =>
    match parseCardCount drawText, lifeAmount? ("lose " ++ lifeText) "lose " with
    | some 1, some 1 =>
      some (.sequence [
        .draw (.controller .this) 1,
        .loseLife (.controller .this) 1])
    | _, _ => none
  | none => none

/-- The subtype printed in `amass Goblins`: the plural drops a trailing `s`. -/
def amassSubtype? (s : String) : Option CardSubtype :=
  if s.endsWith "s" && s.length > 1 then subtypeOfOracle? (s.dropEnd 1).copy else none

/-- `Recruit.` Recruit is a keyword action of this card's controller
(CR 701.57). A reminder parenthetical is not rules text. -/
def parseRecruit (sentence : String) : Option CardAction :=
  if sentenceIs sentence "recruit" then some (.keyword (.controller .this) .recruit) else none

/-- `Draw a card.` / `Draw two cards.` The player is this spell's controller.
One card is singular. More than one is plural. -/
def parseDrawCards (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "draw ").bind parseCardCount |>.map fun k =>
    .draw (.controller .this) (Value.nat k)

/-- `Amass Goblins 1.` The controller amasses that subtype that many (CR 701.45).
The subtype is plural. `N` is a positive count. `Amass Goblins X, where X is
this creature's power` uses that power. -/
def parseAmass (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "amass ").bind fun rest =>
    match rest.splitOn " " |>.map copied |>.filter (· != "") with
    | typeText :: nWords =>
      let nText := " ".intercalate nWords
      (amassSubtype? typeText).bind fun st =>
        let amount :=
          (positiveCount nText).map Value.nat <|>
            ((after? nText "x, where x is ").bind selfPowerAmount?)
        amount.map fun v => .keyword (.controller .this) (.amass st v)
    | [] => none

/-- `Return up to one target creature card from your graveyard to your hand.`
Up to one target is zero or one (CR 115.1). That card is in your graveyard.
The target is numbered `n`. -/
def parseReturnUpToOneFromYourGraveyard (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (between? (normSentence sentence)
      "return up to one target " " from your graveyard to your hand").bind
    fun obj =>
      (before? obj " card").bind typeOfOracle? |>.map fun t =>
        (.returnToHand
          (.targets n (.range 0 1)
            (.intersection [
              .inGraveyard,
              .cardType t,
              .owner (.controller .this)])),
         n + 1)

/-- `Search your library for a legendary creature card, reveal it, put it into your hand, then shuffle.`
The found card is variable `n`. A legendary creature card, with no further
subtype. -/
def parseSearchLegendaryCreatureToHand (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  if sentenceIs sentence
      "search your library for a legendary creature card, reveal it, put it into your hand, then shuffle" then
    some (searchRevealToHand n
      (.intersection [.inLibrary, .cardType .creature, .supertype .legendary]))
  else none

/-- A parsed action that does not choose a new target. -/
def unchanged (parsed : Option CardAction) (n : Nat) : Option (CardAction × Nat) :=
  parsed.map (·, n)

/-- An instant or a sorcery. -/
def instantOrSorcery : Selector :=
  .union [.cardType .instant, .cardType .sorcery]

/-- Instant and sorcery cards among the objects of action `id`. -/
def instantOrSorceryAmong (id : Nat) : Selector :=
  .intersection [.wasObjectOfAction id, instantOrSorcery]

/-- Mill `k` cards as action `n`, then `put` those cards. -/
def millThen (n k : Nat) (put : Nat → CardAction) : CardAction × Nat :=
  (
    .sequence [
      .actionId n (.mill (.controller .this) (.nat k)),
      put n],
    n + 1)

/-- A plural mill count in `mill <count><tail>`. One card is not this count. -/
def millPluralCount? (sentence tail : String) : Option Nat :=
  (after? (normSentence sentence) "mill ").bind (before? · tail) |>.bind
    (nounCount? · true)

/-- `Mill four cards, then put an instant or sorcery card from among them into your hand.`
More than one card uses the plural `cards`. The milled cards are action `n`.
One instant or sorcery card from among them goes to hand. -/
def parseMillThenPutInstantOrSorcery (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (millPluralCount? sentence
      " cards, then put an instant or sorcery card from among them into your hand").map
    fun k =>
      millThen n k fun id =>
        .returnToHand
          (.selected (.controller .this) (.range 1 1) (instantOrSorceryAmong id))

/-- `Mill six cards, then put all instant and sorcery cards from among them into your hand.`
More than one card uses the plural `cards`. Every instant and sorcery card
from among them goes to hand. The milled cards are action `n`. -/
def parseMillThenPutAllInstantsOrSorceries (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (millPluralCount? sentence
      " cards, then put all instant and sorcery cards from among them into your hand").map
    fun k => millThen n k fun id => .returnToHand (instantOrSorceryAmong id)

/-- `Mill four cards, then put all Elf cards from among them into your hand.`
More than one card uses the plural `cards`. The subtype is printed singular
(`Elf`, not `Elves`). Every card of that subtype from among them goes to
hand. The milled cards are action `n`. -/
def parseMillThenPutAllSubtype (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "mill ").bind fun rest =>
    (split2? rest " cards, then put all ").bind fun (countText, tail) =>
      (nounCount? countText true).bind fun k =>
        ((before? tail " cards from among them into your hand").bind
            subtypeOfOracle?).map fun st =>
          millThen n k fun id =>
            .returnToHand
              (.intersection [.wasObjectOfAction id, .subtype st])

/-- Two creatures and/or lands this object's controller controls. -/
def twoCreaturesOrLandsYouControl : Selector :=
  permanentWith [.creature, .land] [youControl]

/-- `Exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control.`
Those two permanents are target `n`, and that exile is action `n`.
They return under their owner's control. -/
def parseExileTwoThenReturn (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  if sentenceIs sentence
      "exile two target creatures and/or lands you control, then return them to the battlefield under their owner's control" then
    some (
      .sequence [
        .actionId n
          (.exile (.targets n (.range 2 2) twoCreaturesOrLandsYouControl)),
        .putOntoBattlefieldInState
          (.wasCreatedByAction n)
          [.controlled (.owner (.wasCreatedByAction n))]],
      n + 1)
  else none

/-- `Mill four cards, then put up to two land cards from among them into your hand.`
More than one milled card uses the plural `cards`. Up to one land card is
singular; more than one is plural. The milled cards are action `n`. -/
def parseMillThenPutUpToLands (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence) "mill ").bind fun rest =>
    (split2? rest " cards, then put up to ").bind fun (countText, tail) =>
      (nounCount? countText true).bind fun k =>
        let landTail :=
          (before? tail " land cards from among them into your hand").map
            (true, ·) <|>
          (before? tail " land card from among them into your hand").map
            (false, ·)
        match landTail with
        | some (plural, maxText) =>
          (nounCount? maxText plural).map fun max =>
            millThen n k fun id =>
              .returnToHand
                (.selected
                  (.controller .this)
                  (.range (Value.nat 0) (Value.nat max))
                  (.intersection [.wasObjectOfAction id, .cardType .land]))
        | none => none

/-- `Mill two cards.` More than one card uses the plural `cards`. -/
def parseMillCards (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (millPluralCount? sentence " cards").map fun k => (.mill (.controller .this) (.nat k), n)

/-- Each creature an opponent of this object's controller controls. -/
def eachOppCreature : Selector :=
  .intersection [
    .permanent,
    .cardType .creature,
    .controlled (.opponent (.controller .this))]

/-- Each creature that is not a Dragon. -/
def eachNonDragonCreature : Selector :=
  .intersection [
    .permanent, .cardType .creature, .not (.subtype .dragon)]

/-- `<this card> deals 1 damage to each creature your opponents control.`
Also `… to each non-Dragon creature.` The source is this card. -/
def parseDealDamageToEach (cardName : String) (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence sentence) " deals ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else
      (split2? rest " damage to each ").bind fun (amt, obj) =>
        (positiveCount amt).bind fun amount =>
          let (obj, opponents) :=
            match before? obj " and each opponent" with
            | some rest => (rest, true)
            | none => (obj, false)
          let dest :=
            if obj == "creature your opponents control" then some eachOppCreature
            else if obj == "non-dragon creature" then some eachNonDragonCreature
            else if obj == "creature" then some (.intersection [.permanent, .cardType .creature])
            else
              (between? obj "non-" " creature").bind subtypeOfOracle? |>.map fun st =>
                .intersection [.permanent, .cardType .creature, .not (.subtype st)]
          dest.map fun sel =>
            if opponents then
              (.sequence [.dealDamage .this sel (.nat amount),
                .dealDamage .this (.opponent (.controller .this)) (.nat amount)], n)
            else (.dealDamage .this sel (.nat amount), n)

/-- One sentence. The first parser that accepts it wins. -/
def parseSentence (cardName sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  parseGainsUntilEndOfTurn sentence n <|>
    parseTap sentence n <|>
    parseUntap sentence n <|>
    parseItGetsUntilEndOfTurn sentence n <|>
    parseIfItsSubtypeMayAttach sentence n <|>
    parseDealDamage cardName sentence n <|>
    parseDealDamageToEach cardName sentence n <|>
    parseDestroyArtifactToken sentence n <|>
    parseDealsDamageEqualToPower sentence n <|>
    parseDestroy sentence n <|>
    parsePutPlusOneUpToOne sentence n <|>
    parseTargetPlayerGainsLife sentence n <|>
    parseYouGainLife sentence n <|>
    unchanged (parseYouDrawCardLoseLife sentence) n <|>
    unchanged (parseAmass sentence) n <|>
    unchanged (parseRecruit sentence) n <|>
    parseReturnUpToOneFromYourGraveyard sentence n <|>
    parseAdditionalLand sentence n <|>
    parseScry sentence n <|>
    parseOwnerPutsTopOrBottom sentence n <|>
    parseExchangeControlSharingCardType sentence n <|>
    parseTargetGetsUntilEndOfTurn sentence n <|>
    parseTargetPlayerControlsGet sentence n <|>
    parseTargetPlayerDrawsLosesLife sentence n <|>
    parseSearchLegendaryCreatureToHand sentence n <|>
    parseMillThenPutAllInstantsOrSorceries sentence n <|>
    parseMillThenPutInstantOrSorcery sentence n <|>
    parseMillThenPutUpToLands sentence n <|>
    parseMillThenPutAllSubtype sentence n <|>
    parseMillCards sentence n <|>
    parseExileTwoThenReturn sentence n

/-- Creatures you control other than target `n`. -/
def eachOtherCreatureThanTarget (n : Nat) : Selector :=
  .intersection [
    .not (.targetReference n),
    .permanent,
    .cardType .creature,
    youControl]

/-- `If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.`
The extra counter is on every creature you control except target `n`. -/
def parseAlsoPlusOneEachOther (sentence : String) (n : Nat) : Option CardAction :=
  (after? (normSentence sentence)
      "if this spell was cast from a graveyard, also put ").bind fun rest =>
    (split2? rest " +1/+1 counter on each ").bind fun (countText, who) =>
      match nounCount? countText false, who with
      | some 1, "other creature you control" =>
        some (.putCounter (eachOtherCreatureThanTarget n) .plusOnePlusOne 1)
      | _, _ => none

/-- `Put a +1/+1 counter on target creature you control. If this spell was cast from a graveyard, also put a +1/+1 counter on each other creature you control.`
The creature is target `n`. The extra counters happen only when this spell
was cast from a graveyard. That cast is an event since the start of the game. -/
def parsePlusOneThenEachOtherIfFromGy (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [put, also] =>
    match parsePutPlusOneOnTarget put n, parseAlsoPlusOneEachOther also n with
    | some (putAction, n'), some alsoAction =>
      some ([
        putAction,
        .if (.happened (.castSpellFromGraveyard .this) .gameStart) [alsoAction]
      ], n')
    | _, _ => none
  | _ => none

/-- The effect after `If this spell was cast from a graveyard, `, without
the trailing `instead`. -/
def fromGraveyardInstead? (sentence : String) : Option String :=
  (after? (normSentence sentence) "if this spell was cast from a graveyard, ").bind
    fun rest => before? rest " instead"

/-- Draw, or amass, and the same action with a different count when this
spell was cast from a graveyard. Both amass the same subtype. The
cast-from-graveyard action is the “instead” branch. -/
def insteadFromGraveyardPair (normal instead : String) :
    Option (CardAction × CardAction) :=
  let drawPair :=
    match parseDrawCards normal, (fromGraveyardInstead? instead).bind parseDrawCards with
    | some normalA, some fromGyA => some (fromGyA, normalA)
    | _, _ => none
  let amassPair :=
    match parseAmass normal, (fromGraveyardInstead? instead).bind parseAmass with
    | some (.keyword who (.amass st na)), some (.keyword who' (.amass st' ga)) =>
      if who == who' && st == st' then
        some (.keyword who (.amass st ga), .keyword who (.amass st na))
      else none
    | _, _ => none
  drawPair <|> amassPair

/-- `Draw a card. If this spell was cast from a graveyard, draw two cards instead.`
Also the same shape for amass. The second sentence replaces the first when
this spell was cast from a graveyard. -/
def parseInsteadFromGraveyard (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [normal, instead] =>
    (insteadFromGraveyardPair normal instead).map fun (fromGyA, normalA) =>
      ([.ifElse
          (.happened (.castSpellFromGraveyard .this) .gameStart)
          [fromGyA]
          [normalA]],
        n)
  | _ => none

/-- `Put two +1/+1 counters on target creature you control.`
The creature is target `n`. A creature type is a different ability. -/
def parsePutPlusOneOnCreatureYouControl (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (parsePutPlusOneOn? sentence).bind fun (k, who) =>
    match parseTargetPhrase who with
    | some sel =>
      if sel == permanentWith [.creature] [youControl] then
        some (.putCounter (.target n sel) .plusOnePlusOne (.nat k), n + 1)
      else none
    | none => none

/-- `Put two +1/+1 counters on target creature you control. Then it fights target creature an opponent controls.`
The creature you control is target `n`. The opponent's creature is the next
target. -/
def parsePlusOneThenFight (text : String) (n : Nat) : Option (List CardAction × Nat) :=
  match sentences text with
  | [put, fights] =>
    match parsePutPlusOneOnCreatureYouControl put n,
        (after? (normSentence fights) "then it fights ").bind parseOppControlledTarget with
    | some (putAction, n'), some dest =>
      some ([putAction, .fight (.targetReference n) (.target n' dest)], n' + 1)
    | _, _ => none
  | _ => none

/-- `Add four mana in any combination of colors. Spend this mana only to cast Dragon spells.`
The mana is one addition in any combination of colors, not that much mana
of one color. That mana can be spent only to cast a spell of the printed
subtype. The addition is action `n`. -/
def parseAddManaCombination (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [add, spend] =>
    (between? (normSentence add) "add " " mana in any combination of colors").bind
      fun countText =>
        if !countText.isEmpty && (split2? countText " ").isSome then none
        else
          (positiveCount countText).bind fun k =>
            (between? (normSentence spend) "spend this mana only to cast " " spells").bind
              subtypeOfOracle? |>.map fun st =>
                ([
                  .actionId n
                    (.addManaInAnyCombination
                      (.controller .this) ManaSymbol.anyColor (.nat k)),
                  .continuous
                    [.forbid
                      (.spendManaCreatedByAction n
                        (.not (.castSpell (.subtype st))))]
                    .endOfTurn],
                  n + 1)
  | _ => none

/-- How many cards `<count> card(s)` names.
One takes the singular. Any larger count takes the plural. -/
def topCount? (phrase : String) : Option Nat :=
  parseCardCount phrase

/-- `Exile all attacking creatures target player controls. That player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle.`
The player is target `n`, and the exile is action `n`. “That many” is how
many of those creatures are exiled. That player chooses whether to search,
and may find any number from zero up to that many (CR 701.19b). -/
def parseExileAttackersSearchBasics (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [exile, search] =>
    if !sentenceIs exile
        "exile all attacking creatures target player controls" then none
    else if !sentenceIs search
        "that player may search their library for that many basic land cards, put those cards onto the battlefield tapped, then shuffle" then
      none
    else
      let exiled := .count (.wasObjectOfAction n)
      some ([
        .actionId n
          (.exile
            (.intersection [
              .permanent,
              .cardType .creature,
              .attacking .all,
              .controlled (.target n .player)])),
        .optional (.targetReference n)
          (.searchLibraryThenShuffle
            (.targetReference n)
            [
              .putOntoBattlefieldInState
                (.selected
                  (.targetReference n)
                  (.range (.nat 0) exiled)
                  (.intersection [
                    .inLibrary,
                    .cardType .land,
                    .supertype .basic]))
                [.tapped]])],
        n + 1)
  | _ => none

/-- `Look at the top two cards of your library and exile them face down. For as long as they remain exiled, you may play them if you control a Wizard.`
The looked-at cards are action `n`. The exile is action `n + 1`. One card
uses the singular. Those cards are exiled face down. You may play them
while they remain exiled and you control a permanent of that subtype. -/
def parseLookAtTopExileFaceDownPlayIf (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [look, play] =>
    (after? (normSentence look) "look at the top ").bind fun tail =>
      (before? tail " of your library and exile them face down").bind topCount? |>.bind
        fun k =>
          (after? (normSentence play)
              "for as long as they remain exiled, you may play them if you control ").bind
            dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
              let exileId := n + 1
              ([
                .actionId n
                  (.lookAt (.topOfLibrary (.controller .this) (.nat k))),
                .actionId exileId
                  (.exileFaceDown (.wasObjectOfAction n)),
                .continuous
                  [.if
                    (.any
                      (.intersection [
                        .permanent,
                        .subtype st,
                        youControl]))
                    [.canPlay
                      (.controller .this)
                      (.intersection [
                        .inExile,
                        .wasCreatedByAction exileId])]]
                  .endOfGame],
                exileId + 1)
  | _ => none

/-- Vision Quest: the player chooses to search the library and graveyard, or
only the graveyard, for an artifact creature of mana value X or less. The
found card is variable `n`. It enters with X +1/+1 counters and gains haste
when X is 4 or greater. Searching the library shuffles. -/
def parseVisionQuest (text : String) (n : Nat) : Option (List CardAction × Nat) :=
  match (sentences text).map normSentence with
  | [search, haste, shuffle] =>
    if search == "search your library and/or graveyard for an artifact creature card with mana value x or less and put it onto the battlefield with x additional +1/+1 counters on it" &&
        haste == "if x is 4 or greater, it gains haste until end of turn" &&
        shuffle == "if you search your library this way, shuffle" then
      let artifactCreature :=
        [
          .cardType .artifact,
          .cardType .creature,
          .manaValueAtMost .x]
      let found (zone : Selector) : CardAction :=
        .defineSelectorVariable n
          (.selected (.controller .this) (.range 1 1)
            (.intersection (zone :: artifactCreature)))
      let enter : List CardAction := [
        .putOntoBattlefield (.variable n),
        .putCounter (.variable n) .plusOnePlusOne .x,
        .if (.greaterOrEqual .x (.nat 4))
          [.continuous [.gainAbility (.variable n) (.keyword .haste)] .endOfTurn]]
      some ([
        .playerSelectAction (.controller .this) (.range 1 1) [
          .searchLibraryThenShuffle (.controller .this)
            (found (.union [.inLibrary, .inGraveyard]) :: enter),
          .sequence (found .inGraveyard :: enter)]],
        n + 1)
    else none
  | _ => none

/-- `Return target spell to its owner's hand. If the gift was promised, players can't cast spells this turn.`
The spell is target `n`. Promising the gift is an event since the start of
the game (CR 702.174k). Players can't cast spells until end of turn only
when that event has occurred. -/
def parseReturnSpellIfGiftCantCast (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match sentences text with
  | [ret, lock] =>
    if sentenceIs ret "return target spell to its owner's hand" &&
        sentenceIs lock
          "if the gift was promised, players can't cast spells this turn" then
      some ([
        .returnToHand (.target n .spell),
        .if (.happened (.giftPromised .this) .gameStart) [
          .continuous [.forbid (.castSpell .all)] .endOfTurn]
      ], n + 1)
    else none
  | _ => none

/-- Every sentence of `text` must parse. An unrecognized sentence fails
the text. No sentences (reminder-only or empty text) succeeds with no actions.
Multi-sentence templates are tried before the sentence split. -/
def actionsFromText (cardName : String) (text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let oneAction (parsed : Option (CardAction × Nat)) : Option (List CardAction × Nat) :=
    parsed.map fun (action, n') => ([action], n')
  parseReturnSpellIfGiftCantCast text n <|>
    parseVisionQuest text n <|>
    parseExileAttackersSearchBasics text n <|>
    parseLookAtTopExileFaceDownPlayIf text n <|>
    parseCounterExilePermanentMayCast text n <|>
    parseCounterThenRecruitIfMv text n <|>
    parsePlusOneThenEachOtherIfFromGy text n <|>
    parseInsteadFromGraveyard text n <|>
    parsePlusOneThenFight text n <|>
    parseAddManaCombination text n <|>
    oneAction (parseDealDamageExileIfDies cardName text n) <|>
    oneAction (parsePumpExileIfDies text n) <|>
    oneAction (parsePutPlusOneThenGains text n) <|>
    List.foldlM (fun (acc, n) s =>
      (parseSentence cardName s n).map fun (a, n') => (acc ++ [a], n'))
      ([], n) (sentences text)

end OracleParts

end Mtg.Engine
