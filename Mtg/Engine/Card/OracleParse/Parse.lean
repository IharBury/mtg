import Mtg.Engine.Card.OracleParse.CatalogLines
import Mtg.Engine.Card.OracleParse.Numbering

/-!
# Oracle lines

One Oracle line, a mode list, or an Adventure face. `parseOracleParts`
reads the whole text and fails when any part is not recognized.
-/

namespace Mtg.Engine

namespace OracleParts

/-- A triggered ability whose effect is a `choose one —` list: the trigger
event, or `none` when `line` is not such a header. -/
def triggeredChooseOne? (cardName line : String) : Option Trigger :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm effect == "choose one —" then parseTriggerEvent cardName clause else none

/-- One mode of a catalog modal ability. -/
def parseCatalogMode (cardName text : String) (n : Nat) : Option (CardAction × Nat) :=
  parseModeAction cardName text n <|> parseCatalogEffect cardName text n <|>
    (afterAbilityWord? text).bind fun rest =>
      parseModeAction cardName rest n <|> parseCatalogEffect cardName rest n

/-- `<this> can't be blocked if her/his/its/their power is N or less.` -/
def parseCantBeBlockedIfOwnPower (cardName line : String) : Option CardPart :=
  (split2? (normLine line) " can't be blocked if ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      let power? :=
        after? rest "her power is " <|> after? rest "his power is " <|>
          after? rest "its power is " <|> after? rest "their power is "
      (power?.bind (before? · " or less")).bind positiveCount |>.map fun p =>
        .ability (.static (.if
          (.lessOrEqual (.greatestPower (.source .this)) (.int p))
          [.forbid (.block .any (.source .this))]))

/-- `Whenever you cast a noncreature spell, you may draw X cards, where X is
the amount of mana spent to cast that spell. If you do, discard two cards.`
The spell is trigger `n`. Drawing is action `n`, and X is the greatest
amount of mana spent to cast a spell matching that trigger (CR 601.2h),
not its mana value. One spell is that amount. Discarding two cards
happens only when that draw is taken. -/
def parseCastNoncreatureMayDrawManaSpent (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    match (sentences effect).map normSentence with
    | [may, ifYouDo] =>
      if norm clause != "you cast a noncreature spell" ||
          may != "you may draw x cards, where x is the amount of mana spent to cast that spell" ||
          ifYouDo != "if you do, discard two cards" then none
      else
        some (
          .ability (.triggered
            (.triggerId n
              (.castSpell (.intersection [
                .spell, .not (.cardType .creature), youControl])))
            (.sequence [
              .optional (.controller .this)
                (.actionId n
                  (.draw (.controller .this)
                    (.greatestManaSpent (.wasArgumentOfTrigger n 1)))),
              .if (.happened (.actionWithId n) .gameStart)
                [.discard (.controller .this) 2]])),
          n + 1)
    | _ => none

/-- `Whenever you cast a creature spell, put X +1/+1 counters on target
creature you control, where X is that spell's mana value.` The spell is
trigger `n` and the creature is target `n`. -/
def parseCastCreaturePutCountersEqualMv (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm clause != "you cast a creature spell" ||
        normSentence effect !=
          "put x +1/+1 counters on target creature you control, where x is that spell's mana value" then
      none
    else
      some (
        .ability (.triggered
          (.triggerId n (.castSpell (.intersection [.spell, .cardType .creature, youControl])))
          (.putCounter
            (.target n (.intersection [.zone .battlefield, .cardType .creature, youControl]))
            .plusOnePlusOne
            (.greatestManaValue (.wasArgumentOfTrigger n 1)))),
        n + 1)

/-- `Whenever this creature attacks, you may sacrifice another creature. If
you do, put a number of +1/+1 counters on this creature equal to the
sacrificed creature's power.` The sacrifice is action `n`. -/
def parseAttackMaySacrificePlusOneEqualPower (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    match (sentences effect).map normSentence with
    | [may, result] =>
      if may == "you may sacrifice another creature" &&
          result == "if you do, put a number of +1/+1 counters on this creature equal to the sacrificed creature's power" then
        some (
          .sequence [
            .optional (.controller .this)
              (.actionId n
                (.sacrifice
                  (.selected (.controller .this) (.range 1 1)
                    (.intersection [.not .this, .zone .battlefield, .cardType .creature, youControl])))),
            .if (.happened (.actionWithId n) .gameStart)
              [.putCounter (.source .this) .plusOnePlusOne
                (.greatestPower (.wasObjectOfAction n))]],
          n + 1)
      else none
    | _ => none

/-- `When <this> enters, put a hone counter on <this> for each creature target
opponent controls. Attach <this> to up to one target creature you control.`
The opponent is target `n`. The creature is target `n + 1`. -/
def parseEnterHonePerOppAttach (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences (rulesText line) with
  | [entered, attach] =>
    let attachWho :=
      (after? (normSentence attach) "attach ").bind
        (before? · " to up to one target creature you control")
    onEnterN cardName entered fun effect =>
      (after? (norm effect) "put a hone counter on ").bind
        (before? · " for each creature target opponent controls") |>.bind fun who =>
          match attachWho with
          | some whom =>
            if refersToSelf cardName who && refersToSelf cardName whom then
              some (
                .sequence [
                  .putCounter (.source .this) (.hone)
                    (.count
                      (.intersection [
                        .zone .battlefield,
                        .cardType .creature,
                        .controlled (.target n (.opponent (.controller .this)))])),
                  .attach .this
                    (.targets (n + 1) (.range 0 1)
                      (.intersection [.zone .battlefield, .cardType .creature, youControl]))],
                n + 2)
            else none
          | none => none
  | _ => none

/-- `<this> enters with a hope counter on it for each creature you control`,
or `<this> enters with X +1/+1 counters on it`. Both replace how this enters. -/
def parseEntersWithCounters (cardName line : String) : Option CardPart :=
  let s := normLine line
  let hope :=
    (before? s " enters with a hope counter on it for each creature you control").bind
      fun who =>
        if !refersToSelf cardName who then none
        else
          some (.ability (.static (.replace (.enter .this) [
            .putCounter (.source .this) (.hope)
              (.count
                (.intersection [
                  .zone .battlefield,
                  .cardType .creature,
                  youControl])),
            .keepReplacedAction])))
  let plus :=
    (before? s " enters with x +1/+1 counters on it").bind fun who =>
      if !refersToSelf cardName who then none
      else
        some (.ability (.static (.replace (.enter .this) [
          .putCounter (.source .this) .plusOnePlusOne .x,
          .keepReplacedAction])))
  hope <|> plus

/-- `At the beginning of your end step, remove a hope counter from this
enchantment. If you do, draw a card. Then if this enchantment has no hope
counters on it, sacrifice it and you gain 4 life.` The removal is action `n`. -/
def parseEndStepRemoveHopeDrawSac (line : String) (n : Nat) : Option (CardPart × Nat) :=
  match (sentences (rulesText line)).map normSentence with
  | [remove, draw, thenSac] =>
    if remove == "at the beginning of your end step, remove a hope counter from this enchantment" &&
        draw == "if you do, draw a card" &&
        thenSac == "then if this enchantment has no hope counters on it, sacrifice it and you gain 4 life" then
      some (
        .ability (.triggered (.endStep (.controller .this)) (.sequence [
          .actionId n (.removeCounter (.source .this) (.hope) (.int 1)),
          .if (.happened (.actionWithId n) .gameStart) [
            .draw (.controller .this) (.int 1),
            .if (.not (.any (.intersection [.source .this, .hasCounter (.hope)]))) [
              .sacrifice (.source .this),
              .gainLife (.controller .this) (.int 4)]]])),
        n + 1)
    else none
  | _ => none

/-- `At the beginning of combat on your turn, put a trample counter on up to
one target creature you control. It becomes a Bear in addition to its other
types. Then if you control three or more Bears, draw two cards.` -/
def parseBeornCombat (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if normLine line !=
      "at the beginning of combat on your turn, put a trample counter on up to one target creature you control. it becomes a bear in addition to its other types. then if you control three or more bears, draw two cards" then
    none
  else
    some ([.ability (.triggered (.combatStart (.controller .this)) (.sequence [
      .putCounter
        (.targets n (.range 0 1)
          (.intersection [.zone .battlefield, .cardType .creature, youControl]))
        .trample 1,
      .continuous [.gainSubtype (.targetReference n) .bear] .endOfGame,
      .if (.greaterOrEqual
          (.count (.intersection [.zone .battlefield, .subtype .bear, youControl]))
          3)
        [.draw (.controller .this) 2]]))], n + 1)

/-- Bolg's enter ability, including the reflexive “when you do”.
The sacrificed creature's power is recorded before it leaves the
battlefield (CR 608.2h). Bolg deals that much damage. -/
def parseBolgEnters (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.enter .this) then none
    else if norm effect !=
        "you may sacrifice another creature. when you do, bolg deals damage equal to that creature's power to another target creature. if excess damage was dealt this way, amass goblins x, where x is that excess damage" then
      none
    else
      let chosen := n
      let power := n + 1
      let damage := n + 2
      let another :=
        .selected (.controller .this) (.range 1 1)
          (.intersection [.not .this, .zone .battlefield, .cardType .creature, youControl])
      some ([.ability (.triggered (.enter .this) (.sequence [
        .optional (.controller .this) (.sequence [
          .defineSelectorVariable chosen another,
          .defineValueVariable power (.greatestPower (.variable chosen)),
          .actionId chosen (.sacrifice (.variable chosen))]),
        .reflexive chosen [
          .actionId damage
            (.dealDamage .this
              (.target chosen
                (.intersection [
                  .not (.wasObjectOfAction chosen), .zone .battlefield, .cardType .creature]))
              (.variable power)),
          .if (.happened (.actionWithIdDealtExcessDamage damage) .gameStart) [
            .keyword (.controller .this)
              (.amass .goblin (.excessDamageOfActionWithId damage))]]]))],
        damage + 1)

/-- `Whenever you attack with creatures with total power 12 or greater for the
first time each turn, untap all attacking creatures. After this phase, there
is an additional combat phase.`
The static `+2/+0 for each Mountain` line is the shared grammar. -/
def parseAttackTotalPowerExtraCombat (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if normLine line !=
      "whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. after this phase, there is an additional combat phase" then
    none
  else
    let attacking :=
      .intersection [.zone .battlefield, .cardType .creature, .attacking .all]
    -- Total power is a predicate of the attack, so the ability does not
    -- trigger when that total is lower. It is not checked again on resolution.
    -- “For the first time each turn” is the first such attack since turn start.
    some ([.ability (.triggered
      (.ordinal 1 .turnStart
        (.attackSimultaneously creaturesYouControl .all [.totalPowerAtLeast 12]))
      (.sequence [
        .untap attacking,
        .addPhaseAfterThisPhase .combat]))], n)

/-- Sentences of `line` except a trailing “this ability triggers only once
each turn”. -/
def onceEachTurn? (line : String) : Option (List String) :=
  match sentences line with
  | [] => none
  | ss =>
    match ss.getLast? with
    | some last =>
      if sentenceIs last "this ability triggers only once each turn" then
        some ss.dropLast
      else none
    | none => none

/-- `Whenever <this> enters or attacks, put a hone counter on each Equipment
you control.` The reminder that each hone counter grants +1/+0 is not rules
text. -/
def parseHoneEachEquipment (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.or (.enter .this) (.attack .this .all)) then
      none
    else if normSentence effect != "put a hone counter on each equipment you control" then none
    else
      some ([.ability (.triggered
        (.or (.enter .this) (.attack .this .all))
        (.putCounter
          (.intersection [.zone .battlefield, .subtype .equipment, youControl])
          .hone 1))], n)

/-- `When <this> enters, create a colorless Equipment artifact token named Axe
with "Equipped creature gets +1/+0" and equip {2}. When you do, attach it to
target creature you control.` The create is numbered. “When you do” is a
reflexive trigger of that action (CR 603.12), not an “if you do” in the same
resolution. -/
def parseCreateAxeWhenYouDo (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.enter .this) then none
    else
      (before? effect ". When you do, attach it to target creature you control").bind
        fun createText =>
          (split2? createText " named ").bind fun (lead, rest) =>
            (split2? rest " with \"").bind fun (tokenName, afterName) =>
              (split2? afterName "\" and ").bind fun (quoted, equipText) =>
                if norm lead != "create a colorless equipment artifact token" ||
                    tokenName != "Axe" then none
                else
                  match parseEquippedGets quoted, parseEquip equipText with
                  | some quotedParts, some equipPart =>
                    let parts :=
                      [.name tokenName, .type .artifact, .subtype .equipment,
                        .colorIndicator []] ++ quotedParts ++ [equipPart]
                    some ([.ability (.triggered (.enter .this) (.sequence [
                      .actionId n (.createTokens (.controller .this) 1 parts),
                      .reflexive n [
                        .attach (.wasCreatedByAction n)
                          (.target n (.intersection [
                            .zone .battlefield, .cardType .creature, youControl]))]]))],
                      n + 1)
                  | _, _ => none

/-- `Whenever <this> attacks, each equipped attacking creature gains double
strike until end of turn.`
An equipped creature is the host of an Equipment. -/
def parseEquippedAttackersDoubleStrike (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.attack .this .all) then none
    else if normSentence effect !=
        "each equipped attacking creature gains double strike until end of turn" then none
    else
      some ([.ability (.triggered (.attack .this .all)
        (.continuous [
          .gainAbility
            (.intersection [
              .zone .battlefield, .cardType .creature, .attacking .all,
              .hostOf (.intersection [.zone .battlefield, .subtype .equipment])])
            (.keyword .doubleStrike)]
          .endOfTurn))], n)

/-- `Whenever you activate an ability of a creature, draw a card. This ability
triggers only once each turn.` -/
def parseActivateCreatureDrawOnce (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  match onceEachTurn? line with
  | some [draw] =>
    if normSentence draw != "whenever you activate an ability of a creature, draw a card" then
      none
    else
      -- “You” is this ability's controller. Another player's activation
      -- is not this event. “This ability triggers only once each turn” is
      -- the first such activation since turn start.
      some ([.ability (.triggered
        (.ordinal 1 .turnStart
          (.activateAbility (.controller .this)
            (.intersection [.zone .battlefield, .cardType .creature])))
        (.draw (.controller .this) 1))], n)
  | _ => none

/-- `{5}{U}{U}: Exile up to two other target nonland permanents you control.
Return those cards to the battlefield under their owner's control at the
beginning of the next end step.`
The exile is action `n`. Resolving this ability creates a delayed triggered
ability (CR 603.7). That ability puts those cards onto the battlefield the
next time an end step begins (CR 603.7b), under their owner's control. -/
def parseExileReturnEndStep (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (parsePrintedCosts cardName costText).bind fun costs =>
      if norm effect !=
          "exile up to two other target nonland permanents you control. return those cards to the battlefield under their owner's control at the beginning of the next end step" then
        none
      else
        some ([.ability (.activated costs
          (.sequence [
            .actionId n
              (.exile
                (.targets n (.range 0 2)
                  (.intersection [
                    .not .this, .zone .battlefield, .not (.cardType .land), youControl]))),
            .delayedTrigger (.endStep .player)
              [.putOntoBattlefield (.wasCreatedByAction n)]]))], n + 1)

/-- `When this artifact is put into a graveyard from the battlefield, reveal
the top thirteen cards of your library. Put a random creature card from among
them onto the battlefield. Put the rest on the bottom of your library in a
random order.`
The reveal is action `n`. The random creature is variable `n + 1`:
`defineSelectorVariable` of `Selector.chooseRandom` of the creature cards
among those revealed cards. Later actions use that variable. -/
def parseRevealRandomCreature (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if normLine line !=
      "when this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. put a random creature card from among them onto the battlefield. put the rest on the bottom of your library in a random order" then
    none
  else
    let creature := n + 1
    some ([.ability (.triggered (.putToGraveyard .this) (.sequence [
      .actionId n (.reveal (.topOfLibrary (.controller .this) 13)),
      .defineSelectorVariable creature
        (.chooseRandom
          (.intersection [.wasObjectOfAction n, .cardType .creature])),
      .putOntoBattlefield (.variable creature),
      .putOnLibraryBottomInRandomOrder
        (.intersection [.wasObjectOfAction n, .not (.variable creature)])]))], n + 2)

/-- `As <this> enters, choose odd or even.` A reminder that zero is even is
not rules text. The choice is variable `n`: 0 is even and 1 is odd.
The counter stays `n` so the following trigger can name that same
variable. That trigger reserves the next number for the spell. -/
def parseChooseOddEven (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  let s := (after? (normLine line) "as ").getD (normLine line)
  let lead :=
    (before? s " enters, choose odd or even").bind fun who =>
      if refersToSelf cardName who then some () else none
  if lead.isSome then
    some ([.ability (.static (.replace (.enter .this)
      [.chooseOddEven n (.controller .this), .keepReplacedAction]))], n)
  else none

/-- `If a creature an opponent controls would die, exile it instead. When you
do, create a 2/2 green Wolf creature token.` The exile is numbered. “When you
do” is a reflexive trigger of that replacement (CR 603.12). The die event
never happens (CR 614.6). -/
def parseExileOppDeathWolf (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if normLine line !=
      "if a creature an opponent controls would die, exile it instead. when you do, create a 2/2 green wolf creature token" then
    none
  else
    let oppCreature :=
      .intersection [
        .zone .battlefield, .cardType .creature,
        .controlled (.opponent (.controller .this))]
    some ([.ability (.static (.replace (.die oppCreature) [
      .actionId n (.exile .replacingObject),
      .reflexive n [
        .createTokens (.controller .this) 1 [
          .type .creature, .subtype .wolf, .colorIndicator [.green],
          .power 2, .toughness 2]]]))], n + 1)

/-- `{cost}, {T}, Discard a legendary card with the same name as a legendary
permanent you control: Draw two cards.` The discarded card is one legendary
card from a hand. It shares a name with a legendary permanent this object's
controller controls (CR 201.2). -/
def parseDiscardLegendaryDraw (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    if normSentence effect != "draw two cards" then none
    else
      let parts := costText.splitOn ", " |>.map copied |>.filter (· != "")
      match parts with
      | [manaText, tapText, discardText] =>
        if norm tapText != "{t}" ||
            norm discardText !=
              "discard a legendary card with the same name as a legendary permanent you control" then
          none
        else
          let legendaryYouControl :=
            .intersection [.zone .battlefield, .supertype .legendary, youControl]
          (nonemptyMana? manaText).bind fun syms =>
            some ([.ability (.activated
              [.mana syms, .tapSymbol,
               .discard (.selected (.controller .this) (.range 1 1)
                 (.intersection [
                   .zone .hand, .supertype .legendary, .owner (.controller .this),
                   .sharesNameWith legendaryYouControl]))]
              (.draw (.controller .this) 2))], n)
      | _ => none

/-- `Whenever a Mountain you control enters, put a quest counter on this
enchantment. If it has six or more quest counters on it, sacrifice it. If
you do, search your hand and/or library for a Dragon card and put it onto
the battlefield. If you search your library this way, shuffle.`
The sacrifice is action `n`. “If you do” is that action having happened.
The search covers a hand and a library. Searching the library shuffles
(CR 701.19). -/
def parseMountainQuestDragon (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if normLine line !=
      "whenever a mountain you control enters, put a quest counter on this enchantment. if it has six or more quest counters on it, sacrifice it. if you do, search your hand and/or library for a dragon card and put it onto the battlefield. if you search your library this way, shuffle" then
    none
  else
    let mountain :=
      .intersection [.zone .battlefield, .subtype .mountain, youControl]
    some ([.ability (.triggered (.enter mountain) (.sequence [
      .putCounter (.source .this) .quest 1,
      .if (.greaterOrEqual (.counterCount (.source .this) .quest) 6) [
        .actionId n (.sacrifice (.source .this)),
        .if (.happened (.actionWithId n) .gameStart) [
          .searchHandOrLibrary (.controller .this) [
            .putOntoBattlefield
              (.selected (.controller .this) (.range 1 1) (.subtype .dragon))]]]]))], n + 1)

/-- Keyword, counter, and activated-ability lines. Tried before triggers. -/
private def parseOneLineHead (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  parseMountainQuestDragon line n <|>
    parseDiscardLegendaryDraw line n <|>
    parseExileOppDeathWolf line n <|>
    parseChooseOddEven cardName line n <|>
    parseRevealRandomCreature line n <|>
    parseAttackTotalPowerExtraCombat line n <|>
    parseBolgEnters cardName line n <|>
    parseBeornCombat line n <|>
    parseHoneEachEquipment cardName line n <|>
    parseCreateAxeWhenYouDo cardName line n <|>
    parseEquippedAttackersDoubleStrike cardName line n <|>
    parseActivateCreatureDrawOnce line n <|>
    parseExileReturnEndStep cardName line n <|>
    (keywordParts? line).map (·, n) <|>
    sole (parseDrawExceptFirstDrawStep line) n <|>
    sole (parseTwiceTokensYouWouldCreate line) n <|>
    carry (parseTokenEntersByResolveCount line n) <|>
    sole (parseCantBeBlockedIfOwnPower cardName line) n <|>
    sole (parseEntersWithCounters cardName line) n <|>
    carry (parseCastCreaturePutCountersEqualMv line n) <|>
    carry (parseAttackMaySacrificePlusOneEqualPower cardName line n) <|>
    carry (parseEnterHonePerOppAttach cardName line n) <|>
    carry (parseEndStepRemoveHopeDrawSac line n) <|>
    sole (parseEntersTapped cardName line) n <|>
    sole (parseEntersTappedUnlessEquipment cardName line) n <|>
    sole (parseTypecycling line) n <|>
    sole (parseHarness cardName line) n <|>
    parseInfinity cardName line n <|>
    carry (parseActivatedAbility cardName line n) <|>
    parseActivatedCreateCostsLess cardName line n <|>
    carry (parseActivatedDiscardDraw cardName line n) <|>
    carry (parseActivatedAddOrLoot cardName line n) <|>
    sole (parseTapAddOneOf line) n <|>
    carry (parseTapAddAnyColorEqualToPower cardName line n) <|>
    sole (parseAnotherElfEntersGets line) n <|>
    carry (parseLandYouControlEnters line n) <|>
    sole (parseLandfallCreate line) n <|>
    (parseLandsCharacteristic cardName line).map (·, n) <|>
    (parseCreaturesPowerCharacteristic cardName line).map (·, n) <|>
    (parseCardsInHandPowerCharacteristic cardName line).map (·, n) <|>
    sole (parseCantBeCountered line) n <|>
    sole (parseCastAsThoughFlash line) n <|>
    (parseStaticGets line).map (·, n) <|>
    (parseOtherSubtypeYouControlGets line).map (·, n) <|>
    sole (parseCreaturesWithPlusOneHaveMenace line) n <|>
    sole (parseYouCastNoncreatureAmass line) n <|>
    sole (parseYouCastNoncreaturePumpAndDamage cardName line) n <|>
    carry (parseCastNoncreatureMayDrawManaSpent line n) <|>
    sole (parseYouCastSpellIfTreasureDrawLoseLife line) n

/-- Attack, enters, and other triggered lines. -/
private def parseOneLineMiddle (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  sole (parseYouAttackAmass line) n <|>
    sole (parseYouAttackRecruit line) n <|>
    sole (parseEnterOrAttackRecruit cardName line) n <|>
    sole (parseEnterAmass cardName line) n <|>
    sole (parseDiesAmass cardName line) n <|>
    sole (parseEnterSearchForest cardName line) n <|>
    carry (parseEnterSearchBasicToHand cardName line n) <|>
    carry (parseEnterDealDamageDestroyIfSubtype cardName line n) <|>
    sole (parseGraveyardReturn line) n <|>
    carry (parseOwnerShuffleDraw cardName line n) <|>
    carry (parseReturnFromGyAttach line n) <|>
    carry (parseEnterExileOppGyLoseLife cardName line n) <|>
    sole (parseEquipAbilitiesTargetingThisCostLess line) n <|>
    sole (parseCostReduction line) n <|>
    sole (parseCostLessByFlyingPower line) n <|>
    sole (parseInstantSorceryCostLessByEquippedPower line) n <|>
    sole (parseHasteIfAnother cardName line) n <|>
    sole (parseLifelinkIfAnother cardName line) n <|>
    sole (parseFirstEquipFreeIfEnduringStory line) n <|>
    sole (parseEnduringStoryGets cardName line) n <|>
    sole (parseEnduringStoryTeamGets line) n <|>
    sole (parseEnduringStoryTeamWard line) n <|>
    sole (parseEnduringStoryAttackTax line) n <|>
    sole (parseDoesntUntapUnlessEnduringStory cardName line) n <|>
    sole (parseThisOrNontokenSubtypeEntersCreate cardName line) n <|>
    sole (parseOpponentFirstNoncreatureRecruit line) n <|>
    sole (parseAttackTriggered line) n <|>
    carry (parseAttackTargetGains cardName line n) <|>
    carry (parseAttackDamageEqualTreasures cardName line n) <|>
    carry (parseAttackSetBasePT cardName line n) <|>
    sole (parseFerociousThisAttacks line) n <|>
    sole (parseFerociousYouAttack line) n <|>
    sole (parseFerociousBeginCombat line) n

/-- Enters, static, equipment, and spell lines, then the catalog grammar. -/
private def parseOneLineTail (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  carry (parseEnterGainLifeMaySearchBasicOnTop cardName line n) <|>
    sole (parseEnterYouGainLife cardName line) n <|>
    sole (parseThresholdGets cardName line) n <|>
    carry (parseEnterUntapPlusOneIfSubtype cardName line n) <|>
    sole (parseEnterRecruit cardName line) n <|>
    sole (parseDiesRecruit cardName line) n <|>
    sole (parseEnterScry cardName line) n <|>
    sole (parseEnterCreateTreasure cardName line) n <|>
    sole (parseEnterCreateNamedEquipment cardName line) n <|>
    sole (parseEnterCreateTappedTreasuresEqualOppArtifacts cardName line) n <|>
    carry (parseEnterLookAtTopReveal cardName line n) <|>
    carry (parseEnterExileTopMayPlay cardName line n) <|>
    carry (parseEnterPutPlusOneOnTarget cardName line n) <|>
    carry (parseEnterReturnOtherPlusOne cardName line n) <|>
    sole (parseEnterDraw cardName line) n <|>
    sole (parseEnterEachOpponentDiscards cardName line) n <|>
    carry (parseEnterDividedDamage cardName line n) <|>
    carry (parseEnterMayDiscardDraw cardName line n) <|>
    carry (parseEnterTargetOpponentSacrifices cardName line n) <|>
    carry (parseDiesOppGets cardName line n) <|>
    carry (parseOtherCreaturesDieScry line n) <|>
    sole (parseDrawSecondPlusOne line) n <|>
    sole (parseYouDrawPlusOne line) n <|>
    sole (parseCantBeBlockedByTokens cardName line) n <|>
    sole (parseCantBeBlockedByPower cardName line) n <|>
    sole (parseCantBeBlocked cardName line) n <|>
    sole (parseCantBlock cardName line) n <|>
    sole (parseBecomesTargetDraw cardName line) n <|>
    sole (parseFirstMainAddMana line) n <|>
    sole (parseCantAttackUnlessNOther cardName line) n <|>
    sole (parseAnotherSubtypeOrEquipmentEntersDraw line) n <|>
    sole (parseArtifactYouControlEntersDraw line) n <|>
    sole (parseUpkeepCreateCreature line) n <|>
    sole (parseYourEndStepDraw line) n <|>
    carry (parseEnterCreateThenAttach cardName line n) <|>
    carry (parseEnterAmassThenAttach cardName line n) <|>
    carry (parseEnterAttachToTarget cardName line n) <|>
    carry (parseEnterAttachTargetEquipment cardName line n) <|>
    sole (parseFlashback line) n <|>
    sole (parseKicker line) n <|>
    sole (parseSneak line) n <|>
    sole (parseAffinity line) n <|>
    sole (parseWard line) n <|>
    sole (parseCrew line) n <|>
    sole (parseTeamwork line) n <|>
    sole (parseGift line) n <|>
    sole (parseCombatDamageLoot cardName line) n <|>
    sole (parseAdditionalCostSacrificeCreature line) n <|>
    sole (parseAdditionalCostSacrificeOrPay line) n <|>
    carry (parseEnchant line n) <|>
    (parseEquippedHasAndCantBeBlocked line).map (·, n) <|>
    (parseEquippedGets line).map (·, n) <|>
    sole (parseEquipPayLife line) n <|>
    sole (parseEquip line) n <|>
    spellActions (actionsFromText cardName line n) <|>
    parseCatalogLine cardName line n <|>
    (afterAbilityWord? line).bind (parseCatalogLine cardName · n)

/-- One non-empty Oracle line. A reminder-only line contributes no parts.
Anything else that the grammar does not cover fails.
The first parser that accepts the line wins. -/
@[noinline]
def parseOneLine (cardName : String) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if (rulesText line).isEmpty then some ([], n)
  else
    parseOneLineHead cardName line n <|>
      parseOneLineMiddle cardName line n <|>
      parseOneLineTail cardName line n

/-- `Landfall — Whenever a land you control enters, choose one —`.
`Landfall` may be omitted. The em dash after `choose one` keeps this from
being only an ability-word line. -/
def landfallChooseOne? (line : String) : Bool :=
  let choose := landYouControlEnters ++ "choose one —"
  match after? (normLine line) "landfall — " with
  | some rest => rest == choose
  | none => normLine line == choose

/-- How a list of `•` modes after a header becomes card parts, and how one
mode is read. -/
structure ModeList where
  wrap : List CardAction → List CardPart
  mode : String → Nat → Option (CardAction × Nat)

/-- `<trigger>, choose up to X —`. The controller chooses up to X distinct modes.
`X` is the value of X (CR 107.3). -/
def chooseUpToXModes (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes :=
    [.ability (.triggered trigger (.chooseUniqueModes (.range (.int 0) .x) modes))]
  mode := parseCatalogMode cardName

/-- A triggered “choose one —” ability: exactly one mode (CR 700.2). -/
def triggeredModes (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes := [.ability (.triggered trigger (.chooseUniqueModes (.range 1 1) modes))]
  mode := parseCatalogMode cardName

/-- `<trigger>, choose one that hasn't been chosen —`. Mode `i` may be chosen
only if no player chose it since `since`. `.turnStart` is “this turn”.
`.gameStart` is “hasn't been chosen” with no turn limit. -/
def restrictedModesSince (since : Trigger) (cardName : String) (trigger : Trigger) : ModeList where
  wrap modes :=
    [.ability (.triggered trigger (.chooseModeRestricted (.controller .this)
      ((List.range modes.length).zip modes |>.map fun (i, action) =>
        (i + 1, .not (.happened (.modeWithIdChosen .player (i + 1)) since), [action]))))]
  mode := parseCatalogMode cardName

/-- `<trigger>, choose one that hasn't been chosen this turn —`. Mode `i` may be
chosen only if no player chose it this turn. -/
def restrictedModes (cardName : String) (trigger : Trigger) : ModeList :=
  restrictedModesSince .turnStart cardName trigger

/-- Gollum's modal trigger. `parity` is the `chooseOddEven` variable:
0 is even and 1 is odd. `spell` numbers the cast trigger so the spell
is its first selector argument. The spell's mana value has the chosen
quality when the remainder of that mana value divided by 2 equals
`parity`. -/
def gollumParityModes (cardName : String) (parity spell : Nat) : ModeList where
  wrap modes :=
    [.ability (.triggeredWhile
      (.triggerId spell
        (.castSpell (.intersection [
          .spell,
          .controlled (.opponent (.controller .this))])))
      (.equal
        (.remainder (.greatestManaValue (.wasArgumentOfTrigger spell 1)) 2)
        (.variable parity))
      (.chooseModeRestricted (.controller .this)
        ((List.range modes.length).zip modes |>.map fun (i, action) =>
          (i + 1, .not (.happened (.modeWithIdChosen .player (i + 1)) .gameStart), [action]))))]
  mode := parseCatalogMode cardName

/-- `Choose up to two. Return those cards from your graveyard to your hand.`
Each mode is `Target <type> card.`, a card in your graveyard. -/
def chooseUpToReturnModes (k : Nat) : ModeList where
  wrap modes :=
    [.actions [.playerSelectAction (.controller .this) (.range 0 (Value.int k))
      (modes.map fun sel => sel)]]
  mode text n :=
    (between? (normSentence text) "target " " card").bind typeOfOracle? |>.map fun t =>
      (.returnToHand (.target n (.intersection [.zone .graveyard, .cardType t, .owner (.controller .this)])),
        n + 1)

/-- A header whose `•` modes follow, and how many numbers that header
reserves after `n`. The headers are a triggered `choose one —`, a triggered
`choose one that hasn't been chosen this turn —` (after an ability word), a
triggered `choose up to X —`, or
`Choose up to N. Return those cards from your graveyard to your hand.`
`chooseOddEven` leaves the counter on its variable, so Gollum's header
uses `n` for that variable and `n + 1` for the spell. -/
def modeListHeader? (cardName line : String) (n : Nat) : Option (ModeList × Nat) :=
  let gollum :=
    if normLine line ==
        "whenever an opponent casts a spell with mana value of the chosen quality, choose one that hasn't been chosen —" then
      some (gollumParityModes cardName n (n + 1), 2)
    else none
  let line' := (afterAbilityWord? line).getD line
  let restricted :=
    (splitTrigger? line').bind fun (clause, effect) =>
      if norm effect == "choose one that hasn't been chosen this turn —" then
        (parseTriggerEvent cardName clause).map (restrictedModes cardName)
      else if norm effect == "choose up to x —" then
        (parseTriggerEvent cardName clause).map (chooseUpToXModes cardName)
      else none
  let returnCards :=
    (between? (normLine line) "choose up to " ". return those cards from your graveyard to your hand").bind
      positiveCount |>.map chooseUpToReturnModes
  gollum <|>
    ((triggeredChooseOne? cardName line).map fun t => (triggeredModes cardName t, 0)) <|>
    (restricted.map (·, 0)) <|>
    (returnCards.map (·, 0))

/-- `Power-up — <cost>: <effect>` (CR 702.193). The ability is number `n'`,
the next number after its effect. It may be activated only if it has not
been activated since the game began. While this permanent entered this
turn, the ability costs `manaCost`, this card's mana cost, less. `.this` in
that reduction is the ability, so the permanent is its source. A card with
no mana cost is not recognized. -/
def parsePowerUp (cardName : String) (manaCost : List ManaSymbol) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  if manaCost.isEmpty then none
  else
    (after? (rulesText line) "Power-up — ").bind fun rest =>
      (parseOneLine cardName rest n).bind fun
        | ([.ability (.activated costs action)], n') =>
          some ([.ability (.abilityId n' (.activatedWithStaticIf
            (.not (.happened (.abilityWithIdActivated n') .gameStart)) costs action
            (.if (.happened (.enter (.source .this)) .turnStart)
              [.reduceCost .this [.mana manaCost]])))], n' + 1)
        | _ => none

/-- One line outside a mode list. -/
def parseLine (cardName : String) (manaCost : List ManaSymbol) (line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  parsePowerUp cardName manaCost line n <|> parseOneLine cardName line n

mutual
/-- Lines outside a `Choose one —` list. `parseModeLines` reads the list. -/
def parseBodyLines (cardName : String) (manaCost : List ManaSymbol) :
    List String → Nat → Option (List CardPart × Nat)
  | [], n => some ([], n)
  | line :: rest, n =>
    if landfallChooseOne? line then
      parseListedModes cardName manaCost (triggeredModes cardName (.enter landsYouControl))
        rest n []
    else
      match modeListHeader? cardName line n with
      | some (list, reserved) =>
        parseListedModes cardName manaCost list rest (n + reserved) []
      | none =>
      match chooseHeader? line with
      | some orBoth => parseModeLines cardName manaCost rest n [] orBoth
      | none =>
        let oneLine (more : Nat → Option (List CardPart × Nat)) :=
          (parseLine cardName manaCost line n).bind fun (here, nHere) =>
            (more nHere).map fun (more, nMore) => (here ++ more, nMore)
        match rest with
        | [] => oneLine (parseBodyLines cardName manaCost [])
        | gets :: after =>
          ((parseAsEntersChooseCreatureType cardName line gets n).bind fun (here, nHere) =>
            (parseBodyLines cardName manaCost after nHere).map fun (more, nMore) =>
              (here ++ more, nMore)) <|>
            oneLine (parseBodyLines cardName manaCost (gets :: after))

/-- Bullet modes after a header such as a landfall “choose one —” line.
A bullet that does not parse fails. No bullets fails rather than dropping
the printed choice. A later non-bullet ends the list. -/
def parseListedModes (cardName : String) (manaCost : List ManaSymbol) (list : ModeList)
    (lines : List String) (n : Nat) (acc : List CardAction) : Option (List CardPart × Nat) :=
  let modesPart := list.wrap
  match lines with
  | [] =>
    match acc with
    | [] => none
    | modes => some (modesPart modes, n)
  | line :: rest =>
    match stripModeBullet line with
    | some text =>
      (list.mode text n).bind fun (action, n') =>
        parseListedModes cardName manaCost list rest n' (acc ++ [action])
    | none =>
      match acc with
      | [] => none
      | modes =>
        (parseLine cardName manaCost line n).bind fun (here, nHere) =>
          (parseBodyLines cardName manaCost rest nHere).map fun (more, nMore) =>
            (modesPart modes ++ here ++ more, nMore)

/-- `•` modes after `Choose one —` or `Choose one or both —`.
A later non-mode line ends the list.
No parsed modes fails rather than dropping the printed choice. -/
def parseModeLines (cardName : String) (manaCost : List ManaSymbol) (lines : List String)
    (n : Nat) (acc : List CardAction) (orBoth : Bool) : Option (List CardPart × Nat) :=
  match lines with
  | [] => (chooseOneParts acc orBoth).map fun parts => (parts, n)
  | line :: rest =>
    match stripModeBullet line with
    | some text =>
      (parseCatalogMode cardName text n).bind fun (action, n') =>
        parseModeLines cardName manaCost rest n' (acc ++ [action]) orBoth
    | none =>
      (chooseOneParts acc orBoth).bind fun head =>
        match chooseHeader? line with
        | some nested =>
          (parseModeLines cardName manaCost rest n [] nested).map fun (more, nMore) =>
            (head ++ more, nMore)
        | none =>
          (parseLine cardName manaCost line n).bind fun (here, nHere) =>
            (parseBodyLines cardName manaCost rest nHere).map fun (more, nMore) =>
              (head ++ here ++ more, nMore)
end

/-- Oracle lines, including `Choose one —` lists. `manaCost` is this card's
mana cost. -/
def parseMainLines (cardName : String) (manaCost : List ManaSymbol) (lines : List String)
    (n : Nat) : Option (List CardPart × Nat) :=
  parseBodyLines cardName manaCost lines n

def nameOfParts (parts : List CardPart) : Option String :=
  parts.findSome? fun
    | .name n => some n
    | _ => none

/-- Leading `sacrifice a creature` additional-cost lines, and the lines left. -/
def peelLeadingSacrificeCreatureCosts (lines : List String) :
    List CardPart × List String :=
  match lines with
  | [] => ([], [])
  | line :: rest =>
    match parseAdditionalCostSacrificeCreature line with
    | some part =>
      let (more, left) := peelLeadingSacrificeCreatureCosts rest
      (part :: more, left)
    | none => ([], lines)

/-- A Gatherer Adventure face: `Name {cost}`, a type line, then rules text.
A missing name or cost, a line that is not a type line, or effect text the
grammar does not cover makes the parse fail. No effect lines is a face
with no spell effect. A leading sacrifice-a-creature additional cost is an
ability of the face. `Draw a card` is that face's effect only after such a
cost; a draw with no other text stays unrecognized. A lone sentence that
creates creature tokens is also an effect. -/
def parseAdventure (cardName : String) (lines : List String) (n : Nat) :
    Option (List CardPart) :=
  match lines with
  | [] => none
  | nameLine :: rest =>
    (parseNameAndCost nameLine).bind fun nameParts =>
      match rest with
      | [] => some nameParts
      | typeLine :: effectLines =>
        (parseTypeLine typeLine).bind fun typeParts =>
          -- An Adventure face refers to itself by its own name.
          let faceName := nameOfParts nameParts |>.getD cardName
          match effectLines with
          | [] => some (nameParts ++ typeParts)
          | _ =>
            let (costParts, restLines) := peelLeadingSacrificeCreatureCosts effectLines
            let text := String.intercalate " " restLines
            let tokens :=
              match sentences text with
              | [one] => (parseCreateCreatureTokens one).map fun action => ([action], n)
              | _ => none
            let actions? : Option (List CardAction) :=
              if restLines.isEmpty then some []
              else
                match actionsFromText faceName text n <|> tokens with
                | some (actions, _) =>
                  if actions.isEmpty then none else some actions
                | none =>
                  if costParts.isEmpty then none
                  else (parseDrawCards (rulesText text)).map fun action => [action]
            actions?.map fun actions =>
              let actionParts :=
                if actions.isEmpty then [] else [.actions actions]
              nameParts ++ typeParts ++ costParts ++ actionParts

/-- Successive spell lines are one effect, in printed order. -/
def mergeConsecutiveActions (parts : List CardPart) : List CardPart :=
  go parts []
where
  go : List CardPart → List CardPart → List CardPart
    | [], acc => acc.reverse
    | .actions here :: rest, .actions earlier :: acc =>
      go rest
        (.actions (earlier.flatMap flattenAction ++ here.flatMap flattenAction) :: acc)
    | part :: rest, acc => go rest (part :: acc)

end OracleParts

open OracleParts

/-- Parse printed Oracle text into `CardPart`s.
The patterns this accepts are the module's recognized Oracle text.
`name` is the card being parsed. Text that uses that name, the short name
before a comma (CR 201.5), or that name's first word when it is not an
article, means this card, as do `this` and `this <type>`.
`Gollum the Abandoned` refers to itself as `Gollum`.
Returns `none` when a line, sentence, mode, or Adventure face is not
recognized. Reminder parentheticals are not rules text. Empty text is
`some []`. Successive spell lines are one effect, in printed order.
`manaCost` is the card's printed mana cost. Only abilities that refer to
that cost, such as power-up, read it.
Action ids and target numbers are separate sequences. Each starts at 1. -/
def parseOracleParts (name : String) (text : String) (manaCost : List ManaSymbol := []) :
    Option (List CardPart) :=
  let lines :=
    text.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (· != "")
  let (main, adv) := splitAdventure lines
  (parseMainLines name manaCost main 1).bind fun (mainParts, n) =>
    let mainParts := mergeConsecutiveActions mainParts
    match adv with
    | [] => some (separateActionIds mainParts)
    | _ =>
      (parseAdventure name adv n).map fun alt =>
        separateActionIds (mainParts ++ [.alternative alt])

end Mtg.Engine
