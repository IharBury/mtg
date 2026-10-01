import Mtg.Engine.Card.OracleParse.CatalogLines

/-!
# Remaining Hobbit lines

Oracle lines from The Hobbit whose printed text is not covered by the
shared grammar. Each line is the text on the card. A reminder
parenthetical is not rules text.
-/

namespace Mtg.Engine

namespace OracleParts

def lineIs (line expected : String) : Bool :=
  normLine line == expected

def creatureYouControl : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, youControl]

def opponentCreature : Selector :=
  .intersection [
    .zone .battlefield, .cardType .creature, .controlled (.opponent (.controller .this))]

def goblinOrcArmyYouControl : Selector :=
  .intersection [
    .zone .battlefield,
    .union [.subtype .goblin, .subtype .orc, .subtype .army],
    youControl]

def anotherCreatureYouSacrifice : Selector :=
  .selected (.controller .this) (.range 1 1)
    (.intersection [.not .this, .zone .battlefield, .cardType .creature, youControl])

def wolfToken : List CardPart := [
  .type .creature, .subtype .wolf, .colorIndicator [.green], .power 2, .toughness 2]

def birdSoldierToken : List CardPart := [
  .type .creature, .subtype .bird, .subtype .soldier, .colorIndicator [.white],
  .power 4, .toughness 4, .ability (.keyword .flying)]

def axeToken : List CardPart := [
  .name "Axe", .type .artifact, .subtype .equipment, .colorIndicator [],
  .ability (.static (.addPower (.hostOf .this) 1)),
  .ability (.keywordWithCost .equip [.mana [.generic 2]])]

def foodArtifactAbility : List CardPart := [
  .type .artifact, .subtype .food,
  .ability (.activated
    [.mana [.generic 2], .tapSymbol, .sacrifice .this]
    (.gainLife (.controller .this) 3))]

/-- One effect, repeated for each chapter number in `I, II —`. -/
def parseNumberedChapters (line : String) (n : Nat)
    (body : String → Nat → Option (List CardAction × Nat)) : Option (List CardPart × Nat) :=
  match (rulesText line).splitOn " — " with
  | numText :: effectParts@(_ :: _) =>
    let effect := " — ".intercalate effectParts
    (numText.splitOn ", ").mapM (fun s => chapterNumber? (copied s)) |>.bind fun ks =>
      if ks.isEmpty then none
      else
        ks.foldlM (fun (parts, n) k =>
          (body effect n).map fun (actions, n') =>
            (parts ++ [.ability (.keywordWithEffect (.chapter k) actions)], n'))
          (([] : List CardPart), n)
  | _ => none

def onceEachTurn? (line : String) : Option (List String) :=
  match sentences line with
  | [] => none
  | ss =>
    match ss.getLast? with
    | some last =>
      if sentenceIs last "this ability triggers only once each turn" then
        some (ss.dropLast)
      else none
    | none => none

/-- `At the beginning of combat on your turn, put a trample counter on up to
one target creature you control. It becomes a Bear in addition to its other
types. Then if you control three or more Bears, draw two cards.` -/
def parseBeornCombat (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "at the beginning of combat on your turn, put a trample counter on up to one target creature you control. it becomes a bear in addition to its other types. then if you control three or more bears, draw two cards" then
    none
  else
    some ([.ability (.triggered (.combatStart (.controller .this)) (.sequence [
      .putCounter
        (.targets n (.range 0 1) creatureYouControl)
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
      some ([.ability (.triggered (.enter .this) (.sequence [
        .optional (.controller .this) (.sequence [
          .defineSelectorVariable chosen anotherCreatureYouSacrifice,
          .defineValueVariable power (.greatestPower (.variable chosen)),
          .actionId chosen (.sacrifice (.variable chosen))]),
        .reflexive chosen [
          .actionId damage
            (.dealDamage .this
              (.target chosen
                (.intersection [
                  .not (.wasObjectOfAction chosen), .zone .battlefield, .cardType .creature]))
              (.variable power)),
          .if (.greater (.excessDamage damage) 0) [
            .keyword (.controller .this) (.amass .goblin (.excessDamage damage))]]]))],
        damage + 1)

def attackingCreatures : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .attacking .all]

/-- Desert Were-Worm's extra combat. The static line is the shared grammar. -/
def parseAttackTotalPowerExtraCombat (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "whenever you attack with creatures with total power 12 or greater for the first time each turn, untap all attacking creatures. after this phase, there is an additional combat phase" then
    none
  else
    some ([.ability (.triggeredOnce youAttack (.sequence [
      .if (.greaterOrEqual (.totalPower attackingCreatures) 12) [
        .untap attackingCreatures,
        .extraCombat]]))], n)

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

def parseCreateAxeWhenYouDo (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.enter .this) then none
    else if !(norm effect).startsWith "create a colorless equipment artifact token named axe with \"" then
      none
    else if !(norm effect).endsWith "when you do, attach it to target creature you control" then none
    else
      some ([.ability (.triggered (.enter .this) (.sequence [
        .actionId n (.createTokens (.controller .this) 1 axeToken),
        .reflexive n [
          .attach (.wasCreatedByAction n) (.target n creatureYouControl)]]))], n + 1)

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
            (.intersection [.zone .battlefield, .cardType .creature, .attacking .all, .equipped])
            (.keyword .doubleStrike)]
          .endOfTurn))], n)

def parseActivateCreatureDrawOnce (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  match onceEachTurn? line with
  | some [draw] =>
    if normSentence draw != "whenever you activate an ability of a creature, draw a card" then
      none
    else
      some ([.ability (.triggeredOnce
        (.activateAbility (.intersection [.zone .battlefield, .cardType .creature]))
        (.draw (.controller .this) 1))], n)
  | _ => none

def parseExileReturnEndStep (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (parsePrintedCosts cardName costText).bind fun costs =>
      if norm effect !=
          "exile up to two other target nonland permanents you control. return those cards to the battlefield under their owner's control at the beginning of the next end step" then
        none
      else
        some ([.ability (.activated costs
          (.exileThenReturn
            (.targets n (.range 0 2)
              (.intersection [
                .not .this, .zone .battlefield, .not (.cardType .land), youControl]))
            (.endStep .player)))], n + 1)

def parseRevealRandomCreature (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "when this artifact is put into a graveyard from the battlefield, reveal the top thirteen cards of your library. put a random creature card from among them onto the battlefield. put the rest on the bottom of your library in a random order" then
    none
  else
    some ([.ability (.triggered (.putToGraveyard .this) (.sequence [
      .actionId n (.reveal (.topOfLibrary (.controller .this) 13)),
      .actionId (n + 1)
        (.chooseRandom (.intersection [.wasObjectOfAction n, .cardType .creature])),
      .putOntoBattlefield (.wasObjectOfAction (n + 1)),
      .putOnLibraryBottomInRandomOrder
        (.intersection [.wasObjectOfAction n, .not (.wasObjectOfAction (n + 1))])]))], n + 2)

def parseChooseOddEven (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  let s := (after? (normLine line) "as ").getD (normLine line)
  let lead :=
    (before? s " enters, choose odd or even").bind fun who =>
      if refersToSelf cardName who then some () else none
  if lead.isSome then
    some ([.ability (.static (.replace (.enter .this)
      [.chooseOddEven (.controller .this), .keepReplacedAction]))], n)
  else none

def parseExileOppDeathWolf (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "if a creature an opponent controls would die, exile it instead. when you do, create a 2/2 green wolf creature token" then
    none
  else
    some ([.ability (.static (.replace (.die opponentCreature) [
      .actionId n (.exile .replacingObject),
      .reflexive n [.createTokens (.controller .this) 1 wolfToken]]))], n + 1)

def parseExileTopPlayForLife (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "exile the top x cards of target opponent's library. you may play those cards this turn. if you cast a spell this way, pay life equal to its mana value rather than pay its mana cost" then
    none
  else
    some ([.actions [
      .actionId n (.exile (.topOfLibrary (.target n (.opponent (.controller .this))) .x)),
      .continuous [.canPlay (.controller .this) (.wasCreatedByAction n)] .endOfTurn,
      .castPayingLifeInstead (.wasCreatedByAction n)]], n + 1)

def legendaryYouControl : Selector :=
  .intersection [.zone .battlefield, .supertype .legendary, youControl]

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
          (nonemptyMana? manaText).bind fun syms =>
            some ([.ability (.activated
              [.mana syms, .tapSymbol,
               .discard (.selected (.controller .this) (.range 1 1)
                 (.intersection [
                   .zone .hand, .supertype .legendary, .owner (.controller .this),
                   .sharesNameWith legendaryYouControl]))]
              (.draw (.controller .this) 2))], n)
      | _ => none

def parseMountainQuestDragon (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
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

def parsePowerPerFatGraveyard (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitGets? (normLine line)).bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else if rest != "+2/+0 for each graveyard with seven or more cards in it" then none
    else
      some ([.ability (.static
        (.addPower .this (Value.timesCount 2 (.graveyardsAtLeast 7))))], n)

def sagaRemains : Trigger :=
  .leaveBattlefield .this

def parseHexproofWhileSaga (effect : String) (n : Nat) : Option (List CardAction × Nat) :=
  if normSentence effect !=
      "target creature you control gains hexproof for as long as this saga remains on the battlefield" then
    none
  else
    some ([.continuous
      [.gainAbility (.target n creatureYouControl) (.keyword .hexproof)]
      sagaRemains], n + 1)

def parsePreventWhileSaga (effect : String) (n : Nat) : Option (List CardAction × Nat) :=
  if normSentence effect !=
      "prevent all damage that would be dealt by up to one target creature for as long as this saga remains on the battlefield" then
    none
  else
    some ([.continuous [
      .replace
        (.damage
          (.targets n (.range 0 1) (.intersection [.zone .battlefield, .cardType .creature]))
          .all)
        []]
      sagaRemains], n + 1)

def parseSagaHexproofOrPrevent (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseNumberedChapters line n fun effect n =>
    parseHexproofWhileSaga effect n <|> parsePreventWhileSaga effect n

def landsYou : Selector :=
  .intersection [.zone .battlefield, .cardType .land, youControl]

def parseRevealUntilCreature (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "whenever a nontoken creature you control dies, reveal cards from the top of your library until you reveal a creature card. if its mana value is less than or equal to the number of lands you control, put it onto the battlefield. otherwise, put it into your hand. put the rest on the bottom of your library in a random order. this ability triggers only once each turn" then
    none
  else
    let dies :=
      .die (.intersection [
        .zone .battlefield, .cardType .creature, .not .token, youControl])
    some ([.ability (.triggeredOnce dies (.sequence [
      .actionId n (.revealUntil (.controller .this) (.cardType .creature)),
      .ifElse
        (.lessOrEqual
          (.greatestManaValue (.wasObjectOfAction n))
          (.count landsYou))
        [.putOntoBattlefield (.wasObjectOfAction n)]
        [.returnToHand (.wasObjectOfAction n)],
      .putOnLibraryBottomInRandomOrder (.restOfAction n)]))], n + 1)

def parseSeparatePiles (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "look at the top four cards of your library and separate them into a face-down pile and a face-up pile. an opponent chooses one of the piles. put that pile into your hand and the other into your graveyard" then
    none
  else some ([.actions [.separatePiles (.controller .this) 4]], n)

def basicPlains : Selector :=
  .intersection [.supertype .basic, .subtype .plains]

def plainsYou : Selector :=
  .intersection [.zone .battlefield, .subtype .plains, youControl]

def parseRoadsChapter (effect : String) (n : Nat) : Option (List CardAction × Nat) :=
  if norm effect ==
      "search your library for up to two basic plains cards, exile them, then shuffle. you gain 2 life" then
    some ([.sequence [
      .searchLibraryThenShuffle (.controller .this) [
        .exile (.selected (.controller .this) (.range 0 2) basicPlains)],
      .gainLife (.controller .this) 2]], n)
  else if normSentence effect == "put a card exiled with this saga into its owner's hand" then
    some ([.returnToHand
      (.selected (.controller .this) (.range 1 1) (.exiledWith .this))], n)
  else if normSentence effect ==
      "whenever you attack this turn, target creature you control gets +1/+1 until end of turn for each plains you control" then
    some ([.continuous [
      .gainAbility .this
        (.triggered youAttack
          (.continuous [
            .addPower (.target n creatureYouControl) (.count plainsYou),
            .addToughness (.targetReference n) (.count plainsYou)]
            .endOfTurn))]
      .endOfTurn], n + 1)
  else none

def parseRoadsChapters (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseNumberedChapters line n parseRoadsChapter

def creatureOrLandYou : Selector :=
  .intersection [
    .zone .battlefield, .union [.cardType .creature, .cardType .land], youControl]

def parseBlinkChapter (effect : String) (n : Nat) : Option (List CardAction × Nat) :=
  if normSentence effect !=
      "exile up to one target creature or land you control. if you do, return it to the battlefield under its owner's control at the beginning of the next end step" then
    none
  else
    some ([.sequence [
      .actionId n (.exile (.targets n (.range 0 1) creatureOrLandYou)),
      .if (.happened (.actionWithId n) .gameStart) [
        .delayed (.endStep .player) [
          .putOntoBattlefield (.wasObjectOfAction n)]]]], n + 1)

def parseBlinkChapters (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseNumberedChapters line n parseBlinkChapter

def parseLootLandEnters (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.enter .this) then none
    else if norm effect !=
        "draw a card, then discard a card. if you discard a land card this way, put it from your graveyard onto the battlefield tapped" then
      none
    else
      some ([.ability (.triggered (.enter .this) (.sequence [
        .draw (.controller .this) 1,
        .actionId n (.discard (.controller .this) 1),
        .if (.any (.intersection [.wasObjectOfAction n, .cardType .land])) [
          .putOntoBattlefieldInState
            (.intersection [.zone .graveyard, .wasObjectOfAction n])
            [.tapped]]]))], n + 1)

def parseLandfallPayReturn (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  let line := (afterAbilityWord? line).getD line
  if !lineIs line
      "whenever a land you control enters, you may pay {1}{g}{u}. if you do, return this card from your graveyard to your hand" then
    none
  else
    some ([.ability (.triggered (.enter landsYouControl)
      (.optionalPayFor (.controller .this)
        [.mana [.generic 1, .mono .green, .mono .blue]]
        [.returnToHand (.intersection [.zone .graveyard, .this])]))], n)

def parseSupperForSpiders (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "put onto the battlefield under your control all creature cards in your opponents' graveyards that were put there from the battlefield this turn. they are food artifacts with \"{2}, {t}, sacrifice this artifact: you gain 3 life.\"" then
    none
  else
    some ([.actions [
      .actionId n
        (.putOntoBattlefieldInState
          (.intersection [
            .zone .graveyard, .cardType .creature, .owner (.opponent (.controller .this)),
            .wasObjectSince (.putToGraveyard .all) .turnStart])
          [.controlled (.controller .this)]),
      .becomeWith (.affectedByAction n) foodArtifactAbility]], n + 1)

def creatureYouOwn : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .owner (.controller .this)]

def parseEaglesAreComing (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "choose target creature you own. if this spell was kicked, instead choose any number of target creatures you own. return each chosen creature to your hand. at the beginning of the next upkeep, create a 4/4 white bird soldier creature token with flying for each creature returned to your hand this way" then
    none
  else
    some ([.actions [
      .ifElse .kicked
        [.actionId n (.returnToHand (.targets n .any creatureYouOwn))]
        [.actionId n (.returnToHand (.target (n + 1) creatureYouOwn))],
      .delayed (.upkeep .player) [
        .createTokens (.controller .this) (.count (.wasObjectOfAction n)) birdSoldierToken]]],
      n + 2)

def parsePutAnyCountersDamage (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  -- The creature list contains commas, so the trigger is not the first comma.
  let s := normLine line
  let lead := "whenever you put one or more counters on a goblin, orc, or army you control, "
  (after? s lead).bind fun rest =>
    (before? rest " deals 2 damage to target opponent").bind fun who =>
      if !refersToSelf cardName who then none
      else
        some ([.ability (.triggered
          (.putAnyCounters (.controller .this) goblinOrcArmyYouControl)
          (.dealDamage .this (.target n (.opponent (.controller .this))) 2))], n + 1)

def parseAnotherArmyDiesExile (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  -- The creature list contains commas, so the trigger is not the first comma.
  if !lineIs line
      "whenever another goblin, orc, or army you control dies, exile the top card of your library. you may play it until the end of your next turn" then
    none
  else
      let another := .intersection [.not .this, goblinOrcArmyYouControl]
      some ([.ability (.triggered (.die another) (.sequence [
        .actionId n (.exile (.topOfLibrary (.controller .this) 1)),
        .continuous [.canPlay (.controller .this) (.wasCreatedByAction n)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))], n + 1)

def parsePlayerLosesLifeMills (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "whenever a player loses life, that player mills that many cards" then none
  else
    some ([.ability (.triggered (.triggerId n (.loseLife .player))
      (.mill (.wasArgumentOfTrigger n 1) (.triggerAmount n)))], n + 1)

def parseDiesDrawPerFatGraveyard (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.die .this) then none
    else if normSentence effect !=
        "draw a card for each graveyard with seven or more cards in it" then none
    else
      some ([.ability (.triggered (.die .this)
        (.draw (.controller .this) (.count (.graveyardsAtLeast 7))))], n)

def parseCopySelfNonlegendary (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if parseTriggerEvent cardName clause != some (.enter .this) then none
    else
      (after? (norm effect) "if they're not a token, ").bind fun rest =>
        if !rest.startsWith "create two tokens that are copies of " ||
            !rest.endsWith ", except the tokens aren't legendary" then none
        else
          some ([.ability (.triggered (.enter .this)
            (.if (.not (.any (.intersection [.source .this, .token])))
              [.copyTokens .this 2 [.removeSupertype .this .legendary]]))], n)

def elfCardsInYourGraveyard : Selector :=
  .intersection [.zone .graveyard, .subtype .elf, .owner (.controller .this)]

def parseCopyActivatedFromGraveyard (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (split2? (normLine line) " has all activated abilities of all ").bind fun (who, rest) =>
    if !refersToSelf cardName who then none
    else if rest != "elf cards in your graveyard" then none
    else
      some ([.ability (.static (.copyActivatedAbilities .this elfCardsInYourGraveyard))], n)

def parseAnotherLegendaryElfLoot (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm clause != "another legendary elf you control enters" then none
    else if normSentence effect != "draw two cards, then discard a card" then none
    else
      let elf :=
        .intersection [
          .not .this, .zone .battlefield, .cardType .creature, .subtype .elf,
          .supertype .legendary, youControl]
      some ([.ability (.triggered (.enter elf)
        (.sequence [.draw (.controller .this) 2, .discard (.controller .this) 1]))], n)

def parseSacrificeDrawPower (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    if norm effect !=
        "draw cards equal to the sacrificed creature's power, then discard a card" then none
    else
      let parts := costText.splitOn ", " |>.map copied
      match parts with
      | [manaText, sacText] =>
        if norm sacText != "sacrifice another creature" then none
        else
          (nonemptyMana? manaText).bind fun syms =>
            some ([.ability (.activated
              [.mana syms,
               .sacrifice (.intersection [
                 .not .this, .zone .battlefield, .cardType .creature, youControl])]
              (.sequence [
                .draw (.controller .this) (.greatestPower .sacrificedAsCost),
                .discard (.controller .this) 1]))], n)
      | _ => none

/-- Tom, Bert, and William's name contains commas, so the trigger is the
whole line rather than the first comma. -/
def parseDieReturnAsArtifact (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "when tom, bert, and william die, if they were a creature, return them to the battlefield. they're an artifact" then
    none
  else
    some ([.ability (.triggered (.die .this)
      (.if (.wasCreature .this) [
        .putOntoBattlefield .this,
        .continuous [.setCardTypes .this [.artifact]] .endOfGame]))], n)

def parseEquippedTriggersAgain (line : String) (n : Nat) : Option (List CardPart × Nat) :=
  if !lineIs line
      "if a triggered ability of equipped creature triggers, that ability triggers an additional time" then
    none
  else
    some ([.ability (.static (.replace
      (.abilityTriggers (.hostOf .this))
      [.duplicateReplacingTrigger 2]))], n)

/-- `Each opponent loses 2 life and you gain 2 life.` One mode of Gollum. -/
def hobbitModeAction (text : String) (n : Nat) : Option (CardAction × Nat) :=
  if normSentence text == "each opponent loses 2 life and you gain 2 life" then
    some (.sequence [
      .loseLife (.opponent (.controller .this)) 2,
      .gainLife (.controller .this) 2], n)
  else none

/-- A line from the remaining Hobbit cards, or `none` so the shared grammar
can try it. -/
def hobbitRemainingLine (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseBeornCombat line n <|>
    parseBolgEnters cardName line n <|>
    parseAttackTotalPowerExtraCombat line n <|>
    parseHoneEachEquipment cardName line n <|>
    parseCreateAxeWhenYouDo cardName line n <|>
    parseEquippedAttackersDoubleStrike cardName line n <|>
    parseActivateCreatureDrawOnce line n <|>
    parseExileReturnEndStep cardName line n <|>
    parseRevealRandomCreature line n <|>
    parseChooseOddEven cardName line n <|>
    parseExileOppDeathWolf line n <|>
    parseExileTopPlayForLife line n <|>
    parseDiscardLegendaryDraw line n <|>
    parseMountainQuestDragon line n <|>
    parsePowerPerFatGraveyard cardName line n <|>
    parseSagaHexproofOrPrevent line n <|>
    parseRevealUntilCreature line n <|>
    parseSeparatePiles line n <|>
    parseRoadsChapters line n <|>
    parseBlinkChapters line n <|>
    parseLootLandEnters cardName line n <|>
    parseLandfallPayReturn line n <|>
    parseSupperForSpiders line n <|>
    parseEaglesAreComing line n <|>
    parsePutAnyCountersDamage cardName line n <|>
    parseAnotherArmyDiesExile line n <|>
    parsePlayerLosesLifeMills line n <|>
    parseDiesDrawPerFatGraveyard cardName line n <|>
    parseCopySelfNonlegendary cardName line n <|>
    parseCopyActivatedFromGraveyard cardName line n <|>
    parseAnotherLegendaryElfLoot line n <|>
    parseSacrificeDrawPower line n <|>
    parseDieReturnAsArtifact line n <|>
    parseEquippedTriggersAgain line n

end OracleParts

end Mtg.Engine
