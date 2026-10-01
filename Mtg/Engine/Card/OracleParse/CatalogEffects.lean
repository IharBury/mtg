import Mtg.Engine.Card.OracleParse.CatalogSentences

/-!
# Catalog effects

Effects that take more than one sentence, read in printed order.
-/

namespace Mtg.Engine

namespace OracleParts

/-- `sacrifice another creature or artifact`, `sacrifice another creature`,
`sacrifice an artifact`, or `sacrifice an artifact or discard a card`, as an
action the controller may take. The sacrificed permanent is one they control
(CR 701.17a). With `or`, the controller chooses which to do. -/
def parseMayAction (s : String) : Option CardAction :=
  let s := norm s
  let sacrifice (obj : String) : Option CardAction :=
    let (obj, other) :=
      match after? obj "another " with
      | some rest => (rest, true)
      | none => ((dropArticle? obj).getD obj, false)
    (typesInPhrase obj).map fun ts =>
      .sacrifice
        (.selected (.controller .this) (.range 1 1)
          (.intersection (
            (if other then [.not .this] else []) ++
            [.zone .battlefield, selectorOfTypes ts, youControl])))
  match split2? s " or discard " with
  | some (sac, discarded) =>
    match (after? sac "sacrifice ").bind sacrifice, parseCardCount discarded with
    | some sacAction, some k =>
      some (.playerSelectAction (.controller .this) (.range 1 1)
        [sacAction, .discard (.controller .this) (Value.nat k)])
    | _, _ => none
  | none => (after? s "sacrifice ").bind sacrifice

/-- `You may <action>. If you do, <effect>.` or `… When you do, <effect>.`
The optional action is action `n`. The effect happens only when that action
happened. -/
def parseMayIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [may, result] =>
    let r := normSentence result
    let effect? := after? r "if you do, " <|> after? r "when you do, "
    match (after? (normSentence may) "you may ").bind parseMayAction, effect? with
    | some action, some effect =>
      (parseCatalogSentence cardName effect n).map fun (then_, n') =>
        ([
          .optional (.controller .this) (.actionId n action),
          .if (.happened (.actionWithId n) .gameStart) (flattenAction then_)],
         n')
    | _, _ => none
  | _ => none

/-- `Exile the top card of your library. Until the end of your next turn, you
may play that card.` The exile is action `n`. -/
def parseExileTopUntilNextTurn (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [exile, play] =>
    if sentenceIs exile "exile the top card of your library" &&
        sentenceIs play "until the end of your next turn, you may play that card" then
      some (flattenAction (exileTopPlayUntilEndOfNextTurn n), n + 1)
    else none
  | _ => none

/-- `Add one mana of any color. Spend this mana only to cast an instant or
sorcery spell.` The mana is action `n`. Spending it on anything else is
forbidden. -/
def parseAddAnyColorSpendOnly (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    if sentenceIs add "add one mana of any color" &&
        sentenceIs spend "spend this mana only to cast an instant or sorcery spell" then
      some ([.sequence [
        .actionId n (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1),
        .continuous
          [.forbid (.spendManaCreatedByAction n (.not (.castSpell instantOrSorcery)))]
          .endOfTurn]], n)
    else none
  | _ => none

/-- `Choose target permanent card in your graveyard that was put there from
anywhere this turn. Return it to your hand.` The card is target `n`. -/
def parseChooseGraveyardCardReturn (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, ret] =>
    if sentenceIs ret "return it to your hand" then
      (between? (normSentence choose) "choose target "
          " card in your graveyard that was put there from anywhere this turn").bind
        fun kind =>
          let kindSel? : Option Selector :=
            if kind == "permanent" then some (.zone .battlefield) else (typeOfOracle? kind).map Selector.cardType
          kindSel?.map fun kindSel =>
            ([.returnToHand (.target n (.intersection [
                .zone .graveyard, kindSel, .owner (.controller .this),
                .wasObjectSince (.putToGraveyard .all) .turnStart]))], n + 1)
    else none
  | _ => none

/-- `Mill N cards. You may put a <kind> card from among the milled cards into
your hand.` Also `… from among those cards …`. The mill is action `n`. -/
def parseMillMayPut (ss : List String) (n : Nat) : Option (List CardAction × List String × Nat) :=
  match ss with
  | mill :: put :: rest =>
    let p := normSentence put
    let kind? :=
      (between? p "you may put " " card from among the milled cards into your hand") <|>
        (between? p "you may put " " card from among those cards into your hand")
    match (after? (normSentence mill) "mill ").bind parseCardCount,
        kind?.bind dropArticle? |>.bind typeOrSubtypeList? with
    | some k, some kind =>
      let among := extendIntersection [.wasObjectOfAction n] kind []
      some ([
        .actionId n (.mill (.controller .this) (Value.nat k)),
        .optional (.controller .this)
          (.returnToHand (.selected (.controller .this) (.range 1 1) among))],
        rest, n + 1)
    | _, _ => none
  | _ => none

/-- `Sacrifice an artifact or discard a nonland card`: one of those two costs. -/
def parseSacrificeOrDiscardCost (s : String) : Option Cost :=
  (after? (norm s) "sacrifice ").bind (split2? · " or discard ") |>.bind fun (obj, card) =>
    match (dropArticle? obj).bind typesInPhrase,
        (dropArticle? card).bind (before? · " card") with
    | some ts, some kind =>
      let discarded : Option Selector :=
        match after? kind "non" with
        | some t => (typeOfOracle? t).map fun t => .not (.cardType t)
        | none => (typeOfOracle? kind).map Selector.cardType
      discarded.map fun d => .or [.sacrificeCount (permanentWith ts [youControl]) 1, .discard d]
    | _, _ => none

/-- `You may pay {1}. When you do, <effect>.` The effect happens only if the
controller pays (CR 603.12). -/
def parseMayPayWhenYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [pay, result] =>
    let cost? : Option Cost :=
      ((after? (normSentence pay) "you may pay ").bind nonemptyMana? |>.map Cost.mana) <|>
        ((after? (normSentence pay) "you may ").bind parseSacrificeOrDiscardCost)
    match cost?, after? (normSentence result) "when you do, " with
    | some cost, some effect =>
      (parseCatalogSentence cardName effect n).map fun (action, n') =>
        ([.optionalPayFor (.controller .this) [cost] (flattenAction action)], n')
    | _, _ => none
  | _ => none

/-- `You may draw a card for each artifact you control. If you do, each
opponent draws a card.` Each of those objects is variable `n`. -/
def parseMayDrawForEachIfYouDo (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [may, result] =>
    match (after? (normSentence may) "you may draw a card for each ").bind (parseObjectDesc · false),
        normSentence result with
    | some among, "if you do, each opponent draws a card" =>
      some ([.optional (.controller .this) (.sequence [
        .forEachVariable n among [.draw (.controller .this) 1],
        .draw (.opponent (.controller .this)) 1])], n)
    | _, _ => none
  | _ => none

/-- `Put a +1/+1 counter on target creature. If that creature is another Hero,
put two +1/+1 counters on it instead.` The target is `n`. The extra counters
go on it when it is another permanent of that subtype. -/
def parsePutCounterMoreIfSubtype (ss : List String) (n : Nat) : Option (List CardAction × Nat) :=
  match ss with
  | [put, instead] =>
    match parsePutPlusOneOn? put, after? (normSentence instead) "if that creature is another " with
    | some (k, who), some rest =>
      (split2? rest ", ").bind fun (stText, more) =>
        match subtypeOfOracle? stText, (between? more "put " " instead").bind parsePutPlusOneOn?',
            parseTargetDesc who n with
        | some st, some (k', "it"), some sel =>
          if k' <= k then none
          else
            some ([
              .putCounter sel .plusOnePlusOne (.nat k),
              .if (.anySubtype (.intersection [.targetReference n, .not .this]) st)
                [.putCounter (.targetReference n) .plusOnePlusOne (.nat (k' - k))]],
              n + 1)
        | _, _, _ => none
    | _, _ => none
  | _ => none
where
  parsePutPlusOneOn?' (s : String) : Option (Nat × String) := parsePutPlusOneOn? ("put " ++ s)

/-- `Destroy up to one other target creature. Its controller amasses Goblins X, where X is that creature's power. If you controlled that creature, draw a card.`
The creature is target `n`. Before it is destroyed, value variable `n`
records its power and selector variable `n + 1` its controller, so both are
its last-known information (CR 608.2h). With no target, that controller is
no player, so no one amasses and no card is drawn. -/
def parseDestroyAmassPowerDrawIfYours (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, amass, draw] =>
    let ctl := n + 1
    match (after? (normSentence destroy) "destroy ").bind (parseTargetDesc · n),
        (between? (normSentence amass)
          "its controller amasses " " x, where x is that creature's power").bind amassSubtype?,
        (after? (normSentence draw) "if you controlled that creature, ").bind parseDrawCards with
    | some sel, some st, some drawAction =>
      some ([
        .defineValueVariable n (.greatestPower sel),
        .defineSelectorVariable ctl (.controller (.targetReference n)),
        .destroy (.targetReference n),
        .keyword (.variable ctl) (.amass st (.variable n)),
        .if (.any (.intersection [.variable ctl, .controller .this])) [drawAction]],
        n + 2)
    | _, _, _ => none
  | _ => none

/-- `You may discard your hand. Draw X cards, where X is the number of cards discarded this way. If you have an enduring story, <this> deals X damage to each opponent.`
The discard is action `n`, and X is how many cards it discarded. Declining
discards nothing, so X is zero. The damage source is this card. -/
def parseMayDiscardHandDrawDamage (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [discard, draw, damage] =>
    let discarded := Value.count (.wasObjectOfAction n)
    if !sentenceIs discard "you may discard your hand" ||
        !sentenceIs draw "draw x cards, where x is the number of cards discarded this way" then
      none
    else
      (between? (normSentence damage)
          "if you have an enduring story, " " deals x damage to each opponent").bind fun who =>
        if !damageSource? cardName who then none
        else
          some ([
            .optional (.controller .this)
              (.actionId n (.discard (.controller .this) (.count cardsInYourHand))),
            .draw (.controller .this) discarded,
            .if controllerHasEnduringStory
              [.dealDamage (.source .this) (.opponent (.controller .this)) discarded]],
            n + 1)
  | _ => none

/-- Each sentence as one catalog action, in order. -/
def catalogSentenceActions (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  List.foldlM (fun (acc, n) s =>
    (parseCatalogSentence cardName s n).map fun (a, n') => (acc ++ [a], n'))
    ([], n) ss

/-- `<effect>. Then if you control four or more Treasures, sacrifice this Saga.
If you do, <effect>.` The count is of permanents of that subtype you control.
The sacrifice is action `n`; the last effect happens only if this was
sacrificed. -/
def parseThenIfControlSacrificeIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [first, thenIf, ifYouDo] =>
    (between? (normSentence thenIf) "then if you control " ", sacrifice this saga").bind
        (split2? · " or more ") |>.bind fun (countText, plural) =>
      match positiveCount countText, pluralCreatureType? plural,
          after? (normSentence ifYouDo) "if you do, " with
      | some k, some st, some effect =>
        (catalogSentenceActions cardName [first] (n + 1)).bind fun (firstActions, n1) =>
          (parseCatalogSentence cardName effect n1).map fun (last, n2) =>
            (firstActions ++ [
              .if (.greaterOrEqual
                  (.count (.intersection [.zone .battlefield, .subtype st, youControl])) (Value.nat k))
                [.actionId n (.sacrifice .this),
                 .if (.happened (.actionWithId n) .gameStart) (flattenAction last)]],
             n2)
      | _, _, _ => none
  | _ => none

/-- `You may pay {1}. If you do, <effect>.` The effect happens only if the
cost was paid (CR 118.1 / 608.2d). -/
def parseMayPayIfYouDo (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [pay, ifYouDo] =>
    match (after? (normSentence pay) "you may pay ").bind nonemptyMana?,
        after? (normSentence ifYouDo) "if you do, " with
    | some syms, some effect =>
      (parseCatalogSentence cardName effect n).map fun (action, n') =>
        ([.optionalPayFor (.controller .this) [.mana syms] (flattenAction action)], n')
    | _, _ => none
  | _ => none

/-- `You may tap any number of untapped Humans you control. Draw a card for
each Human tapped this way.` The tap is action `n`; any number includes none. -/
def parseTapAnyNumberDrawForEach (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [tap, draw] =>
    match (after? (normSentence tap) "you may tap any number of ").bind (parseObjectDesc · false),
        (between? (normSentence draw) "draw a card for each " " tapped this way") with
    | some sel, some _ =>
      some ([.actionId n (.tap (.selected (.controller .this) .any sel)),
        .draw (.controller .this) (.count (.wasObjectOfAction n))], n + 1)
    | _, _ => none
  | _ => none

/-- `Return target Elf card from your graveyard to your hand. You gain life
equal to that card's power.` That card is the target. -/
def parseReturnGyGainLifeEqualPower (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [ret, gain] =>
    if !sentenceIs gain "you gain life equal to that card's power" then none
    else
      (between? (normSentence ret) "return target " " from your graveyard to your hand").bind
        parseGraveyardCard |>.map fun sel =>
          ([.returnToHand (.target n sel),
            .gainLife (.controller .this) (.greatestPower (.targetReference n))], n + 1)
  | _ => none

/-- `Destroy all artifacts and enchantments your opponents control. You gain 1
life for each permanent destroyed this way.` The destruction is action `n`. -/
def parseDestroyAllGainLifePer (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, gain] =>
    if !sentenceIs gain "you gain 1 life for each permanent destroyed this way" then none
    else
      (after? (normSentence destroy) "destroy all ").bind
        (fun obj => parseObjectDesc (obj.replace " and " " or ") false) |>.map fun sel =>
          ([.actionId n (.destroy sel),
            .gainLife (.controller .this) (.count (.wasObjectOfAction n))], n + 1)
  | _ => none

/-- `Choose a creature type. Return all creatures that aren't of the chosen
type to their owners' hands.` The choice is action `n` (CR 205.3m). -/
def parseChooseTypeReturnOthers (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, ret] =>
    if sentenceIs choose "choose a creature type" &&
        sentenceIs ret "return all creatures that aren't of the chosen type to their owners' hands" then
      some ([.actionId n (.chooseCreatureType (.controller .this)),
        .returnToHand (.intersection [
          .zone .battlefield, .cardType .creature, .not (.hasCreatureTypeChosenByAction n)])], n + 1)
    else none
  | _ => none

/-- `Add {R}{R}. Spend this mana only to cast Dwarf, Equipment, and Saga
spells.` The mana is action `n`; it can't be spent on anything else
(CR 106.6). -/
def parseAddManaSpendOnlySubtypes (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    match (after? (normSentence add) "add ").bind nonemptyMana?,
        (between? (normSentence spend) "spend this mana only to cast " " spells").bind fun kinds =>
          (orList (kinds.replace ", and " ", ")).mapM subtypeOfOracle? with
    | some syms, some sts@(_ :: _) =>
      let spells := Selector.intersection [.spell, .union (sts.map Selector.subtype)]
      some ([.sequence [
        .actionId n (.addMana (.controller .this) syms),
        .continuous [.forbid (.spendManaCreatedByAction n (.not (.castSpell spells)))] .endOfTurn]],
        n + 1)
    | _, _ => none
  | _ => none

/-- `Add one mana of any color. Spend this mana only to cast a Hero spell or to
activate an ability of a Hero source.`, `… only to cast an artifact spell.`,
and `Add {U}. This mana can't be spent to cast a nonartifact spell.` The mana
is action `n`; the restricted spending is forbidden (CR 106.6). -/
def parseAddManaSpendRestricted (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [add, spend] =>
    let a := normSentence add
    let s := normSentence spend
    let add? : Option CardAction :=
      if a == "add one mana of any color" then
        some (.addManaOfOneColor (.controller .this) ManaSymbol.anyColor 1)
      else (after? a "add ").bind nonemptyMana? |>.map (.addMana (.controller .this) ·)
    let sourceSubtype? : Option Trigger :=
      (between? s "spend this mana only to cast a " " source").bind
          (split2? · " spell or to activate an ability of a ") |>.bind fun (k, k') =>
        if k != k' then none
        else (subtypeOfOracle? k).map fun st =>
          .not (.or (.castSpell (.intersection [.spell, .subtype st]))
            (.activateAbility (.subtype st)))
    let spellType? : Option Trigger :=
      (between? s "spend this mana only to cast an " " spell").bind typeOfOracle? |>.map fun t =>
        .not (.castSpell (.intersection [.spell, .cardType t]))
    let nonType? : Option Trigger :=
      (between? s "this mana can't be spent to cast a non" " spell").bind typeOfOracle? |>.map
        fun t => .castSpell (.intersection [.spell, .not (.cardType t)])
    match add?, sourceSubtype? <|> spellType? <|> nonType? with
    | some addAction, some forbidden =>
      some ([.sequence [
        .actionId n addAction,
        .continuous [.forbid (.spendManaCreatedByAction n forbidden)] .endOfTurn]], n + 1)
    | _, _ => none
  | _ => none

/-- `Look at the top three cards of your library. You may reveal a Hero card
from among them and put it into your hand. Put the rest on the bottom of your
library in any order.` The looked-at cards are action `n`; the revealed card is
action `n + 1`. The owner orders the rest (CR 401.4). -/
def parseLookAtTopRevealAnyOrder (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [look, reveal, rest] =>
    if normSentence rest != "put the rest on the bottom of your library in any order" then none
    else
      match (between? (normSentence look) "look at the top " " of your library").bind
          topCount?,
        (between? (normSentence reveal) "you may reveal "
          " card from among them and put it into your hand").bind dropArticle? |>.bind
          subtypeOfOracle? with
      | some k, some st =>
        some (lookAtTopMayRevealToHand n k (.subtype st) .putOnBottomOfLibrary, n + 2)
      | _, _ => none
  | _ => none

/-- `Choose a creature type. Create a Treasure token for each creature you
control of that type.` The choice is action `n` (CR 205.3m); each counted
creature is variable `n + 1`. -/
def parseChooseTypeCreateForEach (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [choose, create] =>
    if normSentence choose != "choose a creature type" then none
    else
      (before? (normSentence create) " for each creature you control of that type").bind
        createOneToken? |>.map fun token =>
          ([.actionId n (.chooseCreatureType (.controller .this)),
            .forEachVariable (n + 1)
              (.intersection [
                .zone .battlefield, .cardType .creature, youControl, .hasCreatureTypeChosenByAction n])
              [token]], n + 2)
  | _ => none

/-- `Destroy target land. Its controller may search their library for a basic
land card, put it onto the battlefield tapped, then shuffle.` The land is target
`n`; its controller searches (CR 701.19). -/
def parseDestroyThenControllerSearchesBasic (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [destroy, search] =>
    if normSentence search !=
        "its controller may search their library for a basic land card, put it onto the battlefield tapped, then shuffle"
    then none
    else
      match catalogSentenceActions cardName [destroy] n with
      | some ([.destroy (.target t sel)], n1) =>
        let who := Selector.controller (.targetReference t)
        some ([
          .destroy (.target t sel),
          .optional who (.searchLibraryThenShuffle who [
            .putOntoBattlefieldInState (.selected who (.range 1 1) basicLandInLibrary) [.tapped]])],
          n1)
      | _ => none
  | _ => none

/-- `Exile all creatures. Each player may put any number of creature cards from
their hand onto the battlefield. Then put all cards exiled this way into their
owners' hands. Exile <this>.` The exile is action `n`; each player is variable
`n + 1`. -/
def parseExileAllPutFromHandReturnExiled (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss.map normSentence with
  | [exileAll, put, ret, exileSelf] =>
    let kind? := (after? exileAll "exile all ").bind typesInPhrase
    let putKind? :=
      (between? put "each player may put any number of "
        " cards from their hand onto the battlefield").bind typeOfOracle?
    let self := (after? exileSelf "exile ").any (refersToSelf cardName)
    match kind?, putKind? with
    | some ts, some t =>
      if ret != "then put all cards exiled this way into their owners' hands" || !self then none
      else
        let p := Selector.variable (n + 1)
        some ([
          .actionId n (.exile (permanentWith ts [])),
          .forEachVariable (n + 1) .player [
            .optional p (.putOntoBattlefield
              (.selected p .any (.intersection [.zone .hand, .owner p, .cardType t])))],
          .returnToHand (.wasCreatedByAction n),
          .exile .this], n + 2)
    | _, _ => none
  | _ => none

/-- `<effect> if there are two or more creature cards in your graveyard.
Otherwise, <effect>.` The condition is checked on resolution. -/
def parseIfGraveyardOtherwise (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [first, other] =>
    (split2? first " if ").bind fun (effect, condText) =>
      (after? (normSentence other) "otherwise, ").bind fun otherText =>
        match graveyardCountCondition? (norm condText), catalogSentenceActions cardName [effect] n with
        | some cond, some (yes, n1) =>
          (catalogSentenceActions cardName [otherText] n1).map fun (no, n2) =>
            ([.ifElse cond yes no], n2)
        | _, _ => none
  | _ => none

/-- `You may put an artifact card from your hand onto the battlefield. If it's
an Equipment, attach it to <this>.` The put is action `n`. -/
def parseMayPutThenAttachEquipment (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [put, attach] =>
    match parseMayPutFromHand (normSentence put) n,
        (after? (normSentence attach) "if it's an equipment, attach it to ").map (refersToSelf cardName) with
    | some (.optional who (.putOntoBattlefield card), _), some true =>
      some ([.optional who (.sequence [
        .actionId n (.putOntoBattlefield card),
        .if (.anySubtype (.wasObjectOfAction n) .equipment)
          [.attach (.wasObjectOfAction n) (.source .this)]])], n + 1)
    | _, _ => none
  | _ => none

/-- `Search your library for a basic land card, put it onto the battlefield tapped, then shuffle. You may behold an Elf. If you do, untap that land.`
Variable `n` is the library card. Putting it onto the battlefield is
action `n + 1`; the land there is `affectedByAction` of that action
(CR 400.7). Beholding that subtype is action `n + 2` (CR 701.4). The land
untaps only when that behold happened (CR 701.4b). -/
def parseSearchBasicBeholdUntap (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [search, may, ifYouDo] =>
    if !sentenceIs ifYouDo "if you do, untap that land" then none
    else
      match parseSearchBasicLandTapped search n,
          (after? (normSentence may) "you may ").bind beholdKeyword? with
      | some _, some (.behold st) =>
        some ([
          .searchLibraryThenShuffle (.controller .this) [
            .defineSelectorVariable n
              (.selected (.controller .this) (.range 1 1) basicLandInLibrary),
            .actionId (n + 1)
              (.putOntoBattlefieldInState (.variable n) [.tapped])],
          .optional (.controller .this)
            (.actionId (n + 2) (.keyword (.controller .this) (.behold st))),
          .if (.happened (.actionWithId (n + 2)) .gameStart)
            [.untap (.affectedByAction (n + 1))]],
          n + 3)
      | _, _ => none
  | _ => none

/-- `attach any number of target Equipment you control to target creature you
control. When one or more Equipment become attached to that creature this way,
that creature deals damage equal to its power to up to one target creature.`
The Equipment are targets `n` and the creature is target `n + 1`. Attaching
them takes the next number on this counter; `parseOracleParts` then numbers
that action on its own sequence, so it does not consume a target number.
One or more of those Equipment is that action's objects. The damage target
is the next target after the creature. -/
def parseAttachEquipmentThenDamage (cardName : String) (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [attach, reflex] =>
    if !sentenceIs reflex
        "when one or more equipment become attached to that creature this way, that creature deals damage equal to its power to up to one target creature" then
      none
    else
      match parseCatalogAttach cardName attach n with
      | some (.attach attached host, nAttach) =>
        let id := n + 2
        if attached == .targets n .any equipmentYouControl &&
            host == .target (n + 1) creaturesYouControl && nAttach == id then
          some ([
            .actionId id (.attach attached host),
            .if (.greaterOrEqual (.count (.wasObjectOfAction id)) (.nat 1))
              [.dealDamageEqualToPower (.targetReference (n + 1))
                (.targets (id + 1) (.range 0 1)
                  (.intersection [.zone .battlefield, .cardType .creature]))]],
            id + 2)
        else none
      | _ => none
  | _ => none

/-- `Target opponent reveals their hand. You choose a nonland card from it.
That player discards that card.`
The opponent is target `n`. Revealing that hand is action `n`. The chosen
nonland card, from among the revealed cards, is variable `n + 1`. That
player discards the chosen card. -/
def parseOpponentRevealsChooseNonlandDiscard (ss : List String) (n : Nat) :
    Option (List CardAction × Nat) :=
  match ss with
  | [reveal, choose, discard] =>
    if sentenceIs reveal "target opponent reveals their hand" &&
        sentenceIs choose "you choose a nonland card from it" &&
        sentenceIs discard "that player discards that card" then
      some ([
        .actionId n
          (.reveal
            (.intersection [
              .zone .hand,
              .owner (.target n (.opponent (.controller .this)))])),
        .defineSelectorVariable (n + 1)
          (.selected (.controller .this) (.range 1 1)
            (.intersection [.wasObjectOfAction n, .not (.cardType .land)])),
        .discard (.variable (n + 1)) 1], n + 2)
    else none
  | _ => none

/-- Every sentence of `text` as catalog actions, in order. Multi-sentence
templates come first. A leading sentence may come before exiling the top card
to play later. -/
def catalogActionsFromText (cardName text : String) (n : Nat) :
    Option (List CardAction × Nat) :=
  let ss := sentences text
  parseOpponentRevealsChooseNonlandDiscard ss n <|>
    parseAttachEquipmentThenDamage cardName ss n <|>
    parseSearchBasicBeholdUntap ss n <|>
    parseMayIfYouDo cardName ss n <|>
    parseThenIfControlSacrificeIfYouDo cardName ss n <|>
    parseDestroyAmassPowerDrawIfYours ss n <|>
    parseMayDiscardHandDrawDamage cardName ss n <|>
    parseMayPayWhenYouDo cardName ss n <|>
    parseMayDrawForEachIfYouDo ss n <|>
    parseChooseGraveyardCardReturn ss n <|>
    parsePutCounterMoreIfSubtype ss n <|>
    ((parseMillMayPut ss n).bind fun (first, rest, n1) =>
      (catalogSentenceActions cardName rest n1).map fun (more, n2) => (first ++ more, n2)) <|>
    parseExileTopUntilNextTurn ss n <|>
    parseAddAnyColorSpendOnly ss n <|>
    parseChooseTypeCreateForEach ss n <|>
    parseMayPayIfYouDo cardName ss n <|>
    parseTapAnyNumberDrawForEach ss n <|>
    parseReturnGyGainLifeEqualPower ss n <|>
    parseDestroyAllGainLifePer ss n <|>
    parseChooseTypeReturnOthers ss n <|>
    parseAddManaSpendOnlySubtypes ss n <|>
    parseAddManaSpendRestricted ss n <|>
    parseLookAtTopRevealAnyOrder ss n <|>
    parseDestroyThenControllerSearchesBasic cardName ss n <|>
    parseIfGraveyardOtherwise cardName ss n <|>
    parseMayPutThenAttachEquipment cardName ss n <|>
    parseExileAllPutFromHandReturnExiled cardName ss n <|>
    (match ss with
      | first :: rest =>
        (catalogSentenceActions cardName [first] n).bind fun (a, n1) =>
          (parseExileTopUntilNextTurn rest n1).map fun (b, n2) => (a ++ b, n2)
      | [] => none) <|>
    catalogSentenceActions cardName ss n

/-- A card name with `. ` in it, such as `M.O.D.O.K.`, would split a
sentence. Such a name in `text` is this permanent. -/
def withoutDottedName (cardName text : String) : String :=
  if (cardName.splitOn ". ").length > 1 || cardName.endsWith "." then
    text.replace (cardName ++ " ") "this permanent "
  else text

/-- One effect of a triggered or activated ability. -/
def parseCatalogEffect (cardName text : String) (n : Nat) : Option (CardAction × Nat) :=
  (catalogActionsFromText cardName (withoutDottedName cardName text) n).bind
    fun (actions, n') => (combineActions actions).map (·, n')

end OracleParts

end Mtg.Engine
