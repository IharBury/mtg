import Mtg.Engine.Card.OracleParse.CatalogEffects

/-!
# Catalog lines

Triggered, activated, and static abilities of a catalog card, including
Saga chapters.
-/

namespace Mtg.Engine

namespace OracleParts

/-- A spell you cast: `a noncreature spell`, `an instant or sorcery spell`,
`a Villain spell`, or `a spell`. -/
def parseSpellYouCast (s : String) : Option Selector :=
  let s := norm s
  if s == "an instant or sorcery spell" then some (.intersection [instantOrSorcery, youControl])
  else if s == "a spell" then some (.intersection [.spell, youControl])
  else
    (before? s " spell").bind dropArticle? |>.bind fun kind =>
      let kindSel :=
        ((after? kind "non").bind typeOfOracle? |>.map fun t => Selector.not (.cardType t)) <|>
          ((typeOfOracle? kind).map Selector.cardType) <|>
          ((subtypeOfOracle? kind).map Selector.subtype)
      kindSel.map fun k => .intersection [.spell, k, youControl]

/-- The event of a trigger condition (CR 603.1), after `when` or `whenever`:
this card entering, dying, attacking, or becoming blocked; another permanent
entering; creatures attacking together; one or more objects dealing damage
to a player; you sacrificing a token; a spell being cast; you drawing a
card; or a second draw or spell in a turn. -/
def parseTriggerEvent (cardName clause : String) : Option Trigger :=
  let c := norm clause
  let self (tail : String) : Option Unit :=
    (before? c tail).bind fun who => if refersToSelf cardName who then some () else none
  -- A plural name takes the plural verb (`The Sackville-Bagginses enter`).
  let selfEvent :=
    ((self " enters or attacks").map fun _ => Trigger.or (.enter .this) (.attack .this .all)) <|>
      ((self " enters" <|> self " enter").map fun _ => Trigger.enter .this) <|>
      ((self " dies" <|> self " die").map fun _ => Trigger.die .this) <|>
      ((self " attacks" <|> self " attack").map fun _ => Trigger.attack .this .all) <|>
      ((self " becomes blocked" <|> self " become blocked").map fun _ => Trigger.block .all .this) <|>
      ((self " deals combat damage to a player" <|> self " deal combat damage to a player").map fun _ =>
        Trigger.combatDamage .this .player)
  let fixed : Option Trigger :=
    match c with
    | "you attack" => some youAttack
    | "you draw a card" => some (.draw (.controller .this) .all)
    | "you draw your second card each turn" =>
      some (.ordinal 2 .turnStart (.draw (.controller .this) .all))
    | "a player casts their second spell each turn" =>
      some (.ordinal 2 .turnStart (.castSpell .spell))
    | "an opponent draws their second card each turn" =>
      some (.ordinal 2 .turnStart (.draw (.opponent (.controller .this)) .all))
    | "equipped creature attacks" => some (.attack (.hostOf .this) .all)
    | "equipped creature deals combat damage to a player" =>
      some (.combatDamage (.hostOf .this) .player)
    | "you sacrifice a token" =>
      some (.sacrifice (.intersection [.zone .battlefield, .token, youControl]))
    | _ => none
  let cast := (after? c "you cast ").bind parseSpellYouCast |>.map Trigger.castSpell
  let selfOrAnother :=
    (before? c " enters").bind (split2? · " or another ") |>.bind fun (who, other) =>
      if !refersToSelf cardName who then none
      else
        (parseObjectDesc ("another " ++ other) true).map fun sel =>
          Trigger.or (.enter .this) (.enter sel)
  let andOr :=
    (before? c " enters").bind (after? · "another ") |>.bind (split2? · " and/or ") |>.bind
      fun (a, b) =>
        let (b, ctl) := splitControllerClause b
        let ctlText := if ctl.isEmpty then "" else " you control"
        match parseObjectDesc ("another " ++ a ++ ctlText) false,
            parseObjectDesc ("another " ++ b ++ ctlText) false with
        | some x, some y => some (Trigger.enter (.union [x, y]))
        | _, _ => none
  let enters :=
    (before? c " enters").bind fun who =>
      let who := (dropArticle? who).getD who
      (parseObjectDesc who false).map Trigger.enter
  let returned :=
    (before? c " is returned to its owner's hand").bind fun who =>
      (parseObjectDesc who false).map Trigger.returnToHand
  let attackTogether :=
    (before? c " attack a player").bind fun who =>
      let counted :=
        ((after? who "one or more ").map (·, ([] : List SetPredicate))) <|>
          ((after? who "two or more ").map (·, [SetPredicate.countAtLeast 2]))
      counted.bind fun (obj, preds) =>
        (parseObjectDesc obj true).map fun sel => Trigger.attackSimultaneously sel .player preds
  let combat :=
    (before? c " deals combat damage to a player or battle").bind fun who =>
      (parseObjectDesc ((dropArticle? who).getD who) true).map fun sel =>
        Trigger.combatDamage sel (.union [.player, .cardType .battle])
  let damageTogether :=
    (before? c " deal damage to a player").bind fun who =>
      (after? who "one or more ").bind fun obj =>
        (parseObjectDesc obj true).map fun sel =>
          Trigger.damageSimultaneously sel .player []
  let leaves :=
    (before? c " leaves your graveyard").bind parseGraveyardCard' |>.map Trigger.leaveGraveyard
  let putCounters :=
    (after? c "you put one or more +1/+1 counters on ").bind fun obj =>
      let obj := (after? obj "one or more ").getD obj
      (parseObjectDesc obj false).map fun sel =>
        Trigger.putCountersSimultaneously (.controller .this) sel .plusOnePlusOne
  -- Plural `enter`, so one trigger for the group. Singular `enters` is per object.
  let enterTogether :=
    (before? c " enter").bind fun who =>
      (after? who "one or more ").bind fun obj =>
        (parseObjectDesc obj false).map fun sel =>
          Trigger.enterSimultaneously sel []
  selfEvent <|> fixed <|> cast <|> selfOrAnother <|> andOr <|> returned <|>
    attackTogether <|> combat <|> damageTogether <|> leaves <|> putCounters <|>
    enterTogether <|> enters
where
  parseGraveyardCard' (s : String) : Option Selector :=
    (dropArticle? s).bind parseGraveyardCard

/-- `When(ever) <event>, <effect>`. The first comma ends the trigger condition
(CR 603.1). -/
def splitTrigger? (line : String) : Option (String × String) :=
  let s := copied (rulesText line)
  let lower := norm s
  let lead :=
    if lower.startsWith "whenever " then some "whenever ".length
    else if lower.startsWith "when " then some "when ".length
    else none
  lead.bind fun k =>
    match (s.drop k).copy.splitOn ", " with
    | clause :: effect :: more =>
      some (copied clause, copied (String.intercalate ", " (effect :: more)))
    | _ => none

/-- A cast trigger whose spell targets something: `a spell that targets a
creature you control`, `an instant or sorcery spell that targets an artifact or
land`, or `a spell that targets one or more creatures`. The trigger is
trigger `n`; its spell is that trigger's first argument. -/
def parseCastTargetsTrigger (clause : String) (n : Nat) : Option (Trigger × Selector) :=
  (after? (norm clause) "you cast ").bind (split2? · " that targets ") |>.bind
    fun (spellText, targetText) =>
      let spell? :=
        if spellText == "an instant or sorcery spell" then
          some [Selector.spell, instantOrSorcery, youControl]
        else if spellText == "a spell" then some [Selector.spell, youControl]
        else none
      let target? :=
        match after? targetText "one or more " with
        | some obj => parseObjectDesc obj false
        | none => (dropArticle? targetText).bind (parseObjectDesc · false)
      match spell?, target? with
      | some spell, some target =>
        some (.triggerId n (.castSpell (.intersection (spell ++ [.hasTarget target]))), target)
      | _, _ => none

/-- `Copy that spell. You may choose new targets for the copy.` The spell is
the first argument of trigger `id` (CR 707.10). -/
def parseCopyThatSpell (id : Nat) (ss : List String) : Option (CardAction × List String) :=
  match ss with
  | copy :: choose :: rest =>
    if sentenceIs copy "copy that spell" &&
        sentenceIs choose "you may choose new targets for the copy" then
      some (.copyWithNewTargets (.controller .this) (.wasArgumentOfTrigger id 1), rest)
    else none
  | _ => none

/-- `Those creatures gain <keywords> until end of turn.` Those creatures are
the targets of the spell that is the first argument of trigger `id`. -/
def parseThoseCreaturesGain (id : Nat) (sentence : String) : Option CardAction :=
  (between? (normSentence sentence) "those creatures gain " " until end of turn").bind
    parseKeywordPhrase |>.bind fun kws =>
      gainUntilEnd
        (.intersection [.zone .battlefield, .cardType .creature, .isTargetOf (.wasArgumentOfTrigger id 1)])
        kws

/-- A cast trigger whose spell targets something, with its effect. -/
def parseCastTargetsLine (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (parseCastTargetsTrigger clause n).bind fun (trigger, _) =>
      let ss := sentences effect
      let copied :=
        (parseCopyThatSpell n ss).bind fun (copy, rest) =>
          (catalogActionsFromText cardName (String.intercalate ". " rest) (n + 1)).bind
            fun (more, n') => (combineActions (copy :: more)).map (·, n')
      let those :=
        match ss with
        | [one] => (parseThoseCreaturesGain n one).map (·, n + 1)
        | _ => none
      (copied <|> those).map fun (action, n') => (.ability (.triggered trigger action), n')

/-- `Whenever you cast a spell that targets a creature you control, <effect>`
where the effect is about this card. The spell's targets are checked when the
ability resolves. -/
def parseCastTargetsYoursLine (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "you cast a spell that targets a ").bind fun obj =>
      (parseObjectDesc obj false).bind fun target =>
        (parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered (.castSpell (.intersection [.spell, youControl]))
            (.if (.targetsIncludeAny .this target) (flattenAction action))), n')

/-- `a` or `b`. `Condition` spells disjunction as the negation of both failing. -/
def either (a b : Condition) : Condition :=
  .not (.and (.not a) (.not b))

/-- `you attacked with a Hero this turn` or `an artifact entered the
battlefield under your control this turn`. -/
def thisTurnCondition? (s : String) : Option Condition :=
  let yours (obj : String) : Option Selector :=
    (dropArticle? obj).bind (parseObjectDesc · false) |>.map andYouControl
  ((between? s "you attacked with " " this turn").bind yours |>.map fun sel =>
    .happened (.attack sel .all) .turnStart) <|>
  ((before? s " entered the battlefield under your control this turn").bind yours |>.map fun sel =>
    .happened (.enter sel) .turnStart)

/-- The condition of an intervening `if` clause (CR 603.4). -/
def interveningCondition? (s : String) : Option Condition :=
  match norm s with
  | "you've drawn two or more cards this turn" =>
    some (.happened (.ordinal 2 .turnStart (.draw (.controller .this) .all)) .turnStart)
  | s =>
    thisTurnCondition? s <|>
      (split2? s " or ").bind fun (a, b) =>
        match thisTurnCondition? a, thisTurnCondition? b with
        | some ca, some cb => some (either ca cb)
        | _, _ => none

/-- `<effect>`, or `if <condition>, <effect>` when that condition is an
intervening if (CR 603.4). A condition this grammar does not know stays part
of the effect. The printed `if` is lowercase, as in the middle of a sentence. -/
def splitInterveningIf (effect : String) : Option Condition × String :=
  match (after? effect "if ").bind (split2? · ", ") with
  | some (c, rest) =>
    match interveningCondition? c with
    | some cond => (some cond, rest)
    | none => (none, effect)
  | none => (none, effect)

/-- Wrap `action` in an intervening if. No condition leaves the effect as printed. -/
def applyInterveningIf (cond? : Option Condition) (action : CardAction) : CardAction :=
  match cond? with
  | some c => CardAction.if c (flattenAction action)
  | none => action

/-- A triggered ability: `When(ever) <event>, <effect>`. -/
def parseCatalogTriggeredPlain (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  let line := withoutDottedName cardName line
  parseCastTargetsLine cardName line n <|>
    parseCastTargetsYoursLine cardName line n <|>
    (splitTrigger? line).bind fun (clause, effect) =>
      (parseTriggerEvent cardName clause).bind fun trigger =>
        let (cond, effect) := splitInterveningIf effect
        (parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered trigger (applyInterveningIf cond action)), n')

/-- The triggered ability in quoted text, such as `Whenever Redwing attacks,
surveil 1.`, of an object named `name`. -/
def quotedTriggered? (name text : String) : Option Ability :=
  (parseCatalogTriggeredPlain name text 1).bind fun
    | (.ability a, _) => some a
    | _ => none

/-- `create Redwing, a legendary 1/1 blue Bird Scout creature token with flying
and "<ability>"`. The token has that name, supertype, power, toughness, color,
subtypes, keywords, and quoted triggered ability. -/
def parseCreateNamedToken (sentence : String) : Option CardAction :=
  let raw := copied sentence
  (if (norm raw).startsWith "create " then
      some ((raw.drop "create ".length).trimAscii.copy)
    else none).bind (split2? · ", a ") |>.bind fun (tokenName, rest) =>
    (split2? rest " creature token with ").bind fun (desc, abilities) =>
        (split2? abilities " and \"").bind fun (kwText, quotedRest) =>
        let kwText :=
          if kwText.endsWith "," then (kwText.dropEnd 1).trimAscii.copy else kwText
        let quotedText := (before? quotedRest "\"").getD quotedRest
        let words := desc.splitOn " " |>.map copied |>.filter (· != "")
        let (sups, words) :=
          match words with
          | w :: more =>
            match supertypeOfOracle? w with
            | some sup => ([sup], more)
            | none => ([], words)
          | [] => ([], [])
        match words with
        | pt :: colorText :: subtypeTexts =>
          match parseUnsignedPT pt, colorName? (norm colorText), subtypeTexts.mapM subtypeOfOracle?,
              parseKeywordPhrase kwText, quotedTriggered? tokenName quotedText with
          | some (p, t), some c, some (st :: sts), some kws, some quoted =>
            some (.createTokens (.controller .this) 1 (
              [.name tokenName, .type .creature] ++ sups.map CardPart.supertype ++
                (st :: sts).map CardPart.subtype ++
                [.colorIndicator [c], .power p, .toughness t] ++
                kws.map (fun k => .ability (.keyword k)) ++ [.ability quoted]))
          | _, _, _, _, _ => none
        | _ => none

/-- `Whenever an equipped creature you control attacks, it connives.` The
attacker is the host of an Equipment you control. -/
def parseEquippedAttacksConnives (line : String) : Option CardPart :=
  if normLine line == "whenever an equipped creature you control attacks, it connives" then
    let host := Selector.hostOf equipmentYouControl
    some (.ability (.triggered (.attack host .all) (.keyword host (.connive (.nat 1)))))
  else none

/-- `Whenever equipped creature attacks, create <tokens>. If that creature is
legendary, instead create <count> of those tokens that are tapped and
attacking.` That creature is this object's host. -/
def parseEquippedAttacksCreateInstead (line : String) : Option CardPart :=
  (splitTrigger? line).bind fun (clause, effect) =>
    if norm clause != "equipped creature attacks" then none
    else
      match sentences effect with
      | [create, instead] =>
        match parseCreateCreatureTokens create,
            between? (normSentence instead) "if that creature is legendary, instead create "
              " of those tokens that are tapped and attacking" with
        | some (.createTokens who k parts [.tapped]), some countText =>
          if (positiveCount countText).map Value.nat != some k then none
          else
            some (.ability (.triggered (.attack (.hostOf .this) .all)
              (.ifElse (.any (.intersection [.hostOf .this, .supertype .legendary]))
                [.createTokens who k parts [.tapped, .attacking]]
                [.createTokens who k parts [.tapped]])))
        | _, _ => none
      | _ => none

/-- `create a 1/1 green Minion creature token named Moloid with "<ability>"`.
The token has that name and the quoted triggered ability. -/
def parseCreateNamedQuotedToken (sentence : String) : Option CardAction :=
  (split2? (stripTrailingPeriod (copied sentence)) " named ").bind fun (head, rest) =>
    (split2? rest " with \"").bind fun (tokenName, quotedRest) =>
      let quotedText := (before? quotedRest "\"").getD quotedRest
      match parseCreateCreatureTokens head, quotedTriggered? tokenName quotedText with
      | some (.createTokens who k parts states), some quoted =>
        some (.createTokens who k (.name tokenName :: parts ++ [.ability quoted]) states)
      | _, _ => none

/-- A triggered ability, including one that creates a named token with a
quoted ability. -/
def parseCatalogTriggered (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (parseEquippedAttacksConnives line).map (·, n) <|>
    (parseEquippedAttacksCreateInstead line).map (·, n) <|>
    ((splitTrigger? line).bind fun (clause, effect) =>
      (parseTriggerEvent cardName clause).bind fun trigger =>
        ((parseCreateNamedToken effect <|> parseCreateNamedQuotedToken effect).map fun action =>
          (.ability (.triggered trigger action), n))) <|>
    parseCatalogTriggeredPlain cardName line n

/-- One printed activation cost, including `Discard this card`, `Pay N life`,
and `Sacrifice an artifact or discard a nonland card`. -/
def parseCatalogCost (cardName s : String) : Option Cost :=
  parseSacrificeOrDiscardCost s <|>
    parsePrintedCost cardName s <|>
    (parsePayLife s).map Cost.life <|>
    ((after? (norm s) "discard ").bind fun obj =>
      if refersToSelf cardName obj || obj == "this card" then some (.discard .this) else none)

/-- `Sacrifice Mount Doom and a legendary artifact`: this object and one other
matching permanent (CR 701.17a). -/
def parseSacrificeThisAnd (cardName s : String) : Option (List Cost) :=
  (after? (norm s) "sacrifice ").bind (split2? · " and ") |>.bind fun (self, obj) =>
    if !refersToSelf cardName self then none
    else
      (dropArticle? obj).bind (parseObjectDesc · false) |>.map fun sel =>
        [.sacrifice .this, .sacrificeCount sel 1]

/-- Costs separated by commas. One unrecognized cost fails the list.
Sacrificing a permanent that is not `another` or `this` is not a cost on its
own, only one item of a list. -/
def parseCatalogCosts (cardName s : String) : Option (List Cost) :=
  let parts := s.splitOn ", " |>.map copied |>.filter (· != "")
  let costs (part : String) : Option (List Cost) :=
    (parseSacrificeThisAnd cardName part) <|> (parseCatalogCost cardName part).map ([·])
  match parts with
  | [] => none
  | [one] => if (parseSacrificeAn one).isSome then none else costs one
  | _ => (parts.mapM costs).map List.flatten

/-- `Activate only if there are two or more creature cards in your graveyard.`
or `Activate only if you control a legendary creature.` -/
def parseActivateOnlyIf (s : String) : Option Condition :=
  ((after? (normSentence s) "activate only if you control ").bind youControlCondition?) <|>
  ((after? (normSentence s) "activate only if this land entered this turn or if you control ").bind
    youControlCondition? |>.map fun cond =>
      either (.happened (.enter (.source .this)) .turnStart) cond) <|>
  (after? (normSentence s) "activate only if ").bind graveyardCountCondition?

/-- `This ability costs {2} less to activate if you control a legendary
creature.` A static ability that reduces this ability's cost. -/
def parseAbilityCostsLessIf (s : String) : Option CardPart :=
  let controls :=
    (after? (normSentence s) "this ability costs ").bind
      (split2? · " less to activate if you control ") |>.bind fun (costText, obj) =>
        (nonemptyMana? costText).bind fun syms =>
          (youControlCondition? (copied obj)).map (syms, ·)
  let targets :=
    (after? (normSentence s) "this ability costs ").bind
      (split2? · " less to activate if it targets ") |>.bind fun (costText, obj) =>
        (nonemptyMana? costText).bind fun syms =>
          (dropArticle? obj).bind parseTargetObject |>.map fun sel =>
            (syms, Condition.targetsIncludeAny .this sel)
  (controls <|> targets).map fun (syms, cond) =>
    .ability (.static (.if cond [.reduceCost .this [.mana syms]]))

/-- `<costs>: <effect>`, with an optional activation limit (CR 602.5) or a
cost reduction that follows the effect. -/
def parseCatalogActivated (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  let line := withoutDottedName cardName line
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    (parseCatalogCosts cardName costText).bind fun costs =>
      let ss := sentences effect
      let (body, limit) := splitActivateLimit ss
      let (body, extra, cond?) :=
        match body.reverse with
        | last :: restRev =>
          match parseActivateOnlyIf last, parseAbilityCostsLessIf last with
          | some cond, _ => (restRev.reverse, [], some cond)
          | none, some part => (restRev.reverse, [part], none)
          | none, none => (body, [], none)
        | [] => (body, [], none)
      if body.isEmpty then none
      else if body.map normSentence ==
          ["return this card from your graveyard to the battlefield tapped"] then
        let gyCond? :=
          match cond?, limit with
          | some cond, .unlimited => some cond
          | none, .asSorcery => some (.timeToCastSorcery (.controller .this))
          | _, _ => none
        gyCond?.map fun cond =>
          ([.ability (.graveyardActivatedIf cond costs
            (.putOntoBattlefieldInState (.intersection [.zone .graveyard, .source .this])
              [.tapped]))] ++ extra, n)
      else
        let effect? :=
          (match body with
            | [one] => parseGainsQuotedUntilEnd cardName one n (quotedTriggered? cardName)
            | _ => none) <|>
          parseCatalogEffect cardName (String.intercalate ". " body) n
        effect?.map fun (action, n') =>
          match cond? with
          | some cond => ([.ability (.activatedIf cond costs action)] ++ extra, n')
          | none =>
            let (part, n'') := activatedWithCost n costs action limit n'
            ([part] ++ extra, n'')

/-- The permanent a static ability is about: the equipped or enchanted creature,
this card, or the printed object. A bare subtype is a creature when
`withCreature` is true. -/
def staticSubject? (cardName who : String) (withCreature : Bool) : Option Selector :=
  match who with
  | "equipped creature" | "enchanted creature" => some (.hostOf .this)
  | _ =>
    if refersToSelf cardName who then some .this else parseObjectDesc who withCreature

/-- `<objects> get +P/+T` or `<objects> get +P/+T for each <objects>`, with no
duration: a static ability (CR 604.2). `Equipped` and `enchanted` creature
is this object's host. A subtype is a creature of that subtype. -/
def parseCatalogStaticGets (cardName line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (splitGets? s).bind fun (who, rest) =>
      let who? := staticSubject? cardName who true
      let (ptText, has?) : String × Option (List Ability) :=
        match split2? rest " and has " <|> split2? rest " and have " with
        | some (pt, has) =>
          (pt, (parseKeywordPhrase has).map (List.map Ability.keyword) <|>
            (genericWard? has).map fun k => [Ability.keywordWithCost .ward [.mana [.generic k]]])
        | none => (rest, some [])
      match who?, has? with
      | some sel, some abilities =>
        match split2? ptText " for each " with
        | some (pt, each) =>
          match parsePowerToughness pt, parseObjectDesc each false with
          | some (p, t), some among =>
            let effects := scaledPowerToughness sel p t
              (fun k => if k == 1 then Value.count among else Value.timesCount k among)
              (fun k => if k == 1 then Value.count among else Value.timesCount k among)
            if effects.isEmpty then none
            else some (effects.map fun e => .ability (.static e))
          | _, _ => none
        | none =>
          (parsePowerToughness ptText).bind fun (p, t) =>
            (staticPowerToughness sel p t).map fun parts =>
              parts ++ abilities.map fun a => .ability (.static (.gainAbility sel a))
      | _, _ => none

/-- `<objects> have <keywords>` or `Equipped creature has <keywords>`: a static
ability. -/
def parseCatalogStaticHas (cardName line : String) : Option (List CardPart) :=
  let s := normLine line
  (split2? s " have " <|> split2? s " has ").bind fun (who, kwText) =>
    let who? := staticSubject? cardName who false
    match who?, parseKeywordPhrase kwText with
    | some sel, some kws =>
      if kws.isEmpty then none
      else some (kws.map fun k => .ability (.static (.gainAbility sel (.keyword k))))
    | _, _ => none

/-- `Other Elves you control have "{T}: Add {G} or {U}."`: the quoted
activated ability is granted by a static ability (CR 113.1a / 604.1). -/
def parseCatalogStaticHasQuoted (cardName line : String) : Option (List CardPart) :=
  (split2? (rulesText line) " have \"" <|> split2? (rulesText line) " has \"").bind
    fun (who, quoted) =>
      (before? quoted "\"").bind fun inner =>
        (parseObjectDesc who false).bind fun sel =>
          match parseCatalogActivated cardName inner 1 with
          | some ([.ability a], _) => some [.ability (.static (.gainAbility sel a))]
          | _ => none

/-- `<this> <mark> <object>`. The condition holds while this object's controller
does not control that object. `mark` is the printed restriction, such as
` enters tapped unless you control `. -/
def notYouControl? (cardName line mark : String) : Option Condition :=
  (split2? (normLine line) mark).bind fun (subject, obj) =>
    if !refersToSelf cardName subject then none
    else (youControlCondition? obj).map Condition.not

/-- `<this> enters tapped unless you control a legendary creature.` It enters
tapped while its controller controls no such permanent. The ability functions
in every zone (CR 113.6) so it can replace how this card enters the
battlefield. -/
def parseEntersTappedUnlessYouControl (cardName line : String) : Option CardPart :=
  (notYouControl? cardName line " enters tapped unless you control ").map fun cond =>
    .ability (.everywhereStatic (.if cond
      [.replace (.enter .this) [.putOntoBattlefieldInState .this [.tapped]]]))

/-- `<this> can't block unless you control a Goblin or Orc.` -/
def parseCantBlockUnlessYouControl (cardName line : String) : Option CardPart :=
  (notYouControl? cardName line " can't block unless you control ").map fun cond =>
    .ability (.static (.if cond [.forbid (.block .this .any)]))

/-- `As long as there are two or more creature cards in your graveyard,
<this> gets +P/+T [and is all creature types].` -/
def parseCatalogAsLongAsGraveyard (cardName line : String) : Option (List CardPart) :=
  (after? (normLine line) "as long as there are ").bind (split2? · " in your graveyard, ") |>.bind
    fun (countText, effect) =>
      (split2? countText " or more ").bind fun (k, cards) =>
        match positiveCount k, (before? cards " cards").bind typeOfOracle? with
        | some k, some t =>
          let cond := Condition.greaterOrEqual
            (.count (.intersection [.zone .graveyard, .cardType t, .owner (.controller .this)]))
            (Value.nat k)
          let (effect, allTypes) :=
            match before? effect " and is all creature types" with
            | some e => (e, true)
            | none => (effect, false)
          (splitGets? effect).bind fun (who, ptText) =>
            if !refersToSelf cardName who then none
            else
              (parsePowerToughness ptText).bind fun (p, t) =>
                staticWhile cond
                  (flatPowerToughness .this p t ++
                    (if allTypes then [.gainAllSubtypes .this .creature] else [])) |>.map ([·])
        | _, _ => none

/-- `As long as you control another Elf, you may play an additional land on
each of your turns.` -/
def parseAnotherAdditionalLand (line : String) : Option CardPart :=
  (between? (normLine line) "as long as you control another "
      ", you may play an additional land on each of your turns").bind subtypeOfOracle? |>.map
    fun st =>
      .ability (.static (.if (.any (anotherSubtypeYouControl st))
        [.increaseLandPlayLimit (.controller .this) (Value.nat 1)]))

/-- `This spell costs {1} less to cast if you control a Villain`, or `… if it
targets an attacking creature`. The reduction functions on the stack
(CR 604.2). -/
def parseCatalogCostReduction (line : String) : Option CardPart :=
  (costsLessBy? (normLine line) " less to cast if ").bind fun (syms, cond) =>
    let controls :=
      (after? cond "you control ").bind dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
        Condition.anySubtype youControl st
    let targets :=
      (after? cond "it targets ").bind dropArticle? |>.bind parseTargetObject |>.map fun sel =>
        Condition.targetsIncludeAny .this sel
    (controls <|> targets <|> graveyardCountCondition? cond).map (reduceOnStack · syms)

/-- `As an additional cost to cast this spell, sacrifice an artifact or
creature.` The ability functions while this spell is on the stack. -/
def parseAdditionalCostSacrificeAn (line : String) : Option CardPart :=
  (after? (normLine line) "as an additional cost to cast this spell, ").bind parseSacrificeAn |>.map
    fun cost => .ability (.stackStatic (.additionalCost .this [cost]))

/-- `Equip Human {1}`: equip onto a creature of that subtype only. -/
def parseEquipSubtype (line : String) : Option CardPart :=
  (after? (rulesText line) "Equip ").bind fun rest =>
    let (word, costText) := splitNameCost rest
    match subtypeOfOracle? word, nonemptyMana? costText with
    | some st, some syms => some (.ability (.keywordWithSubtypeAndCost .equip st (.mana syms)))
    | _, _ => none

/-- `Creatures with flying can't attack you or block creatures you control.` -/
def parseKeywordCantAttackYouOrBlock (line : String) : Option CardPart :=
  (between? (normLine line) "creatures with " " can't attack you or block creatures you control").bind
    keywordOfOracle? |>.map fun k =>
      let with_ := Selector.intersection [.zone .battlefield, .cardType .creature, .keyword k]
      .ability (.static (.forbid (.or
        (.attack with_ (.controller .this))
        (.block with_ creaturesYouControl))))

/-- `<this card> can't be blocked` after an ability word. -/
def parseCatalogCantBeBlocked (cardName line : String) : Option CardPart :=
  (before? (normLine line) " can't be blocked").bind fun who =>
    if refersToSelf cardName who then some (.ability (.static (.forbid (.block .any .this))))
    else none

/-- A Saga chapter ability `I — <effect>` (CR 714.2). `III, IV — <effect>`
is one chapter ability for each number (CR 714.2b), numbered in turn. -/
def parseChapter (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (match (rulesText line).splitOn " — " with
    | nums :: effect@(_ :: _) => some (copied nums, copied (" — ".intercalate effect))
    | _ => none).bind fun (nums, effect) =>
    ((nums.splitOn ", ").mapM chapterNumber?).bind fun ks =>
      if ks.isEmpty then none
      else
        ks.foldlM (fun (parts, n) k =>
          (((parseCreateNamedToken effect).map ([·], n)) <|>
              (catalogActionsFromText cardName effect n) <|>
              (parseSagaGainsQuoted cardName effect).map ([·], n)).map fun (actions, n') =>
            (parts ++ [CardPart.ability (.keywordWithEffect (.chapter k) actions)], n'))
          (([] : List CardPart), n)
where
  /-- `This Saga gains "<triggered ability>".` No duration is printed, so the
  ability lasts until the end of the game (CR 611.2a). -/
  parseSagaGainsQuoted (cardName effect : String) : Option CardAction :=
    (between? (copied effect) "This Saga gains \"" "\"").bind fun quoted =>
      if !(copied effect).endsWith "\"" then none else
      let quoted := (stripTrailingPeriod quoted)
      let quoted := (afterAbilityWord? quoted).getD quoted
      (quotedTriggered? cardName quoted).map fun ability =>
        .continuous [.gainAbility .this ability] .endOfGame

/-- A line about `equipped creature` or `enchanted creature`, which is an
ability of an Equipment or Aura rather than a spell. -/
def hostSubject? (line : String) : Bool :=
  (normLine line).startsWith "equipped creature " || (normLine line).startsWith "enchanted creature "

/-- `Whenever you discard a card, you may exile that card from your graveyard.
If you do, until the end of your next turn, you may play that card.` The
discard is trigger `n` and the exile is action `n`. -/
def parseDiscardMayExilePlay (line : String) (n : Nat) : Option (CardPart × Nat) :=
  if normLine line ==
      "whenever you discard a card, you may exile that card from your graveyard. if you do, until the end of your next turn, you may play that card" then
    some (.ability (.triggered (.triggerId n (.discard (.controller .this)))
      (.optional (.controller .this) (.sequence [
        .actionId n (.exile (.intersection [
          .zone .graveyard, .wasArgumentOfTrigger n 1, .owner (.controller .this)])),
        .continuous [.canPlay (.controller .this) (.wasCreatedByAction n)]
          (.sequence [.turnStart, .endOfPlayerTurn (.controller .this)])]))), n + 1)
  else none

/-- `As long as you've put one or more +1/+1 counters on <this> this turn,
<this> has <keyword>.` -/
def parseKeywordIfCountersPutThisTurn (cardName line : String) : Option CardPart :=
  (after? (normLine line) "as long as you've put one or more +1/+1 counters on ").bind
    (split2? · " this turn, ") |>.bind fun (who, rest) =>
      (split2? rest " has ").bind fun (who', kw) =>
        if refersToSelf cardName who && damageSource? cardName who' then
          (keywordOfOracle? kw).map fun k =>
            .ability (.static (.if
              (.happened
                (.putCountersSimultaneously (.controller .this) .this .plusOnePlusOne)
                .turnStart)
              [.gainAbility .this (.keyword k)]))
        else none

/-- `If damage would be dealt to <this>, instead that damage is dealt, but all
other damage already dealt to him is healed.` A replacement effect (CR 614.1):
the damage is dealt after the damage already marked is removed. -/
def parseDamageHealsOther (cardName line : String) : Option CardPart :=
  (between? (normLine line) "if damage would be dealt to " " is healed").bind fun rest =>
    (split2? rest ", instead that damage is dealt, but all other damage already dealt to ").bind
      fun (who, pronoun) =>
        if refersToSelf cardName who && (pronoun == "him" || pronoun == "her" || pronoun == "it") then
          some (.ability (.static (.replace (.damage .all .this)
            [.healAllDamage .this, .keepReplacedAction])))
        else none

/-- `As this enchantment enters, choose a creature type.` then
`Creatures you control of the chosen type get +2/+2.` The choice is action
`n`. This object's controller makes it as a replacement of this object
entering (CR 614.12). The bonus is a static ability on creatures of that
type. A zero bonus is omitted. `+0/+0` is not an effect. -/
def parseAsEntersChooseCreatureType (cardName choose gets : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (between? (normLine choose) "as " " enters, choose a creature type").bind fun who =>
    if !refersToSelf cardName who then none
    else
      (splitGets? (normLine gets)).bind fun (whoGets, ptText) =>
        match (before? whoGets " of the chosen type").bind parseControlledPhrase,
            parsePowerToughness ptText with
        | some (.intersection sel), some (p, t) =>
          let chosen := Selector.intersection (sel ++ [.hasCreatureTypeChosenByAction n])
          (staticPowerToughness chosen p t).map fun bonus =>
            (.ability (.static (.replace (.enter .this)
                [.actionId n (.chooseCreatureType (.controller .this)), .keepReplacedAction])) ::
              bonus,
              n + 1)
        | _, _ => none

/-- The step or phase of `At the beginning of <phase>` (CR 503.1 / 507.1 /
513.1): `combat on your turn`, `each combat`, `your upkeep`, `your end step`,
`each end step`, or `the upkeep of enchanted creature's controller`. -/
def beginningPhase? (s : String) : Option Trigger :=
  match norm s with
  | "combat on your turn" => some (.combatStart (.controller .this))
  | "each combat" => some (.combatStart .player)
  | "your upkeep" => some (.upkeep (.controller .this))
  | "your end step" => some (.endStep (.controller .this))
  | "each end step" => some (.endStep .player)
  | "the upkeep of enchanted creature's controller" =>
    some (.upkeep (.controller (.hostOf .this)))
  | _ => none

/-- `At the beginning of <phase>, [if <condition>,] <effect>.` The condition is
an intervening if (CR 603.4): checked when the phase begins and again on
resolution. -/
def parseBeginningOfTriggered (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (after? (copied (rulesText line)) "At the beginning of ").bind fun rest =>
    match rest.splitOn ", " with
    | phase :: more =>
      (beginningPhase? phase).bind fun trigger =>
        let (cond, effect) : Option Condition × String :=
          match more with
          | c :: effect@(_ :: _) =>
            match (after? (norm c) "if ").bind interveningCondition? with
            | some cond => (some cond, ", ".intercalate effect)
            | none => (none, ", ".intercalate more)
          | _ => (none, ", ".intercalate more)
        let thatPlayer : Option (CardAction × Nat) :=
          match trigger with
          | .upkeep who =>
            if norm effect == "that player draws a card" then some (.draw who 1, n) else none
          | _ => none
        (thatPlayer <|> parseCatalogEffect cardName effect n).map fun (action, n') =>
          (.ability (.triggered trigger (applyInterveningIf cond action)), n')
    | [] => none

/-- `∞ — At the beginning of <phase>, <effect>.` ∞ (CR 702.186) means this
permanent has that ability as long as it is harnessed. -/
def parseInfinity (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  (after? (rulesText line) "∞ — ").bind fun rest =>
    (parseBeginningOfTriggered cardName rest n).bind fun (part, n') =>
      match part with
      | .ability a => some ([.ability (.keywordWithAbility .infinity a)], n')
      | _ => none

/-- `The first creature spell you cast each turn costs {2} less to cast and can
be cast as though it had flash.` The spell is first when no creature spell of
yours was cast earlier this turn. Neither effect grants flash. -/
def parseFirstCreatureSpellCostsLessFlash (line : String) : Option (List CardPart) :=
  (between? (normLine line) "the first creature spell you cast each turn costs "
      " less to cast and can be cast as though it had flash").bind parseManaSymbols |>.map
    fun syms =>
      let creatureSpell := Selector.intersection [.spell, .cardType .creature, youControl]
      let first := Condition.didNotHappen (.castSpell creatureSpell) .turnStart
      [.ability (.static (.if first [.reduceCost creatureSpell [.mana syms]])),
       .ability (.static (.canBeCastAsThoughWithFlashIf creatureSpell first))]

/-- `Whenever another creature you control enters, if it has greater power or
toughness than <this>, put a +1/+1 counter on <this>.` The entering creature is
argument 1 of trigger 1. The comparison is an intervening if (CR 603.4). -/
def parseEntersGreaterThanSelfCounter (cardName line : String) : Option CardPart :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "another ").bind (before? · " enters") |>.bind fun obj =>
      (parseObjectDesc ("another " ++ obj) false).bind fun sel =>
        (after? (norm effect) "if it has greater power or toughness than ").bind
          (split2? · ", put a +1/+1 counter on ") |>.bind fun (a, b) =>
            if !(refersToSelf cardName a && refersToSelf cardName b) then none
            else
              let it := Selector.wasArgumentOfTrigger 1 1
              let greater := fun (v : Selector → Value) => Condition.greater (v it) (v (.source .this))
              some (.ability (.triggered (.triggerId 1 (.enter sel))
                (.if (either (greater .greatestPower) (greater .greatestToughness))
                  [.putCounter (.source .this) .plusOnePlusOne 1])))

/-- `Whenever you cast a spell that targets a creature you control, <this>
gains "<activated ability>" until end of turn.` -/
def parseCastTargetsYoursGainsQuoted (cardName line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitTrigger? line).bind fun (clause, effect) =>
    (after? (norm clause) "you cast a spell that targets a ").bind fun obj =>
      (parseObjectDesc obj false).bind fun target =>
        let quoted (text : String) : Option Ability :=
          match parseCatalogActivated cardName text 1 with
          | some ([.ability a], _) => some a
          | _ => none
        (parseGainsQuotedActivatedUntilEnd cardName effect n quoted).map fun (action, n') =>
          (.ability (.triggered (.castSpell (.intersection [.spell, youControl]))
            (.if (.targetsIncludeAny .this target) [action])), n')

/-- `Flying, first strike, ward {1}`: keywords, then generic ward last. -/
def parseKeywordsThenWard (line : String) : Option (List CardPart) :=
  let tokens := (rulesText line).splitOn "," |>.map copied |>.filter (· != "")
  match tokens.reverse with
  | last :: restRev@(_ :: _) =>
    match genericWard? last, restRev.reverse.mapM keywordOfOracle? with
    | some n, some kws =>
      some (kws.map (fun k => .ability (.keyword k)) ++
        [.ability (.keywordWithCost .ward [.mana [.generic n]])])
    | _, _ => none
  | _ => none

/-- `Prevent all damage that would be dealt to <this>.` A prevention effect
replaces that damage with nothing (CR 615.1). -/
def parsePreventAllDamageToSelf (cardName line : String) : Option CardPart :=
  (after? (normLine line) "prevent all damage that would be dealt to ").bind fun who =>
    if refersToSelf cardName who then
      some (.ability (.static (.replace (.damage .all .this) [])))
    else none

/-- `As long as an opponent has cast a spell this turn, you may cast spells as
though they had flash.` The spells don't gain flash (CR 702.8). -/
def parseFlashIfOpponentCast (line : String) : Option CardPart :=
  if normLine line ==
      "as long as an opponent has cast a spell this turn, you may cast spells as though they had flash" then
    some (.ability (.static (.canBeCastAsThoughWithFlashIf
      (.intersection [.spell, youControl])
      (.happened (.castSpell (.intersection [.spell, .controlled (.opponent (.controller .this))]))
        .turnStart))))
  else none

/-- One `you control <object>` piece: `an artifact creature` or `a Plan`. An
object of several card types has all of them. -/
def youControlPiece? (obj : String) : Option Condition :=
  youControlCondition? obj <|>
    ((dropArticle? obj).bind (fun o => ((norm o).splitOn " ").mapM typeOfOracle?) |>.map fun ts =>
      .any (.intersection ([.zone .battlefield] ++ ts.map Selector.cardType ++ [youControl])))

/-- `As long as you control an artifact creature or a Plan, <this> has
indestructible.` Either permanent satisfies the condition. -/
def parseAsLongAsYouControlHas (cardName line : String) : Option CardPart :=
  (after? (normLine line) "as long as you control ").bind (split2? · ", ") |>.bind
    fun (obj, rest) =>
      (split2? rest " has ").bind fun (who, kwText) =>
        if !refersToSelf cardName who then none
        else
          let cond? : Option Condition :=
            match split2? obj " or " with
            | some (a, b) =>
              match youControlPiece? a, youControlPiece? b with
              | some ca, some cb => some (either ca cb)
              | _, _ => none
            | none => youControlPiece? obj
          match cond?, parseKeywordPhrase kwText with
          | some cond, some kws =>
            some (.ability (.static (.if cond (kws.map fun k => .gainAbility .this (.keyword k)))))
          | _, _ => none

/-- `discard a card or pay {2}` as one cost with two choices. -/
def discardOrPayCost? (s : String) : Option Cost :=
  (split2? (norm s) " or pay ").bind fun (discard, pay) =>
    if discard != "discard a card" then none
    else (nonemptyMana? pay).map fun syms =>
      .or [.discard (.selected (.controller .this) (.range 1 1)
        (.intersection [.zone .hand, .owner (.controller .this)])), .mana syms]

/-- `As an additional cost to cast this spell, discard a card or pay {2}.` -/
def parseAdditionalCostDiscardOrPay (line : String) : Option CardPart :=
  (after? (normLine line) "as an additional cost to cast this spell, ").bind discardOrPayCost? |>.map
    fun cost => .ability (.stackStatic (.additionalCost .this [cost]))

/-- `Ward—Discard a card or pay {2}.` (CR 702.21) -/
def parseWardDiscardOrPay (line : String) : Option CardPart :=
  (after? (normLine line) "ward—").bind discardOrPayCost? |>.map fun cost =>
    .ability (.keywordWithCost .ward [cost])

/-- `You may play lands from your graveyard.` -/
def parseMayPlayLandsFromGraveyard (line : String) : Option CardPart :=
  if normLine line == "you may play lands from your graveyard" then
    some (.ability (.static (.canPlay (.controller .this)
      (.intersection [.zone .graveyard, .cardType .land, .owner (.controller .this)]))))
  else none

/-- `Enchanted creature loses all abilities and doesn't untap during its
controller's untap step.` -/
def parseEnchantedLosesAbilitiesDoesntUntap (line : String) : Option (List CardPart) :=
  if normLine line ==
      "enchanted creature loses all abilities and doesn't untap during its controller's untap step" then
    some [
      .ability (.static (.removeAllAbilities (.hostOf .this))),
      .ability (.static (.doesntUntap (.hostOf .this)))]
  else none

/-- `Whenever <this> enters or attacks, put a +1/+1 counter on target creature.`
The entering or attacking object is this card. The creature is target `n`. -/
def parseEnterOrAttackPlusOne (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (triggerSelfEffect? cardName "whenever" (normLine line) " enters or attacks, ").bind
    (parsePutPlusOneOnTarget · n) |>.map fun (action, n') =>
      (.ability (.triggered (.or (.enter .this) (.attack .this .all)) action), n')

/-- `As long as you have an enduring story, if a triggered ability of a <subtype> you control triggers, that ability triggers an additional time.`
The source is a permanent of that subtype this object's controller controls.
`replace` of `abilityTriggers` is that triggering.
`duplicateReplacingTrigger 2` is that ability triggering twice instead of
once, which is one additional time (CR 603.2d). -/
def parseExtraTriggerIfEnduringStory (line : String) : Option CardPart :=
  (after? (normLine line)
      "as long as you have an enduring story, if a triggered ability of ").bind fun rest =>
    (before? rest " triggers, that ability triggers an additional time").bind fun who =>
      let (obj, controlled) := splitYouControl who
      if !controlled then none
      else
        (dropArticle? obj).bind subtypeOfOracle? |>.map fun st =>
          .ability (.static (.if (.enduringStory (.controller .this)) [
            .replace
              (.abilityTriggers
                (.intersection [.zone .battlefield, .subtype st, youControl]))
              [.duplicateReplacingTrigger 2]]))

/-- `Spells you cast from anywhere other than your hand cost {N} less to cast.`
`{N}` is generic mana and is not zero. Those spells are ones this object's
controller casts. `castFromZone .hand` is that player's hand. -/
def parseNotFromHandCostLess (line : String) : Option CardPart :=
  (between? (normLine line)
      "spells you cast from anywhere other than your hand cost "
      " less to cast").bind positiveGeneric? |>.map fun k =>
    .ability (.static (.reduceCost
      (.intersection [
        .spell,
        youControl,
        .not (.castFromZone .hand)])
      [.mana [.generic k]]))

/-- An artifact, instant, or sorcery card in this object's controller's graveyard. -/
def artifactInstantOrSorceryInYourGraveyard : Selector :=
  .intersection [
    .zone .graveyard,
    .owner (.controller .this),
    .union [.cardType .artifact, .cardType .instant, .cardType .sorcery]]

/-- `Whenever <this> attacks, you may cast an artifact, instant, or sorcery spell from your graveyard. If an instant or sorcery spell cast this way would be put into your graveyard, exile it instead.`
The cast is action `n` and pays that spell's cost. `mayCast` allows any
number of matching spells; `selected` with range 1–1 is this one spell.
An instant or sorcery that was that action is exiled instead of being put
into a graveyard. The printed text states no shorter duration, so the
replacement lasts until the end of the game (CR 611.2a). -/
def parseAttackMayCastFromGraveyard (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [cast, exile] =>
    match triggerSelfEffect? cardName "whenever" (normSentence cast) " attacks, " with
    | some effect =>
      if sentenceIs effect
          "you may cast an artifact, instant, or sorcery spell from your graveyard" &&
          sentenceIs exile
            "if an instant or sorcery spell cast this way would be put into your graveyard, exile it instead" then
        some (
          .ability (.triggered (.attack .this .all) (.sequence [
            .actionId n
              (.mayCast
                (.controller .this)
                (.selected (.controller .this) (.range 1 1)
                  artifactInstantOrSorceryInYourGraveyard)),
            .continuous
              [.replace
                (.putToGraveyard
                  (.intersection [
                    .wasObjectOfAction n,
                    .union [.cardType .instant, .cardType .sorcery]]))
                [.exile .replacingObject]]
              .endOfGame])),
          n + 1)
      else none
    | none => none
  | _ => none

/-- Static and cost lines of a catalog card, before its triggers. -/
private def parseCatalogLineStatic (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (parseExtraTriggerIfEnduringStory line).map ([·], n) <|>
    (parseNotFromHandCostLess line).map ([·], n) <|>
    (parseEnchantedLosesAbilitiesDoesntUntap line).map (·, n) <|>
    (parseMayPlayLandsFromGraveyard line).map ([·], n) <|>
    (parseKeywordsThenWard line).map (·, n) <|>
    (parseEntersGreaterThanSelfCounter cardName line).map ([·], n) <|>
    (parseCastTargetsYoursGainsQuoted cardName line n).map (fun (p, n') => ([p], n')) <|>
    (parsePreventAllDamageToSelf cardName line).map ([·], n) <|>
    (parseFlashIfOpponentCast line).map ([·], n) <|>
    (parseAsLongAsYouControlHas cardName line).map ([·], n) <|>
    (parseAdditionalCostDiscardOrPay line).map ([·], n) <|>
    (parseWardDiscardOrPay line).map ([·], n) <|>
    (parseCreaturesWithPlusOneHave line).map (·, n) <|>
    (parseEquipSubtype line).map ([·], n) <|>
    (parseDiscardMayExilePlay line n).map (fun (p, n') => ([p], n')) <|>
    (parseKeywordIfCountersPutThisTurn cardName line).map ([·], n) <|>
    (parseDamageHealsOther cardName line).map ([·], n) <|>
    (parseCatalogCostReduction line).map ([·], n) <|>
    (parseAdditionalCostSacrificeAn line).map ([·], n) <|>
    (parseAnotherAdditionalLand line).map ([·], n) <|>
    (parseKeywordCantAttackYouOrBlock line).map ([·], n) <|>
    (parseCatalogCantBeBlocked cardName line).map ([·], n) <|>
    (parseCatalogAsLongAsGraveyard cardName line).map (·, n)

/-- Triggered, activated, and spell lines of a catalog card. -/
private def parseCatalogLineRest (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (parseEnterOrAttackPlusOne cardName line n).map (fun (p, n') => ([p], n')) <|>
    (parseAttackMayCastFromGraveyard cardName line n).map (fun (p, n') => ([p], n')) <|>
    parseChapter cardName line n <|>
    (parseCatalogTriggered cardName line n).map (fun (p, n') => ([p], n')) <|>
    parseCatalogActivated cardName line n <|>
    (parseCatalogStaticGets cardName line).map (·, n) <|>
    (parseCatalogStaticHasQuoted cardName line).map (·, n) <|>
    (parseEntersTappedUnlessYouControl cardName line).map ([·], n) <|>
    (parseCantBlockUnlessYouControl cardName line).map ([·], n) <|>
    (parseCatalogStaticHas cardName line).map (·, n) <|>
    (parseBeginningOfTriggered cardName line n).map (fun (p, n') => ([p], n')) <|>
    (parseFirstCreatureSpellCostsLessFlash line).map (·, n) <|>
    if hostSubject? line then none
    else
      spellActions ((catalogActionsFromText cardName line n).map fun (actions, n') =>
        (actions.flatMap flattenAction, n'))

/-- One catalog line that is not a mode list. -/
@[noinline]
def parseCatalogLine (cardName line : String) (n : Nat) : Option (List CardPart × Nat) :=
  parseCatalogLineStatic cardName line n <|> parseCatalogLineRest cardName line n

end OracleParts

end Mtg.Engine
