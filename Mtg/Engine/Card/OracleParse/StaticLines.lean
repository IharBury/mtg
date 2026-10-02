import Mtg.Engine.Card.OracleParse.Lines

/-!
# Keyword and static lines

Equipment, keyword abilities, enduring story, and other static text.
-/

namespace Mtg.Engine

namespace OracleParts

/-- `<this> to it`: attach this object to the token just created. -/
def attachSelfToIt? (cardName s : String) : Bool :=
  (before? (norm s) " to it").any (refersToSelf cardName)

/-- `<this> to the amassed Army`: attach this object to the Army just amassed. -/
def attachSelfToAmassedArmy? (cardName s : String) : Bool :=
  (before? (norm s) " to the amassed army").any (refersToSelf cardName)

/-- `Whenever an artifact you control enters, draw a card.`
One card. Drawing more than one is a different ability. -/
def parseArtifactYouControlEntersDraw (line : String) : Option CardPart :=
  (after? (normLine line) "whenever an artifact you control enters, ").bind
      fun effect =>
    match (after? effect "draw ").bind parseCardCount with
    | some 1 =>
      some (.ability (.triggered
        (.enter (permanentWith [.artifact] [youControl]))
        (.draw (.controller .this) 1)))
    | _ => none

/-- `<this> can't attack unless you control two or more other Wolves.`
The subject is this card. The subtype is plural. Attacking is forbidden
while its controller controls fewer than that many other permanents of
that subtype. -/
def parseCantAttackUnlessNOther (cardName : String) (line : String) : Option CardPart :=
  (split2? (normLine line) " can't attack unless you control ").bind fun (subject, rest) =>
    if !refersToSelf cardName subject then none
    else
      (split2? rest " or more other ").bind fun (countText, plural) =>
        match positiveCount countText, pluralCreatureType? plural with
        | some n, some st =>
          some (.ability (.static (.if
            (.less
              (.count
                (.intersection [
                  .not .this,
                  .zone .battlefield,
                  .subtype st,
                  youControl]))
              (Value.int n))
            [.forbid (.attack .this .all)])))
        | _, _ => none

/-- `At the beginning of your upkeep, create a 2/2 green Wolf creature token.`
Also `create a Treasure token`. `your` is this object's controller. -/
def parseUpkeepCreateCreature (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your upkeep, ").bind fun effect =>
    (parseCreateColoredCreatureToken effect <|> parseCreateTreasure effect).map
      fun action =>
        .ability (.triggered (.upkeep (.controller .this)) action)

/-- `When this Equipment enters, create a 2/2 red Dwarf creature token, then attach this Equipment to it.`
One token is created. This object is attached to that token. The creation
is action `n`. -/
def parseEnterCreateThenAttach (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (split2? effect ", then attach ").bind fun (createText, attachText) =>
      match parseCreateColoredCreatureToken createText with
      | some (.createTokens who (.int 1) parts []) =>
        if who == .controller .this && attachSelfToIt? cardName attachText then
          some (
            .sequence [
              .actionId n (.createTokens who 1 parts),
              .attach .this (.wasCreatedByAction n)],
            n + 1)
        else none
      | _ => none

/-- `When this Equipment enters, amass Goblins 1, then attach this Equipment to the amassed Army.`
Amass is a keyword action of this card's controller. This object is attached
to the Army that action amassed. The amass is action `n`. A reminder
parenthetical is not rules text. -/
def parseEnterAmassThenAttach (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (split2? effect ", then attach ").bind fun (amassText, attachText) =>
      match parseAmass amassText with
      | some amass =>
        if attachSelfToAmassedArmy? cardName attachText then
          some (
            .sequence [
              .actionId n amass,
              .attach .this (.wasObjectOfAction n)],
            n + 1)
        else none
      | none => none

/-- `Enchant creature.` Enchant (CR 702.5). The permanent is target `n`. -/
def parseEnchant (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (normLine line) "enchant ").bind fun rest =>
    (parseBattlefieldTarget ("target " ++ rest)).map fun sel =>
      (.ability (.keywordWithTarget .enchant n sel), n + 1)

/-- `Ward {3}`. A positive generic cost (CR 702.21). A reminder parenthetical
is not rules text. -/
def parseWard (line : String) : Option CardPart :=
  (genericWard? (normLine line)).map fun n =>
    .ability (.keywordWithCost .ward [.mana [.generic n]])

/-- `Each creature you control with a +1/+1 counter on it has menace.`
A reminder parenthetical is not rules text. -/
def parseCreaturesWithPlusOneHaveMenace (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "each creature you control with a +1/+1 counter on it has menace" then
    some (.ability (.static (.gainAbility
      (.intersection [
        .zone .battlefield, .cardType .creature, youControl, .hasCounter .plusOnePlusOne])
      (.keyword .menace))))
  else none

/-- `Creatures you control with +1/+1 counters on them have trample.` -/
def parseCreaturesWithPlusOneHave (line : String) : Option (List CardPart) :=
  (after? (normLine line) "creatures you control with +1/+1 counters on them have ").bind
    parseKeywordPhrase |>.map fun kws =>
      kws.map fun k => .ability (.static (.gainAbility
        (.intersection [
          .zone .battlefield, .cardType .creature, youControl, .hasCounter .plusOnePlusOne])
        (.keyword k)))

/-- `At the beginning of your end step, draw a card.`
`your` is this object's controller. One card. -/
def parseYourEndStepDraw (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your end step, ").bind fun effect =>
    match (after? effect "draw ").bind parseCardCount with
    | some 1 =>
      some (.ability (.triggered
        (.endStep (.controller .this))
        (.draw (.controller .this) 1)))
    | _ => none

/-- `attach it to target Dwarf you control`. `it` or this card is the
attachment. The destination is target `n`. -/
def parseAttachSelfToTarget (cardName effect : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (split2? (normSentence effect) " to ").bind fun (head, dest) =>
    (after? head "attach ").bind fun subject =>
      if subject != "it" && !refersToSelf cardName subject then none
      else
        (parseBattlefieldTarget dest).map fun sel =>
          (.attach .this (.target n sel), n + 1)

/-- `When this Equipment enters, attach it to target Dwarf you control.`
The entering object is this card. -/
def parseEnterAttachToTarget (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parseAttachSelfToTarget cardName · n)

/-- `attach target Equipment you control to up to one target creature you control.`
The Equipment is target `n`. Up to one creature is target `n + 1`. -/
def parseAttachTargetEquipment (effect : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence effect) "attach target equipment you control to ").bind
    fun dest =>
      let upToOne :=
        if dest == "up to one target creature you control" then
          some (.targets (n + 1) (.range 0 1) creaturesYouControl)
        else if dest == "target creature you control" then
          some (.target (n + 1) creaturesYouControl)
        else none
      upToOne.map fun creature =>
        (.attach (.target n equipmentYouControl) creature, n + 2)

/-- `When <this> enters, attach target Equipment you control to up to one target creature you control.`
The entering object is this card. -/
def parseEnterAttachTargetEquipment (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parseAttachTargetEquipment · n)

/-- A spell or ability controlled by an opponent of this object's controller. -/
def spellOrAbilityOpponentControls : Selector :=
  .intersection [
    .union [.spell, .ability],
    .controlled (.opponent (.controller .this))]

/-- `Whenever <this> becomes the target of a spell or ability an opponent controls, draw a card.`
One card. The spell or ability is the first argument of `target`; this
object is the target. One trigger, even if that spell or ability targets
this more than once. -/
def parseBecomesTargetDraw (cardName : String) (line : String) : Option CardPart :=
  (triggerSelfEffect? cardName "whenever" (normLine line)
      " becomes the target of a spell or ability an opponent controls, ").bind
    fun effect =>
      match (after? effect "draw ").bind parseCardCount with
      | some 1 =>
        some (.ability (.triggered
          (.target spellOrAbilityOpponentControls .this)
          (.draw (.controller .this) 1)))
      | _ => none

/-- `At the beginning of your first main phase, add {R}{R}.`
`your` is this object's controller. Every symbol must be mana that can be added. -/
def parseFirstMainAddMana (line : String) : Option CardPart :=
  (after? (normLine line) "at the beginning of your first main phase, add ").bind
    nonemptyMana? |>.bind fun syms =>
      match CardAction.addedManaTypes? syms with
      | some _ =>
        some (.ability (.triggered
          (.precombatMainPhase (.controller .this))
          (.addMana (.controller .this) syms)))
      | none => none

/-- `Crew 2`. Crew (CR 702.122). `N` is the number of creatures to tap.
A reminder parenthetical is not rules text. -/
def parseCrew (line : String) : Option CardPart :=
  (after? (normLine line) "crew ").bind positiveCount |>.map fun n =>
    .ability (.keyword (.crew n))

/-- `Teamwork 2`. Teamwork (CR 702.194). `N` is a positive total power.
A reminder parenthetical is not rules text. -/
def parseTeamwork (line : String) : Option CardPart :=
  (after? (normLine line) "teamwork ").bind positiveCount |>.map fun n =>
    .ability (.keyword (.teamwork n))

/-- `Gift a Food`, `Gift a card`, `Gift a tapped Fish`, `Gift an extra turn`,
`Gift a Treasure`, or `Gift an Octopus` (CR 702.174d–i). A reminder
parenthetical is not rules text. -/
def parseGift (line : String) : Option CardPart :=
  let gift? :=
    match normLine line with
    | "gift a food" => some Gift.food
    | "gift a card" => some Gift.card
    | "gift a tapped fish" => some Gift.tappedFish
    | "gift an extra turn" => some Gift.extraTurn
    | "gift a treasure" => some Gift.treasure
    | "gift an octopus" => some Gift.octopus
    | _ => none
  gift?.map fun g => .ability (.keyword (.gift g))

/-- `him`, `her`, `them`, or `it`: the object named earlier in this ability. -/
def isObjectPronoun (s : String) : Bool :=
  match norm s with
  | "him" | "her" | "them" | "it" => true
  | _ => false

/-- `{6}: Gandalf's owner shuffles him into their library and draws three cards.`
The owner is bound to variable `n` before the shuffle. That recorded
player draws afterward. -/
def parseOwnerShuffleDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      (parseActivationCost cardName costText).bind fun costs =>
        (split2? (normSentence effect) " owner shuffles ").bind fun (whose, rest) =>
          if !possessiveSelf cardName whose then none
          else
            (split2? rest " into their library and draws ").bind fun (obj, countText) =>
              if !(isObjectPronoun obj || refersToSelf cardName obj) then none
              else
                (parseCardCount countText).map fun k =>
                  activatedWithCost n costs
                    (.sequence [
                      .defineSelectorVariable n (.owner (.source .this)),
                      .shuffleIntoOwnersLibrary (.source .this),
                      .draw (.variable n) (Value.int k)])
                    .unlimited
                    (n + 1)

/-- `Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less.`
The creature is target `n`. `N` is a positive printed power. The card enters
already attached to that creature (CR 303.4f). -/
def parseReturnAttachedPowerAtMost (sentence : String) (n : Nat) :
    Option (CardAction × Nat) :=
  (after? (normSentence sentence)
      "return this card from your graveyard to the battlefield attached to ").bind
    fun dest =>
      (split2? dest " with power ").bind fun (targetText, powerText) =>
        (before? powerText " or less").bind positiveCount |>.bind fun p =>
          (parseTargetPhrase targetText).bind fun sel =>
            if sel != permanentWith [.creature] [youControl] then none
            else
              let among :=
                extendIntersection [] sel [.powerAtMost (Value.int (p : Int))]
              some (
                .putOntoBattlefieldInState
                  (.intersection [.zone .graveyard, .source .this])
                  [.attachedTo (.target n among)],
                n + 1)

/-- `{2}{W/U}{W/U}: Return this card from your graveyard to the battlefield attached to target creature you control with power 1 or less. Activate only as a sorcery.`
The ability functions in a graveyard (CR 113.6). -/
def parseReturnFromGyAttach (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    match sentences effect with
    | [body, restrict] =>
      if !sentenceIs restrict "activate only as a sorcery" then none
      else
        match parsePrintedCosts "" costText, parseReturnAttachedPowerAtMost body n with
        | some costs, some (action, n') =>
          some (
            .ability (
              .graveyardActivatedIf
                (.timeToCastSorcery (.controller .this))
                costs
                action),
            n')
        | _, _ => none
    | _ => none

/-- `Flashback {4}{W}`. A reminder parenthetical is not rules text (CR 702.34). -/
def parseFlashback (line : String) : Option CardPart :=
  match (after? (normLine line) "flashback ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .flashback [.mana syms]))
  | none => none

/-- `Kicker {2}{W}`. A reminder parenthetical is not rules text (CR 702.32). -/
def parseKicker (line : String) : Option CardPart :=
  match (after? (normLine line) "kicker ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .kicker [.mana syms]))
  | none => none

/-- `Sneak {1}{B}{B}`. A reminder parenthetical is not rules text. -/
def parseSneak (line : String) : Option CardPart :=
  match (after? (normLine line) "sneak ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .sneak [.mana syms]))
  | none => none

/-- `Affinity for Elves` or `Affinity for artifacts` (CR 702.40).
The word after `for` is one plural card type or one subtype plural. -/
def parseAffinity (line : String) : Option CardPart :=
  (after? (normLine line) "affinity for ").bind fun rest =>
    if rest.isEmpty then none
    else
      match cardTypes.find? (fun t => norm (Keyword.affinityPhrase [t] []) == rest) with
      | some t => some (.ability (.keyword (.affinity [t] [])))
      | none =>
        match cardSubtypes.find? (fun st => norm (Keyword.affinityPhrase [] [st]) == rest) with
        | some st => some (.ability (.keyword (.affinity [] [st])))
        | none => none

/-- Creature permanents with flying that this object's controller controls. -/
def flyingCreaturesYouControl : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .keyword .flying, youControl]

/-- Treasure artifacts this object's controller controls. -/
def treasuresYouControl : Selector :=
  .intersection [
    .zone .battlefield, .cardType .artifact, .subtype .treasure, youControl]

/-- An attacking creature. -/
def attackingCreatureTarget : Selector :=
  .intersection [.zone .battlefield, .cardType .creature, .attacking .all]

/-- `he`, `she`, `it`, `they`, or another reference to this card. -/
def damageSource? (cardName who : String) : Bool :=
  who != "" && (isPersonalPronoun who || refersToSelf cardName who)

/-- `<this> has <keyword> as long as you control another <subtype>.`
This has that keyword while its controller controls another permanent of
that subtype. The subtype is singular. -/
def parseKeywordIfAnother (cardName line keywordText : String) (k : Keyword) :
    Option CardPart :=
  (split2? (normLine line)
      (" has " ++ keywordText ++ " as long as you control another ")).bind
    fun (subject, stText) =>
      if !refersToSelf cardName subject then none
      else
        (subtypeOfOracle? stText).map fun st =>
          .ability (.static (.if
            (.any (anotherSubtypeYouControl st))
            [.gainAbility .this (.keyword k)]))

/-- `<this> has haste as long as you control another Goblin.` -/
def parseHasteIfAnother (cardName line : String) : Option CardPart :=
  parseKeywordIfAnother cardName line "haste" .haste

/-- `Add {B}{R}.` The controller adds that mana. Does not choose a target. -/
def parseAddMana (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  (after? (normSentence sentence) "add ").bind nonemptyMana? |>.map fun syms =>
    (.addMana (.controller .this) syms, n)

/-- Cost, one effect sentence, and a trailing activation limit of
`<cost>: <effect>`. -/
def activatedSentence? (cardName line : String) :
    Option (List Cost × String × ActivateLimit) :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    let (body, limit) := splitActivateLimit (sentences effect)
    match body, parseActivationCost cardName costText with
    | [one], some costs => some (costs, one, limit)
    | _, _ => none

/-- True when a cost sacrifices another permanent of a printed subtype. -/
def sacrificesAnotherSubtype : List Cost → Bool
  | [] => false
  | .sacrificeCount s 1 :: rest =>
    s.shape.anotherSubtypeYouControl.isSome || sacrificesAnotherSubtype rest
  | _ :: rest => sacrificesAnotherSubtype rest

/-- `{T}, Sacrifice another Goblin: Add {B}{R}.`
Adding mana requires sacrificing another subtype, so `{T}: Add {G}` stays
unrecognized. Also `{2}, {T}: Draw a card, then discard a card.`
An activation limit may follow the effect. -/
def parseActivatedAddOrLoot (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (activatedSentence? cardName line).bind fun (costs, one, limit) =>
    match parseAddMana one n with
    | some (action, n') =>
      if sacrificesAnotherSubtype costs then
        some (activatedWithCost n costs action limit n')
      else none
    | none =>
      match parseDrawThenDiscard one n with
      | some (action, n') => some (activatedWithCost n costs action limit n')
      | none => none

/-- `Whenever <this> attacks, target attacking creature gains first strike until end of turn.`
The attacker is this card. The creature is target `n`. -/
def parseAttackTargetGains (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    (before? effect " until end of turn").bind (split2? · " gains ") |>.bind
      fun (who, gained) =>
        if who != "target attacking creature" then none
        else
          (parseKeywordPhrase gained).bind fun kws =>
            let effects := gainEffects n attackingCreatureTarget kws
            if effects.isEmpty then none
            else some (.continuous effects .endOfTurn, n + 1)

/-- `This spell costs {X} less to cast, where X is the total power of creatures you control with flying.`
The printed reduction is `{X}`, and X is that total power. It functions on
the stack (CR 604.2). -/
def parseCostLessByFlyingPower (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "this spell costs {x} less to cast, where x is the total power of creatures you control with flying" then
    some (.ability (.stackStatic
      (.reduceCostWithX .this [.mana [.x]] (.totalPower flyingCreaturesYouControl))))
  else none

/-- Search for one basic land card, reveal it, and put it into hand.
The found card is variable `n`. -/
def searchBasicLandToHand (n : Nat) : CardAction × Nat :=
  searchRevealToHand n basicLandInLibrary

/-- `When <this> enters, search your library for a basic land card, reveal it, put it into your hand, then shuffle.`
The entering object is this card. The found card is variable `n`. -/
def parseEnterSearchBasicToHand (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    if sentenceIs effect
        "search your library for a basic land card, reveal it, put it into your hand, then shuffle" then
      some (searchBasicLandToHand n)
    else none

/-- `When <this> enters, it deals 1 damage to any target. If a Dragon is dealt damage this way, destroy it.`
The entering object is this card. The recipient is target `n`, and that
damage is action `n`. The object of the action is destroyed only when the
damage is dealt to it and it has the subtype. -/
def parseEnterDealDamageDestroyIfSubtype (cardName : String) (line : String)
    (n : Nat) : Option (CardPart × Nat) :=
  match sentences line with
  | [enter, cond] =>
    onEnterN cardName enter fun effect =>
      (split2? effect " deals ").bind fun (who, rest) =>
        (split2? rest " damage to ").bind fun (amt, dest) =>
          if !damageSource? cardName who || dest != "any target" then none
          else
            match positiveDigits? amt with
            | none => none
            | some amount =>
              (after? (normSentence cond) "if ").bind dropArticle? |>.bind
                fun rest =>
                  (before? rest " is dealt damage this way, destroy it").bind
                    subtypeOfOracle? |>.map fun st =>
                      (
                        .sequence [
                          .actionId n
                            (.dealDamage (.source .this) (.target n .all)
                              (.int amount)),
                          .if (.anySubtype (.wasObjectOfAction n) st)
                            [.destroy (.wasObjectOfAction n)]],
                        n + 1)
  | _ => none

/-- `Whenever <this> attacks, he deals damage equal to the number of Treasures you control to any target.`
The attacker is this card. The recipient is target `n`. -/
def parseAttackDamageEqualTreasures (cardName : String) (line : String)
    (n : Nat) : Option (CardPart × Nat) :=
  onAttackN cardName line fun effect =>
    (split2? effect
        " deals damage equal to the number of treasures you control to ").bind
      fun (who, dest) =>
        if !damageSource? cardName who || dest != "any target" then none
        else
          some (
            .dealDamage (.source .this) (.target n .all) (.count treasuresYouControl),
            n + 1)

/-- `Whenever an opponent casts their first noncreature spell each turn, you recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text. -/
def parseOpponentFirstNoncreatureRecruit (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "whenever an opponent casts their first noncreature spell each turn, you recruit" then
    some (.ability (.triggered
      (.ordinal 1 .turnStart
        (.castSpell (.intersection [
          .spell,
          .not (.cardType .creature),
          .controlled (.opponent (.controller .this))])))
      (.keyword (.controller .this) .recruit)))
  else none

/-- Text after `As long as you have an enduring story,`. -/
def afterEnduringStory? (line : String) : Option String :=
  after? (normLine line) "as long as you have an enduring story, "

/-- This object's controller has an enduring story. -/
def controllerHasEnduringStory : Condition :=
  .enduringStory (.controller .this)

/-- `As long as you have an enduring story, <this> gets +1/+0 and has vigilance.`
A zero bonus is omitted. `+0/+0` with no keywords is not an effect. -/
def parseEnduringStoryGets (cardName line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (splitGetsOnly? rest).bind fun (who, tail) =>
        if !refersToSelf cardName who then none
        else
          let parsed :=
            match split2? tail " and has " with
            | none => some (tail, ([] : List Keyword))
            | some (pt, has) =>
              (parseKeywordPhrase has).map fun kws => (pt, kws)
          parsed.bind fun (ptText, kws) =>
            match parsePowerToughness ptText with
            | some (p, t) =>
              staticWhile controllerHasEnduringStory
                (flatPowerToughness .this p t ++ keywordGains .this kws)
            | none => none

/-- `As long as you have an enduring story, creatures you control get +1/+1.`
The plural `get` is these creatures, not this card. A zero bonus is omitted.
`+0/+0` is not an effect. -/
def parseEnduringStoryTeamGets (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind fun rest =>
    if (split2? rest " gets ").isSome then none
    else
      (splitGets? rest).bind fun (who, ptText) =>
        match parseControlledPhrase who, parsePowerToughness ptText with
        | some sel, some (p, t) =>
          if sel != creaturesYouControl then none
          else staticWhile controllerHasEnduringStory (flatPowerToughness sel p t)
        | _, _ => none

/-- `As long as you have an enduring story, artifacts and creatures you control have ward {1}.`
`{N}` is a positive generic cost. -/
def parseEnduringStoryTeamWard (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (split2? rest " have ward ").bind fun (who, cost) =>
        (genericWard? ("ward " ++ cost)).bind fun n =>
          if who != "artifacts and creatures you control" then none
          else
            staticWhile controllerHasEnduringStory
              [.gainAbility
                (permanentWith [.artifact, .creature] [youControl])
                (.keywordWithCost .ward [.mana [.generic n]])]

/-- `As long as you have an enduring story, creatures can't attack you unless their controller pays {1} for each of those creatures.`
`you` is this object's controller. `{N}` is a positive generic cost. -/
def parseEnduringStoryAttackTax (line : String) : Option CardPart :=
  (afterEnduringStory? line).bind
    fun rest =>
      (between? rest
          "creatures can't attack you unless their controller pays "
          " for each of those creatures").bind
        fun costText =>
          (positiveGeneric? costText).bind fun n =>
            staticWhile controllerHasEnduringStory
              [.cantAttackUnlessPays
                (permanentWith [.creature])
                (.controller .this)
                [.mana [.generic n]]]

/-- `<this> doesn't untap during your untap step unless you have an enduring story.`
The subject is this card. `your` is its controller (CR 502.3). This does not
untap when that player does not have an enduring story. -/
def parseDoesntUntapUnlessEnduringStory (cardName line : String) : Option CardPart :=
  (before? (normLine line)
      " doesn't untap during your untap step unless you have an enduring story").bind
    fun subject =>
      if !refersToSelf cardName subject then none
      else
        staticWhile (.not controllerHasEnduringStory) [.doesntUntap .this]

/-- `Whenever <this> or another nontoken Dwarf you control enters, create a 2/2 red Dwarf creature token.`
The subject is this card. `another` excludes this object. The subtype is
singular. One token uses the singular noun. -/
def parseThisOrNontokenSubtypeEntersCreate (cardName line : String) : Option CardPart :=
  (after? (normLine line) "whenever ").bind fun rest =>
    (split2? rest " or another nontoken ").bind fun (subject, tail) =>
      if !refersToSelf cardName subject then none
      else
        (split2? tail " you control enters, ").bind fun (subtypeText, effect) =>
          match subtypeOfOracle? subtypeText, parseCreateColoredCreatureToken effect with
          | some st, some action =>
            some (.ability (.triggered
              (.or
                (.enter .this)
                (.enter
                  (.intersection [
                    .not .this,
                    .not .token,
                    .zone .battlefield,
                    .cardType .creature,
                    .subtype st,
                    youControl])))
              action))
          | _, _ => none

/-- `{1}, {T}, Discard a card: Draw a card.`
Discarding one card is part of the cost. One card is drawn. An activation
limit may follow the effect. -/
def parseActivatedDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (activatedSentence? cardName line).bind fun (costs, one, limit) =>
    if !costs.any (fun c => c == discardOneCardFromHand) then none
    else
      (parseDrawCards one).map fun action => activatedWithCost n costs action limit n

/-- Cards in this object's controller's hand. -/
def cardsInYourHand : Selector :=
  .intersection [.zone .hand, .owner (.controller .this)]

/-- Cards in this object's controller's graveyard. -/
def cardsInYourGraveyard : Selector :=
  .intersection [.zone .graveyard, .owner (.controller .this)]

/-- `Threshold — This creature gets +1/+1 as long as there are seven or more cards in your graveyard.`
`Threshold` is an ability word (CR 207.2c / 702.62) and may be omitted.
Seven or more cards in your graveyard is that ability. A zero bonus is
omitted. `+0/+0` is not an effect. -/
def parseThresholdGets (cardName line : String) : Option CardPart :=
  let s := withoutAbilityWord (normLine line) "threshold"
  (before? s " as long as there are seven or more cards in your graveyard").bind
    fun pump =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        if !refersToSelf cardName who then none
        else
          match parsePowerToughness ptText with
          | some (p, t) =>
            staticWhile
              (.greaterOrEqual (.count cardsInYourGraveyard) 7)
              (flatPowerToughness .this p t)
          | none => none

/-- `Equip abilities you activate that target this creature cost {N} less to activate.`
`{N}` is generic mana, and it is not zero. -/
def parseEquipAbilitiesTargetingThisCostLess (line : String) : Option CardPart :=
  (between? (normLine line)
      "equip abilities you activate that target this creature cost "
      " less to activate").bind positiveGeneric? |>.map fun k =>
    .ability (.static (.reduceCost
      (.intersection [
        Selector.keywordAbility .equip,
        .hasTarget .this,
        youControl])
      [.mana [.generic k]]))

/-- Equip abilities of permanents this object's controller controls. -/
def equipAbilitiesYouControl : Selector :=
  .intersection [Selector.keywordAbility .equip, youControl]

/-- `As long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn.`
`{0}` is an alternative cost for those Equip abilities (CR 118.9), not a
cost reduction. It applies only while that player has not activated one
since the turn began. Any other mana cost is a different ability. -/
def parseFirstEquipFreeIfEnduringStory (line : String) : Option CardPart :=
  if normLine line ==
      "as long as you have an enduring story, you may pay {0} rather than pay the equip cost of the first equip ability you activate each turn" then
    staticWhile
      (.and
        controllerHasEnduringStory
        (.not (.happened
          (.activateAbility (.controller .this) equipAbilitiesYouControl) .turnStart)))
      [.alternativeCost equipAbilitiesYouControl [.mana [.generic 0]]]
  else none

/-- “This ability triggers only once each turn” (CR 603.2).
Ability `n` fires for `event` only while that ability has not triggered
since `.turnStart`. That is not the first occurrence of `event`: the
ability can still trigger when its source arrives after that event. -/
def triggersOnceEachTurn (n : Nat) (event : Trigger) (action : CardAction) : Ability :=
  .abilityId n
    (.triggeredWhile event
      (.not (.happened (.abilityTriggers (.abilityWithId n)) .turnStart))
      action)

/-- `Whenever another <subtype> or Equipment you control enters, draw a card. This ability triggers only once each turn.`
The entering permanent is another permanent of that subtype or an Equipment.
One card. Ability `n` is that trigger, and it fires only while it has not
triggered since `.turnStart`. -/
def parseAnotherSubtypeOrEquipmentEntersDraw (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, once] =>
    if !sentenceIs once "this ability triggers only once each turn" then none
    else
      (after? (norm enter) "whenever another ").bind fun rest =>
        (before? rest " enters, draw a card").bind fun who =>
          let (obj, controlled) := splitYouControl who
          if !controlled then none
          else
            match parseSubtypeList obj with
            | some [st, .equipment] =>
              some (
                .ability (triggersOnceEachTurn n
                  (.enter (.intersection [
                    .not .this,
                    .zone .battlefield,
                    .union [.subtype st, .subtype .equipment],
                    youControl]))
                  (.draw (.controller .this) 1)),
                n + 1)
            | _ => none
  | _ => none

/-- `When this creature enters, return up to one other target permanent you control to its owner's hand. If you do, put a +1/+1 counter on this creature.`
Up to one target is zero or one (CR 115.1). That target is `n`, and the return
is action `n`. The counter is put only when that action returns a permanent. -/
def parseEnterReturnOtherPlusOne (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, cond] =>
    if !sentenceIs cond "if you do, put a +1/+1 counter on this creature" then none
    else
      onEnterN cardName enter fun effect =>
        if effect !=
            "return up to one other target permanent you control to its owner's hand" then
          none
        else
          some (
            .sequence [
              .actionId n
                (.returnToHand
                  (.targets n (.range 0 1)
                    (.intersection [.not .this, .zone .battlefield, youControl]))),
              .if (.happened (.actionWithId n) .gameStart)
                [.putCounter (.source .this) .plusOnePlusOne 1]],
            n + 1)
  | _ => none

/-- `Equipped creature has <keywords> and can't be blocked.`
The keywords and the restriction are static abilities of this Equipment. -/
def parseEquippedHasAndCantBeBlocked (line : String) : Option (List CardPart) :=
  (after? (normLine line) "equipped creature has ").bind fun rest =>
    (before? rest " and can't be blocked").bind parseKeywordPhrase |>.bind
      fun kws =>
        match kws with
        | [] => none
        | _ =>
          some (
            (kws.map fun k =>
              .ability (.static (.gainAbility (.hostOf .this) (.keyword k)))) ++
            [.ability (.static (.forbid (.block .any (.hostOf .this))))])

/-- `Equip—{cost}, Pay N life.`
The Equip keyword (CR 702.6). The cost is that mana plus `N` life.
`N` is a positive life payment. Equip only as a sorcery. -/
def parseEquipPayLife (line : String) : Option CardPart :=
  (after? (normLine line) "equip—").bind fun rest =>
    match split2? rest ", " with
    | some (costText, lifeText) =>
      match nonemptyMana? costText, parsePayLife lifeText with
      | some syms, some life =>
        some (.ability (.keywordWithCost .equip [.mana syms, .life (.int life)]))
      | _, _ => none
    | none => none

/-- `As an additional cost to cast this spell, sacrifice a creature.`
The sacrifice is one creature and is announced at CR 601.2b. The ability
functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeCreature (line : String) : Option CardPart :=
  if normLine line ==
      "as an additional cost to cast this spell, sacrifice a creature" then
    some (.ability (.stackStatic
      (.additionalCost .this
        [.sacrificeCount (permanentWith [.creature]) 1])))
  else none

/-- `<this> has lifelink as long as you control another Dwarf.` -/
def parseLifelinkIfAnother (cardName line : String) : Option CardPart :=
  parseKeywordIfAnother cardName line "lifelink" .lifelink

/-- A card that is one of two subtypes, e.g. `a Dwarf or Equipment card`. -/
def twoSubtypesCard? (s : String) : Option (CardSubtype × CardSubtype) :=
  (dropArticle? s).bind fun rest =>
    (before? rest " card").bind fun mid =>
      (split2? mid " or ").bind fun (a, b) =>
        match subtypeOfOracle? a, subtypeOfOracle? b with
        | some sa, some sb => some (sa, sb)
        | _, _ => none

/-- Look at the top `k` cards of your library (action `n`). You may reveal one
card of `kind` from among them and put it into your hand (action `n + 1`).
`onBottom` puts the rest on the bottom of that library. -/
def lookAtTopMayRevealToHand (n k : Nat) (kind : Selector)
    (onBottom : Selector → CardAction) : List CardAction :=
  let looked := Selector.wasObjectOfAction n
  let revealed := Selector.wasObjectOfAction (n + 1)
  [
    .actionId n (.lookAt (.topOfLibrary (.controller .this) (.int k))),
    .optional (.controller .this) (.sequence [
      .actionId (n + 1)
        (.reveal
          (.selected (.controller .this) (.range 1 1)
            (.intersection [looked, kind]))),
      .returnToHand revealed]),
    onBottom (.intersection [looked, .not revealed])]

/-- `When <this> enters, look at the top four cards of your library. You may reveal a Dwarf or Equipment card from among them and put it into your hand. Put the rest on the bottom of your library in a random order.`
The looked-at cards are action `n`. The revealed card is action `n + 1`.
One card uses the singular. The revealed card may also be `a permanent card`. -/
def parseEnterLookAtTopReveal (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, reveal, restBottom] =>
    if !sentenceIs restBottom
        "put the rest on the bottom of your library in a random order" then none
    else
      onEnterN cardName enter fun effect =>
        (after? effect "look at the top ").bind fun tail =>
          (before? tail " of your library").bind topCount? |>.bind fun k =>
            (after? (normSentence reveal) "you may reveal ").bind fun rev =>
              (before? rev " from among them and put it into your hand").bind
                (fun kind =>
                  (twoSubtypesCard? kind).map (fun (a, b) =>
                    Selector.union [.subtype a, .subtype b]) <|>
                  (if kind == "a permanent card" then some (.zone .battlefield) else none))
                |>.map fun kindSel =>
                  (.sequence (lookAtTopMayRevealToHand n k kindSel
                    .putOnLibraryBottomInRandomOrder),
                   n + 2)
  | _ => none

/-- `Create X tapped Treasure tokens, where X is the number of artifacts your opponents control.` -/
def parseCreateTappedTreasuresEqualOppArtifacts (sentence : String) :
    Option CardAction :=
  if sentenceIs sentence
      "create x tapped treasure tokens, where x is the number of artifacts your opponents control" then
    some (.createTokens (.controller .this)
      (.count (.intersection [
        .zone .battlefield, .cardType .artifact,
        .controlled (.opponent (.controller .this))]))
      PredefinedToken.treasureToken
      [.tapped])
  else none

/-- `When <this> enters, create X tapped Treasure tokens, where X is the number of artifacts your opponents control.`
X is how many artifact permanents those opponents control. -/
def parseEnterCreateTappedTreasuresEqualOppArtifacts (cardName line : String) :
    Option CardPart :=
  onEnter cardName line parseCreateTappedTreasuresEqualOppArtifacts

/-- Any spell this object's controller casts. -/
def anySpellYouCast : Selector :=
  .intersection [.spell, youControl]

/-- Anything with the Treasure subtype, the source of “mana from a Treasure”. -/
def treasureManaSource : Selector :=
  .subtype .treasure

/-- `Whenever you cast a spell, if mana from a Treasure was spent to cast it, you draw a card and lose 1 life.`
The ability triggers once when that spell is cast, not once for each mana
spent. First, mana from a Treasure — any object with that subtype — is
spent to cast a spell this object's controller casts. That cast is
numbered. Then that spell, argument 1 of the numbered cast, is cast. The
payment happens before the spell becomes cast (CR 601.2h / 601.2i). The
“if” is an intervening if (CR 603.4). One card and 1 life. -/
def parseYouCastSpellIfTreasureDrawLoseLife (line : String) : Option CardPart :=
  (after? (normLine line)
      "whenever you cast a spell, if mana from a treasure was spent to cast it, ").bind
    parseYouDrawCardLoseLife |>.map fun action =>
      .ability (.triggered
        (.sequence [
          .spendManaFrom treasureManaSource
            (.triggerId 1 (.castSpell anySpellYouCast)),
          .castSpell (.wasArgumentOfTrigger 1 1)])
        action)

/-- `Instant and sorcery spells you cast cost {X} less to cast, where X is equipped creature's power.`
The printed reduction is `{X}`. X is the equipped creature's power. -/
def parseInstantSorceryCostLessByEquippedPower (line : String) : Option CardPart :=
  if sentenceIs (normLine line)
      "instant and sorcery spells you cast cost {x} less to cast, where x is equipped creature's power" then
    some (.ability (.static (.reduceCostWithX
      (.intersection [.spell, instantOrSorcery, youControl])
      [.mana [.x]]
      (.greatestPower (.hostOf .this)))))
  else none

/-- Tokens that would be created under this object's controller. -/
def tokensCreatedUnderYou : Selector :=
  .intersection [.token, .controlled (.controller .this)]

/-- A token permanent this object's controller controls. -/
def tokenYouControl : Selector :=
  .intersection [.zone .battlefield, .token, youControl]

/-- `If you would draw a card except the first one you draw in each of your
draw steps, draw two cards instead.`
`replace` of `Trigger.draw` is that draw (CR 614). It applies except while
it is your draw step and the first card of that step has not been drawn
(CR 121.2). -/
def parseDrawExceptFirstDrawStep (line : String) : Option CardPart :=
  if sentenceIs line
      "if you would draw a card except the first one you draw in each of your draw steps, draw two cards instead" then
    some (.ability (.static (.if
      (notFirstCardOfDrawStep (.controller .this))
      [.replace
        (.draw (.controller .this) .all)
        [.draw (.controller .this) 2]])))
  else none

/-- `If one or more tokens would be created under your control, twice that
many of those tokens are created instead.`
`replace` of `Trigger.createTokens` is that creation (CR 614).
`modifyReplacementCreatedTokenCount (fun n => .int (n * 2))` keeps creating
those tokens, twice as many. -/
def parseTwiceTokensYouWouldCreate (line : String) : Option CardPart :=
  if sentenceIs line
      "if one or more tokens would be created under your control, twice that many of those tokens are created instead" then
    some (.ability (.static (.replace
      (.createTokens tokensCreatedUnderYou)
      [.modifyReplacementCreatedTokenCount (fun n => .int (n * 2))])))
  else none

/-- `Whenever a token you control enters, you gain 1 life if this is the
first time this ability has resolved this turn. If it's the second time,
draw a card. If it's the third time, put a +1/+1 counter on each creature
you control.`
The ability is numbered. The trigger fires once for each token. Each branch
is how many times that ability has finished resolving since the start of
the turn. This resolution is not counted: none is one life, one is a card,
and two is a +1/+1 counter on each creature you control. -/
def parseTokenEntersByResolveCount (line : String) (n : Nat) : Option (CardPart × Nat) :=
  let finished (k : Nat) : Condition :=
    if k == 0 then
      .not (.happened (.abilityWithIdResolved n) .turnStart)
    else
      .and
        (.happened (.ordinal k .turnStart (.abilityWithIdResolved n)) .turnStart)
        (.not (.happened (.ordinal (k + 1) .turnStart (.abilityWithIdResolved n)) .turnStart))
  match sentences (rulesText line) with
  | [first, second, third] =>
    match after? (normSentence first) "whenever a token you control enters, " with
    | some gain =>
      if sentenceIs gain
          "you gain 1 life if this is the first time this ability has resolved this turn" &&
          sentenceIs second "if it's the second time, draw a card" &&
          sentenceIs third
            "if it's the third time, put a +1/+1 counter on each creature you control" then
        some (
          .ability (.abilityId n (.triggered
            (.enter tokenYouControl)
            (.sequence [
              .if (finished 0) [.gainLife (.controller .this) 1],
              .if (finished 1) [.draw (.controller .this) 1],
              .if (finished 2) [.putCounter creaturesYouControl .plusOnePlusOne 1]]))),
          n + 1)
      else none
    | none => none
  | _ => none

/-- Steps of a sequence, in order. A sequence is those steps. -/
def flattenAction : CardAction → List CardAction
  | .sequence as => as.flatMap flattenAction
  | action => [action]

/-! ### Catalog grammar

Phrases of the Hobbit Eternal and Marvel Super Heroes catalog cards. They
are tried after the templates above, so a line those templates read keeps
that reading. -/

/-- A Saga chapter number: `I` through `VI` (CR 714.2). -/
def chapterNumber? (s : String) : Option Nat :=
  match copied s with
  | "I" => some 1
  | "II" => some 2
  | "III" => some 3
  | "IV" => some 4
  | "V" => some 5
  | "VI" => some 6
  | _ => none

/-- The rules text after a leading ability word or flavor word, such as
`Alliance —` or `Seismic Takedown —`. That word has no rules meaning
(CR 207.2c). It is one or more words with no punctuation. A Saga chapter
number is not such a word. The rest keeps its printed case. -/
def afterAbilityWord? (line : String) : Option String :=
  (split2? (rulesText line) " — ").bind fun (word, rest) =>
    if word.isEmpty || rest.isEmpty || (chapterNumber? word).isSome ||
        word.any (fun c => c == ',' || c == '.' || c == ':' || c == '•' || c == '(') then
      none
    else
      match norm word with
      | "ferocious" | "power-up" | "∞" | "infinity" => none
      | "landfall" =>
        if (norm rest).startsWith "whenever a land you control enters, " then some rest else none
      | _ => some rest

end OracleParts

end Mtg.Engine
