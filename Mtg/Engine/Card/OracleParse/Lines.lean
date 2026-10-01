import Mtg.Engine.Card.OracleParse.SpellActions

/-!
# Printed ability lines

Adventure faces and triggered, static, and mana lines, including Ferocious
and Landfall.
-/

namespace Mtg.Engine

namespace OracleParts

/-- Split off a Gatherer `//ADV//` Adventure section. A marker that shares
its line with the Adventure name keeps that name. -/
def splitAdventure (lines : List String) : List String × List String :=
  go lines []
where
  go : List String → List String → List String × List String
    | [], acc => (acc.reverse, [])
    | line :: rest, acc =>
      if line == "//ADV//" then (acc.reverse, rest)
      else
        match after? line "//ADV//" with
        | some restLine =>
          let adv := if restLine.isEmpty then rest else restLine :: rest
          (acc.reverse, adv)
        | none => go rest (line :: acc)

/-- `As an additional cost to cast this spell, sacrifice an artifact or creature or pay {4}.`
The sacrifice and the generic mana are alternatives announced at CR 601.2b.
The ability functions while this spell is on the stack (CR 113.6 / 604.2). -/
def parseAdditionalCostSacrificeOrPay (line : String) : Option CardPart :=
  match (after? (normLine line)
      "as an additional cost to cast this spell, sacrifice ").bind
      (split2? · " or pay ") with
  | some (obj, costText) =>
    match (dropArticle? obj).bind typesInPhrase, parseManaSymbols costText with
    | some ts, some [.generic k] =>
      some (.ability (.stackStatic (
        .additionalCost .this
          [.or [
            .sacrificeCount (permanentWith ts) 1,
            .mana [.generic k]]])))
    | _, _ => none
  | none => none

/-- Drop a leading ability word (`Ferocious —`) when that word is present.
Any other dash stays part of the text. -/
def withoutAbilityWord (s word : String) : String :=
  match split2? s "—" with
  | some (w, rest) => if w == word then rest else s
  | none => s

/-- Creatures this object's controller controls. -/
def creaturesYouControl : Selector :=
  permanentWith [.creature] [youControl]

/-- A creature you control with power 4 or greater. -/
def ferociousCreature : Selector :=
  permanentWith [.creature] [youControl, .powerAtLeast (Value.int 4)]

/-- Creatures you control are declared as attackers together (CR 508.3). -/
def youAttack : Trigger :=
  .attackSimultaneously creaturesYouControl .all []

/-- Effect of `Whenever you attack, <effect>`. -/
def youAttackEffect? (line : String) : Option String :=
  after? (normLine line) "whenever you attack, "

/-- `you control a creature with power 4 or greater`, the Ferocious condition. -/
def ferociousCondition : String :=
  "you control a creature with power 4 or greater, "

/-- `Ferocious —` has no rules meaning (CR 207.2c) and may be omitted. -/
def withoutFerocious (line : String) : String :=
  withoutAbilityWord (normLine line) "ferocious"

/-- `until end of turn, this creature gets +P/+0 and creatures you control gain trample.`
The bonus and trample both last until end of turn. A zero power, or any
toughness change, is a different ability. -/
def parseSourceGetsAndTeamTrample (effect : String) : Option CardAction :=
  (after? (norm effect) "until end of turn, ").bind fun rest =>
    (split2? rest " and creatures you control gain ").bind fun (pump, gained) =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        if parsePumpWho who != some (.source .this) then none
        else
          match parsePowerToughness ptText, parseKeywordPhrase gained with
          | some (p, 0), some [.trample] =>
            if p == 0 then none
            else
              some (.continuous
                [.addPower (.source .this) (Value.int p),
                  .gainAbility creaturesYouControl (.keyword .trample)]
                .endOfTurn)
          | _, _ => none

/-- `Put a +1/+1 counter on each creature you control.`
One counter uses the singular noun. `each` is every creature you control. -/
def parsePutPlusOneOnEachYouControl (sentence : String) : Option CardAction :=
  match (after? (normSentence sentence) "put ").bind
      (split2? · " +1/+1 counter on each ") with
  | some (countText, who) =>
    match nounCount? countText false, parseControlledPhrase who with
    | some 1, some sel =>
      if sel == creaturesYouControl then
        some (.putCounter creaturesYouControl .plusOnePlusOne 1)
      else none
    | _, _ => none
  | none => none

/-- `Ferocious — Whenever this creature attacks while you control a creature
with power 4 or greater, <effect>.`
`Ferocious` is an ability word (CR 207.2c) and may be omitted. The “while”
clause is part of the trigger condition (CR 603.2): it is checked when this
creature attacks, and it is not checked again when the ability resolves.
The effect is gaining life, this creature getting +P/+T until end of turn,
this creature getting +P/+0 and your creatures gaining trample until end of
turn, or a +1/+1 counter on each creature you control. -/
def parseFerociousThisAttacks (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "whenever this creature attacks while " ++ ferociousCondition
  (after? s lead).bind fun effect =>
    let gainLife :=
      match parseYouGainLife effect 0 with
      | some (.gainLife _ k, _) => some (.gainLife (.controller .this) k)
      | _ => none
    let pump :=
      (parsePumpUntilEndOfTurn effect).bind fun action =>
        (sourceGetsUntilEnd? action).map fun _ => action
    (gainLife <|> pump <|>
        parseSourceGetsAndTeamTrample effect <|>
        parsePutPlusOneOnEachYouControl effect).map fun action =>
      .ability (.triggeredWhile (.attack .this .all) (.any ferociousCreature) action)

/-- `Ferocious — Whenever you attack while you control a creature with power
4 or greater, you draw a card and lose 1 life.`
`Ferocious` may be omitted (CR 207.2c). “Whenever you attack” is one trigger
when creatures you control attack at the same time (CR 508.3 / 603.2d). -/
def parseFerociousYouAttack (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "whenever you attack while " ++ ferociousCondition
  (after? s lead).bind parseYouDrawCardLoseLife |>.map fun action =>
    .ability (.triggeredWhile youAttack (.any ferociousCreature) action)

/-- `Ferocious — At the beginning of combat on your turn, if you control a
creature with power 4 or greater, put a +1/+1 counter on this creature.`
`Ferocious` may be omitted (CR 207.2c). Beginning of combat is CR 507.1.
The “if” is an intervening if (CR 603.4). -/
def parseFerociousBeginCombat (line : String) : Option CardPart :=
  let s := withoutFerocious line
  let lead := "at the beginning of combat on your turn, if " ++ ferociousCondition
  (after? s lead).bind parsePutPlusOneOnThis |>.map fun action =>
    .ability (.triggered (.combatStart (.controller .this))
      (.if (.any ferociousCreature) [action]))

/-- `you may have this creature's base power and toughness become P/T until end of turn.`
The change is optional. `this creature` is the source of this ability. -/
def parseMaySetBasePT (effect : String) : Option CardAction :=
  (after? (norm effect)
      "you may have this creature's base power and toughness become ").bind
    fun rest =>
      (before? rest " until end of turn").bind parsePowerToughness |>.map
        fun (p, t) =>
          .optional (.controller .this) (.continuous
            [.setBasePower (.source .this) (Value.int p),
              .setBaseToughness (.source .this) (Value.int t)]
            .endOfTurn)

/-- `Whenever a land you control enters,` after case-folding. -/
def landYouControlEnters : String :=
  "whenever a land you control enters, "

/-- Text after an optional `Landfall —` ability word (CR 207.2c). -/
def withoutLandfall (line : String) : String :=
  withoutAbilityWord (normLine line) "landfall"

/-- `Landfall — Whenever a land you control enters, <effect>.`
`Landfall` is an ability word (CR 207.2c) and may be omitted.
The effect is `this creature gets +P/+T until end of turn`,
`you may have this creature's base power and toughness become P/T until end of turn`,
or `put a +1/+1 counter on target <permanent> you control`.
`you control` is required on that target; a bare target is a different ability.
The target, when there is one, is `n`. A line that also says `choose one —`
is a modal trigger, not this ability. -/
def parseLandYouControlEnters (line : String) (n : Nat) : Option (CardPart × Nat) :=
  (after? (withoutLandfall line) landYouControlEnters).bind fun effect =>
    onTriggerN (.enter landsYouControl) <|
      match parsePumpUntilEndOfTurn effect with
      | some action => (sourceGetsUntilEnd? action).map fun _ => (action, n)
      | none =>
        match parseMaySetBasePT effect with
        | some action => some (action, n)
        | none =>
          if !effect.endsWith " you control" then none
          else parsePutPlusOneOnTarget effect n

/-- `When this Equipment enters, target opponent sacrifices a creature of their choice.`
The entering object is this card. The opponent is target `n` and chooses which
creature to sacrifice (CR 701.17a). -/
def parseEnterTargetOpponentSacrifices (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line fun effect =>
    (between? effect "target opponent sacrifices " " of their choice").bind fun obj =>
      (dropArticle? obj).bind fun named =>
        if named != "creature" then none
        else
          some (
            .sacrifice
              (.selected
                (.target n (.opponent (.controller .this)))
                (.range 1 1)
                (permanentWith [.creature] [.controlled (.targetReference n)])),
            n + 1)

/-- `ward {N}` with a positive generic cost. -/
def genericWard? (s : String) : Option Nat :=
  (after? (norm s) "ward ").bind positiveGeneric?

/-- `Equipped creature gets +2/+1.` Also `Enchanted creature gets +2/+2 and has flying.`
And `Equipped creature gets +2/+2 and has ward {1}.`
The bonus, keywords, or generic ward are static abilities of the Equipment
or Aura (CR 604.1 / 301.5 / 303.4). `and has` may be omitted. A zero bonus
is omitted. `+0/+0` is not an effect. A bonus that lasts until end of turn
is a different ability. Ward is a generic cost, not a keyword. -/
def parseEquippedGets (line : String) : Option (List CardPart) :=
  let rest? :=
    after? (normLine line) "equipped creature gets " <|>
      after? (normLine line) "enchanted creature gets "
  rest?.bind fun rest =>
    if (split2? rest " until end of turn").isSome then none
    else
      let parsed : Option (String × Option Nat × List Keyword) :=
        match split2? rest " and has " with
        | none => some (rest, none, [])
        | some (pt, has) =>
          match genericWard? has with
          | some n => some (pt, some n, [])
          | none =>
            match has.splitOn " and ward " with
            | [kwText, cost] =>
              match parseKeywordPhrase kwText, genericWard? ("ward " ++ cost) with
              | some kws, some n => some (pt, some n, kws)
              | _, _ => none
            | _ => (parseKeywordPhrase has).map fun kws => (pt, none, kws)
      parsed.bind fun (ptText, ward?, kws) =>
        match parsePowerToughness ptText with
        | some (p, t) =>
          if p == 0 && t == 0 then none
          else
            let keywordEffects :=
              kws.map fun k =>
                (.gainAbility (.hostOf .this) (.keyword k) : ContinuousEffect)
            let wardEffects :=
              match ward? with
              | none => []
              | some n =>
                [.gainAbility (.hostOf .this)
                  (.keywordWithCost .ward [.mana [.generic n]])]
            let effects :=
              flatPowerToughness (.hostOf .this) p t ++ keywordEffects ++ wardEffects
            if effects.isEmpty then none
            else some (effects.map fun e => .ability (.static e))
        | none => none

/-- `Equip {2}.` Reminder text such as
`({2}: Attach to target creature you control. Equip only as a sorcery.)`
is not rules text (CR 207.2 / 702.6). -/
def parseEquip (line : String) : Option CardPart :=
  match (after? (normLine line) "equip ").bind nonemptyMana? with
  | some syms => some (.ability (.keywordWithCost .equip [.mana syms]))
  | none => none

/-- `When <this> enters, create a colorless Equipment artifact token named Axe with "Equipped creature gets +1/+0" and equip {2}.`
The token is a colorless Equipment artifact with that name. Colorless is an
empty color indicator. The quoted text is a static ability of the token.
Equip is another ability of the token. A zero bonus is omitted. `+0/+0` is
not an effect. -/
def parseEnterCreateNamedEquipment (cardName : String) (line : String) :
    Option CardPart :=
  let raw := rulesText line
  let (raw, attach) :=
    match split2? raw ". Attach it to " with
    | some (rest, who) => if refersToSelf cardName who then (rest, true) else (raw, false)
    | none => (raw, false)
  (split2? raw " named ").bind fun (lead, rest) =>
    (split2? rest " with \"").bind fun (tokenName, afterName) =>
      (split2? afterName "\" and ").bind fun (quoted, equipText) =>
        if tokenName.isEmpty then none
        else
          onEnter cardName lead fun effect =>
            if effect != "create a colorless equipment artifact token" then none
            else
              match parseEquippedGets quoted, parseEquip equipText with
              | some quotedParts, some equipPart =>
                let create := CardAction.createTokens (.controller .this) 1
                  ([.name tokenName, .type .artifact, .subtype .equipment,
                    .colorIndicator []] ++
                    quotedParts ++ [equipPart])
                if attach then
                  some (.sequence [.actionId 1 create, .attach (.wasCreatedByAction 1) (.source .this)])
                else some create
              | _, _ => none

/-- `Each opponent loses 2 life.` The amount is a printed number. -/
def parseEachOpponentLosesLife (sentence : String) : Option Nat :=
  lifeAmount? (normSentence sentence) "each opponent loses "

/-- `When <this card> enters, exile up to one target card from an opponent's graveyard. Each opponent loses N life.`
Up to one target is zero or one (CR 115.1). That target is numbered `n`. -/
def parseEnterExileOppGyLoseLife (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, lose] =>
    onEnterN cardName enter fun effect =>
      if effect != "exile up to one target card from an opponent's graveyard" then none
      else
        (parseEachOpponentLosesLife lose).map fun k =>
          (.sequence [
              .exile
                (.targets n (.range 0 1)
                  (.intersection [
                    .zone .graveyard,
                    .owner (.opponent (.controller .this))])),
              .loseLife (.opponent (.controller .this)) (Value.int k)],
           n + 1)
  | _ => none

def returnThisFromGraveyardToHand : CardAction :=
  .returnToHand (.intersection [.zone .graveyard, .source .this])

def parseReturnThisFromGraveyard (sentence : String) : Option CardAction :=
  if sentenceIs sentence "return this card from your graveyard to your hand" then
    some returnThisFromGraveyardToHand
  else
    none

/-- `{2}, Sacrifice an artifact or creature: Return this card from your graveyard to your hand. Activate only as a sorcery.`
The effect moves this card out of the graveyard, so the ability functions
there (CR 113.6). “Activate only as a sorcery” is the condition
(CR 307.1 / 117.1a). The ability is `graveyardActivatedIf`. -/
def parseGraveyardReturn (line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind fun (costText, effect) =>
    match sentences effect with
    | [ret, restrict] =>
      if !sentenceIs restrict "activate only as a sorcery" then none
      else
        match parsePrintedCosts "" costText, parseReturnThisFromGraveyard ret with
        | some costs, some action =>
          some (.ability (
            .graveyardActivatedIf
              (.timeToCastSorcery (.controller .this))
              costs
              action))
        | _, _ => none
    | _ => none

/-- `When this creature enters, each opponent discards a card.`
The entering object is this card. -/
def parseEnterEachOpponentDiscards (cardName : String) (line : String) :
    Option CardPart :=
  onEnter cardName line fun effect =>
    (after? effect "each opponent discards ").bind parseCardCount |>.map fun k =>
      .discard (.opponent (.controller .this)) (Value.int k)

/-- A pronoun for the object named earlier in the same ability. -/
def isPersonalPronoun (s : String) : Bool :=
  match norm s with
  | "he" | "she" | "it" | "they" => true
  | _ => false

/-- `When Gandalf enters, he deals 3 damage divided as you choose among one, two, or three targets.`
The entering object is this card. The damage source is a pronoun for that
object, or another reference to this card. Its controller divides the damage
(CR 601.2d). `targets` with no type is any target. The counts are a positive
contiguous range, and those targets are numbered `n`. -/
def parseEnterDividedDamage (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (before? (normLine line) " targets").bind fun body =>
    onEnterN cardName body fun effect =>
      (split2? effect " deals ").bind fun (who, rest) =>
        if who.isEmpty || !(isPersonalPronoun who || refersToSelf cardName who) then none
        else
          (split2? rest " damage divided as you choose among ").bind fun (amt, counts) =>
            match positiveCount amt, parseContiguousCounts counts with
            | some amount, some (lo, hi) =>
              some (
                .divideDamage
                  (.controller .this)
                  (.source .this)
                  (.targets n (.range (Value.int lo) (Value.int hi)) .all)
                  (Value.int amount),
                n + 1)
            | _, _ => none

/-- `When this Equipment enters, you may discard a card. If you do, draw two cards.`
The entering object is this card. “If you do” means the draw happens only
when that discard is taken. The discard is action `n`. -/
def parseEnterMayDiscardDraw (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [may, ifYouDo] =>
    onEnterN cardName may fun effect =>
      (after? effect "you may discard ").bind fun discardedText =>
        match parseCardCount discardedText,
            (after? (norm ifYouDo) "if you do, draw ").bind parseCardCount with
        | some discarded, some drawn =>
          some (
            .sequence [
              .optional (.controller .this)
                (.actionId n
                  (.discard (.controller .this) (Value.int discarded))),
              .if
                (.happened (.actionWithId n) .gameStart)
                [.draw (.controller .this) (Value.int drawn)]],
            n + 1)
        | _, _ => none
  | _ => none

/-- `Galion's` or `this creature's` names this card. -/
def possessiveSelf (cardName whose : String) : Bool :=
  (before? (norm whose) "'s").any (refersToSelf cardName)

/-- `up to one other target creature you control` as zero or one other
permanent of those types you control (CR 115.1). -/
def parseUpToOneOtherYouControl (s : String) : Option Selector :=
  (between? (norm s) "up to one other target " " you control").bind fun obj =>
    parseControlledPhrase ("other " ++ obj ++ " you control")

/-- `Whenever Galion attacks, choose up to one other target creature you control. Its base power and toughness become equal to Galion's power and toughness until end of turn.`
The attacker is this card. The chosen creature is target `n`. -/
def parseAttackSetBasePT (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [attack, become] =>
    onAttackN cardName attack fun effect =>
      (after? effect "choose ").bind parseUpToOneOtherYouControl |>.bind fun among =>
        (between? (normSentence become)
            "its base power and toughness become equal to "
            " power and toughness until end of turn").bind fun whose =>
          if !possessiveSelf cardName whose then none
          else
            some (
              .continuous
                [.setBasePower
                  (.targets n (.range 0 1) among)
                  (Value.greatestPower (.source .this)),
                 .setBaseToughness
                  (.targetReference n)
                  (Value.greatestToughness (.source .this))]
                .endOfTurn,
              n + 1)
  | _ => none

/-- `Whenever another Elf you control enters, this creature gets +1/+1 until end of turn.`
`another` excludes this object. -/
def parseAnotherElfEntersGets (line : String) : Option CardPart :=
  triggeredSourcePump (normLine line) "whenever another elf you control enters, "
    (.enter
      (.intersection [
        .not .this,
        .zone .battlefield,
        .subtype .elf,
        youControl]))
    (· == (1, 1))

/-- `{T}: Add X mana of any one color, where X is this creature's power. Spend this mana only to cast Elf spells and activate abilities of Elf sources.`
The tap symbol is the cost. X is this creature's power. The produced mana is
action `n`. -/
def parseTapAddAnyColorEqualToPower (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        match sentences effect with
        | [add, spend] =>
          (after? (normSentence add) "add x mana of any one color, where x is ").bind
              (before? · " power") |>.bind fun whose =>
            if possessiveSelf cardName whose &&
                sentenceIs spend
                  "spend this mana only to cast elf spells and activate abilities of elf sources" then
              some (
                .ability (
                  .activated
                    [.tapSymbol]
                    (.sequence [
                      .actionId n
                        (.addManaOfOneColor
                          (.controller .this)
                          ManaSymbol.anyColor
                          (.greatestPower .this)),
                      .continuous
                        [.forbid
                          (.spendManaCreatedByAction n
                            (.not
                              (.or
                                (.castSpell (.subtype .elf))
                                (.activateAbility (.subtype .elf)))))]
                        .endOfTurn])),
                n + 1)
            else none
        | _ => none

/-- `<this>'s power and toughness are each equal to the number of lands you control.`
A characteristic-defining ability (CR 208.2a / 604.3). -/
def parseLandsCharacteristic (cardName : String) (line : String) : Option (List CardPart) :=
  (before? (normLine line) (" " ++ landsCharacteristicSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some (powerToughnessEqualLandsAbilities.map fun a => .ability a)
    else none

/-- The printed clause after `<this>'s`. -/
def creaturesPowerSuffix : String :=
  "power is equal to the number of creatures you control"

/-- `<this>'s power is equal to the number of creatures you control.`
A characteristic-defining ability (CR 208.2a / 604.3). Power is set to that
count. Toughness is not changed. -/
def parseCreaturesPowerCharacteristic (cardName : String) (line : String) :
    Option (List CardPart) :=
  (before? (normLine line) (" " ++ creaturesPowerSuffix)).bind fun whose =>
    if possessiveSelf cardName whose then
      some [.ability (.static (.setPower .this (.count creaturesYouControl)))]
    else none

/-- `<this>'s power is equal to the number of cards in your hand.`
A characteristic-defining ability (CR 208.2a / 604.3). Toughness is not
changed. -/
def parseCardsInHandPowerCharacteristic (cardName : String) (line : String) :
    Option (List CardPart) :=
  (before? (normLine line) " power is equal to the number of cards in your hand").bind
    fun whose =>
      if possessiveSelf cardName whose then
        some [.ability (.static (.setPower .this
          (.count (.intersection [.zone .hand, .owner (.controller .this)]))))]
      else none

/-- `When this creature enters, search your library for a Forest card, put that card onto the battlefield, then shuffle.`
The entering object is this card. -/
def parseEnterSearchForest (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect =>
    if sentenceIs effect
        "search your library for a forest card, put that card onto the battlefield, then shuffle" then
      some (.searchLibraryThenShuffle
        (.controller .this)
        [.putOntoBattlefield
          (.selected
            (.controller .this)
            (.range 1 1)
            (.intersection [.zone .library, .subtype .forest]))])
    else none

/-- One card part that does not advance the target number. -/
def sole (part? : Option CardPart) (n : Nat) : Option (List CardPart × Nat) :=
  part?.map fun part => ([part], n)

/-- One card part together with the target number it produced. -/
def carry (parsed : Option (CardPart × Nat)) : Option (List CardPart × Nat) :=
  parsed.map fun (part, n') => ([part], n')

/-- Spell actions. Empty actions are a failed parse, not a blank spell. -/
def spellActions (parsed : Option (List CardAction × Nat)) : Option (List CardPart × Nat) :=
  parsed.bind fun (actions, n') =>
    if actions.isEmpty then none else some ([.actions actions], n')

/-- `<this> enters tapped.` A replacement effect (CR 614.1). A spell does not
enter the battlefield. -/
def parseEntersTapped (cardName line : String) : Option CardPart :=
  (before? (normLine line) " enters tapped").bind fun subject =>
    if subject.isEmpty || norm subject == "this spell" ||
        !refersToSelf cardName subject then
      none
    else
      some (.ability (.static (.replace (.enter .this)
        [.putOntoBattlefieldInState .this [.tapped]])))

/-- `<this> enters tapped unless you control an Equipment.`
It enters tapped while its controller controls no Equipment. The ability
functions in every zone (CR 113.6) so it can replace how this card enters
the battlefield. -/
def parseEntersTappedUnlessEquipment (cardName line : String) : Option CardPart :=
  (split2? (normLine line) " enters tapped unless you control ").bind
    fun (subject, rest) =>
      if !refersToSelf cardName subject then none
      else
        match dropArticle? rest with
        | some "equipment" =>
          some (.ability (.everywhereStatic (.if (.not (.any equipmentYouControl))
            [.replace (.enter .this)
              [.putOntoBattlefieldInState .this [.tapped]]])))
        | _ => none

/-- One colored or colorless symbol that can be added to a mana pool. -/
def addableSymbol? (s : String) : Option ManaSymbol :=
  match parseManaSymbols s with
  | some [sym] =>
    match CardAction.addedManaType? sym with
    | some _ => some sym
    | none => none
  | _ => none

/-- `Add {G} or {U}`: the player chooses one listed symbol. -/
def parseAddOneOf (effect : String) : Option (List CardAction) :=
  (after? (normSentence effect) "add ").bind fun rest =>
    let options := rest.splitOn " or " |>.map copied |>.filter (· != "")
    if options.length < 2 then none
    else
      options.mapM fun opt =>
        (addableSymbol? opt).map fun sym => .addMana (.controller .this) [sym]

/-- `{T}: Add {G} or {U}.` The tap symbol is the cost (CR 107.5). -/
def parseTapAddOneOf (line : String) : Option CardPart :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      if norm costText != "{t}" then none
      else
        (parseAddOneOf effect).map fun actions =>
          .ability (.activated [.tapSymbol]
            (.playerSelectAction (.controller .this) (.range 1 1) actions))

/-- One word of a typecycling type phrase. -/
def addCyclingWord
    (acc : Option (List CardSupertype × List CardType × List CardSubtype))
    (w : String) : Option (List CardSupertype × List CardType × List CardSubtype) :=
  acc.bind fun (sups, tys, sts) =>
    match supertypeOfOracle? w with
    | some s => some (sups ++ [s], tys, sts)
    | none =>
      match typeOfOracle? w with
      | some t => some (sups, tys ++ [t], sts)
      | none =>
        match subtypeOfOracle? w with
        | some st => some (sups, tys, sts ++ [st])
        | none => none

/-- `Halfling` or `Basic land` as the type a cycling ability searches for. -/
def parseCyclingWords (phrase : String) :
    Option (List CardSupertype × List CardType × List CardSubtype) :=
  let words := (norm phrase).splitOn " " |>.map copied |>.filter (· != "")
  if words.isEmpty then none
  else
    match words.foldl addCyclingWord (some ([], [], [])) with
    | some (sups, tys, sts) =>
      if tys.isEmpty && sts.isEmpty then none else some (sups, tys, sts)
    | none => none

/-- `Halflingcycling {4}`. Reminder text is not rules text (CR 702.29). -/
def parseTypecycling (line : String) : Option CardPart :=
  let line := rulesText line
  let (phrase, costText) := splitNameCost line
  if costText.isEmpty then none
  else
    (before? (norm phrase) "cycling").bind fun kind =>
      match parseCyclingWords kind, nonemptyMana? costText with
      | some (sups, tys, sts), some syms =>
        some (.ability (.keywordWithCost (.typecycling sups tys sts) [.mana syms]))
      | _, _ => none

/-- `When this Equipment enters, you gain 2 life.` The entering object is this card. -/
def parseEnterYouGainLife (cardName line : String) : Option CardPart :=
  onEnter cardName line fun effect => actionOf (parseYouGainLife effect 0)

/-- Search for one basic land, reveal it, hold it out of the shuffle, then
put that card on top. The found card is variable `n`. -/
def searchBasicLandOnTop (n : Nat) : CardAction :=
  .sequence [
    .searchLibraryThenShuffle (.controller .this) [
      .defineSelectorVariable n
        (.selected (.controller .this) (.range 1 1) basicLandInLibrary),
      .reveal (.variable n),
      .holdOutInLibrary (.variable n)],
    .putOnTopOfLibrary (.variable n)]

/-- `You may search your library for a basic land card, reveal it, then shuffle and put that card on top.`
The found card is variable `n`. -/
def parseMaySearchBasicOnTop (sentence : String) (n : Nat) : Option (CardAction × Nat) :=
  if sentenceIs sentence
      "you may search your library for a basic land card, reveal it, then shuffle and put that card on top" then
    some (.optional (.controller .this) (searchBasicLandOnTop n), n + 1)
  else none

/-- `When <this> enters, you gain N life. You may search your library for a basic land card, reveal it, then shuffle and put that card on top.`
The entering object is this card. The found card is variable `n`. -/
def parseEnterGainLifeMaySearchBasicOnTop (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, search] =>
    onEnterN cardName enter fun effect =>
      match actionOf (parseYouGainLife effect n), parseMaySearchBasicOnTop search n with
      | some gain, some (maySearch, n') =>
        some (.sequence [gain, maySearch], n')
      | _, _ => none
  | _ => none

/-- `When this creature enters, untap another target creature you control. If that creature is a Bear, put a +1/+1 counter on it.`
The creature is target `n`. `another` excludes this object. -/
def parseEnterUntapPlusOneIfSubtype (cardName line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, ifSubtype] =>
    onEnterN cardName enter fun effect =>
      (after? effect "untap ").bind parseBattlefieldTarget |>.bind fun sel =>
        if !sel.shape.anotherCreatureYouControl then none
        else
          (between? (normSentence ifSubtype)
              "if that creature is " ", put a +1/+1 counter on it").bind
            dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
            (.sequence [
                .untap (.target n sel),
                .if
                  (.anySubtype (.targetReference n) st)
                  [.putCounter (.targetReference n) .plusOnePlusOne 1]],
             n + 1)
  | _ => none

/-- `recruit` as a keyword action of this card's controller. -/
def recruitEffect? (effect : String) : Option CardAction :=
  if effect == "recruit" then some (.keyword (.controller .this) .recruit) else none

/-- `When <this card> enters, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterRecruit (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line recruitEffect?

/-- `When <this card> dies, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseDiesRecruit (cardName : String) (line : String) : Option CardPart :=
  onDies cardName line recruitEffect?

/-- `When <this card> enters, scry N.`
`N` is a positive printed number. A reminder parenthetical is not rules text. -/
def parseEnterScry (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line fun effect => actionOf (parseScry effect 0)

/-- `create a Treasure token` or `create a tapped Treasure token`.
A tapped token enters tapped (CR 110.5). -/
def parseCreateTreasure (sentence : String) : Option CardAction :=
  match normSentence sentence with
  | "create a tapped treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken [.tapped])
  | "create a treasure token" =>
    some (.createTokens (.controller .this) 1 PredefinedToken.treasureToken)
  | _ => none

/-- `When <this card> enters, create a Treasure token.`
Also `create a tapped Treasure token`. -/
def parseEnterCreateTreasure (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line parseCreateTreasure

/-- `When <this card> enters, exile the top card of your library. Until the end of your next turn, you may play that card.`
The exile is action `n`. The exiled card may be played until the end of your
next turn (CR 611.2a). -/
def parseEnterExileTopMayPlay (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  match sentences line with
  | [enter, play] =>
    onEnterN cardName enter fun effect =>
      if !sentenceIs effect "exile the top card of your library" then none
      else if !sentenceIs play
          "until the end of your next turn, you may play that card" then none
      else some (exileTopPlayUntilEndOfNextTurn n, n + 1)
  | _ => none

/-- `This spell can't be countered.`
Countering this spell is forbidden. The ability functions while this spell
is on the stack (CR 113.6b). -/
def parseCantBeCountered (line : String) : Option CardPart :=
  if sentenceIs (rulesText line) "this spell can't be countered" then
    some (.ability (.stackStatic (.forbid (.counter .this))))
  else none

/-- A noncreature spell this object's controller casts. -/
def noncreatureSpellYouCast : Selector :=
  .intersection [.spell, .not (.cardType .creature), youControl]

/-- Effect of `Whenever you cast a noncreature spell, <effect>`. -/
def youCastNoncreatureEffect? (line : String) : Option String :=
  after? (normLine line) "whenever you cast a noncreature spell, "

/-- `Whenever you cast a noncreature spell, amass Goblins 1.`
Amass is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseYouCastNoncreatureAmass (line : String) : Option CardPart :=
  onTrigger (.castSpell noncreatureSpellYouCast)
    ((youCastNoncreatureEffect? line).bind parseAmass)

/-- `Whenever you cast a noncreature spell, <this> gets +1/+1 until end of turn and deals 1 damage to each opponent.`
`<this>` is this card. The bonus lasts until end of turn. `N` is a positive
count. Each opponent of this object's controller is dealt that damage. -/
def parseYouCastNoncreaturePumpAndDamage (cardName : String) (line : String) :
    Option CardPart :=
  (youCastNoncreatureEffect? line).bind fun effect =>
    (split2? effect " until end of turn and deals ").bind fun (pump, damage) =>
      (splitGetsOnly? pump).bind fun (who, ptText) =>
        (before? damage " damage to each opponent").bind fun amt =>
          if !refersToSelf cardName who then none
          else
            match parsePowerToughness ptText, positiveCount amt with
            | some (p, t), some n =>
              (pumpUntilEnd (.source .this) p t none).map fun pumpAction =>
                .ability (.triggered
                  (.castSpell noncreatureSpellYouCast)
                  (.sequence [
                    pumpAction,
                    .dealDamage (.source .this)
                      (.opponent (.controller .this)) (.int n)]))
            | _, _ => none

/-- `When <this card> enters, amass Goblins 1.`
The entering object is this card. -/
def parseEnterAmass (cardName : String) (line : String) : Option CardPart :=
  onEnter cardName line parseAmass

/-- `When <this card> dies, amass Goblins 4.`
The dying object is this card. -/
def parseDiesAmass (cardName : String) (line : String) : Option CardPart :=
  onDies cardName line parseAmass

/-- `Whenever you attack, amass Goblins 2.`
“Whenever you attack” is one trigger when creatures you control attack at
the same time (CR 508.3 / 603.2d). -/
def parseYouAttackAmass (line : String) : Option CardPart :=
  onTrigger youAttack ((youAttackEffect? line).bind parseAmass)

/-- `Whenever you attack, recruit.`
“Whenever you attack” is one trigger when creatures you control attack at
the same time (CR 508.3 / 603.2d). A reminder parenthetical is not rules text. -/
def parseYouAttackRecruit (line : String) : Option CardPart :=
  onTrigger youAttack ((youAttackEffect? line).bind recruitEffect?)

/-- `You may cast this spell as though it had flash if you control a Human.`
The permission is checked as you begin to cast this spell, before the card
is put onto the stack (CR 601.3 / 702.8). `you` is `Selector.caster`, the
player who would cast the spell. The spell does not gain flash. -/
def parseCastAsThoughFlash (line : String) : Option CardPart :=
  (after? (normLine line)
      "you may cast this spell as though it had flash if you control ").bind
    dropArticle? |>.bind subtypeOfOracle? |>.map fun st =>
      .ability (.everywhereStatic (
        .canBeCastAsThoughWithFlashIf
          .this
          (.any (.intersection [.zone .battlefield, .subtype st, .controlled .caster]))))

/-- `<permanents> get +P/+T.` No duration is printed, so this is a static
ability (CR 604.2 / 613.4c). A zero bonus is omitted. `+0/+0` is not an
effect. A bonus that lasts until end of turn is a different ability. -/
def parseStaticGets (line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (splitGets? s).bind fun (who, ptText) =>
      match parseControlledPhrase who, parsePowerToughness ptText with
      | some sel, some (p, t) => staticPowerToughness sel p t
      | _, _ => none

/-- `Whenever <this card> enters or attacks, recruit.`
Recruit is a keyword action of this card's controller. A reminder
parenthetical is not rules text (CR 207.2). -/
def parseEnterOrAttackRecruit (cardName : String) (line : String) : Option CardPart :=
  (triggerSelfEffect? cardName "whenever" (normLine line) " enters or attacks, ").bind
    recruitEffect? |>.map fun action =>
      .ability (.triggered (.or (.enter .this) (.attack .this .all)) action)

/-- `When <this card> enters, put a +1/+1 counter on target <permanent>.`
The entering object is this card. The target is `n`. -/
def parseEnterPutPlusOneOnTarget (cardName : String) (line : String) (n : Nat) :
    Option (CardPart × Nat) :=
  onEnterN cardName line (parsePutPlusOneOnTarget · n)

/-- A color word such as `red` or `green`. -/
def colorName? (s : String) : Option Color :=
  match norm s with
  | "white" => some .white
  | "blue" => some .blue
  | "black" => some .black
  | "red" => some .red
  | "green" => some .green
  | _ => none

/-- Unsigned `2/2`. A sign is a pump, not a token's power and toughness. -/
def parseUnsignedPT (s : String) : Option (Nat × Nat) :=
  (split2? s "/").bind fun (p, t) =>
    match natOfDigits? p, natOfDigits? t with
    | some p, some t => some (p, t)
    | _, _ => none

/-- The subtype whose printed plural is `word` (`Wolves` is Wolf). -/
def pluralCreatureType? (word : String) : Option CardSubtype :=
  cardSubtypes.find? fun st =>
    norm (StaticAbility.pluralSubtype (toString st)) == norm word

/-- `Other Elves you control get +1/+1.`
No duration is printed, so this is a static ability. The subtype is plural.
A zero bonus is omitted. `+0/+0` is not an effect. -/
def parseOtherSubtypeYouControlGets (line : String) : Option (List CardPart) :=
  let s := normLine line
  if (split2? s " until end of turn").isSome then none
  else
    (after? s "other ").bind fun rest =>
      (split2? rest " you control get ").bind fun (plural, ptText) =>
        match pluralCreatureType? plural, parsePowerToughness ptText with
        | some st, some (p, t) =>
          staticPowerToughness
            (.intersection [
              .not .this, .zone .battlefield, .cardType .creature, .subtype st, youControl])
            p t
        | _, _ => none

/-- `create a 2/2 red Dwarf creature token` or
`create two 2/2 green Wolf creature tokens`.
One token uses the singular noun. More than one uses the plural.
The token is a creature of that power, toughness, color, and subtype. -/
def parseCreateColoredCreatureToken (sentence : String) : Option CardAction :=
  (after? (normSentence sentence) "create ").bind fun rest =>
    match rest.splitOn " " |>.map copied |>.filter (· != "") with
    | [countText, pt, colorText, subtypeText, creatureWord, tokenWord] =>
      let plural := tokenWord == "tokens"
      if creatureWord != "creature" || (tokenWord != "token" && !plural) then none
      else
        match nounCount? countText plural, parseUnsignedPT pt,
            colorName? colorText, subtypeOfOracle? subtypeText with
        | some n, some (p, t), some c, some st =>
          some (.createTokens (.controller .this) (Value.int n) [
            .type .creature,
            .subtype st,
            .colorIndicator [c],
            .power p,
            .toughness t])
        | _, _, _, _ => none
    | _ => none

/-- `Landfall — Whenever a land you control enters, create a 1/1 green Elf creature token.`
`Landfall` is an ability word (CR 207.2c) and may be omitted. -/
def parseLandfallCreate (line : String) : Option CardPart :=
  (after? (withoutLandfall line) landYouControlEnters).bind
    parseCreateColoredCreatureToken |>.map fun action =>
      .ability (.triggered (.enter landsYouControl) action)

/-- `This ability costs {1} less to activate for each Equipment you control.`
`{N}` is generic mana. Zero is not a reduction. -/
def parseAbilityCostsLessPerEquipment (sentence : String) : Option Nat :=
  (between? (normSentence sentence)
      "this ability costs " " less to activate for each equipment you control").bind
    positiveGeneric?

/-- `{4}{R}, {T}: Create a 2/2 red Dwarf creature token. This ability costs {1} less to activate for each Equipment you control. Activate only as a sorcery.`
The reduction is `{N}` for each Equipment this object's controller controls.
It is a static effect of that activated ability. `.this` in the effect is
the ability. Sorcery timing is the activation restriction. -/
def parseActivatedCreateCostsLess (cardName line : String) (n : Nat) :
    Option (List CardPart × Nat) :=
  (splitPrintedAbility? line).bind
    fun (costText, effect) =>
      let (body, limit) := splitActivateLimit (sentences effect)
      match body, limit with
      | [createText, lessText], .asSorcery =>
        match parseCreateColoredCreatureToken createText,
            parseAbilityCostsLessPerEquipment lessText,
            parsePrintedCosts cardName costText with
        | some create, some k, some costs =>
          some ([
            .ability (.activatedWithStaticIf
              (.timeToCastSorcery (.controller .this))
              costs
              create
              (.reduceCostWithX .this
                [.mana [.generic k]]
                (.count equipmentYouControl)))],
            n)
        | _, _, _ => none
      | _, _ => none

end OracleParts

end Mtg.Engine
