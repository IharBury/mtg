import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.Targeting

/-!
# Reality Fracture Commander Oracle lines

Lines the shared parser does not already model, lowered directly into the
unified Phase-8 `Instruction`, `StaticAbility`, `ActivatedAbility`, and
`TriggeredAbility` AST.
-/

namespace Mtg.Engine

open OracleActivate

private def low (s : String) : String :=
  s.map Char.toLower

private def parseSym (s : String) : Option (ManaSymbol × String) :=
  let s := s.trimAscii.copy
  if !s.startsWith "{" then none
  else
    match (s.drop 1).copy.splitOn "}" with
    | [] => none
    | head :: rest =>
      let sym := head.trimAscii.copy.map Char.toUpper
      let after := (String.intercalate "}" rest).trimAscii.copy
      let color? : String → Option Color
        | "W" => some .white
        | "U" => some .blue
        | "B" => some .black
        | "R" => some .red
        | "G" => some .green
        | _ => none
      if sym == "X" then some (.x, after)
      else if sym == "C" then some (.colorless, after)
      else if sym == "T" then none
      else
        match sym.splitOn "/" with
        | [a, b] =>
          match color? a, color? b with
          | some ca, some cb => some (.hybrid ca cb, after)
          | _, _ => none
        | _ =>
          match color? sym with
          | some c => some (.colored c, after)
          | none =>
            if sym.all Char.isDigit && !sym.isEmpty then some (.generic sym.toNat!, after)
            else none

private def collectMana (s : String) : Array ManaSymbol :=
  let rec go (fuel : Nat) (left : String) (acc : Array ManaSymbol) : Array ManaSymbol :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let left := left.trimAscii.copy
      if left.isEmpty then acc
      else if (low left).startsWith "{t}" then
        go fuel ((left.drop 3).copy) acc
      else
        match parseSym left with
        | some (sym, rest) =>
          if rest.length < left.length then go fuel rest (acc.push sym) else acc
        | none => go fuel ((left.drop 1).copy) acc
  go s.length s #[]

private def costOf (s : String) : ManaCost :=
  { symbols := collectMana s }

private def frcInstr (body : Instruction) (spec : TargetSpec := .none) : Effect :=
  { targets := spec, body }

private def creature : TargetSpec :=
  .creature

private def oppPlayer : TargetSpec :=
  .opponent

private def cap (w : String) : String :=
  if w.isEmpty then w else String.singleton w.front.toUpper ++ (w.drop 1).copy

private def addKw (c : CardDef) (text : String) : CardDef :=
  (text.splitOn ",").foldl (fun c part =>
    match KeywordAbility.ofSimpleName? part.trimAscii.copy with
    | some k => c.withKeyword k
    | none => c) c

private def colorsFrom (text : String) : Array Color :=
  let parts := (low text).splitOn " and "
  (parts.filterMap fun p =>
    if p.contains "white" then some Color.white
    else if p.contains "blue" then some Color.blue
    else if p.contains "black" then some Color.black
    else if p.contains "red" then some Color.red
    else if p.contains "green" then some Color.green
    else none).toArray

private def pushTrig (c : CardDef) (pattern : TriggerPattern) (e : Effect)
    (spec : TargetSpec := .none) (grouping : BatchGrouping := .perOccurrence)
    (interveningIf? : Option Condition := none) (activeZones : Array ZoneKind := #[.battlefield]) :
    CardDef :=
  { c with
    triggeredAbilities :=
      c.triggeredAbilities.push
        (TriggeredAbility.ofPattern pattern e.body spec
          (grouping := grouping) (interveningIf? := interveningIf?)
          (activeZones := activeZones)) }

private def pushAct (c : CardDef) (e : Effect) (lineText : String) (costText : String)
    (sorcery := false) (loyalty : Option LoyaltySymbol := none) : CardDef :=
  let costLow := low costText
  let ab := activated e (mana := costOf costText)
    (tap := costLow.contains "{t}")
    (sacrificeSource := costLow.contains "sacrifice")
    (timing := if sorcery || (low lineText).contains "only as a sorcery" then .sorcery else .instant)
    (loyalty := loyalty)
    (removeStoryCounter := costLow.contains "story counter")
  { c with activatedAbilities := c.activatedAbilities.push ab }

private def pushSpell (c : CardDef) (e : Effect) : CardDef :=
  c.withSpellEffect e

/-- Draw `drawN` cards, then put `putN` cards from your hand on top of your library. -/
private def instrDrawPutOnTop (drawN putN : Nat) : Instruction :=
  .seq #[
    Instruction.drawFixed drawN,
    .moveZone (.inZones .yourHand .anyObject) (.library .owner .top false) .put
      { choice? := some { chooser := .controller, count := .exact (.const putN) } }]

/-- Search your library for a basic land card of one of `kinds`, put it onto the
battlefield tapped, then shuffle; if `untapAt > 0` and you control `untapAt` or
more lands, untap it. -/
private def instrSearchBasics (kinds : Array CardSubtype) (untapAt : Nat) : Instruction :=
  let kindPred : ObjectPred :=
    .any (kinds.map fun k => .hasSubtype (.literal k))
  let untapCond? : Option Condition :=
    if untapAt == 0 then none
    else some (.cmp .ge
      (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .land, .controlledBy .you])))
      (.const untapAt))
  .player (.searchLibrary {
    filter := .all #[.hasSupertype .basic, .hasType .land, kindPred]
    count := .upTo (.const 1)
    dest := .battlefield .controller
    mods := { tapped := true }
    reveal := true
    shuffle := true
    untapIf? := untapCond? })

/-- Animate this permanent into a `p/t` creature until end of turn, optionally
with flying and/or first strike during your turn. -/
private def instrAnimate (p t : Nat) (flying firstStrikeOnYourTurn : Bool) : Instruction :=
  let mods : Array ContinuousModification := Id.run do
    let mut out : Array ContinuousModification := #[
      .modifyTypes { mode := .add, types := #[.creature] },
      .setBasePT (some (.const p)) (some (.const t))]
    if flying then
      out := out.push (.grantKeywords #[Keyword.flying])
    if firstStrikeOnYourTurn then
      out := out.push (.grantStatic #[
        .continuous (some .isYourTurn) StaticAbility.scopeSelf (.grantKeywords #[Keyword.firstStrike])])
    return out
  .installEffect (.applyContinuous .untilEndOfTurn .this (.all mods))

/-- The effect of one loyalty ability, when it is an FRC ability. -/
def parseFrcLoyaltyEffect (text : String) : Option Effect :=
  let l := low text
  if l.contains "create three 1/1 white soldier" then
    some (Effect.createTokens .soldier11white 3)
  else if l.contains "destroy all creatures with power 4" ||
      l.contains "destroy creature with power 4" then
    some (frcInstr
      (Instruction.destroy (.inZones .battlefield (.all #[.hasType .creature, .stat .power .ge (.const 4)])))
      )
  else if l.contains "emblem" && l.contains "flying" then
    some (frcInstr
      (.create (.emblem .you { staticAbilities := #[StaticAbility.creaturesYouControlGetAndHave 2 2 #[Keyword.flying]] }))
      )
  else if l.contains "draw two cards, then put a card from your hand on the bottom" ||
      l.contains "draw 2 cards. put a from card in your hand on the bottom" then
    some (frcInstr
      (.seq #[
        Instruction.drawFixed 2,
        .moveZone (.inZones .yourHand .anyObject) (.library .owner .bottom false) .put
          { choice? := some { chooser := .controller, count := .exact (.const 1) } }])
      )
  else if l.contains "exile another target planeswalker or creature" then
    some (frcInstr
      (.seq #[
        Instruction.exile (.target 0),
        .player (.inspectLibrary {
          source := .revealUntil .you (.any #[.hasType .creature, .hasType .planeswalker]) (.const 1)
          action := .moveAll (.battlefield .controller)
          rest := .bottomRandom })])
      (.ofDomain (.object .battlefield (.all #[
        .otherThan .this,
        .any #[.hasType .planeswalker, .hasType .creature],
        .controlledBy .you
      ]))))
  else none

private def effectText (raw : String) : Option Effect :=
  match parseFrcLoyaltyEffect raw with
  | some e => some e
  | none =>
    let l := low raw
    if l.contains "draw three cards, then put two cards" ||
        l.contains "draw 3 cards. put two from card in your hand on top" then
      some (frcInstr (instrDrawPutOnTop 3 2))
    else if l.contains "draw four cards, then put two cards" ||
        l.contains "draw 4 cards. put two from card in your hand on top" then
      some (frcInstr (instrDrawPutOnTop 4 2))
    else if l.contains "exile target permanent with mana value 4" then
      some (frcInstr (Instruction.exile (.target 0))
        (.ofDomain (.object .battlefield (.stat .manaValue .ge (.const 4)))))
    else if l.contains "exile target creature. its controller may search" ||
        l.contains "exile target creature. its controller may its controller searches" then
      some (frcInstr
        (.seq #[
          Instruction.exile (.target 0),
          Instruction.may (.controllerOf (.target 0)) none
            (.player (.searchLibrary {
              searcher := .controllerOf (.target 0)
              zones := .libraryOf (.controllerOf (.target 0))
              filter := .all #[.hasSupertype .basic, .hasType .land]
              count := .upTo (.const 1)
              dest := .battlefield (.player (.controllerOf (.target 0)))
              mods := { tapped := true }
              reveal := true
              shuffle := true }))])
        creature)
    else if l.contains "exile target creature. its controller gains life" ||
        l.contains "exile target creature. its controller gains target's power life" then
      some (frcInstr
        (.seq #[
          Instruction.exile (.target 0),
          .life (.gain (.controllerOf (.target 0)) (.objectStat .power (.target 0)))])
        creature)
    else if l.contains "destroy target nonland" then
      some (frcInstr
        (.seq #[
          Instruction.destroy (.target 0),
          Instruction.createTokensFixed .human11white 1 (.controllerOf (.target 0))])
        .nonland)
    else if l.contains "create x 1/1 green and white citizen" ||
        l.contains "create x 1/1 white and green citizen" then
      some (frcInstr
        (.seq #[
          .create (.tokens .you .chosenX .citizen),
          Instruction.grantKeywords
            (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you]))
            #[Keyword.indestructible]])
       )
    else if l.contains "create x 1/1 white soldier" && l.contains "if x is 5" then
      some (frcInstr
        (.bind ⟨0⟩ (.create (.tokens .you .chosenX .soldier11white))
          (Instruction.ifThen (.cmp .ge .chosenX (.const 5))
            (Instruction.destroy (.inZones .battlefield (.all #[.hasType .creature, .otherThan (.stepVar ⟨0⟩)])))))
       )
    else if l.contains "create x 1/1 white warrior" then
      some (frcInstr (.create (.tokens .you .chosenX .warrior)))
    else if l.contains "you gain x life" && l.contains "phyrexian mite" then
      some (frcInstr
        (.seq #[
          .life (.gain .you .chosenX),
          .bind ⟨0⟩ (.create (.tokens .you .chosenX .mite))
            (Instruction.ifThen (.cmp .ge .chosenX (.const 5))
              (Instruction.destroy (.inZones .battlefield (.all #[.hasType .creature, .otherThan (.stepVar ⟨0⟩)]))))])
       )
    else if l.contains "draw x cards, then discard x cards" ||
        l.contains "draw x cards. discard x cards. create the number of card types" then
      some (frcInstr
        (.seq #[
          .player (.drawCards .you .chosenX),
          .bind ⟨0⟩ (Instruction.discard .chosenX)
            (.create (.tokens .you (.cardTypeCount (.stepObjects ⟨0⟩)) .spirit))])
       )
    else if l.contains "exile all creatures. incubate" ||
        l.contains "exile creature. create a incubator token" then
      some (frcInstr
        (.bind ⟨0⟩ (Instruction.exile (.inZones .battlefield (.hasType .creature)))
          (.create (.tokens .you (.const 1) .incubator
            { counters := #[(.plusOnePlusOne, .stepMetric .movedCount ⟨0⟩)] })))
       )
    else if l.contains "exile all creatures you control, then reveal" ||
        (l.contains "exile creature you control. reveal cards from the top" && l.contains "moved this way") then
      some (frcInstr
        (.bind ⟨0⟩ (Instruction.exile (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])))
          (.player (.inspectLibrary {
            source := .revealUntil .you (.hasType .creature) (.stepMetric .movedCount ⟨0⟩)
            action := .moveAll (.battlefield .controller)
            rest := .shuffleIntoLibrary })))
       )
    else if l.contains "exile all creatures you control. at the beginning of the next end step" ||
        l.contains "exile creature you control. until end of turn, at the beginning of each end step" then
      some (frcInstr
        (.bind ⟨0⟩ (Instruction.exile (.inZones .battlefield (.all #[.hasType .creature, .controlledBy .you])))
          (.installEffect (.createDelayedTrigger {
            pattern := .stepBegins .end (.player .any)
            duration := .untilEndOfTurn
            oneShot := true
            effect := {
              body := .player (.inspectLibrary {
                source := .revealUntil .you (.hasType .creature) (.stepMetric .movedCount ⟨0⟩)
                action := .moveAll (.battlefield .controller)
                rest := .shuffleIntoLibrary }) } })))
       )
    else if l.contains "reveal the top five cards" then
      some (frcInstr
        (.player (.inspectLibrary {
          source := .topCards .you (.const 5) true
          action := .splitIntoPiles .opponents .you 2 (.hand .controller) .graveyard
          rest := .graveyard }))
       )
    else if l.contains "create two 1/1 white spirit" then
      some (Effect.createTokens .spirit 2)
    else if l.contains "creatures you control gain indestructible" then
      some (Effect.teamGain #[Keyword.indestructible])
    else if l.contains "you gain 6 life" then
      some (Effect.gainLife 6)
    else if l == "scry 1." || l == "scry 1" || l.contains "whenever this land attacks, scry 1" then
      some (Effect.scry 1)
    else if l == "draw a card." || l == "draw a card" then
      some (Effect.draw 1)
    else if l.contains "each opponent loses 1 life and you gain 1" ||
        l.contains "each opponent loses 1 life. you gain 1 life" then
      some (frcInstr (.seq #[.life (.lose .opponents (.const 1)), .life (.gain .you (.const 1))]))
    else if l.contains "draw a card, then discard a card" then
      some (frcInstr (.seq #[Instruction.drawFixed 1, Instruction.discardFixed 1]))
    else if l.contains "put a card exiled with this artifact" ||
        l.contains "move a card exiled with this permanent into its owner's graveyard" then
      some (frcInstr
        (.bind ⟨0⟩ (.moveZone (.linkedExile .this) .graveyard .put
            { choice? := some { chooser := .controller, count := .exact (.const 1) } })
          (Instruction.ifThen (.cmp .ge (.stepMetric .movedCount ⟨0⟩) (.const 1))
            (.ifCond (.exists (.filter (.stepObjects ⟨0⟩) (.hasType .land)))
              (Instruction.createTokensFixed .treasure 1)
              (Instruction.createTokensFixed .rogue22black 1))))
       )
    else if l.contains "put target creature on the bottom" then
      some (frcInstr
        (.seq #[
          .moveZone (.target 0) (.library .owner .bottom false) .put,
          .player (.inspectLibrary {
            source := .revealUntil (.controllerOf (.target 0)) (.hasType .creature) (.const 1)
            action := .moveAll (.battlefield (.player (.controllerOf (.target 0))))
            rest := .bottomRandom })])
        creature)
    else if l.contains "becomes a 2/3" || l.contains "becomes a creature with base power and toughness 2/3" then
      some (frcInstr (instrAnimate 2 3 true false))
    else if l.contains "becomes a 2/1" || l.contains "becomes a creature with base power and toughness 2/1" then
      some (frcInstr (instrAnimate 2 1 false true))
    else if l.contains "create a 0/1 red kobold" then
      some (frcInstr (Instruction.createTokensFixed .kobold 1))
    else if l.contains "gets +1/+0 until end of turn" then
      some (frcInstr (Instruction.pumpFixed .this 1 0))
    else if l.contains "search your library for a basic plains, island, or swamp" then
      some (frcInstr (instrSearchBasics #[.plains, .island, .swamp] 0))
    else if l.contains "search your library for a basic island, mountain, or plains" then
      some (frcInstr (instrSearchBasics #[.island, .mountain, .plains] 0))
    else if l.contains "search your library for a basic land card" ||
        l.contains "search your library for a basic plains, island, swamp, mountain, or forest" then
      some (frcInstr (instrSearchBasics #[.plains, .island, .swamp, .mountain, .forest] 4))
    else if l.contains "add {c}{c}" || l.contains "add {C}{C}" then
      some (Effect.addMana #[.colorless, .colorless])
    else if l.contains "copy target instant or sorcery" then
      some (frcInstr (.stack (.copyStackObject (.target 0) (.const 2) true))
        (.ofDomain (.object .stack (.all #[
          .any #[.hasType .instant, .hasType .sorcery], .isKind .spell, .controlledBy .opponent
        ]))))
    else if l.contains "create two tokens that are copies" then
      some (frcInstr
        (.create (.tokens .you (.const 2) (.copyOf (.target 0) #[]) {
          grantKeywordsUntilEot := #[Keyword.haste]
          delayedAction? := some .sacrificeAtEndStep }))
        .oppPermanent)
    else none

/-- One unrecognized Oracle line on an FRC card, if this module models it. -/
def parseFrcLine (c : CardDef) (line : String) : Option CardDef :=
  let l := low line
  let static : Option CardDef :=
    if l.contains "protection from" && (l.contains "flying" || l.contains "trample" || l.startsWith "protection") then
      let before := (line.splitOn "protection from").headD ""
      let cols := colorsFrom ((line.splitOn "protection from").getLastD "")
      let prots := cols.map (fun col => KeywordAbility.protection (.color (.literal col)))
      some ((addKw c before).withKeywords prots)
    else if l.startsWith "morph " then
      some (c.withKeyword (.morph (CostSpec.ofMana (costOf line))))
    else if l.startsWith "impending " then
      let n :=
        match (l.drop "impending ".length).takeWhile Char.isDigit with
        | "" => 0
        | d => d.toNat!
      some (c.withKeyword (.impending n (CostSpec.ofMana (costOf line))))
    else if l.startsWith "cycling " then
      let cost := costOf ((line.splitOn "(").headD line)
      let ab := activated (Effect.draw 1) (mana := cost) (activeZones := #[.hand])
        (tag? := some (.cycling none)) (discardSource := true)
      let c' := c.withKeyword (.cycling none (CostSpec.ofMana cost))
      some { c' with activatedAbilities := c'.activatedAbilities.push ab }
    else if l.contains "your opponents can't gain life" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.opponentsCantGainLife }
    else if l.contains "can't lose the game" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.cantLoseAndOpponentsCantWin }
    else if l.contains "can't have -1/-1 counters" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.creaturesCantGetMinusCounters }
    else if l.contains "lands you control have" && l.contains "any color" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.grantLandsTapAnyColor }
    else if l.contains "for each unspent mana you have" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.powerPerUnspentMana }
    else if l.contains "that mana becomes colorless instead" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.unspentManaBecomesColorless }
    else if l.contains "other sphinx spells you cast cost" then
      some { c with staticAbilities := c.staticAbilities.push (StaticAbility.eminenceSubtypeSpellsCostLess .sphinx 1) }
    else if l.contains "choose a card type" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.asEntersChooseCardType }
    else if l.contains "protection from the chosen card type" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.protectionFromChosenCardType }
    else if l.contains "creatures you control with toxic have lifelink" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.corruptedToxicLifelink }
    else if l.contains "can be your commander" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.canBeCommander }
    else if l.contains "without paying its mana cost" && l.contains "commander" then
      some { c with staticAbilities := c.staticAbilities.push StaticAbility.freeCastIfControlCommander }
    else if l.contains "enters tapped unless you control two or more basic" then
      some { c with staticAbilities := c.staticAbilities.push (StaticAbility.entersTappedUnlessNBasics 2) }
    else if l.contains "enters tapped unless your opponents control eight" then
      some { c with staticAbilities := c.staticAbilities.push (StaticAbility.entersTappedUnlessOppLands 8) }
    else if l.contains "enters tapped unless you control a" &&
        (l.contains " or a " || l.contains " or an ") then
      let after :=
        if l.contains "control an " then (l.splitOn "control an ").getLastD ""
        else (l.splitOn "control a ").getLastD ""
      let types := ((after.replace " or an " " or a ").splitOn " or a ").map fun p =>
        cap ((p.splitOn " ").headD "" |>.splitOn "." |>.headD "")
      let ab := StaticAbility.entersTappedUnlessAnySubtype (CardSubtype.ofSubtypes types.toArray)
      some { c with staticAbilities := c.staticAbilities.push ab }
    else if l == s!"exile {low c.name}." then
      some c
    else if l.contains "choose mardu or jeskai" then
      let anchorAb := StaticAbility.asEntersChooseNamedAnchors #["Mardu", "Jeskai"]
      let c' :=
        if c.staticAbilities.contains anchorAb then c
        else { c with staticAbilities := c.staticAbilities.push anchorAb }
      if l.contains "jeskai —" || l.contains "mardu —" then
        let goblinInstr : Instruction :=
          Instruction.ifThen (.exists (.filter .this (.chosenAnchorIs "Jeskai")))
            (.create (.tokens .you (.const 1) .goblin11red
              { grantKeywordsUntilEot := #[Keyword.lifelink, Keyword.haste] }))
        some (pushTrig c' .stepYourUpkeep (frcInstr goblinInstr))
      else
        some c'
    else none
  match static with
  | some c => some c
  | none =>
    if l.contains ":" && !l.startsWith "whenever" && !l.startsWith "when " &&
        !l.startsWith "at the beginning" then
      match line.splitOn ":" with
      | cost :: rest =>
        let effectRaw := (String.intercalate ":" rest).trimAscii.copy
        match effectText effectRaw with
        | some e => some (pushAct c e line cost)
        | none => none
      | _ => none
    else
      if l.contains "enters or attacks" &&
          (l.contains "target opponent sacrifices" ||
           l.contains "sacrifices a creature or planeswalker target player controls") then
        let archonInstr : Instruction := .seq #[
          .moveZone
            (.inZones .battlefield (.all #[
              .controlledBy (PlayerFilter.ofExpr (.target 0)),
              .any #[.hasType .creature, .hasType .planeswalker]]))
            .graveyard .sacrifice
            { choice? := some { chooser := .player (.target 0), count := .exact (.const 1) } },
          Instruction.discardFixed 1 (.target 0),
          Instruction.loseLifeFixed 3 (.target 0),
          Instruction.drawFixed 1,
          Instruction.gainLifeFixed 3]
        some (pushTrig c .enterOrAttack (frcInstr archonInstr oppPlayer) oppPlayer)
      else if l.contains "enters or attacks" && l.contains "historic" then
        let jhoiraInstr : Instruction :=
          .bind ⟨0⟩
            (.player (.inspectLibrary {
              source := .revealUntil (.target 0) ObjectPred.historic (.const 1)
              action := .moveAll (.battlefield .controller)
              rest := .bottomRandom }))
            (.life (.lose .you (.aggregate .sum (.stat .manaValue) (.stepObjects ⟨0⟩))))
        some (pushTrig c .enterOrAttack (frcInstr jhoiraInstr oppPlayer) oppPlayer)
      else if l.contains "enters or attacks" && l.contains "insect" then
        some (pushTrig c .enterOrAttack (frcInstr (Instruction.createTokensFixed .insect21flying 2)))
      else if l.contains "another nontoken creature you control dies" ||
          (l.contains "nontoken creature you control dies") then
        let avacynInstr : Instruction :=
          .installEffect (.createDelayedTrigger {
            pattern := .stepBegins .end (.player .any)
            duration := .untilEndOfTurn
            oneShot := true
            effect := {
              body := .moveZone .triggerSubject (.battlefield .controller) .put } })
        some (pushTrig c .nontokenCreatureYouControlDies (frcInstr avacynInstr))
      else if l.contains "you become the monarch" && l.contains "enters" then
        some (pushTrig c .thisEnters (frcInstr (.player (.becomeMonarch .you))))
      else if l.contains "you're the monarch" && l.contains "gingerbrute" then
        let gbInstr : Instruction :=
          Instruction.ifThen (.playerPred .you .isMonarch) (Instruction.createTokensFixed .gingerbrute 1)
        some (pushTrig c .stepEachUpkeep (frcInstr gbInstr)
          (interveningIf? := some TriggeredAbility.condYouAreMonarch))
      else if l.contains "reveal cards from the top of your library until you reveal x creature" ||
          (l.contains "reveal cards from the top of your library until you reveal" && l.contains "opponent goaded") then
        let dackInstr : Instruction :=
          .player (.inspectLibrary {
            source := .revealUntil .you (.hasType .creature) (.playerMetric .opponentsCount .you)
            action := .distributeEachOpponent (.battlefield .controller) { goaded := true }
            rest := .shuffleIntoLibrary })
        some (pushTrig c .thisEnters (frcInstr dackInstr))
      else if l.contains "zombie token you control with power 6" then
        some (pushTrig c .zombieTokenPowerSixAttacks
          (frcInstr (Instruction.grantKeywords .triggerSubject #[Keyword.lifelink])))
      else if l.contains "you lose 1 life and amass zombies" then
        some (pushTrig c .stepYourUpkeep
          (frcInstr (.seq #[Instruction.loseLifeFixed 1, Instruction.amassFixed 1 .zombie])))
      else if l.contains "you lose 1 life and create a 1/1 colorless phyrexian mite" then
        some (pushTrig c .stepYourUpkeep
          (frcInstr (.seq #[Instruction.loseLifeFixed 1, Instruction.createTokensFixed .mite 1])))
      else if l.contains "whenever you gain life, you may pay" then
        let nivPayInstr : Instruction :=
          Instruction.may .you (some (CostSpec.ofItem (.payLife .eventAmount)))
            (.player (.drawCards .you .eventAmount))
        some (pushTrig c (.gainLife .you) (frcInstr nivPayInstr))
      else if l.contains "destroy all tapped creatures your opponents control" ||
          (l.contains "destroy tapped creature an opponent controls" && l.contains "moved this way life") then
        let obEnterInstr : Instruction :=
          .bind ⟨0⟩
            (Instruction.destroy (.inZones .battlefield (.all #[
              .hasType .creature, .tapped true, .controlledBy .opponent])))
            (.life (.gain .you (.stepMetric .movedCount ⟨0⟩)))
        some (pushTrig c .thisEnters (frcInstr obEnterInstr))
      else if l.contains "if you gained life this turn, create a 4/4" ||
          (l.contains "amount of life you gained this turn is 1 or greater" && l.contains "4/4 white angel") then
        let obAngelInstr : Instruction :=
          Instruction.ifThen (TriggeredAbility.condGainedLifeAtLeast 1)
            (Instruction.createTokensFixed .angel44white 1)
        some (pushTrig c .stepEachEndStep (frcInstr obAngelInstr)
          (interveningIf? := some (TriggeredAbility.condGainedLifeAtLeast 1)))
      else if l.contains "whenever a land you control enters, add" then
        some (pushTrig c .landYouControlEnters
          (frcInstr (Instruction.addSimpleMana #[.colorless, .colorless])))
      else if l.contains "whenever a land you control enters, draw a card" then
        let nissaInstr : Instruction :=
          .seq #[
            Instruction.drawFixed 1,
            Instruction.ifThen (.turnHistory .optionalOnceUnusedThisTurn)
              (.player (.inspectLibrary {
                source := .revealUntil .you (.hasType .creature) (.const 1)
                action := .moveAll (.battlefield .controller)
                rest := .bottomRandom }))]
        some (pushTrig c .landYouControlEnters (frcInstr nissaInstr))
      else if l.contains "at the beginning of each end step, each opponent loses life" ||
          (l.contains "at the beginning of each end step" && l.contains "lost this turn life") then
        let despairInstr : Instruction :=
          .forEach (.eachPlayer .opponent) ⟨0⟩
            (.life (.lose (.stepPlayers ⟨0⟩) (.playerMetric .lifeLostThisTurn (.stepPlayers ⟨0⟩))))
        some (pushTrig c .stepEachEndStep (frcInstr despairInstr))
      else if l.contains "whenever you discard a card, you may exile" then
        let currencyExileInstr : Instruction :=
          Instruction.may .you none (.moveZone .triggerSubject .exile .exile { linkToSource := true })
        some (pushTrig c (.discard .you .anyObject) (frcInstr currencyExileInstr))
      else if l.contains "whenever you create one or more creature tokens" ||
          (l.contains "whenever you create one or more creatures tokens" && l.contains "put counters") then
        some (pushTrig c (.createTokens .you (.hasType .creature))
          (frcInstr (Instruction.putCounters .this .story (.const 1)))
          (grouping := .oncePerBatch))
      else if l.contains "when this artifact enters, create a 1/1 white spirit" ||
          l.contains "when this permanent enters, create a 1/1 white spirit" then
        some (pushTrig c .thisEnters (frcInstr (Instruction.createTokensFixed .spirit 1)))
      else if l.contains "when memnarch enters" || l.contains "create two 1/1 colorless myr" then
        some (pushTrig c .thisEnters (frcInstr (Instruction.createTokensFixed .myr 2)))
      else if l.contains "draw a card for each artifact you control" then
        let drawArtInstr : Instruction :=
          .player (.drawCards .you
            (.aggregate .count .one (.inZones .battlefield (.all #[.hasType .artifact, .controlledBy .you]))))
        some (pushTrig c .thisAttacks (frcInstr drawArtInstr))
      else if l.contains "whenever you cast a noncreature spell, create an x/x blue shark" ||
          (l.contains "whenever you cast a noncreature spell" && l.contains "blue shark creature token") then
        let sharkSpec : TokenSpec :=
          .custom {
            types := #[.creature]
            subtypes := #[.shark]
            colors := ColorSet.singleton .blue
            power? := some (.objectStat .manaValue .triggerSubject)
            toughness? := some (.objectStat .manaValue .triggerSubject)
            keywords := #[Keyword.flying] }
        some (pushTrig c .youCastNoncreature
          (frcInstr (.create (.tokens .you (.const 1) sharkSpec))))
      else if l.contains "whenever you cast a noncreature spell, draw a card" then
        some (pushTrig c .youCastNoncreature (Effect.draw 1))
      else if l.contains "when you cycle this card" || l.contains "when you cycle this permanent" then
        let sharkSpec : TokenSpec :=
          .custom {
            types := #[.creature]
            subtypes := #[.shark]
            colors := ColorSet.singleton .blue
            power? := some .eventAmount
            toughness? := some .eventAmount
            keywords := #[Keyword.flying] }
        some (pushTrig c .thisCycled
          (frcInstr (.create (.tokens .you (.const 1) sharkSpec)))
          (activeZones := #[.hand]))
      else if l.contains "combat on each opponent's turn" then
        let jaceTaxInstr : Instruction :=
          .unlessPays .activePlayer (CostSpec.ofGeneric 2)
            (.installEffect (.applyRule .untilEndOfTurn
              (.combat (.cantAttackPlayer
                (.all #[.hasType .creature, .controlledBy (PlayerFilter.ofExpr .activePlayer)])
                .you
                (some (.all #[.hasType .planeswalker, .hasSubtype (.literal .jace)]))))))
        some (pushTrig c .stepOpponentBeginCombat (frcInstr jaceTaxInstr))
      else if l.contains "while you're the monarch, tap those creatures" ||
          (l.contains "while you're the monarch" && l.contains "tap that creature and put a stun counter") then
        some (pushTrig c (.whenCond .combatDamageToYou TriggeredAbility.condYouAreMonarch)
          (frcInstr (Instruction.tapAndStun .triggerSubject))
          (grouping := .oncePerBatch))
      else if l.contains "chosen option is jeskai" && l.contains "1/1 red goblin" then
        let goblinInstr : Instruction :=
          Instruction.ifThen (.exists (.filter .this (.chosenAnchorIs "Jeskai")))
            (.create (.tokens .you (.const 1) .goblin11red
              { grantKeywordsUntilEot := #[Keyword.lifelink, Keyword.haste] }))
        some (pushTrig c .stepYourUpkeep (frcInstr goblinInstr))
      else if l.contains "one or more sphinxes you control attack" ||
          (l.contains "whenever you attack with one or more sphinxes" && l.contains "mills") then
        let urSphinxInstr : Instruction :=
          .forEach (.eachPlayer .any) ⟨0⟩
            (.bind ⟨1⟩ (Instruction.mill .eventAmount (.stepPlayers ⟨0⟩))
              (.stack (.mayCastOrPlay (.stepObjects ⟨1⟩)
                { freeCast := true
                  landsAllowed := false
                  maxCasts? := some 1
                  filter? := some (.not (.hasType .land)) })))
        some (pushTrig c .sphinxesYouControlAttack (frcInstr urSphinxInstr)
          (grouping := .oncePerBatch))
      else if l.contains "whenever this land attacks, create a map" then
        some (pushTrig c .thisAttacks (frcInstr (Instruction.createTokensFixed .map 1)))
      else if l.contains "whenever this land attacks, scry" then
        some (pushTrig c .thisAttacks (Effect.scry 1))
      else if l.contains "as this artifact enters, you may have it become a copy" then
        some { c with staticAbilities := c.staticAbilities.push StaticAbility.asEntersMayCopyCreatureHasteUntilEot }
      else if l.contains "choose target opponent. until that player's next turn" ||
          (l.contains "protection from everything" && l.contains "phases out until target opponent's next turn") then
        let teferiInstr : Instruction := .seq #[
          .installEffect (.applyRule (.untilNextTurnOf (.target 0))
            (.all #[
              .player (.protectionFrom (PlayerFilter.ofExpr (.target 0)) .everything),
              .player (.lifeTotalCantChange (PlayerFilter.ofExpr (.target 0)))])),
          .permanent (.phaseOut
            (.inZones .battlefield (.all #[
              .controlledBy (PlayerFilter.ofExpr (.target 0)),
              .not (.hasType .land)]))
            (some (.target 0))),
          .installEffect (.applyReplacement .untilEndOfTurn .exileOnLeaveStack)]
        some (pushSpell c (frcInstr teferiInstr oppPlayer))
      else if l.contains "when venser enters, choose one" ||
          (l.contains "choose one" && l.contains "copy target instant") then
        match effectText "Copy target instant or sorcery spell an opponent controls twice.",
            effectText "Create two tokens that are copies of target permanent an opponent controls." with
        | some a, some b =>
          let ab := TriggeredAbility.mkModal .thisEnters #[a, b] (word? := some .when)
          some { c with triggeredAbilities := c.triggeredAbilities.push ab }
        | _, _ => none
      else
        match effectText line with
        | some e =>
          if l.startsWith "whenever" || l.startsWith "when " || l.startsWith "at the beginning" then
            none
          else some (pushSpell c e)
        | none => none

end Mtg.Engine
