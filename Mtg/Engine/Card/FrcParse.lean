import Mtg.Engine.Card.CardDef
import Mtg.Engine.Card.OracleActivate
import Mtg.Engine.Card.Targeting

/-!
# Reality Fracture Commander Oracle lines

Lines the shared parser does not already model. Called only after those
matches fail, so an existing card keeps its current reading.
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

private def manaTypesOf (s : String) : Array ManaType :=
  (collectMana s).filterMap fun
    | .colored c => some (.colored c)
    | .colorless => some .colorless
    | _ => none

private def frc (resolution : Resolution) (phrase : String) (kind : EffectTargetKind := .none) : Effect :=
  { targeting := .of kind, resolution, phrase }

private def creature (noun : String := "target creature") : EffectTargetKind :=
  .filtered { noun, types := #[.creature] }

private def oppPlayer (noun : String := "target opponent") : EffectTargetKind :=
  .filtered { noun, zone := .player, controller := .opponent }

private def cap (w : String) : String :=
  if w.isEmpty then w else String.singleton w.front.toUpper ++ (w.drop 1).copy

private def addKw (c : CardDef) (text : String) : CardDef :=
  (text.splitOn ",").foldl (fun c part =>
    match Keywords.ofName? part.trimAscii.copy with
    | some k => { c with keywords := c.keywords.merge k }
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

private def pushTrig (c : CardDef) (w : SharedTriggerWhen) (e : Effect) (phrase : String)
    (kind : EffectTargetKind := .none) : CardDef :=
  { c with
    triggeredAbilities :=
      c.triggeredAbilities.push (TriggeredAbility.fra w phrase e.resolution kind) }

private def pushAct (c : CardDef) (e : Effect) (phrase : String) (costText : String)
    (sorcery := false) (loyalty : Option LoyaltySymbol := none) : CardDef :=
  let costLow := low costText
  let ab := activated e (mana := costOf costText)
    (tap := costLow.contains "{t}")
    (sacrificeSource := costLow.contains "sacrifice")
    (onlyAsSorcery := sorcery || (low phrase).contains "only as a sorcery")
    (loyalty := loyalty)
  let ab := { ab with
    cost := { ab.cost with removeStoryCounter := costLow.contains "story counter" }
    printed := phrase }
  { c with activatedAbilities := c.activatedAbilities.push ab }

private def pushSpell (c : CardDef) (e : Effect) : CardDef :=
  { c with spellEffect := some e }

/-- The effect of one loyalty ability, when it is an FRC ability. -/
def parseFrcLoyaltyEffect (text : String) : Option Effect :=
  let l := low text
  if l.contains "create three 1/1 white soldier" then
    some (Effect.createTokens .soldier11white 3)
  else if l.contains "destroy all creatures with power 4" then
    some (frc (.destroy .creaturesPowerAtLeast4) text)
  else if l.contains "emblem" && l.contains "flying" then
    some (frc (.grant .emblemCreaturesGetTwoTwoFlying .youIfCast) text)
  else if l.contains "draw two cards, then put a card from your hand on the bottom" then
    some (frc (.putOnLibrary .bottomAfterDrawTwo .cardFromHand) text)
  else if l.contains "exile another target planeswalker or creature" then
    some (frc (.exile (.target .another) .forLater .revealUntilCreatureOrPlaneswalker) text (.filtered {
      noun := "another target planeswalker or creature you control"
      controller := .you, another := true }))
  else none

private def effectText (raw : String) : Option Effect :=
  match parseFrcLoyaltyEffect raw with
  | some e => some e
  | none =>
    let l := low raw
    if l.contains "draw three cards, then put two cards" then
      some (frc (.putOnLibrary (.topAfterDraw 3 2) .cardFromHand) raw)
    else if l.contains "draw four cards, then put two cards" then
      some (frc (.putOnLibrary (.topAfterDraw 4 2) .cardFromHand) raw)
    else if l.contains "exile target permanent with mana value 4" then
      some (frc (.exile .target .forLater .despark) raw (.filtered {
        noun := "target permanent with mana value 4 or greater", mvAtLeast := some 4 }))
    else if l.contains "exile target creature. its controller may search" then
      some (frc (.exile .target .forLater .controllerMaySearchBasic) raw (creature "target creature"))
    else if l.contains "exile target creature. its controller gains life" then
      some (frc (.exile .target .forLater .controllerGainsLifePower) raw (creature "target creature"))
    else if l.contains "destroy target nonland" then
      some (frc (.destroy .target .controllerCreatesHuman) raw (.filtered { noun := "target nonland permanent", nonland := true }))
    else if l.contains "create x 1/1 green and white citizen" then
      some (frc (.createTokens .treasure .chosenX false .citizen .you .teamIndestructible) raw)
    else if l.contains "create x 1/1 white soldier" && l.contains "if x is 5" then
      some (frc (.createTokens .soldier11white .chosenX false .kind .you .destroyOthersIfXAtLeast5) raw)
    else if l.contains "create x 1/1 white warrior" then
      some (frc (.createTokens .treasure .chosenX false .warrior) raw)
    else if l.contains "you gain x life" && l.contains "phyrexian mite" then
      some (frc (.createTokens .treasure .chosenX false .mite .you .gainXLifeAndDestroyOthersIf5) raw)
    else if l.contains "draw x cards, then discard x cards" then
      some (frc (.discard .drawAndDiscardXCreateSpiritPerType) raw)
    else if l.contains "exile all creatures. incubate" then
      some (frc (.exile .allCreatures .forLater .incubateCount) raw)
    else if l.contains "exile all creatures you control, then reveal" then
      some (frc (.exile .creaturesYouControl .forLater .revealCreaturesToBattlefield) raw)
    else if l.contains "exile all creatures you control. at the beginning of the next end step" then
      some (frc (.exile .creaturesYouControl .forLater .revealCreaturesAtEndStep) raw)
    else if l.contains "reveal the top five cards" then
      some (frc (.revealLibrary (.top 5) (.returnToHand .factOrFiction)) raw)
    else if l.contains "create two 1/1 white spirit" then
      some (Effect.createTokens .spirit 2)
    else if l.contains "creatures you control gain indestructible" then
      some (Effect.teamGain Keyword.indestructible)
    else if l.contains "you gain 6 life" then
      some (Effect.gainLife 6)
    else if l == "scry 1." || l == "scry 1" || l.contains "whenever this land attacks, scry 1" then
      some (Effect.scry 1)
    else if l == "draw a card." || l == "draw a card" then
      some (Effect.draw 1)
    else if l.contains "each opponent loses 1 life and you gain 1" then
      some (frc (.loseLife (.fixed 1) .eachOpponentAndYouGain1) raw)
    else if l.contains "draw a card, then discard a card" then
      some (frc (.discard .drawOneDiscardOne) raw)
    else if l.contains "put a card exiled with this artifact" then
      some (frc (.createTokens .treasure (.fixed 1) false .rogue .you .currencyReturn) raw)
    else if l.contains "put target creature on the bottom" then
      some (frc (.putOnLibrary .bottomRevealCreature .target) raw (creature "target creature"))
    else if l.contains "becomes a 2/3" then
      some (frc (.grant (.animateLand 2 3 true false) .source) raw)
    else if l.contains "becomes a 2/1" then
      some (frc (.grant (.animateLand 2 1 false true) .source) raw)
    else if l.contains "create a 0/1 red kobold" then
      some (frc (.createTokens .treasure (.fixed 1) false .kobold) raw)
    else if l.contains "gets +1/+0 until end of turn" then
      some (frc (.onSource (.pump 1 0)) raw)
    else if l.contains "search your library for a basic plains, island, or swamp" then
      some (frc (.searchLibrary (.put (.basicSubtypesUntapAt #["Plains", "Island", "Swamp"] 0) .tapped)) raw)
    else if l.contains "search your library for a basic island, mountain, or plains" then
      some (frc (.searchLibrary (.put (.basicSubtypesUntapAt #["Island", "Mountain", "Plains"] 0) .tapped)) raw)
    else if l.contains "search your library for a basic land card" then
      some (frc (.searchLibrary (.put (.basicSubtypesUntapAt #["Plains", "Island", "Swamp", "Mountain", "Forest"] 4) .tapped)) raw)
    else if l.contains "add {c}{c}" || l.contains "add {C}{C}" then
      some (Effect.addMana #[.colorless, .colorless])
    else if l.contains "copy target instant or sorcery" then
      some (frc (.becomeCopy .targetSpellTwice) raw (.filtered {
        noun := "target instant or sorcery spell an opponent controls"
        zone := .stack, controller := .opponent, types := #[.instant, .sorcery] }))
    else if l.contains "create two tokens that are copies" then
      some (frc (.becomeCopy .targetPermanentTwoTokensHasteSacrifice) raw (.filtered {
        noun := "target permanent an opponent controls", controller := .opponent }))
    else none

private def addBoth (c : CardDef) (w1 w2 : SharedTriggerWhen) (e : Effect) (phrase : String)
    (kind : EffectTargetKind := .none) : CardDef :=
  pushTrig (pushTrig c w1 e phrase kind) w2 e phrase kind

/-- One unrecognized Oracle line on an FRC card, if this module models it. -/
def parseFrcLine (c : CardDef) (line : String) : Option CardDef :=
  let l := low line
  let static : Option CardDef :=
    if l.contains "protection from" && (l.contains "flying" || l.contains "trample" || l.startsWith "protection") then
      let before := (line.splitOn "protection from").headD ""
      let cols := colorsFrom ((line.splitOn "protection from").getLastD "")
      some { addKw c before with protectionFromColors := cols }
    else if l.startsWith "morph " then
      some { c with morph := some (costOf line) }
    else if l.startsWith "impending " then
      let n :=
        match (l.drop "impending ".length).takeWhile Char.isDigit with
        | "" => 0
        | d => d.toNat!
      some { c with impending := some (n, costOf line) }
    else if l.startsWith "cycling " then
      let cost := costOf ((line.splitOn "(").headD line)
      let ab := activated (Effect.draw 1) (mana := cost) (activateFromHand := true)
        (discardSource := true)
      let ab := { ab with printed := line }
      some { c with cycling := some cost
                    activatedAbilities := c.activatedAbilities.push ab }
    else if l.contains "your opponents can't gain life" then
      some { c with opponentsCantGainLife := true }
    else if l.contains "can't lose the game" then
      some { c with cantLoseGame := true, opponentsCantWin := true }
    else if l.contains "can't have -1/-1 counters" then
      some { c with creaturesCantGetMinusCounters := true }
    else if l.contains "lands you control have" && l.contains "any color" then
      some { c with grantLandsTapAnyColor := true }
    else if l.contains "for each unspent mana you have" then
      some { c with powerPerUnspentMana := true }
    else if l.contains "that mana becomes colorless instead" then
      some { c with unspentManaBecomesColorless := true }
    else if l.contains "other sphinx spells you cast cost" then
      some { c with eminenceSphinxReduction := 1 }
    else if l.contains "choose a card type" then
      some { c with asEntersChooseCardType := true }
    else if l.contains "protection from the chosen card type" then
      some { c with protectionFromChosenCardType := true }
    else if l.contains "creatures you control with toxic have lifelink" then
      some { c with corruptedToxicLifelink := true }
    else if l.contains "can be your commander" then
      some { c with canBeCommander := true }
    else if l.contains "without paying its mana cost" && l.contains "commander" then
      some { c with freeCastIfControlCommander := true }
    else if l.contains "enters tapped unless you control two or more basic" then
      some { c with entersTappedUnlessNBasics := some 2 }
    else if l.contains "enters tapped unless your opponents control eight" then
      some { c with entersTappedUnlessOppLands := some 8 }
    else if l.contains "enters tapped unless you control a" &&
        (l.contains " or a " || l.contains " or an ") then
      let after :=
        if l.contains "control an " then (l.splitOn "control an ").getLastD ""
        else (l.splitOn "control a ").getLastD ""
      let types := ((after.replace " or an " " or a ").splitOn " or a ").map fun p =>
        cap ((p.splitOn " ").headD "" |>.splitOn "." |>.headD "")
      some { c with entersTappedUnlessAnySubtype := types.toArray.filter (· != "") }
    else if l == s!"exile {low c.name}." then
      some c
    else if l.contains "choose mardu or jeskai" then
      some (pushTrig { c with asEntersChooseMarduOrJeskai := true }
        .yourUpkeep (frc (.createTokens .treasure (.fixed 1) false .goblin .you .ifNotMarduLifelinkHaste) line) line)
    else none
  match static with
  | some c => some c
  | none =>
    if l.contains ":" && !l.startsWith "whenever" && !l.startsWith "when " &&
        !l.startsWith "at the beginning" then
      match line.splitOn ":" with
      | cost :: rest =>
        let effectRaw := (String.intercalate ":" rest).trimAscii.copy
        let colors := manaTypesOf effectRaw
        let costLow := low cost
        if (low effectRaw).contains "add " && colors.size ≥ 2 && costLow.contains "{t}" &&
            ((low effectRaw).contains " or " || (low effectRaw).contains ",") then
          some { c with filterMana := some (costOf cost, colors) }
        else if (low effectRaw).startsWith "add " && colors.size ≥ 2 && costLow.contains "{t}" then
          some (pushAct c (Effect.addMana colors) line cost)
        else
          match effectText effectRaw with
          | some e => some (pushAct c e line cost)
          | none =>
            if (low effectRaw).contains "add " && colors.size == 2 && !costLow.contains "{t}" then
              none
            else none
      | _ => none
    else
      if l.contains "whenever this creature enters or attacks" ||
          (l.contains "enters or attacks" && l.contains "target opponent sacrifices") then
        some (addBoth c .enter .attack (frc (.sacrifice .archonCruelty) line (oppPlayer)) line (oppPlayer))
      else if l.contains "enters or attacks" && l.contains "historic" then
        some (addBoth c .enter .attack (frc (.revealLibrary .untilHistoric (.put .revealed) (.target .opponent)) line (oppPlayer)) line (oppPlayer))
      else if l.contains "enters or attacks" && l.contains "insect" then
        some (addBoth c .enter .attack (frc (.createTokens .treasure (.fixed 2) false .insect) line) line)
      else if l.contains "another nontoken creature you control dies" ||
          (l.contains "nontoken creature you control dies") then
        some (pushTrig c (.fra .nontokenCreatureYouControlDies) (frc (.put (.cause none) .atNextEndStep) line) line)
      else if l.contains "you become the monarch" && l.contains "enters" then
        some (pushTrig c .enter (frc (.grant .monarch .youIfCast) line) line)
      else if l.contains "you're the monarch" && l.contains "gingerbrute" then
        some (pushTrig c .eachUpkeep (frc (.createTokens .treasure (.fixed 1) false .gingerbrute .you .ifMonarch) line) line)
      else if l.contains "reveal cards from the top of your library until you reveal x creature" then
        some (pushTrig c .enter (frc (.revealLibrary .untilCreaturesPerOpponent (.put .revealed)) line) line)
      else if l.contains "zombie token you control with power 6" then
        some (pushTrig c (.fra .zombieTokenAttacks) (frc (.grant (.keywords Keyword.lifelink) (.cause none)) line) line)
      else if l.contains "you lose 1 life and amass zombies" then
        some (pushTrig c .yourUpkeep (frc (.amass (.fixed 1) "Zombie" false .youLose1Life) line) line)
      else if l.contains "you lose 1 life and create a 1/1 colorless phyrexian mite" then
        some (pushTrig c .yourUpkeep (frc (.createTokens .treasure (.fixed 1) false .mite .you .lose1Life) line) line)
      else if l.contains "whenever you gain life, you may pay" then
        some (pushTrig c .youGainLife (frc (.may (.loseLife .lastKnownPower) (.draw .lastKnownPower) .ifYouDo) line) line)
      else if l.contains "destroy all tapped creatures your opponents control" then
        some (pushTrig c .enter (frc (.destroy .oppTappedCreatures .gainLifeEach) line) line)
      else if l.contains "if you gained life this turn, create a 4/4" then
        some (pushTrig c .eachEndStep (frc (.createTokens .treasure (.fixed 1) false .angel .you .ifGainedLife) line) line)
      else if l.contains "whenever a land you control enters, add" then
        some (pushTrig c .landYouControlEnters (frc (.addMana #[.colorless, .colorless]) line) line)
      else if l.contains "whenever a land you control enters, draw a card" then
        some (pushTrig c .landYouControlEnters (frc (.revealLibrary .firstResolveUntilCreature (.put .revealed)) line) line)
      else if l.contains "at the beginning of each end step, each opponent loses life" then
        some (pushTrig c .eachEndStep (frc (.loseLife .lifeLostThisTurn .eachOpponent) line) line)
      else if l.contains "whenever you discard a card, you may exile" then
        some (pushTrig c (.fra .youDiscardOne) (frc (.exile (.cause none) .untilSourceLeaves) line) line)
      else if l.contains "whenever you create one or more creature tokens" then
        some (pushTrig c (.fra .youCreateCreatureTokens) (frc (.putCounters (.ofKind .story 1) .source) line) line)
      else if l.contains "when this artifact enters, create a 1/1 white spirit" then
        some (pushTrig c .enter (frc (.createTokens .spirit (.fixed 1) false) line) line)
      else if l.contains "when memnarch enters" || l.contains "create two 1/1 colorless myr" then
        some (pushTrig c .enter (frc (.createTokens .treasure (.fixed 2) false .myr) line) line)
      else if l.contains "draw a card for each artifact you control" then
        some (pushTrig c .attack (frc (.draw (.perControlled .artifact)) line) line)
      else if l.contains "whenever you cast a noncreature spell, create an x/x blue shark" then
        some (pushTrig c .youCastNoncreature (frc (.createTokens .treasure .spellManaValue false .shark) line) line)
      else if l.contains "whenever you cast a noncreature spell, draw a card" then
        some (pushTrig c .youCastNoncreature (Effect.draw 1) line)
      else if l.contains "when you cycle this card" then
        some (pushTrig c (.fra .youCycle) (frc (.createTokens .treasure .lastKnownPower false .shark) line) line)
      else if l.contains "combat on each opponent's turn" then
        some (pushTrig c (.fra .opponentBeginCombat) (frc (.cant (.attackJaces .opponentsCreatures)) line) line)
      else if l.contains "while you're the monarch, tap those creatures" then
        some (pushTrig c .combatDamageToYou (frc (.putCounters (.ofKind .stun 1) .combatDamagerIfMonarch) line) line)
      else if l.contains "one or more sphinxes you control attack" then
        some (pushTrig c (.fra .sphinxesAttack) (frc (.mill .lastKnownPower .eachPlayer .freeCastFromGraveyard) line) line)
      else if l.contains "whenever this land attacks, create a map" then
        some (pushTrig c .attack (frc (.createTokens .treasure (.fixed 1) false .map) line) line)
      else if l.contains "whenever this land attacks, scry" then
        some (pushTrig c .attack (Effect.scry 1) line)
      else if l.contains "as this artifact enters, you may have it become a copy" then
        some (pushTrig c .enter (frc (.becomeCopy .anyCreatureOnBattlefieldWithHaste) line) line)
      else if l.contains "choose target opponent. until that player's next turn" then
        some (pushSpell c (frc (.grant .teferisReproach (.player (.target .opponent))) line (oppPlayer "target opponent")))
      else if l.contains "when venser enters, choose one" ||
          (l.contains "choose one" && l.contains "copy target instant") then
        match effectText "Copy target instant or sorcery spell an opponent controls twice.",
            effectText "Create two tokens that are copies of target permanent an opponent controls." with
        | some a, some b =>
          some { pushTrig c .enter (frcEffectChoose line) line with
            fraTriggerModes := #[a, b] }
        | _, _ => none
      else
        match effectText line with
        | some e =>
          if l.startsWith "whenever" || l.startsWith "when " || l.startsWith "at the beginning" then
            none
          else some (pushSpell c e)
        | none => none
where
  frcEffectChoose (phrase : String) : Effect :=
    { resolution := .chooseModes [] (.fraTrigger 1), phrase }

end Mtg.Engine
