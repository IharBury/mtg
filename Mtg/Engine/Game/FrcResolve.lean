import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture Commander resolutions

`applyFrc` performs `Resolution.frc`. Choices that already exist
(library search, random order) stay on those pendings.
-/

namespace Mtg.Engine
namespace Game

private def spellX (g : Game) : Nat :=
  let chosen := fun (id? : Option ObjectId) => id?.bind g.findObject? |>.bind (·.chosenX)
  (chosen g.resolvingSpell).getD ((chosen g.resolvingAbility).getD 0)

private def frcCause? (g : Game) : Option GameObject :=
  g.resolvingAbilityObject?.bind fun ab =>
    ab.fraCauseId.bind fun id => g.findObject? (g.followMoved id)

private def knownN (g : Game) : Nat :=
  ((g.resolvingAbilityObject?.bind (·.lastKnownPower)).getD 0).toNat

private def srcObj? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind fun id => g.findObject? (g.followMoved id)

private def exileId (g : Game) (id : ObjectId) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := o.name
    let (g, _) := g.move id .exile none
    g.logMsg s!"{name} is exiled"

private def handDiscard (g : Game) (p : PlayerId) : Game :=
  match (g.player p).hand.back? with
  | none => g.logMsg s!"{(g.player p).name} has no card to discard"
  | some id =>
    let name := (g.object! id).name
    let (g, _) := g.move id (.graveyard p) none
    g.logMsg s!"{(g.player p).name} discards {name}"

private def destroyIds (g : Game) (ids : Array ObjectId) (pred : GameObject → Bool := fun _ => true) : Game :=
  ids.foldl (fun g id =>
    match g.findObject? id with
    | some o => if o.isOnBattlefield && pred o then g.destroyPermanent o else g
    | none => g) g

private def creatureTokenOf (name : String) (subtypes : Array String) (p t : Int)
    (color : Option Color := none) (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) (toxic : Nat := 0) (cantBlock : Bool := false) : CardDef :=
  let keywordRule : CardKeywordRule :=
    if toxic != 0 then .toxic toxic cantBlock
    else if cantBlock then .cantBlock
    else .none
  { creatureToken name subtypes p t color keywords types with keywordRule }

private def frcPrinted (k : TokenKind) (x : Nat) : CardDef :=
  match k with
  | .shark =>
    creatureTokenOf "Shark" #["Shark"] (Int.ofNat x) (Int.ofNat x) (some .blue) Keyword.flying
  | _ => tokenPrinted k

private def makeFrc (g : Game) (p : PlayerId) (k : TokenKind) (n : Nat := 1) (x : Nat := 0) : Game :=
  if n == 0 || (g.player p).lost then { g with recentTokenIds := #[] }
  else
    Id.run do
      let mut g := g
      let mut ids : Array ObjectId := #[]
      let printed := frcPrinted k x
      for _ in [0:n] do
        let (g', obj) := g.createToken p printed (batch := true)
        g := g'
        ids := ids.push obj.id
      g := { g with recentTokenIds := ids }
      return if printed.isCreature then g.noteCreatureTokenEvent p else g

private def revealUntil (g : Game) (p : PlayerId) (pred : CardDef → Bool) (limit : Nat) :
    Game × Array ObjectId × Array ObjectId :=
  Id.run do
    let mut g := g
    let mut hits : Array ObjectId := #[]
    let mut rest : Array ObjectId := #[]
    let mut fuel := (g.player p).library.size
    while hits.size < limit && fuel > 0 do
      fuel := fuel - 1
      let lib := (g.player p).library
      if lib.isEmpty then
        fuel := 0
      else
        let top := lib.back!
        let card := g.object! top
        let (g', newId) := g.move top .exile none
        g := g'.logMsg s!"{(g.player p).name} reveals {card.name}"
        if pred card.printed then hits := hits.push newId
        else rest := rest.push newId
    return (g, hits, rest)

private def putHits (g : Game) (p : PlayerId) (hits : Array ObjectId) (haste := false) : Game :=
  hits.foldl (fun g id =>
    match g.findObject? id with
    | none => g
    | some _ =>
      let (g, newId) := g.putOntoBattlefield id p (summoningSick := !haste)
      g.afterPermanentEnters (g.object! newId)) g

private def restBottom (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool) : Game :=
  if rest.isEmpty then if shuffle then g.requestShuffle p else g
  else if shuffle then
    let g := g.moveIdsInOrder rest (.library p)
    g.requestShuffle p
  else
    g.requestOrderInto rest (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"

private def historicCard (c : CardDef) : Bool :=
  c.isPermanentCard && (c.isArtifact || c.hasSupertype .legendary || c.hasSubtype "Saga")

private def creatureOrWalker (c : CardDef) : Bool :=
  c.isCreature || c.isPlaneswalker

private def basicOf (kinds : Array String) (c : CardDef) : Bool :=
  isBasicLandCard c && kinds.any c.hasSubtype

def applyFrc? (g : Game) (controller : PlayerId) (_effect : Effect) (r : Resolution)
    (targets : Array Target) (sourceId : Option ObjectId) : Option Game :=
  let pl := g.player controller
  match r with
  | .putOnLibrary (.topAfterDraw drawN putN) .cardFromHand =>
    let g := g.draw controller drawN
    let hand := (g.player controller).hand
    let n := min putN hand.size
    let back := hand.extract (hand.size - n) hand.size
    let g := back.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        if o.zone == .hand controller then
          let (g, newId) := g.move id (.library controller) none
          g.putIdsOnTop controller #[newId]
        else g
      | none => g) g
    some (g.logMsg s!"{pl.name} puts {n} card(s) on top of their library")
  | .exile .target .forLater .despark =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) => g.exileId id
      | some (Target.card id) => g.exileId id
      | _ => g.logMsg "Despark has no legal target"
  | .exile .target .forLater .controllerMaySearchBasic =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          let owner := o.controller.getD o.owner
          let g := g.exileId id
          g.offerMaySearchBasics owner
        | none => g
      | _ => g
  | .exile .target .forLater .controllerGainsLifePower =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          let owner := o.controller.getD o.owner
          let pw := (g.snapshotPower o).toNat
          let g := g.exileId id
          g.gainLife owner pw
        | none => g
      | _ => g
  | .destroy .target .controllerCreatesHuman =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          let owner := o.controller.getD o.owner
          let g := g.destroyPermanent o
          g.makeFrc owner .human
        | none => g
      | _ => g
  | .createTokens .citizen .chosenX false _ .teamIndestructible =>
    let g := g.makeFrc controller .citizen (g.spellX)
    some (g.grantUntilEotToControlledCreatures controller Keyword.indestructible "indestructible")
  | .createTokens .soldier11white .chosenX false _ .destroyOthersIfXAtLeast5 =>
    let x := g.spellX
    let g := g.createKindTokens controller .soldier11white x
    some <|
      if x >= 5 then
        g.destroyIds (g.battlefield.filter (·.isCreature) |>.map (·.id))
          (fun o => !g.recentTokenIds.contains o.id)
      else g
  | .createTokens .mite .chosenX false _ .gainXLifeAndDestroyOthersIf5 =>
    let x := g.spellX
    let g := g.gainLife controller x
    let g := g.makeFrc controller .mite x
    some <|
      if x >= 5 then
        g.destroyIds (g.battlefield.filter (·.isCreature) |>.map (·.id))
          (fun o => !g.recentTokenIds.contains o.id)
      else g
  | .discard .drawAndDiscardXCreateSpiritPerType =>
    let x := g.spellX
    let g := g.draw controller x
    let hand := (g.player controller).hand
    let n := min x hand.size
    let ids := hand.extract (hand.size - n) hand.size
    let discarded := ids.filterMap g.findObject?
    let g := ids.foldl (fun g id => (g.move id (.graveyard controller) none).1) g
    let types := discarded.foldl (fun acc o =>
      o.printed.types.foldl (fun acc t =>
        let name := CardType.englishName t
        if acc.contains name then acc else acc.push name) acc) (#[] : Array String)
    some (g.createKindTokens controller .spirit types.size)
  | .exile .allCreatures .forLater .incubateCount =>
    let ids := (g.battlefield.filter (·.isCreature)).map (·.id)
    let g := ids.foldl (fun g id => g.exileId id) g
    let g := g.makeFrc controller .incubator
    some <|
      match (g.recentTokenIds.back?).bind g.findObject? with
      | some tok =>
        g.setObject { tok with status := { tok.status with plusOnePlusOne := ids.size } }
          |>.logMsg s!"Incubator enters with {ids.size} +1/+1 counters"
      | none => g
  | .exile .creaturesYouControl .forLater .revealCreaturesToBattlefield =>
    let yours := (g.permanentsOf controller).filter (·.isCreature) |>.map (·.id)
    let g := yours.foldl (fun g id => g.exileId id) g
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) yours.size
    let g := g.putHits controller hits
    some (g.restBottom controller rest true)
  | .exile .creaturesYouControl .forLater .revealCreaturesAtEndStep =>
    let yours := (g.permanentsOf controller).filter (·.isCreature) |>.map (·.id)
    let g := yours.foldl (fun g id => g.exileId id) g
    some ({ g with delayedEndStep := g.delayedEndStep.push (.syntheticDestiny controller yours.size) }
      |>.logMsg "Those creatures return as revealed cards at the next end step")
  | .searchLibrary (.put (.basicSubtypesUntapAt kinds untapAt) _ _) =>
    let g := if untapAt == 0 then g else { g with afterLibrarySearch := .untapSearchedIfLands untapAt }
    some (g.beginLibrarySearch controller (basicOf kinds) "a basic land card" (.battlefield true))
  | .putOnLibrary .bottomRevealCreature .target =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some o =>
          let owner := o.controller.getD o.owner
          let g := g.moveIdsInOrder #[id] (.library owner)
          let (g, hits, rest) := g.revealUntil owner (·.isCreature) 1
          let g := g.putHits owner hits
          g.restBottom owner rest false
        | none => g
      | _ => g
  | .grant (.animateLand p t flying first) .source =>
    some <|
      match g.srcObj? sourceId with
      | none => g
      | some o =>
        let kws :=
          Keywords.merge (if flying then Keyword.flying else Keywords.none)
            (if first then Keywords.none else Keywords.none)
        let g := g.setUntilEotForm o (Int.ofNat p, Int.ofNat t) kws
          s!"{o.name} becomes a {p}/{t} until end of turn"
          (additionalCreature := true)
        if first then g.mapObjectStatus (g.object! o.id) (fun s => { s with firstStrikeOnYourTurn := true })
        else g
  | .createTokens .map (.fixed 1) false _ _ =>
    some (g.makeFrc controller .map)
  | .sacrifice .archonCruelty _ =>
    some <|
      match targets[0]? with
      | some (Target.player pid) =>
        let victim :=
          ((g.permanentsOf pid).find? (·.isCreature)).orElse
            (fun _ => (g.permanentsOf pid).find? (·.printed.isPlaneswalker))
        let g :=
          match victim with
          | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {o.name}"
          | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
        let g := g.handDiscard pid
        let g := g.loseLife pid 3
        let g := g.draw controller 1
        g.gainLife controller 3
      | _ => g
  | .put (.cause none) .atNextEndStep _ =>
    some <|
      match g.frcCause? with
      | some o =>
        if o.zone == .graveyard o.owner then
          { g with delayedEndStep := g.delayedEndStep.push (.returnFromGraveyard o.id controller) }
            |>.logMsg s!"{o.name} returns at the beginning of the next end step"
        else g
      | none => g
  | .revealLibrary .untilCreaturesPerOpponent _ _ =>
    let n := (g.livingOpponents controller).size
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) n
    let g := g.putHits controller hits
    let g := hits.foldl (fun g id =>
      match g.followMoved id |> g.findObject? with
      | some o => g.setObject { o with status := { o.status with goaded := true } }
      | none => g) g
    let opps := g.livingOpponents controller
    let g := Id.run do
      let mut g := g
      let mut i := 0
      for id in hits do
        match opps[i]?, g.followMoved id |> g.findObject? with
        | some opp, some o =>
          g := g.changeControl o opp.id
          i := i + 1
        | _, _ => pure ()
      return g
    some (g.restBottom controller rest true)
  | .revealLibrary .untilHistoric _ _ =>
    some <|
      match targets[0]? with
      | some (Target.player pid) =>
        let (g, hits, rest) := g.revealUntil pid historicCard 1
        let g :=
          match hits[0]? with
          | some id =>
            match g.findObject? id with
            | some card =>
              let mv := card.printed.manaValue
              let g := (g.putHits controller #[id])
              g.loseLife controller mv
            | none => g
          | none => g.logMsg s!"{(g.player pid).name} reveals no historic permanent"
        g.restBottom pid rest false
      | _ => g
  | .revealLibrary .firstResolveUntilCreature _ _ =>
    let g := g.draw controller
    some <|
      match g.srcObj? sourceId with
      | some src =>
        if src.status.optionalOnceUsed then g
        else
          let g := g.mapObjectStatus src (fun s => { s with optionalOnceUsed := true })
          let (g, hits, rest) := g.revealUntil controller (·.isCreature) 1
          let g := g.putHits controller hits
          g.restBottom controller rest false
      | none => g
  | .may (.loseLife .lastKnownPower _) (.draw .lastKnownPower _) .ifYouDo =>
    let n := g.knownN
    some <|
      if (g.player controller).life > Int.ofNat n && n > 0 then
        (g.loseLife controller n).draw controller n
      else g.logMsg s!"{pl.name} declines to pay {n} life"
  | .loseLife (.fixed 1) .eachOpponentAndYouGain1 =>
    let g := g.forEachOpponent controller (fun g pid => g.loseLife pid 1)
    some (g.gainLife controller 1)
  | .destroy .oppTappedCreatures .gainLifeEach =>
    let ids := g.battlefield.filter (fun o =>
      o.isCreature && o.status.tapped &&
        match o.controller with
        | some c => c != controller && !(g.player c).lost
        | none => false) |>.map (·.id)
    let g := g.destroyIds ids
    some (g.gainLife controller ids.size)
  | .createTokens .angel (.fixed 1) false _ .ifGainedLife =>
    some (if (g.player controller).lifeGainedThisTurn > 0 then g.makeFrc controller .angel else g)
  | .destroy .creaturesPowerAtLeast4 _ =>
    some (g.destroyIds (g.battlefield.filter (fun o => o.isCreature && g.snapshotPower o >= 4) |>.map (·.id)))
  | .grant .emblemCreaturesGetTwoTwoFlying .youIfCast =>
    let (g, emb) := g.allocObject {
        name := "Elspeth emblem"
        types := #[.enchantment]
        staticRule := .grantTeamPlusTwoFlying
      } controller .command (some controller)
    some (g.logMsg s!"{pl.name} gets an emblem ({emb.name})")
  | .putOnLibrary .bottomAfterDrawTwo .cardFromHand =>
    let g := g.draw controller 2
    some (handDiscardToBottom g)
  | .exile (.target .another) .forLater .revealUntilCreatureOrPlaneswalker =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        let g := g.exileId id
        let (g, hits, rest) := g.revealUntil controller creatureOrWalker 1
        let g := g.putHits controller hits
        g.restBottom controller rest false
      | _ => g
  | .cant (.attackJaces _) =>
    some <|
      if g.activePlayer == controller then g
      else
        g.modifyPlayer g.activePlayer (fun q => { q with cantAttackJaces := true })
          |>.logMsg s!"{(g.player g.activePlayer).name}'s creatures can't attack Jaces this turn"
  | .grant .monarch .youIfCast =>
    let g := g.players.foldl (fun g q =>
      if q.isMonarch && q.id != controller then
        g.setPlayer { q with isMonarch := false }
      else g) g
    some (g.modifyPlayer controller (fun q => { q with isMonarch := true })
      |>.logMsg s!"{pl.name} becomes the monarch")
  | .createTokens .gingerbrute (.fixed 1) false _ .ifMonarch =>
    some (if (g.player controller).isMonarch then g.makeFrc controller .gingerbrute else g)
  | .putCounters (.ofKind .stun _) .combatDamagerIfMonarch =>
    some <|
      if !(g.player controller).isMonarch then g
      else
        match g.frcCause? with
        | some o =>
          if o.isOnBattlefield && o.isCreature then
            let g := g.becomeTapped o
            let n := g.countersYouPut (g.object! o.id) 1 (putter := some controller)
            g.mapObjectStatus (g.object! o.id) (fun s => { s with stun := s.stun + n })
              |>.logMsg s!"{o.name} gets a stun counter"
          else g
        | none => g
  | .grant .teferisReproach (.player (.target .opponent)) =>
    some <|
      match targets[0]? with
      | some (Target.player pid) =>
        let g := g.modifyPlayer pid (fun q =>
          { q with protectionFromEverything := true, lifeCantChange := true })
        let g := g.logMsg s!"{(g.player pid).name} has protection from everything and their life total can't change"
        let ids := (g.permanentsOf pid).filter (fun o => !o.printed.isLand) |>.map (·.id)
        let g := ids.foldl (fun g id =>
          match g.findObject? id with
          | some o => if o.isOnBattlefield then g.phaseOut o else g
          | none => g) g
        match g.resolvingSpell.bind g.findObject? with
        | some spell =>
          g.setObject { spell with exileInstantSorceryInstead := true }
            |>.logMsg s!"{spell.name} will be exiled"
        | none => g
      | _ => g
  | .mill .lastKnownPower .eachPlayer .freeCastFromGraveyard =>
    let n := g.knownN
    some <|
      g.livingPlayers.foldl (fun g q =>
        Id.run do
          let mut g := g
          for _ in [0:n] do
            let lib := (g.player q.id).library
            if lib.isEmpty then
              g := g.logMsg s!"{q.name} mills nothing (empty library)"
            else
              let top := lib.back!
              let name := (g.object! top).name
              let (g', newId) := g.move top (.graveyard q.id) none
              g := g'.logMsg s!"{q.name} mills {name}"
              match g.findObject? newId with
              | some card =>
                g := g.setObject { card with status := { card.status with freeCastFromGraveyard := true } }
              | none => pure ()
          return g) g
  | .becomeCopy .targetSpellTwice =>
    some <|
      match targets[0]? with
      | some (Target.card id) =>
        match g.findObject? id with
        | some spell => (g.copyStackSpell spell controller).copyStackSpell spell controller
        | none => g
      | _ => g
  | .becomeCopy .targetPermanentTwoTokensHasteSacrifice =>
    some <|
      match targets[0]? with
      | some (Target.permanent id) =>
        match g.findObject? id with
        | some src =>
          Id.run do
            let mut g := g
            for _ in [0:2] do
              let (g', tok) := g.copyBattlefieldPermanent src controller
              g := g'
              g := g.mapObjectStatus tok (·.grantUntilEot Keyword.haste)
              g := { g with delayedEndStep := g.delayedEndStep.push (.sacrificePermanent tok.id) }
            return g.logMsg "The token copies gain haste and are sacrificed at the next end step"
        | none => g
      | _ => g
  | .createTokens .goblin (.fixed 1) false _ .ifNotMarduLifelinkHaste =>
    some <|
      match g.srcObj? sourceId with
      | some src =>
        if src.status.windcragMardu then g
        else
          let g := g.makeFrc controller .goblin
          match (g.permanentsOf controller).reverse.find? (fun o => o.name == "Goblin" && o.printed.isToken) with
          | some tok =>
            g.mapObjectStatus tok (fun s =>
              s.grantUntilEot (Keywords.merge Keyword.lifelink Keyword.haste))
              |>.logMsg s!"{tok.name} gains lifelink and haste until end of turn"
          | none => g
      | none => g
  | .putCounters (.ofKind .story _) .source =>
    some <|
      match g.srcObj? sourceId with
      | some o =>
        g.mapObjectStatus o (fun s => { s with story := s.story + 1 })
          |>.logMsg s!"{o.name} gets a story counter"
      | none => g
  | .exile (.cause none) .untilSourceLeaves _ =>
    some <|
      match g.frcCause? with
      | some card =>
        if card.zone == .graveyard card.owner then
          match g.srcObj? sourceId with
          | some src => g.exileSearchedLinked controller card.id (some src.id)
          | none => g.exileId card.id
        else g
      | none => g
  | .discard .drawOneDiscardOne =>
    let g := g.draw controller
    some (g.handDiscard controller)
  | .createTokens .rogue (.fixed 1) false _ .currencyReturn =>
    some <|
      match g.srcObj? sourceId with
      | none => g
      | some src =>
        match src.linkedExile.find? (fun id => (g.findObject? id).any (·.zone == .exile)) with
        | none => g.logMsg s!"{src.name} has no exiled card"
        | some id =>
          match g.findObject? id with
          | none => g
          | some card =>
            let land := card.printed.isLand
            let (g, _) := g.move id (.graveyard card.owner) none
            let g := g.setObject { (g.object! src.id) with
              linkedExile := src.linkedExile.filter (· != id) }
            if land then g.makeFrc controller .treasure else g.makeFrc controller .rogue
  | .becomeCopy .anyCreatureOnBattlefieldWithHaste =>
    some <|
      match g.srcObj? sourceId with
      | none => g
      | some art =>
        match g.battlefield.find? (fun o => o.isCreature && o.id != art.id) with
        | none => g.logMsg s!"{art.name} does not become a copy"
        | some src =>
          let g := g.becomeCopyOf art src (untilEot := true)
          g.mapObjectStatus (g.object! art.id) (·.grantUntilEot Keyword.haste)
            |>.logMsg s!"{art.name} has haste until end of turn"
  | .loseLife .lifeLostThisTurn .eachOpponent =>
    some (g.forEachOpponent controller fun g pid =>
      g.loseLife pid (g.player pid).lifeLostThisTurn)
  | .amass (.fixed 1) "Zombie" false .youLose1Life =>
    some ((g.loseLife controller 1).amassZombies controller 1)
  | .createTokens .myr (.fixed n) false _ _ =>
    some (g.makeFrc controller .myr n.toNat)
  | .createTokens .shark .spellManaValue false _ _ =>
    let x :=
      match g.frcCause? with
      | some spell => g.objectManaValue spell
      | none => 0
    some (g.makeFrc controller .shark 1 x)
  | .createTokens .shark .lastKnownPower false _ _ =>
    some (g.makeFrc controller .shark 1 g.knownN)
  | .createTokens .mite (.fixed 1) false _ .lose1Life =>
    some ((g.loseLife controller 1).makeFrc controller .mite)
  | .createTokens .insect (.fixed n) false _ _ =>
    some (g.makeFrc controller .insect n.toNat)
  | .revealLibrary (.top 5) (.returnToHand .factOrFiction _) _ =>
    let lib := (g.player controller).library
    let n := min 5 lib.size
    let ids := (List.range n).foldl (fun (acc : Game × Array ObjectId) _ =>
      let (g, acc) := acc
      let top := (g.player controller).library.back!
      let (g, newId) := g.move top .exile none
      (g, acc.push newId)) (g, #[])
    let (g, shown) := ids
    let handN := (shown.size + 1) / 2
    let toHand := shown.extract 0 handN
    let toGy := shown.extract handN shown.size
    let g := toHand.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        let (g, _) := g.move id (.hand controller) none
        g.logMsg s!"{o.name} goes to {pl.name}'s hand"
      | none => g) g
    some (toGy.foldl (fun g id =>
      match g.findObject? id with
      | some o =>
        let (g, _) := g.move id (.graveyard controller) none
        g.logMsg s!"{o.name} goes to {pl.name}'s graveyard"
      | none => g) g)
  | .createTokens .kobold (.fixed 1) false _ _ =>
    some (g.makeFrc controller .kobold)
  | .createTokens .warrior .chosenX false _ _ =>
    some (g.makeFrc controller .warrior (g.spellX))
  | .createTokens .citizen .chosenX false _ .none =>
    some (g.makeFrc controller .citizen (g.spellX))
  | .grant .explored .source =>
    let lib := (g.player controller).library
    some <|
      if lib.isEmpty then g.logMsg s!"{pl.name} explores (empty library)"
      else
        let top := lib.back!
        let card := g.object! top
        if card.printed.isLand then
          let (g, _) := g.move top (.hand controller) none
          g.logMsg s!"{pl.name} explores and puts {card.name} into their hand"
        else
          let g := g.putIdsOnTop controller #[top]
          match g.srcObj? sourceId with
          | some o =>
            if o.isCreature then
              g.mapObjectStatus o (fun s => s.addPlusOnePlusOne 1)
                |>.logMsg s!"{pl.name} explores; {o.name} gets a +1/+1 counter"
            else g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
          | none => g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
  | .grant .transformedIncubator .source =>
    some <|
      match g.srcObj? sourceId with
      | some o =>
        let counters := o.status.plusOnePlusOne
        g.setObject { o with printed :=
          { creatureTokenOf "Phyrexian" #["Phyrexian"] 0 0 (types := #[.artifact, .creature]) with
            name := "Phyrexian" } }
          |>.logMsg s!"{o.name} transforms into a 0/0 Phyrexian with {counters} +1/+1 counters"
      | none => g
  | .grant .faceUp .source =>
    some <|
      match g.srcObj? sourceId with
      | some o =>
        g.setObject { o with status := { o.status with faceDown := false } }
          |>.logMsg s!"{o.name} is turned face up"
      | none => g
  | .cant (.beBlockedExceptByHaste .source) =>
    some <|
      match g.srcObj? sourceId with
      | some o =>
        g.mapObjectStatus o (fun s => { s with cantBeBlockedExceptByHasteUntilEot := true })
          |>.logMsg s!"{o.name} can't be blocked this turn except by creatures with haste"
      | none => g
  | _ => none
where
  handDiscardToBottom (g : Game) : Game :=
    match (g.player controller).hand.back? with
    | none => g
    | some id =>
      let name := (g.object! id).name
      let (g, newId) := g.move id (.library controller) none
      let pl := g.player controller
      let lib := pl.library.filter (· != newId)
      g.setPlayer { pl with library := #[newId] ++ lib }
        |>.logMsg s!"{(g.player controller).name} puts {name} on the bottom of their library"

/-- Reveal creature cards exiled by Synthetic Destiny at the end step. -/
def applyDelayedSynthetic (g : Game) : Game :=
  let synth := g.delayedSynthetic
  let g := { g with delayedEndStep := g.delayedEndStep.filter fun
    | .syntheticDestiny .. => false
    | _ => true }
  synth.foldl (fun g (who, n) =>
    let (g, hits, rest) := g.revealUntil who (·.isCreature) n
    let g := g.putHits who hits
    g.restBottom who rest true) g

end Game
end Mtg.Engine
