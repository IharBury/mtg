import Mtg.Engine.Game.FraHelpers

/-!
# Reality Fracture Commander resolutions

`applyFrc` performs `Resolution.frc`. Choices that already exist
(library search, random order) stay on those pendings.
-/

namespace Mtg.Engine
namespace Game

private def spellX (g : Game) : Nat :=
  let chosen := fun (id? : Option ObjectId) => id?.bind g.chosenXOf?
  (chosen g.resolvingSpell).getD ((chosen g.resolvingAbility).getD 0)

private def frcCause? (g : Game) : Option GameObject :=
  g.resolvingAbilityObject?.bind fun ab =>
    ab.fraCauseId.bind fun id => g.findObject? (g.followMoved id)

private def knownN (g : Game) (lastKnownPower : Option Int := none) : Nat :=
  ((lastKnownPower.orElse (fun _ => g.resolvingAbility.bind g.lastKnownPowerOf?)).getD 0).toNat

private def srcObj? (g : Game) (sourceId : Option ObjectId) : Option GameObject :=
  sourceId.bind fun id => g.findObject? (g.followMoved id)

private def exileId (g : Game) (id : ObjectId)
    (cause : Option EventCause := none) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := g.name o
    let (g, _) := g.move id .exile none (cause := cause)
    g.logMsg s!"{name} is exiled"

private def handDiscard (g : Game) (p : PlayerId) : Game :=
  match (g.player p).hand.back? with
  | none => g.logMsg s!"{(g.player p).name} has no card to discard"
  | some id =>
    let name := (g.object! id).name
    let (g, _) := g.move id (.graveyard p) none
    g.logMsg s!"{(g.player p).name} discards {name}"

private def destroyIds (g : Game) (ids : Array ObjectId) (pred : GameObject → Bool := fun _ => true) : Game :=
  g.withBatch none fun g =>
    ids.foldl (fun g id =>
      match g.findObject? id with
      | some o => if o.isOnBattlefield && pred o then g.destroyPermanent o else g
      | none => g) g

private def creatureTokenOf (name : String) (subtypes : Array CardSubtype) (p t : Int)
    (color : Option Color := none) (keywords : Keywords := Keywords.none)
    (types : Array CardType := #[.creature]) (toxic : Nat := 0) (cantBlock : Bool := false) : CardDef :=
  { creatureToken name subtypes p t color keywords types with toxic, cantBlock }

private def frcPrinted (k : FrcToken) (x : Nat) : CardDef :=
  match k with
  | .citizen =>
    { creatureTokenOf "Citizen" #[.citizen] 1 1 with
      colorIndicator := some (ColorSet.ofList [.green, .white]) }
  | .warrior => creatureTokenOf "Warrior" #[.warrior] 1 1 (some .white)
  | .insect => creatureTokenOf "Insect" #[.insect] 2 1 (some .white) Keyword.flying
  | .myr =>
    creatureTokenOf "Myr" #[.myr] 1 1 (types := #[.artifact, .creature])
  | .kobold =>
    { creatureTokenOf "Kobolds of Kher Keep" #[.kobold] 0 1 (some .red) with name := "Kobolds of Kher Keep" }
  | .mite =>
    creatureTokenOf "Phyrexian Mite" #[.phyrexian, .mite] 1 1
      (types := #[.artifact, .creature]) (toxic := 1) (cantBlock := true)
  | .shark =>
    creatureTokenOf "Shark" #[.shark] (Int.ofNat x) (Int.ofNat x) (some .blue) Keyword.flying
  | .gingerbrute =>
    { creatureTokenOf "Gingerbrute" #[.food, .golem] 1 1
        (keywords := Keyword.haste) (types := #[.artifact, .creature]) with
      activatedAbilities := #[
        { effect := { resolution := .frc .gingerDash, phrase := "This token can't be blocked this turn except by creatures with haste." }
          cost := { mana := ManaCost.ofGeneric 1 } },
        { effect := Effect.gainLife 3
          cost := { mana := ManaCost.ofGeneric 2, tap := true, sacrificeSource := true } } ] }
  | .angel => creatureTokenOf "Angel" #[.angel] 4 4 (some .white) Keyword.flying
  | .human => creatureTokenOf "Human" #[.human] 1 1 (some .white)
  | .goblin => creatureTokenOf "Goblin" #[.goblin] 1 1 (some .red)
  | .map => {
      name := "Map"
      types := #[.artifact]
      isToken := true
      activatedAbilities := #[
        { effect := { resolution := .frc .explore, phrase := "You explore." }
          cost := { mana := ManaCost.ofGeneric 1, tap := true, sacrificeSource := true } } ] }
  | .treasure => treasureToken
  | .rogue => creatureTokenOf "Rogue" #[.rogue] 2 2 (some .black)
  | .incubator => {
      name := "Incubator"
      types := #[.artifact]
      subtypes := #["Incubator"]
      isToken := true
      otherFace := some {
        creatureTokenOf "Phyrexian" #[.phyrexian] 0 0 (types := #[.artifact, .creature]) with
        name := "Phyrexian" }
      activatedAbilities := #[
        { effect := { resolution := .frc .transformIncubator, phrase := "Transform this token." }
          cost := { mana := ManaCost.ofGeneric 2 } } ] }

private def makeFrc (g : Game) (p : PlayerId) (k : FrcToken) (n : Nat := 1) (x : Nat := 0)
    (extraCounters : CounterBag := #[]) (cause : Option EventCause := none) : Game :=
  if n == 0 || (g.player p).lost then g.change (.recentTokenIds #[])
  else
    let batchCause := cause.orElse (fun _ => g.resolvingBatchCause p none)
    g.withBatch batchCause fun g =>
      Id.run do
        let mut g := g
        let mut ids : Array ObjectId := #[]
        let printed := frcPrinted k x
        for _ in [0:n] do
          let (g', obj) := g.createToken p printed
            (extraCounters := extraCounters) (cause := cause)
          g := g'
          ids := ids.push obj.id
        return g.change (.recentTokenIds ids)

private def revealUntil (g : Game) (p : PlayerId) (pred : CardDef → Bool) (limit : Nat)
    (cause : Option EventCause := none) :
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
        let (g', newId) := g.move top .exile none (cause := cause)
        g := g'.logMsg s!"{(g.player p).name} reveals {card.name}"
        if pred card.printed then hits := hits.push newId
        else rest := rest.push newId
    return (g, hits, rest)

private def putHits (g : Game) (p : PlayerId) (hits : Array ObjectId) (haste := false)
    (cause : Option EventCause := none) : Game :=
  g.withBatch cause fun g =>
    hits.foldl (fun g id =>
      match g.findObject? id with
      | none => g
      | some _ =>
        let (g, newId) := g.putOntoBattlefield id p (summoningSick := !haste) (cause := cause)
        g.afterPermanentEnters (g.object! newId)) g

private def restBottom (g : Game) (p : PlayerId) (rest : Array ObjectId) (shuffle : Bool)
    (cause : Option EventCause := none) : Game :=
  if rest.isEmpty then if shuffle then g.requestShuffle p else g
  else if shuffle then
    let g := g.moveIdsInOrder rest (.library p) (cause := cause)
    g.requestShuffle p
  else
    g.requestOrderInto rest (.library p)
      s!"{(g.player p).name} puts the rest on the bottom of their library in a random order"
      (cause := cause)

private def historicCard (c : CardDef) : Bool :=
  c.isPermanentCard && (c.isArtifact || c.hasSupertype .legendary || c.hasSubtype .saga)

private def creatureOrWalker (c : CardDef) : Bool :=
  c.isCreature || c.isPlaneswalker

private def basicOf (kinds : Array CardSubtype) (c : CardDef) : Bool :=
  isBasicLandCard c && kinds.any fun k => c.hasSubtype k

def applyFrc (g : Game) (controller : PlayerId) (_effect : Effect) (e : FrcEffect)
    (targets : Array Target) (sourceId : Option ObjectId)
    (lastKnownPower : Option Int := none) : Game :=
  let pl := g.player controller
  let nKnown := g.knownN lastKnownPower
  match e with
  | .drawPutOnTop drawN putN =>
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
    g.logMsg s!"{pl.name} puts {n} card(s) on top of their library"
  | .exileTarget =>
    match targets[0]? with
    | some (Target.permanent id) => g.exileId id
    | some (Target.card id) => g.exileId id
    | _ => g.logMsg "Despark has no legal target"
  | .pathToExile =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let g := g.exileId id
        g.offerMaySearchBasics owner
      | none => g
    | _ => g
  | .swords =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let pw := (g.snapshotPower o).toNat
        let g := g.exileId id
        g.gainLife owner pw
      | none => g
    | _ => g
  | .stroke =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let g := g.destroyPermanent o
        g.makeFrc owner .human
      | none => g
    | _ => g
  | .grandCrescendo =>
    let g := g.makeFrc controller .citizen (g.spellX)
    g.grantUntilEotToControlledCreatures controller Keyword.indestructible "indestructible"
  | .martialCoup =>
    let x := g.spellX
    let src := g.resolvingSpell
    let g := g.createKindTokens controller .soldier11white x
    let _ := src
    if x >= 5 then
      g.destroyIds (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .whiteSuns =>
    let x := g.spellX
    let src := g.resolvingSpell
    let g := g.gainLife controller x
    let g := g.makeFrc controller .mite x
    let _ := src
    if x >= 5 then
      g.destroyIds (g.battlefield.filter (g.isCreature ·) |>.map (·.id))
        (fun o => !g.recentTokenIds.contains o.id)
    else g
  | .occult =>
    let x := g.spellX
    let g := g.draw controller x
    let hand := (g.player controller).hand
    let n := min x hand.size
    let ids := hand.extract (hand.size - n) hand.size
    let discarded := ids.filterMap g.findObject?
    let g := g.withBatch none fun g =>
      ids.foldl (fun g id => (g.move id (.graveyard controller) none).1) g
    let types := discarded.foldl (fun acc o =>
      o.printed.types.foldl (fun acc t =>
        let name := CardType.englishName t
        if acc.contains name then acc else acc.push name) acc) (#[] : Array String)
    g.createKindTokens controller .spirit types.size
  | .sunfall =>
    let ids := (g.battlefield.filter (g.isCreature ·)).map (·.id)
    let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
    let g := g.withBatch (some exileCause) fun g =>
      ids.foldl (fun g id => g.exileId id (cause := some exileCause)) g
    let (g, incubateCause) := g.allocDelayedCause (some controller) sourceId
    let extra : CounterBag :=
      if ids.size > 0 then #[(.plusOnePlusOne, ids.size)] else #[]
    g.withBatch (some incubateCause) fun g =>
      let g := g.makeFrc controller .incubator 1 0
        (extraCounters := extra) (cause := some incubateCause)
      match (g.recentTokenIds.back?).bind g.findObject? with
      | some tok =>
        g.addPlusOnePlusOneTo tok ids.size (entersWith := true)
          (byPlayer := some controller) (cause := some incubateCause)
      | none => g
  | .massPolymorph =>
    let yours := (g.permanentsOf controller).filter (g.isCreature ·) |>.map (·.id)
    let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
    let g := g.withBatch (some exileCause) fun g =>
      yours.foldl (fun g id => g.exileId id (cause := some exileCause)) g
    let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) yours.size (cause := some revealCause)
    let g := g.putHits controller hits (cause := some revealCause)
    g.restBottom controller rest true (cause := some revealCause)
  | .syntheticDestiny =>
    let yours := (g.permanentsOf controller).filter (g.isCreature ·) |>.map (·.id)
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let src := sourceId.bind g.findObject?
    let g := g.withBatch (some cause) fun g =>
      yours.foldl (fun g id => g.exileId id (cause := some cause)) g
    g.change (.pushDelayedTrigger { controller, source := src, kind := .endStepSynthetic yours.size, cause })
      |>.logMsg "Those creatures return as revealed cards at the next end step"
  | .searchBasics kinds untapAt =>
    let g := if untapAt == 0 then g else g.change (.untapSearchedIfLands (some untapAt))
    g.beginLibrarySearch controller (basicOf kinds) "a basic land card" (.battlefield true)
  | .proteus =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some o =>
        let owner := (g.controllerOf o).getD o.owner
        let (g, putCause) := g.allocDelayedCause (some controller) sourceId
        let g := g.moveIdsInOrder #[id] (.library owner) (cause := some putCause)
        let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
        let (g, hits, rest) := g.revealUntil owner (·.isCreature) 1 (cause := some revealCause)
        let g := g.putHits owner hits (cause := some revealCause)
        g.restBottom owner rest false (cause := some revealCause)
      | none => g
    | _ => g
  | .animate p t flying first =>
    match g.srcObj? sourceId with
    | none => g
    | some o =>
      let kws :=
        Keywords.merge (if flying then Keyword.flying else Keywords.none)
          (if first then Keywords.none else Keywords.none)
      let g := g.setUntilEotForm o (Int.ofNat p, Int.ofNat t) kws
        s!"{g.name o} becomes a {p}/{t} until end of turn"
        (additionalCreature := true)
      if first then g.createEffect (.firstStrikeOnYourTurn o.id)
      else g
  | .mapToken => g.makeFrc controller .map
  | .archon =>
    match targets[0]? with
    | some (Target.player pid) =>
      let victim :=
        ((g.permanentsOf pid).find? (g.isCreature ·)).orElse
          (fun _ => (g.permanentsOf pid).find? (g.isPlaneswalker ·))
      let g :=
        match victim with
        | some o => g.sacrificeToGraveyard o s!"{(g.player pid).name} sacrifices {g.name o}"
        | none => g.logMsg s!"{(g.player pid).name} has no creature or planeswalker to sacrifice"
      let g := g.handDiscard pid
      let g := g.loseLife pid 3
      let g := g.draw controller 1
      g.gainLife controller 3
    | _ => g
  | .avacyn =>
    match g.frcCause? with
    | some o =>
      if o.zone == .graveyard o.owner then
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        let src := (sourceId.bind g.findObject?).orElse (fun _ => some o)
        g.change (.pushDelayedTrigger { controller, source := src, kind := .endStepGraveReturn o.id controller, cause })
          |>.logMsg s!"{o.name} returns at the beginning of the next end step"
      else g
    | none => g
  | .dack =>
    let n := (g.livingOpponents controller).size
    let (g, cause) := g.allocDelayedCause (some controller) sourceId
    let (g, hits, rest) := g.revealUntil controller (·.isCreature) n (cause := some cause)
    let g := g.putHits controller hits (cause := some cause)
    let g := hits.foldl (fun g id =>
      match g.followMoved id |> g.findObject? with
      | some o => g.record (GameEvent.designation g.turnNumber (g.snapshot o) (.goaded controller false) true (cause := some cause))
      | none => g) g
    let opps := g.livingOpponents controller
    let g := Id.run do
      let mut g := g
      let mut i := 0
      for id in hits do
        match opps[i]?, g.followMoved id |> g.findObject? with
        | some opp, some o =>
          g := g.changeControl o opp.id (cause := some cause)
          i := i + 1
        | _, _ => pure ()
      return g
    g.restBottom controller rest true (cause := some cause)
  | .jhoira =>
    match targets[0]? with
    | some (Target.player pid) =>
      let (g, cause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntil pid historicCard 1 (cause := some cause)
      let g :=
        match hits[0]? with
      | some id =>
          match g.findObject? id with
          | some card =>
            let mv := card.printed.manaValue
            let g := (g.putHits controller #[id] (cause := some cause))
            g.loseLife controller mv (cause := some cause)
          | none => g
        | none => g.logMsg s!"{(g.player pid).name} reveals no historic permanent"
      g.restBottom pid rest false (cause := some cause)
    | _ => g
  | .nissa =>
    let g := g.draw controller
    match g.srcObj? sourceId with
    | some src =>
      if g.optionalOnceUsedThisTurn src.id then g
      else
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        let g := g.record (GameEvent.optionalOnceActed g.turnNumber controller src.id (cause := some cause))
        let (g, hits, rest) := g.revealUntil controller (·.isCreature) 1 (cause := some cause)
        let g := g.putHits controller hits (cause := some cause)
        g.restBottom controller rest false (cause := some cause)
    | none => g
  | .nivPay =>
    let n := nKnown
    if (g.player controller).life > Int.ofNat n && n > 0 then
      let before := (g.player controller).life
      let payCause : Option EventCause :=
        g.currentResolvingContext?.map fun (src, _) =>
          .costPayment .life controller
            (g.resolvingAbility.orElse (fun _ => sourceId.orElse (fun _ => src)))
      match g.payLifeCost controller n (cause := payCause) with
      | .ok g =>
        if (g.player controller).life < before then g.draw controller n else g
      | .error _ => g.logMsg s!"{pl.name} declines to pay {n} life"
    else g.logMsg s!"{pl.name} declines to pay {n} life"
  | .nivDrain =>
    g.eachOpponentLosesYouGain controller 1
  | .obEnter =>
    let ids := g.battlefield.filter (fun o =>
      g.isCreature o && o.status.tapped &&
        match g.controllerOf o with
        | some c => c != controller && !(g.player c).lost
        | none => false) |>.map (·.id)
    let g := g.destroyIds ids
    g.gainLife controller ids.size
  | .obAngel =>
    if g.loggedLifeGained controller > 0 then g.makeFrc controller .angel
    else g
  | .omnathCc =>
    g.changePlayer controller (.addMana .colorless 2)
      |>.logMsg (s!"{pl.name} adds " ++ "{C}{C}")
  | .elspethDestroy =>
    g.destroyIds (g.battlefield.filter (fun o => g.isCreature o && g.snapshotPower o >= 4) |>.map (·.id))
  | .elspethEmblem =>
    let (g, emb) := g.allocObject {
        name := "Elspeth emblem"
        types := #[.enchantment]
        grantTeamPlusTwoFlying := true
      } controller .command (some controller)
    g.logMsg s!"{pl.name} gets an emblem ({emb.name})"
  | .jacePlus =>
    let g := g.draw controller 2
    handDiscardToBottom g
  | .jaceMinus =>
    match targets[0]? with
    | some (Target.permanent id) =>
      let (g, exileCause) := g.allocDelayedCause (some controller) sourceId
      let g := g.exileId id (cause := some exileCause)
      let (g, revealCause) := g.allocDelayedCause (some controller) sourceId
      let (g, hits, rest) := g.revealUntil controller creatureOrWalker 1 (cause := some revealCause)
      let g := g.putHits controller hits (cause := some revealCause)
      g.restBottom controller rest false (cause := some revealCause)
    | _ => g
  | .jaceTax =>
    if g.activePlayer == controller then g
    else
      g.createEffect (.cantAttackJacesThisTurn g.activePlayer)
        |>.logMsg s!"{(g.player g.activePlayer).name}'s creatures can't attack Jaces this turn"
  | .monarch =>
    let prev := (g.players.find? (·.isMonarch)).map (·.id)
    g.record (GameEvent.becameMonarch g.turnNumber controller prev
      (cause := g.resolvingOneShotCause controller sourceId))
      |>.logMsg s!"{pl.name} becomes the monarch"
  | .gingerbrute =>
    if (g.player controller).isMonarch then g.makeFrc controller .gingerbrute
    else g
  | .tamiyoStun =>
    if !(g.player controller).isMonarch then g
    else
      match g.frcCause? with
      | some o =>
        if o.isOnBattlefield && g.isCreature o then
          let g := g.becomeTapped o
          let n := g.countersYouPut (g.object! o.id) 1 (putter := some controller)
          g.recordPutCounters o.id .stun n (byPlayer := some controller)
            |>.logMsg s!"{g.name o} gets a stun counter"
        else g
      | none => g
  | .teferi =>
    match targets[0]? with
    | some (Target.player pid) =>
      let g := g.createEffects
        #[.protectionFromEverything pid, .lifeCantChange pid]
      let g := g.logMsg s!"{(g.player pid).name} has protection from everything and their life total can't change"
      let ids := (g.permanentsOf pid).filter (fun o => !g.isLand o) |>.map (·.id)
      let phaseCause := g.resolvingBatchCause controller sourceId
      let g := g.withBatch phaseCause fun g =>
        ids.foldl (fun g id =>
          match g.findObject? id with
          | some o => if o.isOnBattlefield then g.phaseOut o (cause := phaseCause) else g
          | none => g) g
      match g.resolvingSpell.bind g.findObject? with
      | some spell =>
        g.createEffect (.exileInstantSorceryInstead spell.id)
          |>.logMsg s!"{spell.name} will be exiled"
      | none => g
    | _ => g
  | .urSphinx =>
    let n := nKnown
    g.withBatch none fun g =>
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
                g := g.createEffect (.freeCastFromGraveyardUntilEot card.id)
              | none => pure ()
          return g) g
  | .venserSpell =>
    match targets[0]? with
    | some (Target.card id) =>
      match g.findObject? id with
      | some spell => (g.copyStackSpell spell controller).copyStackSpell spell controller
      | none => g
    | _ => g
  | .venserPerm =>
    match targets[0]? with
    | some (Target.permanent id) =>
      match g.findObject? id with
      | some src =>
        let (g, cause) := g.allocDelayedCause (some controller) sourceId
        g.withBatch (some cause) fun g =>
          Id.run do
            let mut g := g
            for _ in [0:2] do
              let (g', tok) := g.copyBattlefieldPermanent src controller (cause := some cause)
              g := g'
              g := g.createEffect (.keywordsUntilEot tok.id Keyword.haste) (cause := some cause)
              g := g.change (.pushDelayedTrigger { controller, source := some tok, kind := .endStepSacrifice tok.id, cause })
            return g.logMsg "The token copies gain haste and are sacrificed at the next end step"
      | none => g
    | _ => g
  | .goblin =>
    match g.srcObj? sourceId with
    | some src =>
      if src.status.windcragMardu then g
      else
        let g := g.makeFrc controller .goblin
        match (g.permanentsOf controller).reverse.find? (fun o => g.name o == "Goblin" && o.printed.isToken) with
        | some tok =>
          g.createEffect (.keywordsUntilEot tok.id (Keywords.merge Keyword.lifelink Keyword.haste))
            |>.logMsg s!"{g.name tok} gains lifelink and haste until end of turn"
        | none => g
    | none => g
  | .spirit => g.createKindTokens controller .spirit 1
  | .story =>
    match g.srcObj? sourceId with
    | some o =>
      g.recordPutCounters o.id .story 1 (byPlayer := some controller)
        |>.logMsg s!"{g.name o} gets a story counter"
    | none => g
  | .currencyExile =>
    match g.frcCause? with
    | some card =>
      if card.zone == .graveyard card.owner then
        match g.srcObj? sourceId with
        | some src => g.exileSearchedLinked controller card.id (some src.id)
        | none => g.exileId card.id
      else g
    | none => g
  | .currencyLoot =>
    let g := g.draw controller
    g.handDiscard controller
  | .currencyReturn =>
    match g.srcObj? sourceId with
    | none => g
    | some src =>
      match src.linkedExile.find? (fun id => (g.findObject? id).any (·.zone == .exile)) with
      | none => g.logMsg s!"{g.name src} has no exiled card"
      | some id =>
        match g.findObject? id with
        | none => g
        | some card =>
          let land := card.printed.isLand
          let (g, _) := g.move id (.graveyard card.owner) none
          let g := g.changeObject src.id (.linkedExile (src.linkedExile.filter (· != id)))
          if land then g.makeFrc controller .treasure else g.makeFrc controller .rogue
  | .cursedCopy =>
    match g.srcObj? sourceId with
    | none => g
    | some art =>
      match g.battlefield.find? (fun o => g.isCreature o && o.id != art.id) with
      | none => g.logMsg s!"{g.name art} does not become a copy"
      | some src =>
        let g := g.becomeCopyOf art src (untilEot := true)
        g.createEffect (.keywordsUntilEot art.id Keyword.haste)
          |>.logMsg s!"{g.name (g.object! art.id)} has haste until end of turn"
  | .despair =>
    g.withBatch (g.resolvingBatchCause controller sourceId) fun g =>
      g.forEachOpponent controller fun g pid =>
        g.loseLife pid (g.loggedLifeLost pid)
  | .dreadUpkeep =>
    let (g, cause?) : Game × Option EventCause :=
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
        (g, some c)
      | none => (g, none)
    (g.loseLife controller 1 (cause := cause?)).amassZombies controller 1 (cause := cause?)
  | .dreadLink =>
    match g.frcCause? with
    | some o =>
      if o.isOnBattlefield then g.grantUntilEotLogged o Keyword.lifelink else g
    | none => g
  | .myr n => g.makeFrc controller .myr n
  | .drawPerArtifact =>
    let n := (g.permanentsOf controller).filter (g.isArtifact ·) |>.size
    g.draw controller n
  | .sharkCast =>
    let x :=
      match g.frcCause? with
      | some spell => g.objectManaValue spell
      | none => 0
    g.makeFrc controller .shark 1 x
  | .sharkCycle =>
    g.makeFrc controller .shark 1 nKnown
  | .skrelv =>
    let (g, cause?) : Game × Option EventCause :=
      match g.currentResolvingContext? with
      | some (src, ctrl) =>
        let (g, c) := g.allocDelayedCause (ctrl.orElse (fun _ => some controller)) (src.orElse (fun _ => sourceId))
        (g, some c)
      | none => (g, none)
    (g.loseLife controller 1 (cause := cause?)).makeFrc controller .mite (cause := cause?)
  | .insects => g.makeFrc controller .insect 2
  | .factOrFiction =>
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
    let g := g.withBatch none fun g =>
      toHand.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          let (g, _) := g.move id (.hand controller) none
          g.logMsg s!"{o.name} goes to {pl.name}'s hand"
        | none => g) g
    g.withBatch none fun g =>
      toGy.foldl (fun g id =>
        match g.findObject? id with
        | some o =>
          let (g, _) := g.move id (.graveyard controller) none
          g.logMsg s!"{o.name} goes to {pl.name}'s graveyard"
        | none => g) g
  | .pump n =>
    match g.srcObj? sourceId with
    | some o => g.pumpPermanent o n 0
    | none => g
  | .kobold => g.makeFrc controller .kobold
  | .warriorsX => g.makeFrc controller .warrior (g.spellX)
  | .citizensX => g.makeFrc controller .citizen (g.spellX)
  | .explore =>
    let lib := (g.player controller).library
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
          if g.isCreature o then
            (g.logMsg s!"{pl.name} explores").addPlusOnePlusOneTo o 1 (byPlayer := some controller)
          else g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
        | none => g.logMsg s!"{pl.name} explores and leaves {card.name} on top"
  | .transformIncubator =>
    match g.srcObj? sourceId with
    | some o =>
      let counters := o.status.plusOnePlusOne
      let oName := g.name o
      let (src, ctrl) :=
        match g.currentResolvingContext? with
        | some (s, c) => (s.orElse (fun _ => some o.id), c.orElse (fun _ => some controller))
        | none => (some o.id, some controller)
      let transformCause := some (EventCause.oneShotEffect (some ⟨g.nextEffectId⟩) src ctrl)
      let g := g.expirePrintedStaticEffects o (cause := transformCause)
      let g := g.record
        (GameEvent.transformed g.turnNumber (g.snapshot o) (!o.status.transformed)
          (cause := transformCause))
      g.createPrintedStaticEffects (g.object! o.id)
        |>.logMsg s!"{oName} transforms into a 0/0 Phyrexian with {counters} +1/+1 counters"
    | none => g
  | .turnFaceUp =>
    match g.srcObj? sourceId with
    | some o =>
      let g := g.record (GameEvent.turnedFaceUp g.turnNumber (g.snapshot o))
      g.logMsg s!"{g.name (g.object! o.id)} is turned face up"
    | none => g
  | .gingerDash =>
    match g.srcObj? sourceId with
    | some o =>
      g.createEffect (.cantBeBlockedExceptByHasteUntilEot o.id)
        |>.logMsg s!"{g.name o} can't be blocked this turn except by creatures with haste"
    | none => g
where
  handDiscardToBottom (g : Game) : Game :=
    match (g.player controller).hand.back? with
    | none => g
    | some id =>
      let name := (g.object! id).name
      let (g, newId) := g.move id (.library controller) none
      let pl := g.player controller
      let lib := pl.library.filter (· != newId)
      g.changePlayer controller (.library (#[newId] ++ lib))
        |>.logMsg s!"{(g.player controller).name} puts {name} on the bottom of their library"

/-- Reveal creature cards exiled by Synthetic Destiny at the end step. -/
def applyOneDelayedSynthetic (g : Game) (who : PlayerId) (n : Nat) (cause : EventCause) : Game :=
  let (g, hits, rest) := g.revealUntil who (·.isCreature) n (cause := some cause)
  let g := g.putHits who hits (cause := some cause)
  g.restBottom who rest true (cause := some cause)

end Game
end Mtg.Engine
