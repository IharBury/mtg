import Mtg.Engine.Game.CombatAssignment

/-!
# State-based actions (CR 704)

APNAP order (CR 101.4), the legend rule and its choice prompt
(CR 704.5j), and the state-based-action sweep `checkSBA` (CR 704.5).
-/

namespace Mtg.Engine
namespace Game

/-- Living players in APNAP order (CR 101.4): the active player, then the
next player in turn order, and so on. -/
def apnapPlayers (g : Game) : Array PlayerId :=
  g.playersInOrderFrom g.activePlayer (fun pl => !pl.lost)

/-- Alias of `apnapPlayers` (CR 101.4). -/
def apnapOrder (g : Game) : Array PlayerId :=
  g.apnapPlayers

/-- Legendary permanents `p` currently controls. -/
def legendaryPermanentsOf (g : Game) (p : PlayerId) : Array GameObject :=
  (g.permanentsOf p).filter (·.isLegendary)

/-- First legend-rule group that needs a choice (CR 704.5j / 201.2a): two or
more legendary permanents with the same name controlled by the same player,
taking players in APNAP order. -/
def firstLegendRuleChoice? (g : Game) : Option (PlayerId × String × Array ObjectId) :=
  Id.run do
    for p in g.apnapPlayers do
      let legs := g.legendaryPermanentsOf p
      let mut seen : Array String := #[]
      for o in legs do
        if !seen.contains o.name then
          seen := seen.push o.name
          let group := legs.filter (fun x => x.name == o.name)
          if group.size ≥ 2 then
            return some (p, o.name, group.map (·.id))
    return none

/-- True while a player must choose which legendary permanent to keep. -/
def legendChoicePending? (g : Game) : Bool :=
  match g.pending with
  | .chooseLegend .. => true
  | _ => false

/-- Default legend-rule choice: the copy that entered most recently. -/
def defaultLegendToKeep (g : Game) (ids : Array ObjectId) : ObjectId :=
  ids.foldl (fun best id =>
    match g.findObject? best, g.findObject? id with
    | some a, some b => if b.timestamp ≥ a.timestamp then id else best
    | _, some _ => id
    | _, none => best) (ids[0]!)

/-- Perform applicable state-based actions (CR 704.3). The `Bool` is `true` if
any state-based action was performed (used by CR 514.3a). If a legend-rule
choice is required (CR 704.5j), the check pauses: that SBA is not finished,
so CR 704.3 does not yet repeat, put triggers on the stack, or grant
priority. `keepLegend` resumes the loop. -/
partial def checkSBACounted (g : Game) : Game × Bool :=
  if g.over then (g, false)
  else
    Id.run do
      let mut g := g
      let mut changed := false
      -- Players losing (CR 704.5a–c). They leave after this SBA pass
      -- if the game continues (CR 800.4 / 800.4a).
      for pl in g.players do
        if !pl.lost then
          if pl.life ≤ 0 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (life total {pl.life})"
            changed := true
          else if pl.drewFromEmpty then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (drew from empty library)"
            changed := true
          else if pl.poison ≥ 10 then
            g := g.setPlayer { pl with lost := true }
            g := g.logMsg s!"{pl.name} loses the game (poison)"
            changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, true)
      | none => pure ()
      -- Waiting for a legend-rule choice: do not apply further SBAs until
      -- the player keeps one copy (CR 704.5j). Drop a stale prompt if the
      -- group is no longer two or more.
      match g.pending with
      | .chooseLegend p name ids =>
        let still := ids.filter (fun id =>
          match g.findObject? id with
          | some o =>
            o.isOnBattlefield && o.controlledBy p && o.isLegendary && o.name == name
          | none => false)
        if still.size ≥ 2 then
          return (g, changed)
        else
          g := { g with pending := .none }
      | _ => pure ()
      -- Creatures with 0 toughness or lethal damage (CR 704.5f–g).
      -- Snapshot exile-instead replacements first so a simultaneous death
      -- of Head of the Hunt still exiles opposing creatures.
      let snap := g.battlefield.filter exilesOppDeath?
      let victims :=
        g.battlefield.filterMap (fun o =>
          if !o.isCreature then none
          else
            let t := g.toughness o
            if t ≤ 0 then some (o, s!"{o.name} dies (toughness {t})")
            else if o.status.damage ≥ t && !g.hasIndestructible o then
              some (o, s!"{o.name} dies from lethal damage")
            else if o.status.dealtDeathtouch && !g.hasIndestructible o then
              some (o, s!"{o.name} dies from deathtouch")
            else none)
      if !victims.isEmpty then
        g := { g with
          lockedDeathReplacements := some snap
          suppressOthersDie := true }
        -- CR 614.6: a replaced death never happens, so only creatures that
        -- will actually go to a graveyard cause “die” triggers. A Bee that
        -- dies at the same time as another creature that *does* die still
        -- sees that event (ruling 139).
        let actualDeaths := victims.filter (fun pair =>
          !g.wouldExileInsteadOfDying pair.1)
        if !actualDeaths.isEmpty then
          for o in g.battlefield do
            if actualDeaths.any (fun pair => pair.1.id != o.id) then
              match o.controller with
              | some p =>
                g := { g with waitingTriggers :=
                  g.waitingTriggers ++
                    o.waitingTriggersFor p .oneOrMoreOtherCreaturesDie }
              | none => pure ()
          -- “One or more creature cards” fires once per source still on
          -- the battlefield (Robot Domination; MSH 138).
          let leavingIds := victims.map (fun pair => pair.1.id)
          let gyOwners :=
            actualDeaths.foldl (fun acc pair =>
              if pair.1.printed.isCreature && !pair.1.printed.isToken &&
                  !acc.any (· == pair.1.owner) then
                acc.push pair.1.owner
              else acc) (#[] : Array PlayerId)
          if !gyOwners.isEmpty then
            for o in g.battlefield do
              if !leavingIds.any (· == o.id) then
                match o.controller with
                | some p =>
                  if gyOwners.any (· == p) then
                    g := { g with waitingTriggers :=
                      g.waitingTriggers ++
                        o.waitingTriggersFor p .creatureCardsPutIntoYourGy }
                | none => pure ()
            g := { g with suppressCreatureCardsToGy := true }
      for pair in victims do
        let o := pair.1
        let reason := pair.2
        match g.findObject? o.id with
        | some o =>
          if o.isOnBattlefield && o.isCreature then
            g := g.moveToOwnerGraveyard o reason
            changed := true
        | none => pure ()
      g := { g with
        lockedDeathReplacements := none
        suppressOthersDie := false
        suppressCreatureCardsToGy := false }
      for o in g.battlefield do
        if o.isCreature && o.status.dealtDeathtouch && g.hasIndestructible o then
          g := g.setObject { o with status := { o.status with dealtDeathtouch := false } }
      -- Legend rule (CR 704.5j): pause so the controller chooses one to keep.
      match g.firstLegendRuleChoice? with
      | some (p, name, ids) =>
        g := { g with pending := .chooseLegend p name ids }
        g := g.logMsg
          s!"{(g.player p).name} chooses which {name} to keep (legend rule, CR 704.5j)"
        return (g, true)
      | none => pure ()
      -- Tokens in zones other than the battlefield cease to exist (CR 704.5d).
      for o in g.objects do
        if o.printed.isToken && o.zone != .battlefield then
          g := g.ceaseToExist o.id
          g := g.logMsg s!"{o.name} ceases to exist (token left the battlefield)"
          changed := true
      -- Saga with lore at or past its final chapter and no chapter on the
      -- stack is sacrificed (CR 714.4 / 704.5s).
      for o in g.battlefield do
        match o.printed.saga, o.controller with
        | some sdef, some _ =>
          if o.status.lore ≥ sdef.finalChapterNumber && sdef.finalChapterNumber > 0 &&
              !g.sagaChapterPending o.id then
            g := g.moveToOwnerGraveyard o
              s!"{o.name} is sacrificed (CR 714.4)"
            changed := true
        | _, _ => pure ()
      -- Unattached or illegally attached Auras (CR 704.5m).
      for o in g.battlefield do
        if o.printed.isAura then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.isCreature
            | none => false
          if !legal then
            g := g.moveToOwnerGraveyard o
              s!"{o.name} is put into its owner's graveyard (CR 704.5n)"
            changed := true
      -- Illegally attached Equipment (CR 704.5n). Unattached Equipment stays.
      for o in g.battlefield do
        if o.printed.isEquipment then
          let legal :=
            match o.attachedTo.bind g.findObject? with
            | some host => host.isOnBattlefield && host.printed.isCreature
            | none => true
          if !legal then
            g := g.setObject { o with attachedTo := none }
            g := g.logMsg s!"{o.name} becomes unattached (CR 704.5n)"
            changed := true
      match g.decideGameIfFinished with
      | some finished => return (finished, true)
      | none => pure ()
      if changed then
        let (g', _) := checkSBACounted g
        return (g', true)
      return (g, false)

def checkSBA (g : Game) : Game :=
  let g := (g.checkSBACounted).1
  if g.over then g
  else
    let g := g.leavePlayersWhoLost
    if g.over then g
    else (g.checkSBACounted).1

/-- Triggered abilities waiting to be put onto the stack (CR 603.3 / 603.3b,
514.3a). All triggered abilities wait until a player would receive priority. -/
def hasWaitingTriggers (g : Game) : Bool :=
  !g.waitingTriggers.isEmpty

end Game
end Mtg.Engine
