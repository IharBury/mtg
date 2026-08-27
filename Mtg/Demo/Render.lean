import Mtg.Engine.Game

/-!
# Text rendering of a game for the console demo.
-/

namespace Mtg.Demo.Render

open Mtg.Engine
open Mtg.Engine.Game

/-- Owner and controller of an object (CR 108.3, 110.2). Permanents always
have both. `group = none` prints both so an ungrouped line is unambiguous.
When the listing is grouped under a controller (`some gp`), omit owner and
controller unless they differ from that heading (`gp = none` is the
no-controller group). -/
def controlClause (g : Game) (o : GameObject) (group : Option (Option PlayerId) := none) :
    String :=
  let showOwner :=
    match group with
    | none => true
    | some gp => gp != some o.owner
  let showController :=
    match group with
    | none => true
    | some gp => o.controller != gp
  let owned := s!"owned by {g.player o.owner |>.name}"
  let controlled :=
    match o.controller with
    | some p => s!"controlled by {g.player p |>.name}"
    | none => "no controller"
  let parts : List String :=
    (if showOwner then [owned] else []) ++
    (if showController then [controlled] else [])
  match parts with
  | [] => ""
  | ps => s!" ({String.intercalate ", " ps})"

/-- Identity of an object for cross-references (blocker, Aura host, ability source). -/
def objectRef (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | some o => s!"{o.id} {o.name}"
  | none => toString id

/-- Source of an activated or triggered ability on the stack (CR 113.7). -/
def sourceClause (g : Game) (o : GameObject) : String :=
  match o.sourceId with
  | none => ""
  | some sid => s!" *source {objectRef g sid}*"

/-- Keywords and abilities printed after a card's name (and P/T). -/
def faceExtras (c : CardDef) : String :=
  let s := c.keywordsAndAbilities
  if s.isEmpty then "" else s!" {s}"

/-- How well leftover Oracle `line` matches a stacked ability's structured text. -/
def abilityLineScore (line abilityText : String) : Nat :=
  let words :=
    abilityText.splitOn " " |>.map (fun s => s.trimAscii.copy) |>.filter (fun w => w.length >= 4)
  (words.filter (fun w => (line.splitOn w).length > 1)).length

/-- Printed text of one stacked ability. Sibling abilities of the source card
are omitted. Prefers leftover Oracle wording when a unique line exists or a
leftover line matches `abilityText`. -/
def textForStackedAbility (c : CardDef) (abilityText : String) : String :=
  match c.leftoverOracleLines with
  | [] => abilityText
  | [line] => line
  | lines =>
    match lines.find? (fun line => line == abilityText) with
    | some line => line
    | none =>
      let (bestScore, bestLine) :=
        lines.foldl
          (fun (acc : Nat × String) line =>
            let s := abilityLineScore line abilityText
            if s > acc.1 then (s, line) else acc)
          (0, abilityText)
      if bestScore > 0 then bestLine else abilityText

/-- Extras after a stack object's name. An ability on the stack shows only
that ability, not other abilities printed on the source card. Spells still
show their full printed extras. -/
def stackFaceExtras (o : GameObject) : String :=
  let s :=
    match o.triggeredAbility, o.abilityEffect with
    | some t, _ => textForStackedAbility o.printed (TriggeredAbility.toNotation t)
    | none, some e => textForStackedAbility o.printed (AbilityEffect.toNotation e)
    | none, none => o.printed.keywordsAndAbilities
  if s.isEmpty then "" else s!" {s}"

/-- Like `faceExtras`, but includes keywords granted by other permanents. -/
def objectFaceExtras (g : Game) (o : GameObject) : String :=
  let s := o.printed.keywordsAndAbilitiesOf (g.effectiveKeywords o)
  if s.isEmpty then "" else s!" {s}"

/-- Battlefield line for one permanent: id, name, current type line (CR 205.1a),
P/T when it is a creature, then keywords, control, and status. -/
def objectLine (g : Game) (o : GameObject) (group : Option (Option PlayerId) := none) :
    String :=
  let tap := if o.status.tapped then " (tapped)" else ""
  let sick := if o.hasSummoningSickness then " (summoning sickness)" else ""
  let atk :=
    if o.status.attacking then
      if o.status.blocked then " *attacking, blocked*" else " *attacking*"
    else ""
  let blk :=
    if o.status.blocking.isEmpty then ""
    else
      let refs := o.status.blocking.toList.map (objectRef g)
      s!" *blocking {String.intercalate ", " refs}*"
  let types := s!" {o.typeLine}"
  let pt :=
    if o.isCreature then s!" {g.power o}/{g.toughness o}" else ""
  let ench :=
    match o.attachedTo with
    | none => ""
    | some hostId =>
      if o.printed.isEquipment then
        s!" *equipping {objectRef g hostId}*"
      else
        s!" *enchanting {objectRef g hostId}*"
  let dmg :=
    if o.status.damage > 0 then s!" dmg:{o.status.damage}" else ""
  let exileIfDies :=
    if o.status.untilEotExileIfDies then " *exile if dies*" else ""
  let counters :=
    if o.status.plusOnePlusOne > 0 then s!" +1/+1×{o.status.plusOnePlusOne}" else ""
  s!"{o.id} {o.name}{types}{pt}{counters}{objectFaceExtras g o}{controlClause g o group}{tap}{sick}{atk}{blk}{ench}{dmg}{exileIfDies}"

def handLine (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o => s!"{o.id} {o.printed.summary}"

/-- Whether `viewer` may look at card faces in `z` (CR 400.2, 401.2, 402.2).
`none` is omniscient: public zones and hands are shown, but libraries stay
face-down even to their owner except for cards they are scrying (CR 701.20). -/
def canSeeZoneFaces (viewer : Option PlayerId) : Zone → Bool
  | .library _ => false
  | .hand p =>
    match viewer with
    | none => true
    | some v => v == p
  | .battlefield | .graveyard _ | .stack | .exile | .command | .ante => true

/-- Whether `viewer` may look at the cards `scrying` is looking at (CR 701.20).
`none` is omniscient. -/
def canSeeScry (viewer : Option PlayerId) (scrying : PlayerId) : Bool :=
  match viewer with
  | none => true
  | some v => v == scrying

/-- Cards `p` is looking at while scrying (last = current top). Empty if `p`
is not scrying. -/
def scryLook (g : Game) (p : PlayerId) : Array ObjectId :=
  match g.pending with
  | .scry q n => if q == p then g.scryLookedIds p n else #[]
  | _ => #[]

/-- A looked-at library card: object id plus the face, as when looking at a
card in hand. -/
def scryCardLine (g : Game) (id : ObjectId) : String :=
  handLine g id

/-- Lines for the cards `p` is looking at while scrying `n` (last = current top). -/
def scryLookedLines (g : Game) (p : PlayerId) (n : Nat) : List String :=
  (g.scryLookedIds p n).toList.map (scryCardLine g)

/-- Board-state section for a pending scry. Other players see that a scry is
happening, not the card faces. -/
def scryLookBlock (g : Game) (viewer : Option PlayerId := none) : Option String :=
  match g.pending with
  | .scry p n =>
    if canSeeScry viewer p then
      let cards := scryLookedLines g p n
      if cards.isEmpty then none
      else some <| "Scry (top last):\n  " ++ String.intercalate "\n  " cards
    else
      some s!"{(g.player p).name} is scrying {n}"
  | _ => none

/-- Looking-at lines inside a player's `state` block while they scry. -/
def scryLookSection (g : Game) (pl : Player) (viewer : Option PlayerId) : Option String :=
  match g.pending with
  | .scry p n =>
    if p != pl.id then none
    else if canSeeScry viewer p then
      let cards := scryLookedLines g p n
      if cards.isEmpty then none
      else
        some <| String.intercalate "\n"
          (s!"  Looking at (scry {n}, top last):" :: cards.map (fun c => s!"    {c}"))
    else
      some s!"  Looking at (scry {n}): (hidden)"
  | _ => none

/-- Permanents currently attached to `hostId`. -/
def attachmentsOf (g : Game) (hostId : ObjectId) : Array GameObject :=
  g.battlefield.filter (fun o => o.attachedTo == some hostId)

/-- True when `o` is attached to a permanent on the battlefield. -/
def attachedToBattlefield (g : Game) (o : GameObject) : Bool :=
  match o.attachedTo.bind g.findObject? with
  | some host => host.isOnBattlefield
  | none => false

/-- Unattached permanents from `os` in three unlabeled subgroups: creatures
(including creature-lands), non-creature non-lands, then non-creature lands.
Attached permanents are omitted here; they print under their host. Empty
subgroups are dropped. -/
def battlefieldSubgroups (g : Game) (os : Array GameObject) : Array (Array GameObject) :=
  let hosts := os.filter (fun o => !attachedToBattlefield g o)
  #[
    hosts.filter (·.isCreature),
    hosts.filter (fun o => !o.isCreature && !o.printed.isLand),
    hosts.filter (fun o => !o.isCreature && o.printed.isLand)
  ].filter (fun sg => !sg.isEmpty)

/-- Lines for one unattached host and the permanents attached to it. -/
def battlefieldHostLines (g : Game) (o : GameObject)
    (group : Option (Option PlayerId)) : Array String :=
  Id.run do
    let mut lines : Array String := #[objectLine g o group]
    for att in attachmentsOf g o.id do
      lines := lines.push s!"  {objectLine g att group}"
    return lines

/-- Lines for unattached permanents in `os`, grouped by kind. Each host is
followed by what is attached to it (from the whole battlefield), indented
two extra spaces so attached permanents sit next to their host. -/
def battlefieldPermanentLines (g : Game) (os : Array GameObject)
    (group : Option (Option PlayerId)) : List String :=
  Id.run do
    let mut lines : Array String := #[]
    for sg in battlefieldSubgroups g os do
      for o in sg do
        lines := lines ++ battlefieldHostLines g o group
    return lines.toList

def playerBlock (g : Game) (pl : Player) (viewer : Option PlayerId := none) : String :=
  let marker := if pl.id == g.activePlayer then " (active)" else ""
  let bf := battlefieldPermanentLines g (g.permanentsOf pl.id) (some (some pl.id))
  let bfText := if bf.isEmpty then "  (none)" else String.intercalate "\n  " bf
  let handText :=
    if canSeeZoneFaces viewer (.hand pl.id) then
      let hand := pl.hand.toList.map (handLine g)
      if hand.isEmpty then "  (empty)" else String.intercalate "\n  " hand
    else
      "  (hidden)"
  let gy := pl.graveyard.toList.map (fun id =>
    match g.findObject? id with
    | none => s!"{id} (missing)"
    | some o => s!"{o.id} {o.name}{faceExtras o.printed}")
  let gyText := if gy.isEmpty then "  (empty)" else String.intercalate "\n  " gy
  let scryLines : List String :=
    match scryLookSection g pl viewer with
    | some s => [s]
    | none => []
  String.intercalate "\n" (
    [s!"{pl.name}{marker} — life {pl.life} — library {pl.library.size} — GY {pl.graveyard.size} — mana {pl.manaPool}"] ++
    scryLines ++
    [s!"  Hand ({pl.hand.size}):",
     "  " ++ handText,
     "  Battlefield:",
     "  " ++ bfText,
     s!"  Graveyard ({pl.graveyard.size}):",
     "  " ++ gyText])

def stackBlock (g : Game) : String :=
  if g.stack.isEmpty then "Stack: (empty)"
  else
    let lines := g.stack.toList.reverse.map (fun e =>
      match g.findObject? e.objectId with
      | some o =>
        s!"  {o.name}{stackFaceExtras o}{sourceClause g o} (controlled by {g.player e.controller |>.name})"
      | none => "  (missing)")
    "Stack (top first):\n" ++ String.intercalate "\n" lines

/-- Locked-in total cost of a proposed spell or ability (CR 601.2f / 602.2b). -/
def proposedCostNotation (prop : ProposedSpell) : String :=
  let sacOther :=
    if !prop.needsSacrificeOther then none
    else if prop.kind == .spell then
      some "Sacrifice an artifact or creature"
    else
      some "Sacrifice another creature or artifact"
  let parts : List String :=
    (if prop.cost.symbols.isEmpty then [] else [toString prop.cost]) ++
    (if prop.tapSource then ["{T}"] else []) ++
    (if prop.sacrificeSource then ["Sacrifice"] else []) ++
    sacOther.toList
  String.intercalate ", " parts

/-- Cost notation while the player may still pay (CR 601.2g / 602.2b). -/
def pendingCostNotation (g : Game) : Option String :=
  match g.pending with
  | .activateManaAbilities _ =>
    match g.proposedSpell with
    | some prop =>
      let cost := proposedCostNotation prop
      if cost.isEmpty then none else some cost
    | none => none
  | _ => none

/-- Board line for a cost that still needs to be paid. -/
def pendingCostLine (g : Game) : Option String :=
  pendingCostNotation g |>.map (fun cost => s!"Cost: {cost}")

/-- Snapshot section for a cost that still needs to be paid. -/
def costBlock (g : Game) : Option String :=
  pendingCostLine g

def header (g : Game) (viewer : Option PlayerId := none) : String :=
  let viewTag :=
    match viewer with
    | none => ""
    | some p => s!" [{g.player p |>.name}'s view]"
  let pending :=
    match g.pending with
    | .none => ""
    | .declareAttackers => " [declare attackers]"
    | .declareBlockers => " [declare blockers]"
    | .activateManaAbilities _ =>
      match pendingCostNotation g with
      | some cost => s!" [activate mana abilities (CR 601.2g); cost {cost}]"
      | none => " [activate mana abilities (CR 601.2g)]"
    | .chooseMode p =>
      s!" [choose a mode (CR 601.2b, {g.player p |>.name})]"
    | .chooseTargets p =>
      s!" [choose targets (CR 601.2c, {g.player p |>.name})]"
    | .sacrificePermanent p _ =>
      s!" [sacrifice a creature or artifact ({g.player p |>.name})]"
    | .declareMulligan p =>
      s!" [mulligan: {g.player p |>.name} may keep or mulligan (CR 103.5)]"
    | .putOnBottom p n =>
      let cards := if n == 1 then "1 card" else s!"{n} cards"
      s!" [mulligan: {g.player p |>.name} puts {cards} on the bottom (CR 103.5)]"
    | .scry p n =>
      s!" [scry {n} ({g.player p |>.name})]"
    | .mayDiscardDraw p n =>
      s!" [may discard a card, then draw {n} ({g.player p |>.name})]"
    | .assignCombatDamage p true =>
      s!" [assign combat damage (CR 510.1c, {g.player p |>.name})]"
    | .assignCombatDamage p false =>
      s!" [assign combat damage (CR 510.1d, {g.player p |>.name})]"
  let result :=
    match g.result with
    | none => ""
    | some (.won p) => s!"  RESULT: {g.player p |>.name} wins"
    | some .draw => "  RESULT: draw"
  if g.openingHandsPending then
    s!"Opening hands{viewTag}{pending}{result}"
  else
    s!"Turn {g.turnNumber} · {g.step} · priority: {g.player g.priority |>.name}{viewTag}{pending}{result}"

def snapshot (g : Game) (viewer : Option PlayerId := none) : String :=
  let players := g.players.toList.map (fun pl => playerBlock g pl viewer)
  let exiled := g.objects.filter (fun o => o.zone == .exile)
  let exileBlock :=
    if exiled.isEmpty then []
    else
      let lines := exiled.toList.map (fun o =>
        let extra :=
          match o.playPermission with
          | some perm => s!" (may be played by {g.player perm.player |>.name})"
          | none => ""
        s!"  {o.id} {o.name}{faceExtras o.printed}{extra}")
      ["Exile:\n" ++ String.intercalate "\n" lines]
  let cost :=
    match costBlock g with
    | some line => [line]
    | none => []
  String.intercalate "\n\n"
    (header g viewer :: cost ++ [stackBlock g] ++ players ++ exileBlock)

/-- Hide draws and library rearrangements that `viewer` is not allowed to see
(CR 401.2, 402.2, 103.5, 701.20). Other log lines are public. -/
def redactLogLine (g : Game) (viewer : PlayerId) (line : String) : String :=
  Id.run do
    for pl in g.players do
      if pl.id != viewer then
        let drawPrefix := s!"{pl.name} draws "
        if line.startsWith drawPrefix then
          return s!"{pl.name} draws a card"
        let putsPrefix := s!"{pl.name} puts "
        if line.startsWith putsPrefix && line.endsWith " on the bottom of their library" then
          return s!"{pl.name} puts a card on the bottom of their library"
        if line.startsWith putsPrefix && line.endsWith " on top of their library" then
          return s!"{pl.name} puts a card on top of their library"
    return line

/-- New log lines starting at `startIdx`, optionally redacted for `viewer`. -/
def newLog (g : Game) (startIdx : Nat) (viewer : Option PlayerId := none) : Array String :=
  let lines := g.log.extract startIdx g.log.size
  match viewer with
  | none => lines
  | some p => lines.map (redactLogLine g p)

/-- Current life total, matching the snapshot's `life N` fragment. -/
def lifeLine (pl : Player) : String :=
  s!"{pl.name} — life {pl.life}"

/-- Players whose life totals differ between two game states. -/
def changedLifeTotals (before after : Game) : Array Player :=
  after.players.filter (fun pl => (before.player pl.id).life != pl.life)

/-- Current mana pool, matching the snapshot's `mana {pool}` fragment. -/
def manaLine (pl : Player) : String :=
  s!"{pl.name} — mana {pl.manaPool}"

/-- Players whose mana pools differ between two game states. -/
def changedManaPools (before after : Game) : Array Player :=
  after.players.filter (fun pl => (before.player pl.id).manaPool != pl.manaPool)

/-- Player-facing name of a zone, using seat names rather than `Player N`. -/
def zoneLabel (g : Game) : Zone → String
  | .library p => s!"{g.player p |>.name}'s library"
  | .hand p => s!"{g.player p |>.name}'s hand"
  | .graveyard p => s!"{g.player p |>.name}'s graveyard"
  | .battlefield => "battlefield"
  | .stack => "stack"
  | .exile => "exile"
  | .command => "command"
  | .ante => "ante"

/-- Object identities currently occupying `z`, in zone order. -/
def zoneObjectIds (g : Game) : Zone → Array ObjectId
  | .library p => (g.player p).library
  | .hand p => (g.player p).hand
  | .graveyard p => (g.player p).graveyard
  | .stack => g.stack.map (fun e => e.objectId)
  | .battlefield => g.battlefield.map (·.id)
  | .exile => g.objects.filter (fun o => o.zone == .exile) |>.map (·.id)
  | .command => g.objects.filter (fun o => o.zone == .command) |>.map (·.id)
  | .ante => g.objects.filter (fun o => o.zone == .ante) |>.map (·.id)

/-- Every zone the demo tracks, in a stable print order. -/
def allZones (g : Game) : Array Zone :=
  Id.run do
    let mut zs : Array Zone := #[]
    for pl in g.players do
      zs := zs.push (.library pl.id)
      zs := zs.push (.hand pl.id)
      zs := zs.push (.graveyard pl.id)
    return zs.push .battlefield |>.push .stack |>.push .exile |>.push .command |>.push .ante

/-- Visible battlefield lines, including tap/combat/damage status (CR 110.5)
and summoning sickness on creatures (CR 302.6). -/
def battlefieldView (g : Game) : Array String :=
  g.battlefield.map (objectLine g)

/-- Permanents grouped by controller, in seat order (CR 110.2). Empty groups
are omitted. Permanents attached to another battlefield permanent are listed
with that host rather than in their own controller's group. Within each
controller, unattached permanents are split into unlabeled subgroups:
creatures, non-creature non-lands, then non-creature lands. Permanents with
no controller are listed last. The `Option PlayerId` is the group heading
(`none` = no controller). -/
def battlefieldGroups (g : Game) : Array (String × Option PlayerId × Array GameObject) :=
  Id.run do
    let mut groups : Array (String × Option PlayerId × Array GameObject) := #[]
    for pl in g.players do
      let ps := (g.permanentsOf pl.id).filter (fun o => !attachedToBattlefield g o)
      if !ps.isEmpty then
        groups := groups.push (pl.name, some pl.id, ps)
    let uncontrolled := g.battlefield.filter (fun o =>
      o.controller.isNone && !attachedToBattlefield g o)
    if !uncontrolled.isEmpty then
      groups := groups.push ("(no controller)", none, uncontrolled)
    return groups

/-- Shared-zone battlefield lines grouped under each controller's name.
Owner and controller are omitted on each permanent unless they differ from
the group heading. Attached permanents are indented under their host. -/
def battlefieldGroupLines (g : Game) : List String :=
  Id.run do
    let mut lines : Array String := #[]
    for (label, group, os) in battlefieldGroups g do
      lines := lines.push s!"{label}:"
      for line in battlefieldPermanentLines g os (some group) do
        lines := lines.push s!"  {line}"
    return lines.toList

/-- Zones whose occupants, order, visible status, or scry look differ between
two game states. Tapping or untapping a land does not move it, but it does
change the battlefield (CR 110.5 / 502.2), so the demo reprints that zone.
Starting or finishing a scry does not move library cards, but the scrying
player may look at the top cards (CR 701.20), so the demo reprints that
library. -/
def changedZones (before after : Game) : Array Zone :=
  (allZones after).filter (fun z =>
    match z with
    | .battlefield => battlefieldView before != battlefieldView after
    | .library p =>
      zoneObjectIds before z != zoneObjectIds after z ||
        scryLook before p != scryLook after p
    | _ => zoneObjectIds before z != zoneObjectIds after z)

def zoneLine (g : Game) (z : Zone) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o =>
    match z with
    | .hand _ => handLine g id
    | .battlefield => objectLine g o
    | .stack =>
      let ctrl :=
        match o.controller with
        | some p => s!" (controlled by {g.player p |>.name})"
        | none => ""
      s!"{o.id} {o.name}{stackFaceExtras o}{sourceClause g o}{ctrl}"
    | .exile =>
      let extra :=
        match o.playPermission with
        | some perm => s!" (may be played by {g.player perm.player |>.name})"
        | none => ""
      s!"{o.id} {o.name}{faceExtras o.printed}{extra}"
    | _ => s!"{o.id} {o.name}{faceExtras o.printed}"

/-- Current contents of `z`. Hidden zones show only their size (CR 400.2),
except that a scrying player (or omniscient view) sees the looked-at library
cards (CR 701.20). -/
def zoneBlock (g : Game) (z : Zone) (viewer : Option PlayerId := none) : String :=
  let ids := zoneObjectIds g z
  let shown :=
    match z with
    | .stack => ids.reverse
    | _ => ids
  let title := s!"zone {zoneLabel g z} ({shown.size})"
  match z with
  | .library owner =>
    let looked := scryLook g owner
    if looked.isEmpty || !canSeeScry viewer owner then
      title
    else
      let lines := looked.toList.map (scryCardLine g)
      title ++ ":\n  looking at (top last):\n  " ++ String.intercalate "\n  " lines
  | _ =>
    if !canSeeZoneFaces viewer z then
      title
    else if shown.isEmpty then
      s!"{title}: (empty)"
    else
      let lines :=
        match z with
        | .battlefield => battlefieldGroupLines g
        | _ => shown.toList.map (zoneLine g z)
      title ++ ":\n  " ++ String.intercalate "\n  " lines

end Mtg.Demo.Render
