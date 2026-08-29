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

/-- Identity of a target for stack listings (CR 115). Players print by
seat name; objects use `objectRef`. -/
def targetRef (g : Game) : Target → String
  | .player pid => (g.player pid).name
  | .permanent oid | .card oid => objectRef g oid

/-- One announced target, with divided damage when that was chosen (CR 601.2d). -/
def describeStackTarget (g : Game) (e : StackEntry) (i : Nat) : String :=
  let name := targetRef g (e.targets[i]!)
  match e.dividedDamage[i]? with
  | some n => s!"{name} for {n}"
  | none => name

/-- True when every announced target of `e` belongs to one instance of the
word “target” (chosen together) rather than successive instances. -/
def targetsShareOneTargetWord (g : Game) (e : StackEntry) : Bool :=
  match g.findObject? e.objectId with
  | some o => (g.targetingOf o).kind.spec.slots.isEmpty
  | none => true

/-- Join same-instance targets with `and`; successive “target” words with
`; then`. -/
def targetListSeparator (g : Game) (e : StackEntry) : String :=
  if targetsShareOneTargetWord g e then " and " else "; then "

/-- Announced targets of a stack object (CR 115 / 601.2c). Nothing prints
until a target is chosen; choosing none prints `*no target*` (CR 603.3d).
Several targets of one “target” word are listed with `and`; each further
instance is listed after `; then`. -/
def targetClause (g : Game) (e : StackEntry) : String :=
  if e.targets.isEmpty then
    if e.targetsAnnounced then " *no target*" else ""
  else
    Id.run do
      let mut refs : Array String := #[]
      for i in [0:e.targets.size] do
        refs := refs.push (describeStackTarget g e i)
      return s!" *targeting {String.intercalate (targetListSeparator g e) refs.toList}*"

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

/-- One object on the stack, including announced targets (CR 115 / 601.2c).
`withId` prefixes the object id, matching zone listings and `state`. -/
def stackObjectLine (g : Game) (e : StackEntry) (withId : Bool := true) : String :=
  match g.findObject? e.objectId with
  | none => if withId then s!"{e.objectId} (missing)" else "(missing)"
  | some o =>
    let id := if withId then s!"{o.id} " else ""
    s!"{id}{o.name}{stackFaceExtras o}{targetClause g e}{sourceClause g o} (controlled by {g.player e.controller |>.name})"

/-- Like `faceExtras`, but includes keywords granted by other permanents. -/
def objectFaceExtras (g : Game) (o : GameObject) : String :=
  let s := o.printed.keywordsAndAbilitiesOf (g.effectiveKeywords o)
  if s.isEmpty then "" else s!" {s}"

/-- Player who would activate `o`'s abilities (controller, else owner). -/
def abilityActivator (o : GameObject) : PlayerId :=
  o.controller.getD o.owner

/-- Parenthetical when `o` can be played or an ability can be activated
without paying mana (CR 118.7). Play-from-exile permissions are rendered
separately by `exilePlayPermissionClause`. -/
def withoutPayingManaClause (g : Game) (o : GameObject) : String :=
  let play :=
    match o.playPermission with
    | some _ => ""
    | none =>
      if g.playsWithoutPayingManaCost o then
        " (may be cast without paying its mana cost)"
      else ""
  let activate :=
    if (g.activatedAbilitiesOf o).any (g.activatesWithoutPayingManaCost (abilityActivator o))
    then " (may be activated without paying its mana cost)"
    else ""
  play ++ activate

/-- Permanent that linked-exiled `o` until it leaves the battlefield (CR 610.3). -/
def linkedExileSource? (g : Game) (o : GameObject) : Option GameObject :=
  g.battlefield.find? (fun src => src.linkedExile.contains o.id)

/-- Cards `o` has exiled until it leaves that are still in exile (CR 610.3). -/
def linkedExiledCards (g : Game) (o : GameObject) : Array GameObject :=
  o.linkedExile.filterMap (fun id =>
    match g.findObject? id with
    | some e => if e.zone == .exile then some e else none
    | none => none)

/-- Battlefield marker for cards this permanent has linked-exiled (CR 610.3). -/
def linkedExileClause (g : Game) (o : GameObject) : String :=
  let cards := linkedExiledCards g o
  if cards.isEmpty then ""
  else
    let refs := cards.toList.map (fun e => objectRef g e.id)
    s!" *exiling {String.intercalate ", " refs}*"

/-- Exile marker naming the permanent that must leave for `o` to return (CR 610.3). -/
def exileUntilLeavesClause (g : Game) (o : GameObject) : String :=
  match linkedExileSource? g o with
  | some src => s!" *exiled until {objectRef g src.id} leaves the battlefield*"
  | none => ""

/-- Battlefield line for one permanent: id, name, current type line (CR 205.1a),
P/T when it is a creature, then keywords, control, status, and cards it has
exiled until it leaves (CR 610.3). -/
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
  let linked := linkedExileClause g o
  let dmg :=
    if o.status.damage > 0 then s!" dmg:{o.status.damage}" else ""
  let exileIfDies :=
    if o.status.untilEotExileIfDies then " *exile if dies*" else ""
  let counters :=
    if o.status.plusOnePlusOne > 0 then s!" +1/+1×{o.status.plusOnePlusOne}" else ""
  s!"{o.id} {o.name}{types}{pt}{counters}{objectFaceExtras g o}{withoutPayingManaClause g o}{controlClause g o group}{tap}{sick}{atk}{blk}{ench}{linked}{dmg}{exileIfDies}"

/-- Printed face of a card in hand, graveyard, or exile: object id plus Oracle
summary (mana cost, type line, P/T, keywords and abilities). Lands omit a
mana cost rather than printing `{0}` (CR 202.1b / 118.6). -/
def printedCardLine (o : GameObject) : String :=
  s!"{o.id} {o.printed.summary}"

def handLine (g : Game) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o => s!"{printedCardLine o}{withoutPayingManaClause g o}"

/-- Printed mana cost to play `o` from exile when someone has permission.
Lands and other cards with no mana cost omit it rather than printing `{0}`
(CR 202.1b / 118.6). A granted “without paying its mana cost” permission
prints `{0}` (CR 107.4d / 118.7). -/
def exilePlayManaCost (o : GameObject) : String :=
  match o.playPermission with
  | some perm =>
    if perm.withoutManaCost && o.printed.manaCost.includesManaPayment then
      toString ManaCost.zero
    else
      toString o.printed.manaCost
  | none => ""

/-- Who may play `o` from exile, if anyone (CR 701.14 / 715.3d), including
when the permission replaces the mana cost with `{0}`. -/
def exilePlayPermissionClause (g : Game) (o : GameObject) : String :=
  match o.playPermission with
  | some perm =>
    let free :=
      if perm.withoutManaCost then " without paying its mana cost" else ""
    s!" (may be played by {g.player perm.player |>.name}{free})"
  | none => ""

/-- One card in exile: printed face (mana cost, type line, P/T), a granted play
permission if any, and a linked-exile return condition (CR 610.3) if any. -/
def exileLine (g : Game) (o : GameObject) : String :=
  s!"{printedCardLine o}{exilePlayPermissionClause g o}{exileUntilLeavesClause g o}"

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

/-- One shared battlefield for the board snapshot, grouped by controller. -/
def battlefieldBlock (g : Game) : String :=
  let n := g.battlefield.size
  let title := s!"Battlefield ({n})"
  let lines := battlefieldGroupLines g
  if lines.isEmpty then s!"{title}: (empty)"
  else title ++ ":\n  " ++ String.intercalate "\n  " lines

/-- Per-player private and graveyard information. The shared battlefield is
rendered separately by `battlefieldBlock`. -/
def playerBlock (g : Game) (pl : Player) (viewer : Option PlayerId := none) : String :=
  let marker := if pl.id == g.activePlayer then " (active)" else ""
  let handText :=
    if canSeeZoneFaces viewer (.hand pl.id) then
      let hand := pl.hand.toList.map (handLine g)
      if hand.isEmpty then "  (empty)" else String.intercalate "\n  " hand
    else
      "  (hidden)"
  let gy := pl.graveyard.toList.map (handLine g)
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
     s!"  Graveyard ({pl.graveyard.size}):",
     "  " ++ gyText])

def stackBlock (g : Game) : String :=
  if g.stack.isEmpty then "Stack: (empty)"
  else
    let lines := g.stack.toList.reverse.map (fun e => s!"  {stackObjectLine g e true}")
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

/-- Names of legal combat-damage recipients for `source`, including the
defending player when unblocked or trampling (CR 510.1a–d / 702.19). -/
def combatDamageTargetRefs (g : Game) (source : GameObject) (forAttackers : Bool) :
    List String :=
  let creatures :=
    (g.legalCombatDamageRecipients source forAttackers).toList.map (fun o =>
      objectRef g o.id)
  if g.canAssignCombatDamageToDefendingPlayer source forAttackers then
    creatures ++ [(g.player (g.opponent g.activePlayer)).name]
  else creatures

/-- One assigning creature: how much damage it must assign and to whom. -/
def combatDamageSourceLine (g : Game) (source : GameObject) (forAttackers : Bool) :
    String :=
  let dmg := g.combatDamageToAssign source forAttackers
  let targets := combatDamageTargetRefs g source forAttackers
  if targets.isEmpty then
    let why :=
      if forAttackers then "no remaining blockers" else "not blocking any creatures"
    s!"{objectRef g source.id} assigns no combat damage ({why})"
  else
    s!"{objectRef g source.id} assigns {dmg}; legal: {String.intercalate ", " targets}"

/-- Snapshot section listing combat damage each creature must assign and the
legal recipients, while a player is announcing CR 510.1. -/
def combatDamageAssignmentBlock (g : Game) : Option String :=
  match g.pending with
  | .assignCombatDamage _ forAttackers =>
    let lines :=
      (g.creaturesAssigningCombatDamage forAttackers).toList.map (fun o =>
        s!"  {combatDamageSourceLine g o forAttackers}")
    if lines.isEmpty then none
    else some ("Assign combat damage:\n" ++ String.intercalate "\n" lines)
  | _ => none

/-- Snapshot section listing which legendary permanents a player may keep
under the legend rule (CR 704.5j). -/
def legendRuleBlock (g : Game) : Option String :=
  match g.pending with
  | .chooseLegend p name ids =>
    let lines :=
      ids.toList.filterMap (fun id =>
        match g.findObject? id with
        | some o => some s!"  {objectRef g o.id}"
        | none => none)
    if lines.isEmpty then none
    else
      some <|
        s!"{(g.player p).name} chooses which {name} to keep (CR 704.5j):\n" ++
          String.intercalate "\n" lines
  | _ => none

/-- One waiting triggered ability: source id (for `stack`), name, and text. -/
def waitingTriggerLine (wt : WaitingTrigger) : String :=
  let text := textForStackedAbility wt.source.printed (TriggeredAbility.toNotation wt.ability)
  s!"{wt.source.id} {wt.source.name} {text}"

/-- Snapshot section listing waiting triggered abilities a player must put
on the stack in an order they choose (CR 603.3b). -/
def triggerOrderBlock (g : Game) : Option String :=
  match g.pending with
  | .chooseTriggerToStack p =>
    let lines :=
      (g.waitingTriggersOf p).toList.map (fun wt => s!"  {waitingTriggerLine wt}")
    if lines.isEmpty then none
    else
      some <|
        s!"{(g.player p).name} chooses the order of triggered abilities (CR 603.3b):\n" ++
          String.intercalate "\n" lines
  | _ => none

/-- Pending prompt while announcing targets (CR 601.2c). Several targets of
one instance of the word “target” are chosen together; each further
instance is a later announcement. -/
def chooseTargetsPending (g : Game) (p : PlayerId) : String :=
  let name := (g.player p).name
  match g.objectAwaitingTargets with
  | none => s!" [choose targets (CR 601.2c, {name})]"
  | some o =>
    let kind := (g.targetingOf o).kind
    let maxN := (g.announcedTargetBounds o).2
    if (o.triggeredAbility.bind TriggeredAbility.dividedDamage?).isSome ||
        (kind.spec.slots.isEmpty && maxN > 1) then
      s!" [choose targets of this \"target\" word together (CR 601.2c, {name})]"
    else if !kind.spec.slots.isEmpty then
      let slotIdx := g.currentTargetSlot o
      let slotNoun := kind.announcedNoun slotIdx
      if slotIdx == 0 then
        s!" [choose the first \"target\" word ({slotNoun}, CR 601.2c, {name})]"
      else
        s!" [choose the next \"target\" word ({slotNoun}, CR 601.2c, {name})]"
    else
      s!" [choose targets (CR 601.2c, {name})]"

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
      chooseTargetsPending g p
    | .sacrificePermanent p _ =>
      s!" [sacrifice a creature or artifact ({g.player p |>.name})]"
    | .sacrificeCreature p =>
      s!" [sacrifice a creature ({g.player p |>.name})]"
    | .declareMulligan p =>
      s!" [mulligan: {g.player p |>.name} may keep or mulligan (CR 103.5)]"
    | .putOnBottom p n =>
      let cards := if n == 1 then "1 card" else s!"{n} cards"
      s!" [mulligan: {g.player p |>.name} puts {cards} on the bottom (CR 103.5)]"
    | .scry p n =>
      s!" [scry {n} ({g.player p |>.name})]"
    | .mayDiscardDraw p n =>
      s!" [may discard a card, then draw {n} ({g.player p |>.name})]"
    | .chooseAdditionalCost p =>
      s!" [choose an additional cost (CR 601.2b, {g.player p |>.name})]"
    | .chooseSacrificeCreature p _ _ =>
      s!" [sacrifice a creature ({g.player p |>.name})]"
    | .chooseDiscardCard p _ =>
      s!" [discard a card ({g.player p |>.name})]"
    | .assignCombatDamage p true =>
      s!" [assign combat damage (CR 510.1c, {g.player p |>.name})]"
    | .assignCombatDamage p false =>
      s!" [assign combat damage (CR 510.1d, {g.player p |>.name})]"
    | .chooseLegend p name _ =>
      s!" [legend rule: {g.player p |>.name} keeps one {name} (CR 704.5j)]"
    | .chooseTriggerToStack p =>
      s!" [choose trigger order (CR 603.3b, {g.player p |>.name})]"
    | .mayPayGeneric p n =>
      s!" [may pay \{{n}} ({g.player p |>.name})]"
    | .chooseLibraryPlacement p _ =>
      s!" [choose top or bottom ({g.player p |>.name})]"
    | .mayAttachEquipment p _ =>
      s!" [may attach Equipment ({g.player p |>.name})]"
    | .tapHumans p =>
      s!" [tap Humans ({g.player p |>.name})]"
    | .payOrLetCounter p n _ =>
      s!" [pay \{{n}} or let the spell be countered ({g.player p |>.name})]"
    | .recruitDiscard p =>
      s!" [recruit: discard a card ({g.player p |>.name})]"
    | .chooseKicker p =>
      s!" [announce kicker (CR 702.32, {g.player p |>.name})]"
    | .chooseGift p =>
      s!" [announce gift (CR 702.185, {g.player p |>.name})]"
    | .chooseRingBearer p =>
      s!" [choose a Ring-bearer ({g.player p |>.name})]"
    | .maySacrificeAnotherBolg p _ =>
      s!" [may sacrifice another creature ({g.player p |>.name})]"
    | .resolveRandom req =>
      match req with
      | .shuffleLibrary p =>
        s!" [shuffle {(g.player p).name}'s library (--norandom)]"
      | .orderInto _ dest =>
        let destName :=
          match dest with
          | .library p => s!"{(g.player p).name}'s library"
          | .hand p => s!"{(g.player p).name}'s hand"
          | .graveyard p => s!"{(g.player p).name}'s graveyard"
          | .battlefield => "the battlefield"
          | .stack => "the stack"
          | .exile => "exile"
          | .command => "command"
          | .ante => "ante"
        s!" [supply a random order into {destName} (--norandom)]"
      | .chooseObject _ =>
        " [pick the randomly chosen object (--norandom)]"
      | .chooseIndex n =>
        if n == 2 then " [coin toss (--norandom)]"
        else s!" [random index 0..{n - 1} (--norandom)]"
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
      let lines := exiled.toList.map (fun o => s!"  {exileLine g o}")
      ["Exile:\n" ++ String.intercalate "\n" lines]
  let cost :=
    match costBlock g with
    | some line => [line]
    | none => []
  let assign :=
    match combatDamageAssignmentBlock g with
    | some block => [block]
    | none => []
  let legend :=
    match legendRuleBlock g with
    | some block => [block]
    | none => []
  let triggerOrder :=
    match triggerOrderBlock g with
    | some block => [block]
    | none => []
  String.intercalate "\n\n"
    (header g viewer :: cost ++ assign ++ legend ++ triggerOrder ++
      [stackBlock g, battlefieldBlock g] ++ players ++ exileBlock)

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

/-- Visible stack lines, including announced targets (CR 115 / 601.2c). -/
def stackView (g : Game) : Array String :=
  g.stack.map (fun e => stackObjectLine g e true)

/-- Zones whose occupants, order, visible status, or scry look differ between
two game states. Tapping or untapping a land does not move it, but it does
change the battlefield (CR 110.5 / 502.2), so the demo reprints that zone.
Announcing or changing targets does not move a spell or ability, but it does
change the stack (CR 115 / 601.2c), so the demo reprints that zone.
Starting or finishing a scry does not move library cards, but the scrying
player may look at the top cards (CR 701.20), so the demo reprints that
library. -/
def changedZones (before after : Game) : Array Zone :=
  (allZones after).filter (fun z =>
    match z with
    | .battlefield => battlefieldView before != battlefieldView after
    | .stack => stackView before != stackView after
    | .library p =>
      zoneObjectIds before z != zoneObjectIds after z ||
        scryLook before p != scryLook after p
    | _ => zoneObjectIds before z != zoneObjectIds after z)

def zoneLine (g : Game) (z : Zone) (id : ObjectId) : String :=
  match g.findObject? id with
  | none => s!"{id} (missing)"
  | some o =>
    match z with
    | .hand _ | .graveyard _ => handLine g id
    | .battlefield => objectLine g o
    | .stack =>
      match g.stack.find? (fun e => e.objectId == o.id) with
      | some e => stackObjectLine g e true
      | none => s!"{o.id} {o.name}{stackFaceExtras o}{sourceClause g o}"
    | .exile => exileLine g o
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
