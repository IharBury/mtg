import Mtg.Engine.Game.Damage

/-!
# Pumps, grants, and counters (CR 613.4c / 122)

Until-end-of-turn pumps and keyword grants, +1/+1 counters and amass
(CR 701.47), finality counters, hand-size effects, improvise
(CR 702.126), boast, and sneak (MSH).
-/

namespace Mtg.Engine
namespace Game

/-- Until-end-of-turn +P/+T on `o` (CR 613.4c / 611.2a). `trample` also grants
trample until end of turn (e.g. Oliphaunt). -/
def pumpPermanent (g : Game) (o : GameObject) (p t : Int) (trample := false) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addPump p t
    if trample then s.grantUntilEot Keyword.trample else s)
  let gain := if trample then " and gains trample" else ""
  g.logMsg s!"{o.name} gets {signedStat p}/{signedStat t}{gain} until end of turn"

/-- Until-end-of-turn +P/+T on each creature `p` controls. -/
def pumpControlledCreatures (g : Game) (p : PlayerId) (pw tw : Int) : Game :=
  g.forEachControlledCreature p (fun g o => g.pumpPermanent o pw tw)

/-- Grant `kw` until end of turn to each creature `p` controls that matches `pred`. -/
def grantUntilEotToControlledCreatures (g : Game) (p : PlayerId) (kw : Keywords)
    (label : String) (pred : Game → GameObject → Bool := fun _ _ => true) : Game :=
  g.forEachControlledCreature p fun g o =>
    if pred g o then
      g.mapObjectStatus o (·.grantUntilEot kw)
        |>.logMsg s!"{o.name} gains {label} until end of turn"
    else g

/-- Grant each keyword in `kws` until end of turn, re-reading `o` after each. -/
def grantUntilEotKeywords (g : Game) (o : GameObject) (kws : List Keywords) : Game :=
  kws.foldl (fun g kw =>
    match g.findObject? o.id with
    | some o => g.mapObjectStatus o (·.grantUntilEot kw)
    | none => g) g

/-- Grant `k` until end of turn and log the standard “gains … until end of turn”. -/
def grantUntilEotLogged (g : Game) (o : GameObject) (k : Keywords) : Game :=
  g.mapObjectStatus o (·.grantUntilEot k)
    |>.logMsg s!"{o.name} gains {k} until end of turn"

/-- Set base P/T, optional creature types, and keywords until end of turn. -/
def setUntilEotForm (g : Game) (o : GameObject) (pt : Int × Int)
    (kws : Keywords) (msg : String)
    (types : Option (Array String) := none)
    (additionalCreature := false) (additionalArtifact := false)
    (pumpPerArtifact := false) : Game :=
  g.mapObjectStatus o (fun s =>
    { s with
      setBasePT := some pt
      replacedCreatureTypesUntilEot := types.orElse fun _ => s.replacedCreatureTypesUntilEot
      untilEotKeywords := Keywords.merge s.untilEotKeywords kws
      additionalCreatureUntilEot := additionalCreature || s.additionalCreatureUntilEot
      additionalArtifactUntilEot := additionalArtifact || s.additionalArtifactUntilEot
      pumpPerArtifactUntilEot := pumpPerArtifact || s.pumpPerArtifactUntilEot })
    |>.logMsg msg

/-- Move `id` to `to`'s hand and log the return. -/
def returnToHand (g : Game) (id : ObjectId) (to : PlayerId) : Game :=
  let name := (g.object! id).name
  let (g, _) := g.move id (.hand to) none
  g.logMsg s!"{name} is returned to {(g.player to).name}'s hand"

/-- Put `n` finality counters on `o` (MSH). Multiple counters are redundant. -/
def addFinalityTo (g : Game) (o : GameObject) (n : Nat := 1) : Game :=
  let n := g.extraCountersOn o.controller n
  let g := g.mapObjectStatus o (fun s => { s with finality := s.finality + n })
  g.logMsg s!"{o.name} gets a finality counter"

/-- Frozen in Ice, Enchanted River's Grasp, or Spider-Woman prevents this
permanent becoming untapped. -/
def hostCantBecomeUntapped (g : Game) (o : GameObject) : Bool :=
  let frozen :=
    g.battlefield.any (fun aura =>
      aura.attachedTo == some o.id &&
        aura.staticAbilities.any (fun
          | .enchantedLosesAbilitiesDoesntUntap => true
          | .enchantedLosesAbilitiesCantUntap => true
          | _ => false))
  let granted :=
    o.status.cantUntapGrantedBy.any (fun sid =>
      match g.findObject? sid with
      | some src => src.isOnBattlefield
      | none => false)
  frozen || granted

/-- Timestamp-ordered maximum hand size (MSH 184 / 376). `10000` is "no maximum". -/
def grantsNoMaxHandSize (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .noMaximumHandSize => true
    | _ => false)

def grantsMaxHandSizeTen (o : GameObject) : Bool :=
  o.printed.staticAbilities.any (fun
    | .maximumHandSize 10 => true
    | .maximumHandSize _ => false
    | _ => false)

def effectiveMaxHandSize (g : Game) (p : PlayerId) : Nat :=
  let effects :=
    ((g.permanentsOf p).filter (fun o =>
      grantsNoMaxHandSize o || grantsMaxHandSizeTen o)).qsort
      (fun a b => decide (a.timestamp < b.timestamp))
  effects.foldl (fun acc o =>
    if grantsMaxHandSizeTen o then 10
    else if grantsNoMaxHandSize o then 10000
    else acc) (g.player p).maxHandSize

/-- Reduce generic mana in `cost` by `n` (improvise taps artifacts for {1}). -/
def improviseReduce (cost : ManaCost) (n : Nat) : ManaCost :=
  cost.reduceGeneric n

/-- Whether `face` has improvise, including from a granting permanent. -/
def spellHasImprovise (g : Game) (face : CardDef) (caster : PlayerId) : Bool :=
  face.hasImprovise ||
    (!face.isCreature &&
      (g.permanentsOf caster).any (fun o => o.printed.grantsImproviseToNoncreature))

/-- Tap untapped artifacts you control for improvise. Each pays {1}. -/
def tapArtifactsForImprovise (g : Game) (p : PlayerId) (ids : Array ObjectId) :
    Except String Game := do
  let mut g := g
  let mut seen : Array ObjectId := #[]
  for id in ids do
    if seen.contains id then
      throw "An artifact cannot be tapped twice for the same improvise payment"
    seen := seen.push id
    let some o := g.findObject? id | throw "no such object"
    if !(o.isOnBattlefield && o.printed.isArtifact && o.controlledBy p) then
      throw s!"{o.name} is not an artifact you control"
    if o.status.tapped then
      throw s!"{o.name} is already tapped"
    g := g.becomeTapped o
  return g.logMsg s!"{(g.player p).name} taps {ids.size} artifact(s) for improvise"

/-- True when a boast ability of `o` may be activated (MSH / CR 702.111). -/
def canActivateBoast (_g : Game) (o : GameObject) : Bool :=
  o.printed.hasBoast && o.status.declaredAsAttackerThisTurn && !o.status.boastUsedThisTurn

/-- Mark a boast activation used for the turn. -/
def markBoastUsed (g : Game) (o : GameObject) : Game :=
  g.mapObjectStatus o (fun s => { s with boastUsedThisTurn := true })
    |>.logMsg s!"{o.name}'s boast ability is activated"

/-- Legal only during the declare blockers step of the caster's turn. -/
def canCastForSneak (g : Game) (p : PlayerId) : Bool :=
  g.activePlayer == p && g.step == .declareBlockers

/-- Pay sneak: return an unblocked attacker you control to hand and mark
the spell. The creature enters tapped and attacking the same player. -/
def paySneak (g : Game) (p : PlayerId) (spellId : ObjectId) (attackerId : ObjectId) :
    Except String Game := do
  if !g.canCastForSneak p then
    throw "Sneak can be paid only during the declare blockers step on your turn"
  let some attacker := g.findObject? attackerId | throw "no such object"
  if !(attacker.isOnBattlefield && attacker.isCreature && attacker.controlledBy p) then
    throw s!"{attacker.name} is not a creature you control"
  if !attacker.status.attacking then
    throw s!"{attacker.name} is not attacking"
  if attacker.status.blocked then
    throw s!"{attacker.name} is blocked"
  let whom := attacker.status.attackingWhom
  let some _spell := g.findObject? spellId | throw "The spell left the stack"
  let g := g.returnToHand attackerId attacker.owner
  let g := g.setObject { (g.object! spellId) with
    sneakPaid := true, sneakAttackWhom := whom }
  return g.logMsg s!"{(g.player p).name} pays a sneak cost"

/-- Equip worthy may attach only to a legendary non-Villain red or white
creature. Other attach effects ignore this restriction. -/
def isWorthyPermanent (_g : Game) (o : GameObject) : Bool :=
  o.isOnBattlefield && o.isCreature && o.printed.isWorthy

/-- Put `n` +1/+1 counters on `o` (CR 122.1). -/
def addPlusOnePlusOneTo (g : Game) (o : GameObject) (n : Nat := 1) : Game :=
  let n := g.extraCountersOn o.controller n
  let g := g.mapObjectStatus o (fun s =>
    { (s.addPlusOnePlusOne n) with gotPlusOneThisTurn := s.gotPlusOneThisTurn || n > 0 })
  let g := g.logMsg s!"{o.name} gets {plusOnePlusOneCountersPhrase n}"
  match o.controller with
  | none => g
  | some p =>
    let g :=
      if n > 0 then g.putControlledTriggers p .youPutPlusOne else g
    if n > 0 &&
        (g.hasSubtype o "Goblin" || g.hasSubtype o "Orc" || g.hasSubtype o "Army") then
      g.putControlledTriggers p .youPutCountersOnGoblinOrcArmy
    else g

/-- Amass `[subtype]` `n` (CR 701.43). If you control no Army, the token
enters as 0/0 and triggers see that power before counters are put on it. If
you control more than one Army, the newest is chosen (the player would
choose; tests use a single Army). -/
def amass (g : Game) (controller : PlayerId) (subtype : String) (n : Nat) : Game :=
  let armies := (g.permanentsOf controller).filter (fun o => g.hasSubtype o "Army")
  let createdFresh := armies.isEmpty
  let (g, army) :=
    match armies.toList with
    | [] => g.createToken controller (armyToken subtype)
    | x :: xs =>
      (g, xs.foldl (fun (best : GameObject) (o : GameObject) =>
        if o.timestamp ≥ best.timestamp then o else best) x)
  let g :=
    if createdFresh then
      let g := g.afterPermanentEnters (g.object! army.id)
      g.logMsg s!"the amassed Army entered as a 0/0 creature"
    else g
  let army := g.object! army.id
  let g :=
    if g.hasSubtype army subtype then g
    else
      g.mapObjectStatus army (fun s =>
        { s with additionalSubtypes := s.additionalSubtypes.push subtype })
  let army := g.object! army.id
  let g := g.addPlusOnePlusOneTo army n
  g.logMsg
    s!"{(g.player controller).name} amasses {subtype}s {n} ({army.name} is the amassed Army)"

/-- Amass Goblins `n` (CR 701.43). -/
def amassGoblins (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Goblin" n

/-- Amass Orcs `n` (CR 701.43). -/
def amassOrcs (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Orc" n

/-- Amass Zombies `n` (CR 701.43). -/
def amassZombies (g : Game) (controller : PlayerId) (n : Nat) : Game :=
  g.amass controller "Zombie" n

/-- +1/+1 counter plus trample and hexproof until end of turn. -/
def grantPlusOnePlusOneTrampleHexproof (g : Game) (o : GameObject) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    (s.addPlusOnePlusOne 1).grantUntilEot (Keyword.trample.merge Keyword.hexproof))
  g.logMsg
    s!"{o.name} gets a +1/+1 counter and gains trample and hexproof until end of turn"

/-- Damage plus until-EOT lose-indestructible and exile-if-dies (e.g. Smite). -/
def dealDamageLoseIndestructibleExileTo (g : Game) (o : GameObject) (n : Nat) : Game :=
  let g := g.mapObjectStatus o (fun s =>
    let s := s.addDamage n
    { s with
      untilEotLosesIndestructible := true
      untilEotExileIfDies := true })
  g.logMsg
    s!"{o.name} is dealt {n} damage, loses indestructible until end of turn, and will be exiled if it would die this turn"

/-- Until-end-of-turn “can't be blocked” (CR 509.1b / 611.2a). -/
def grantCantBeBlockedThisTurn (g : Game) (o : GameObject) : Game :=
  let g := g.mapObjectStatus o
    (·.grantUntilEot { Keywords.none with cantBeBlocked := true })
  g.logMsg s!"{o.name} can't be blocked this turn"

/-- Until-end-of-turn +P/+T and trample (e.g. Oliphaunt). -/
def pumpAndGrantTrample (g : Game) (o : GameObject) (p t : Int) : Game :=
  g.pumpPermanent o p t (trample := true)

end Game
end Mtg.Engine
