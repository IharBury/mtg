import Mtg.Engine.Game.SpellTargets

/-!
# Total costs (CR 601.2f–h)

Finishing a proposed spell or ability, cast cost reductions
(CR 601.2f / 118.7), and activation mana costs including power-up
reductions.
-/

namespace Mtg.Engine
namespace Game

/-- Move `id` to `to`'s hand and log the return if it actually arrives in
`to`'s hand, deferring the log across `Pending.chooseReplacement`. -/
def returnToHand (g : Game) (id : ObjectId) (to : PlayerId)
    (cause : Option EventCause := none) (deferPlayFromExileLogs : Bool := false) : Game :=
  match g.findObject? id with
  | none => g
  | some o =>
    let name := g.name o
    let (g, _) := g.move id (.hand to) none (verb := some .returnToHand) (cause := cause)
      (deferPlayFromExileLogs := deferPlayFromExileLogs)
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.finishPostStep (.logReturnedToHand id to name))
    else if (g.followMovedToZone? id (· == .hand to)).isSome then
      g.logMsg s!"{name} is returned to {(g.player to).name}'s hand"
    else g

/-- Pay sneak: return an unblocked attacker you control to hand and mark
the spell. The creature enters tapped and attacking the same player. -/
def paySneak (g : Game) (p : PlayerId) (spellId : ObjectId) (attackerId : ObjectId) :
    Except String Game := do
  if !g.canCastForSneak p then
    throw "Sneak can be paid only during the declare blockers step on your turn"
  let some attacker := g.findObject? attackerId | throw "no such object"
  if !(attacker.isOnBattlefield && g.isCreature attacker && g.controlledBy attacker p) then
    throw s!"{g.name attacker} is not a creature you control"
  if !attacker.status.attacking then
    throw s!"{g.name attacker} is not attacking"
  if attacker.status.blocked then
    throw s!"{g.name attacker} is blocked"
  let defPlayer := g.defendingPlayerOf attacker
  let atkTarget := attacker.status.attackingTarget.getD (.player defPlayer)
  let some _spell := g.findObject? spellId | throw "The spell left the stack"
  let cause := some (EventCause.costPayment .returnToHand p (some spellId))
  let g := g.returnToHand attackerId attacker.owner (cause := cause)
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement
      (.finishPostStep (.finishPaySneak p spellId attackerId atkTarget cause))
  let g := g.record (GameEvent.announced g.turnNumber spellId
    (costs := #[.sneak attackerId atkTarget]) (cause := cause))
  return g.logMsg s!"{(g.player p).name} pays a sneak cost"

/-- Starting mana cost of `face` before increases and reductions (CR 118.7).
The flashback cost replaces the mana cost only for a cast actually made via Flashback
(CR 702.34a / 601.2b,f): `flashback := some b` states it explicitly (the caster
knows how the spell is being cast); otherwise a card still in a graveyard is assumed
to be cast via its flashback ability (the only way `castSpell` casts a non-free
graveyard card with flashback), and a spell already cast reads
`GameEvent.castWithFlashback` rather than any graveyard origin (so *Bilbo, Thief in
the Night*'s `mayCastFromGraveyard` pays the normal mana cost). -/
def playCostStart (g : Game) (card : GameObject) (face : CardDef)
    (flashback : Option Bool := none) : ManaCost :=
  let inGy := match card.zone with | .graveyard _ => true | _ => false
  if flashback.getD (inGy || GameEvent.castWithFlashback g.events card.id) then
    let kwFace := { face with keywords := g.currentKeywords card }
    kwFace.flashback.getD face.manaCost
  else face.manaCost

/-- Actual spell mana value of `card` cast as `face` (CR 118.9c / 202.3e / 702.37c). -/
def actualCastManaValue (g : Game) (card : GameObject) (face : CardDef) : Nat :=
  match g.actualPrintedManaCost? card face with
  | none => 0
  | some mc => (mc.substituteX (card.chosenX.getD 0)).manaValue

/-- Count spells matching `spellPred` already cast by `caster` this turn (CR 601.2i). -/
def countMatchingSpellsCastThisTurn (g : Game) (caster : PlayerId) (env : EvalEnv)
    (spellPred : ObjectPred) : Nat :=
  if spellPred == .hasType .creature then g.loggedCreatureSpells caster
  else
    g.events.foldl (fun acc e =>
      if e.turn != g.turnNumber then acc
      else
        match e.change with
        | .rules (.cast (.spellCast snap p _)) =>
          if p == caster && EvalExpr.evalObjectPred g env (.lki snap) spellPred then acc + 1
          else acc
        | _ => acc) 0

/-- Evaluate a `StaticAbility.costModifier`'s generic reduction or increase for `(card, face)`
(CR 601.2f / 118.7). -/
private def evalSpellCostMods (g : Game) (card : GameObject) (face : CardDef) (caster : PlayerId)
    (wantIncrease : Bool) : Nat :=
  let mv := g.actualCastManaValue card face
  let spellView := EvalExpr.spellFaceView g card face caster mv
  let selfEnv : EvalEnv :=
    { controller := caster, sourceId := some card.id, chosenX := card.chosenX.getD 0 }
  let isFaceDown := face.name == "" || (card.zone != .exile && card.status.faceDown)
  let spellObj : GameObject :=
    { card with
      printed := face
      zone := .stack
      controller := some caster
      status := { card.status with faceDown := isFaceDown } }
  let faceKws := g.currentKeywords spellObj
  let faceStatics := g.staticAbilities spellObj ++ (KeywordAbility.expandAll faceKws).staticAbilities
  let extractAmt (env : EvalEnv) : CostModification → Option Nat
    | .reduceGeneric amt => if !wantIncrease && !amt.mentionsTarget then some (EvalExpr.evalValue g env amt).toNat else none
    | .increaseGeneric amt => if wantIncrease && !amt.mentionsTarget then some (EvalExpr.evalValue g env amt).toNat else none
    | .alternativeFree => none
  let selfTotal :=
    faceStatics.foldl (fun acc ab =>
      match ab with
      | .costModifier cond? .thisSpell mod =>
        if !cond?.any Condition.mentionsTarget && cond?.all (EvalExpr.evalCondition g selfEnv) then
          acc + (extractAmt selfEnv mod).getD 0
        else acc
      | _ => acc) 0
  let peerTotal :=
    g.objects.foldl (fun acc o =>
      if !o.isOnBattlefield && o.zone != .command then acc
      else
        let srcCtrl := (g.controllerOf o).getD o.owner
        if !g.stillInGame srcCtrl then acc
        else
          let env : EvalEnv := { controller := srcCtrl, sourceId := some o.id }
          (g.staticAbilities o).foldl (fun acc ab =>
            match ab with
            | .costModifier cond? (.spells casterFilter spellPred nth? notFrom? activeZones) mod =>
              if activeZones.contains o.zone.kind &&
                  EvalExpr.matchesPlayerFilter g env casterFilter caster &&
                  notFrom?.all (fun zk => card.zone.kind != zk) &&
                  nth?.all (fun n => g.countMatchingSpellsCastThisTurn caster env spellPred + 1 == n) &&
                  cond?.all (EvalExpr.evalCondition g env) &&
                  EvalExpr.evalObjectPred g env spellView spellPred then
                acc + (extractAmt env mod).getD 0
              else acc
            | _ => acc) acc) 0
  selfTotal + peerTotal

/-- Apply cost reductions to `start` (CR 118.7 / 601.2f). Increases such as
kicker must already be included in `start`. -/
def applyCastCostReductions (g : Game) (card : GameObject) (face : CardDef)
    (start : ManaCost) (caster? : Option PlayerId := none) : ManaCost :=
  let caster := caster?.getD (card.controller.getD card.owner)
  let cardForCaster :=
    if card.controller.isSome then card else { card with controller := some caster }
  let start :=
    match card.chosenX with
    | none => start
    | some x => start.substituteX x
  let statRed := evalSpellCostMods g cardForCaster face caster false
  let (faceTypes, faceSups, _) := g.faceCdaCharacteristics cardForCaster face
  let thisTurnLess :=
    ((g.typeSpellCostLessThisTurn caster).foldl (fun acc (ty, n) =>
      if faceTypes.contains ty then acc + n else acc) 0) +
    ((g.supertypeSpellCostLessThisTurn caster).foldl (fun acc (s, n) =>
      if faceSups.contains s then acc + n else acc) 0)
  start.reduceGeneric (statRed + thisTurnLess)

/-- Mana to pay for `face` after alternative costs and pre-target reductions
(CR 118.7 / 118.9a,c / 601.2f). `withoutManaCost` and a reduction that removes
every mana symbol become `{0}`, not an unpayable empty cost (CR 107.4d / 202.1b).
Target-based reductions lock in after CR 601.2c. Cost increases (kicker, Thalia)
are applied before these reductions. -/
def playManaCost (g : Game) (card : GameObject) (face : CardDef)
    (increase : ManaCost := ManaCost.empty)
    (origPerm : Option PlayPermission := none)
    (flashback : Option Bool := none)
    (explicitAltCost : Bool := false)
    (useImplicitPermissions : Bool := true) : ManaCost :=
  let effPerm :=
    origPerm <|>
      (if !useImplicitPermissions then none
       else
         match card.controller with
         | some c => g.playPermissionFor? c card (face? := some face)
         | none => g.bestActivePlayPermission? card (face? := some face))
  let caster := card.controller.getD ((effPerm.map (·.player)).getD card.owner)
  let cardForCaster :=
    if card.controller.isSome then card else { card with controller := some caster }
  let hasAnyMana : Bool :=
    match effPerm with
    | some perm => perm.anyMana
    | none => useImplicitPermissions && card.zone == .exile && g.mayCastExiledBySource caster card
  -- Cost-increasing static abilities (Thalia, etc., CR 601.2f).
  let tax := evalSpellCostMods g cardForCaster face caster true
  let increase := if tax == 0 then increase else increase.addCost (ManaCost.ofGeneric tax)
  let inGy := match card.zone with | .graveyard _ => true | _ => false
  let kwFlashback? := ({ face with keywords := g.currentKeywords card }).flashback
  let hasPlayableFb :=
    kwFlashback?.any (fun mc => !mc.symbols.isEmpty) ||
      (g.flashbackUntilEot card && !face.manaCost.symbols.isEmpty)
  let usedFlashback :=
    hasPlayableFb && flashback.getD (inGy || GameEvent.castWithFlashback g.events card.id)
  let usedPermAlt := effPerm.any (fun pm => pm.withoutManaCost || pm.payLifeEqualManaValue)
  let printedMc? := g.actualPrintedManaCost? card face
  let usedMorph := printedMc?.isNone
  let usedSubstitutedAlt := printedMc?.any (fun mc => mc != face.manaCost)
  -- CR 118.9a: only one alternative cost can be applied to any one spell.
  let usedAltCost :=
    explicitAltCost || usedFlashback || usedPermAlt || usedMorph || usedSubstitutedAlt
  let start := g.playCostStart card face flashback
  let afterIncrease := start.addCost increase
  let afterEquip := g.applyCastCostReductions card face afterIncrease (caster? := some caster)
  let (faceTypes, _, faceCols) := g.faceCdaCharacteristics cardForCaster face
  let freeRG :=
    !usedAltCost &&
      match g.pendingFreeRGCreature with
      | some p =>
        caster == p && faceTypes.contains .creature &&
          (faceCols.contains .red || faceCols.contains .green)
      | none => false
  let cost :=
    if freeRG then
      let c := g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        (caster? := some caster)
      if hasAnyMana then c.asAnyMana else c
    else
      match effPerm with
      | some perm =>
        if (perm.withoutManaCost || perm.payLifeEqualManaValue) &&
            !(explicitAltCost || usedFlashback || usedMorph || usedSubstitutedAlt) then
          let c := g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
            (caster? := some caster)
          if perm.anyMana then c.asAnyMana else c
        else if perm.anyMana then afterEquip.asAnyMana
        else afterEquip
      | none =>
        -- Null Summoner: mana of any type can be spent when implicit exile permissions apply.
        if hasAnyMana then
          afterEquip.asAnyMana
        else afterEquip
  let mv := g.actualCastManaValue card face
  let spellView := EvalExpr.spellFaceView g cardForCaster face caster mv
  -- Omnipresence / free-cast-from-hand rule-modifying static abilities (CR 118.9a,c).
  let omnipresent :=
    !usedAltCost && !freeRG &&
      card.zone == .hand caster &&
      printedMc?.any (fun mc => !mc.containsX) &&
      g.battlefield.any (fun o =>
        let env : EvalEnv := { controller := (g.controllerOf o).getD o.owner, sourceId := some o.id }
        (g.staticAbilities o).any fun ab =>
          ab.anyRule fun cond? r =>
            match r with
            | .play (.mayPlayFrom who .hand pred _ _ _ true) =>
              EvalExpr.matchesPlayerFilter g env who caster &&
                cond?.all (EvalExpr.evalCondition g env) &&
                EvalExpr.evalObjectPred g env spellView pred
            | _ => false)
  let cost :=
    if omnipresent then
      let c := g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        (caster? := some caster)
      if hasAnyMana then c.asAnyMana else c
    else cost
  -- Self free alternative cost (e.g. Flawless Maneuver: if you control a commander, CR 118.9a).
  let selfEnv : EvalEnv :=
    { controller := caster, sourceId := some card.id, chosenX := card.chosenX.getD 0 }
  let isFaceDown := face.name == "" || (card.zone != .exile && card.status.faceDown)
  let spellObj : GameObject :=
    { card with
      printed := face
      zone := .stack
      controller := some caster
      status := { card.status with faceDown := isFaceDown } }
  let faceStatics := g.staticAbilities spellObj
  let freeSelf :=
    !usedAltCost && !freeRG && !omnipresent &&
      faceStatics.any fun ab =>
        match ab with
        | .costModifier cond? .thisSpell .alternativeFree =>
          !cond?.any Condition.mentionsTarget && cond?.all (EvalExpr.evalCondition g selfEnv)
        | _ => false
  let cost :=
    if freeSelf then
      let c := g.applyCastCostReductions card face (ManaCost.empty.addCost increase)
        (caster? := some caster)
      if hasAnyMana then c.asAnyMana else c
    else cost
  let hasPlayableAlt := usedAltCost || freeRG || omnipresent || freeSelf
  if face.manaCost.symbols.isEmpty && !hasPlayableAlt then
    ManaCost.empty
  else
    let origCost := if face.manaCost.symbols.isEmpty then ManaCost.zero else face.manaCost
    ManaCost.afterReduction origCost cost

/-- True when `face` has a mana cost that would not be paid to play `card`. -/
def playsWithoutPayingManaCost (g : Game) (card : GameObject)
    (face : CardDef := g.baseCard card) : Bool :=
  face.manaCost.includesManaPayment && !(g.playManaCost card face).includesManaPayment

end Game
end Mtg.Engine
