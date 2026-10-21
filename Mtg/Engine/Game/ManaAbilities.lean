import Mtg.Engine.Game.ActivationCosts

/-!
# Mana abilities (CR 605)

Every mana ability of a permanent as one definition: its cost, the mana it
can add, and how that mana may be spent (CR 106.10). Activating one adds
the mana immediately, without using the stack (CR 605.3b).
-/

namespace Mtg.Engine
namespace Game

abbrev ManaRestriction := Mtg.Engine.ManaRestriction

/-- The mana a mana ability adds (CR 106.1). -/
inductive ManaOutput where
  /-- Parameterized mana output: `fixed` (`!chooseType && !colorAmongFlag`), `oneOf` (`chooseType && !combinationFlag && !colorAmongFlag`), `combination` (`chooseType && combinationFlag && !colorAmongFlag`), or `colorAmong` (`colorAmongFlag`). -/
  | manaOutputKind (types : Array ManaType) (amount : Nat := 1)
      (chooseType : Bool := false) (combinationFlag : Bool := false) (colorAmongFlag : Bool := false)
deriving DecidableEq, Repr, Inhabited, BEq

/-- One mana of each color. -/
def anyColorMana : Array ManaType := (Color.all.map ManaType.colored).toArray

namespace ManaOutput

/-- Exactly these mana. -/
@[match_pattern] abbrev fixed (mana : Array ManaType) : ManaOutput :=
  .manaOutputKind mana 1 false false false
/-- `amount` mana of one type chosen from `types`. -/
@[match_pattern] abbrev oneOf (types : Array ManaType) (amount : Nat) : ManaOutput :=
  .manaOutputKind types amount true false false
/-- `amount` mana in any combination of `types`. -/
@[match_pattern] abbrev combination (types : Array ManaType) (amount : Nat) : ManaOutput :=
  .manaOutputKind types amount true true false
/-- One mana of a color among `allowed`; naming another color adds no mana
(Mox Amber, Arcane Signet). -/
@[match_pattern] abbrev colorAmong (allowed : Array ManaType) : ManaOutput :=
  .manaOutputKind allowed 1 false false true

/-- Mana types this output can include. -/
def types : ManaOutput → Array ManaType
  | .fixed m => m.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
  | .oneOf ts n | .combination ts n => if n == 0 then #[] else ts
  | .colorAmong _ => anyColorMana
  | _ => #[]

/-- The mana added when the player names `t`: all of it `t` where the
ability allows a choice. -/
def withType (out : ManaOutput) (t : ManaType) : Option (Array ManaType) :=
  match out with
  | .fixed m => if m.contains t then some m else none
  | .oneOf ts n | .combination ts n =>
    if ts.contains t then some (Array.replicate n t) else none
  | .colorAmong allowed =>
    match t with
    | .colored _ => some (if allowed.contains t then #[t] else #[])
    | .colorless => none
  | _ => none

/-- Whether the ability can add exactly `mana`. -/
def allows (out : ManaOutput) (mana : Array ManaType) : Bool :=
  let count (a : Array ManaType) (t : ManaType) := (a.filter (· == t)).size
  match out with
  | .fixed m => m.size == mana.size && m.all (fun t => count m t == count mana t)
  | .oneOf ts n =>
    mana.size == n &&
      (match mana[0]? with
       | some t => ts.contains t && mana.all (· == t)
       | none => true)
  | .combination ts n => mana.size == n && mana.all ts.contains
  | .colorAmong allowed => mana.isEmpty || (mana.size == 1 && mana.all allowed.contains)
  | _ => false

/-- How much mana this output adds. -/
def amount : ManaOutput → Nat
  | .fixed m => m.size
  | .oneOf _ n | .combination _ n => n
  | .colorAmong allowed => if allowed.isEmpty then 0 else 1
  | _ => 0

end ManaOutput

/-- A mana ability of a permanent (CR 605.1a). -/
structure ManaAbilityDef where
  output : ManaOutput
  tap : Bool := true
  cost : ManaCost := ManaCost.empty
  payLife : Nat := 0
  sacrificeSelf : Bool := false
  /-- Costs paid with objects the player chooses (Bolg's Company). -/
  picks : Array CostPick := #[]
  restriction : ManaRestriction := .none
  /-- Index among `activatedAbilitiesOf` when this is an activated ability
  printed with a full cost. -/
  activatedIdx : Option Nat := none
  onceEachTurn : Bool := false
  /-- Damage this ability deals to its controller as it resolves. -/
  damageYou : Nat := 0
deriving Inhabited

/-- How `.fra u` and the older restricted pool fields read a restriction
spelled out on a card. -/
def restrictionOfText (text : String) : ManaRestriction :=
  if text == "Dwarf, Equipment, and Saga spells" then .fra .dwarfEquipmentSagaSpell
  else .none

private def uniqMana (ts : Array ManaType) : Array ManaType :=
  ts.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]

/-- Mana a land can produce from its own printed abilities. “Could produce”
abilities are not included, so two such lands do not look at each other. -/
def intrinsicLandMana (g : Game) (o : GameObject) : Array ManaType :=
  let c := o.printed
  if !c.isLand && !c.grantLandsTapAnyColor then #[]
  else
    let p := o.controller.getD o.owner
    let fromAbility : Array ManaType :=
      match c.tapManaAbility with
      | .oneOf ts false _ 0 | .together ts "" | .twoAmong ts | .filter _ ts => ts
      | .commanderIdentity _ =>
        if (g.player p).hasCommander then
          ((g.player p).commanderColorIdentity.toList.map ManaType.colored).toArray
        else #[]
      | .anyColor .none _ => anyColorMana
      | _ => #[]
    let lantern :=
      if o.isOnBattlefield && c.isLand then
        match o.controller with
        | some q =>
          if (g.permanentsOf q).any (·.printed.grantLandsTapAnyColor) then anyColorMana
          else #[]
        | none => #[]
      else #[]
    uniqMana (c.simpleTapAddMana ++ fromAbility ++ lantern)

/-- Mana any of `lands` could produce from intrinsic abilities. -/
def landsCouldProduce (g : Game) (lands : Array GameObject) : Array ManaType :=
  uniqMana (lands.foldl (fun acc o => acc ++ g.intrinsicLandMana o) #[])

/-- Mana abilities from a card's printed `{T}: Add` lines, for `o`. -/
def cardManaAbilities (g : Game) (o : GameObject) (c : CardDef) : Array ManaAbilityDef :=
  let p := o.controller.getD o.owner
  let count (subtype : String) := ((g.permanentsOf p).filter (g.hasSubtype · subtype)).size
  let power := (g.power o).toNat
  let one (out : ManaOutput) (r : ManaRestriction := .none) : Array ManaAbilityDef :=
    #[{ output := out, restriction := r }]
  let simple := c.simpleTapAddMana.map (fun t =>
    ({ output := .fixed #[t]
       restriction := if t == .colorless && c.hasSubtype "Vibranium" then .cantNonartifact else .none }
      : ManaAbilityDef))
  let fromAbility : Array ManaAbilityDef :=
    match c.tapManaAbility with
    | .none => #[]
    | .oneOf ts enteredOrBasic damageYou payLife =>
      if ts.isEmpty || (enteredOrBasic && !g.canUseEnteredOrBasicAdd o) then #[]
      else #[{ output := .oneOf ts 1, payLife, damageYou }]
    | .together ts restriction =>
      if ts.isEmpty then #[]
      else one (.fixed ts) (if restriction.isEmpty then .none else restrictionOfText restriction)
    | .forEach entries =>
      entries.map (fun a =>
        ({ output := .fixed (Array.replicate (count a.subtype) a.mana) } : ManaAbilityDef))
    | .anyColor restriction sacrificeSelf =>
      #[{ output := .oneOf anyColorMana 1, sacrificeSelf, restriction }]
    | .anyColorEqualToPower => one (.oneOf anyColorMana power) .elf
    | .twoAmong ts =>
      if ts.size ≥ 2 then one (.combination ts 2) else #[]
    | .anyColorAmongLegendaries =>
      let legendaryColors :=
        (g.permanentsOf p).foldl (fun acc x =>
          if x.isLegendary && (x.isCreature || x.printed.isPlaneswalker) then
            ColorSet.union acc x.printed.colors
          else acc) ColorSet.empty
      one (.colorAmong (legendaryColors.toList.map ManaType.colored).toArray)
    | .commanderIdentity _ =>
      let pl := g.player p
      let identity := if pl.hasCommander then pl.commanderColorIdentity.toList else []
      one (.colorAmong (identity.map ManaType.colored).toArray)
    | .chosenColorPerDifferentPower =>
      one (.oneOf anyColorMana ((g.creaturesControlledBy p).map (g.power ·)).toList.eraseDups.length)
    | .filter cost ts =>
      let types := ts.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
      #[{ output := .combination types 2, cost, tap := true }]
    | .couldProduce opponentLands =>
      let lands :=
        if opponentLands then
          g.livingOpponents p |>.foldl (fun acc pl =>
            acc ++ (g.permanentsOf pl.id).filter (·.printed.isLand)) #[]
        else
          (g.permanentsOf p).filter (fun land => land.printed.isLand && land.id != o.id)
      #[{ output := .colorAmong (g.landsCouldProduce lands) }]
    | _ => #[]
  simple ++ fromAbility

/-- Mana abilities `o` has as printed activated abilities (CR 605.1a). Loyalty
abilities and targeted abilities are not mana abilities. -/
def activatedManaAbilities (g : Game) (o : GameObject) : Array ManaAbilityDef :=
  let abs := g.activatedAbilitiesOf o
  let power := (g.power o).toNat
  (List.range abs.size).toArray.filterMap (fun i =>
    let ab := abs[i]!
    if ab.effect.requiresTarget || ab.cost.loyalty.isSome then none
    else
      let base : ManaAbilityDef := {
        output := .fixed #[], tap := ab.cost.tap, cost := ab.cost.mana
        payLife := ab.cost.payLife, sacrificeSelf := ab.cost.sacrificeSource
        picks := costPicksOf ab, activatedIdx := some i, onceEachTurn := ab.onceEachTurn }
      let with_ (out : ManaOutput) (r : ManaRestriction := .none) :=
        some { base with output := out, restriction := r }
      match ab.effect.resolution with
      | .addMana #[.colored .blue] (.fixed 1) .cantNonartifact =>
        with_ (.fixed #[.colored .blue]) .cantNonartifact
      | .addMana types (.fixed 1) .none => with_ (.fixed types)
      | .addMana #[] (.fixed 1) .anyColor => with_ (.oneOf anyColorMana 1)
      | .addMana #[] (.fixed 1) (.subtypeSpellsOrAbilities s) =>
        with_ (.oneOf anyColorMana 1) (.subtypeSpellOrAbility s)
      | .addMana #[] (.fixed 1) .artifactSpell => with_ (.oneOf anyColorMana 1) (.fra .artifactSpell)
      | .addMana #[] (.fixed 2) .creatureSources => with_ (.oneOf anyColorMana 2) .creatureSource
      | .addMana #[] .equalSourcePower .anyColor => with_ (.oneOf anyColorMana power)
      | .addMana #[] (.fixed 4) .anyCombination => with_ (.combination anyColorMana 4)
      | .addMana #[] (.fixed 2) .equipment => with_ (.oneOf anyColorMana 2) (.fra .equipmentOrEquip)
      | _ => none)

/-- Mana abilities other permanents grant `o`, and Reality Fracture mana
abilities. -/
def grantedManaAbilityDefs (g : Game) (o : GameObject) : Array ManaAbilityDef :=
  let lords := g.grantedManaAbilities o
  let anyColor := anyColorMana.all lords.contains
  let granted : Array ManaAbilityDef :=
    if lords.isEmpty then #[]
    else if anyColor then #[{ output := .oneOf anyColorMana 1 }]
    else #[{ output := .oneOf lords 1 }]
  let fra := o.staticAbilities.foldl (fun acc ab =>
    match ab with
    | .tapAddColorlessNotFromHand =>
      acc.push { output := .fixed #[.colorless], restriction := .fra .notSpellsFromHand }
    | .tapAddAnyColorPlaneswalkerOnly =>
      acc.push { output := .oneOf anyColorMana 1, restriction := .fra .planeswalkerSpell }
    | .tapSacrificeAddThreeOfOneColor =>
      acc.push { output := .oneOf anyColorMana 3, sacrificeSelf := true }
    | .tapAddChosenColor =>
      match o.status.chosenColor with
      | some c => acc.push { output := .fixed #[.colored c] }
      | none => acc
    | _ => acc) (#[] : Array ManaAbilityDef)
  let emrakul : Array ManaAbilityDef :=
    if o.isOnBattlefield && !o.status.colorlessGrantUntilCast.isEmpty then
      #[{ output := .fixed #[.colorless, .colorless] }]
    else #[]
  let lantern : Array ManaAbilityDef :=
    if o.isOnBattlefield && o.printed.isLand then
      match o.controller with
      | some p =>
        if (g.permanentsOf p).any (·.printed.grantLandsTapAnyColor) then
          #[{ output := .oneOf anyColorMana 1 }]
        else #[]
      | none => #[]
    else #[]
  granted ++ fra ++ emrakul ++ lantern

/-- Every mana ability `o` has (CR 605.1a). -/
def manaAbilityDefs (g : Game) (o : GameObject) : Array ManaAbilityDef :=
  let own :=
    if !g.retainsPrintedAbilities o then #[]
    else
      g.cardManaAbilities o o.printed ++
        (g.copiedFromGy o (fun c => #[c])).foldl (fun acc c => acc ++ g.cardManaAbilities o c) #[]
  let defs := own ++ g.activatedManaAbilities o ++ g.grantedManaAbilityDefs o
  let treasure := g.hasSubtype o "Treasure"
  defs.map (fun d =>
    if treasure && d.restriction == .none then { d with restriction := .fra .fromTreasure } else d)

/-- Whether `d` can be activated by tapping alone, without choosing other
objects or paying mana (the `tap` shortcut and automatic payment). -/
def ManaAbilityDef.isPlainTap (d : ManaAbilityDef) : Bool :=
  d.tap && d.picks.isEmpty && !d.cost.includesManaPayment && d.payLife == 0

/-- Mana types `o` can add with plain `{T}` mana abilities. -/
def manaAbilitiesOf (g : Game) (o : GameObject) : Array ManaType :=
  (g.manaAbilityDefs o).foldl (fun acc d =>
    if d.isPlainTap then
      d.output.types.foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
    else acc) #[]

/-- Add `mana` to `p`'s pool with `r` (CR 106.4 / 106.10). -/
def addRestrictedMana (pool : ManaPool) (mana : Array ManaType) (r : ManaRestriction) :
    ManaPool :=
  mana.foldl (fun pool t =>
    match r with
    | .none => pool.add t
    | .only u => pool.addWithUse t u
    | _ => pool.add t) pool


/-- `p` may activate abilities of creatures they control as though those
creatures had haste (Shang-Chi, Master of Kung Fu; MSH 280). -/
def activatesAsThoughHaste (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any (fun o =>
    o.staticAbilities.any (fun
      | .activateCreaturesAsThoughHaste => true
      | _ => false))

/-- A player may activate mana abilities with priority, or while paying a
spell they are casting (CR 605.3a / 601.2g). -/
def canActivateManaAbility (g : Game) (p : PlayerId) : Bool :=
  if g.over then false
  else if g.hasPriority p then true
  else
    match g.pending with
    | .activateManaAbilities caster => caster == p
    | .mayPayGeneric q _ => q == p
    | .fraChoice q (.mayPayThen ..) | .fraChoice q (.mayPayExtort _)
    | .fraChoice q (.mayPayManaForReflexive ..) => q == p
    | .payOrLetCounter q _ _ => q == p
    | .payWard q _ cost =>
      q == p &&
        (match cost with
         | .genericMana _ | .discardOrPay _ => true
         | _ => false)
    | _ => false

/-- Activate mana ability `idx` of `id` (CR 605.3), adding `mana`, paying
choice costs with `costIds` in order. The mana is added immediately; the
ability doesn't use the stack (CR 605.3b). -/
def activateManaAbility (g : Game) (p : PlayerId) (id : ObjectId) (idx : Nat)
    (mana : Array ManaType) (costIds : Array ObjectId := #[]) : Except String Game := do
  if !g.canActivateManaAbility p then
    throw "You can't activate a mana ability now (CR 605.3a)"
  let some o := g.findObject? id | throw "no such object"
  if !o.controlledBy p || !o.isOnBattlefield then
    throw "You don't control that permanent"
  let some d := (g.manaAbilityDefs o)[idx]? | throw s!"{o.name} has no such mana ability"
  if !d.output.allows mana then
    throw s!"{o.name}'s mana ability can't add that mana"
  if d.tap then
    if o.status.tapped then
      throw s!"{o.name} is already tapped"
    if (match g.proposedSpell with
        | some prop => prop.tapSource && prop.sourceId == some id
        | none => false) then
      throw s!"{o.name} is needed to pay \{T}"
    if o.hasSummoningSickness && !g.hasHaste o && !(o.isCreature && g.activatesAsThoughHaste p) then
      throw s!"{o.name} has summoning sickness (CR 302.6)"
  if d.onceEachTurn && d.activatedIdx.any o.status.abilitiesActivatedThisTurn.contains then
    throw s!"{o.name}'s ability can be activated only once each turn"
  if !g.costPicksPayable p id d.picks then
    throw s!"{o.name}'s ability has a cost that can't be paid"
  let need := d.picks.foldl (fun acc pick => acc + pick.count) 0
  if costIds.size != need then
    throw s!"Choose what to {String.intercalate " and " (d.picks.map (·.phrase)).toList}"
  let pl := g.player p
  let pool ←
    if d.cost.includesManaPayment then
      match pl.manaPool.pay? d.cost (g.hasSubtype o "Elf") false (g.hasSubtype o "Hero")
          (g.hasSubtype o "Villain") true o.isCreature with
      | some pool => pure pool
      | none => throw s!"{pl.name} cannot pay {d.cost}"
    else pure pl.manaPool
  let mut g := g.setPlayer { pl with manaPool := pool }
  g ← g.payLifeCost p d.payLife
  let mut rest := costIds
  for pick in d.picks do
    g ← g.payCostPick p id id pick (rest.extract 0 pick.count)
    rest := rest.extract pick.count rest.size
  if d.tap then
    g := g.becomeTapped (g.object! id)
  let src := g.object! id
  if d.sacrificeSelf then
    g := g.sacrificeToGraveyard src s!"{(g.player p).name} sacrifices {src.name}"
  match d.activatedIdx with
  | some i =>
    match g.findObject? id with
    | some x =>
      g := g.setObject { x with status := { x.status with
        activationsThisTurn := x.status.activationsThisTurn + 1
        abilitiesActivatedThisTurn := x.status.abilitiesActivatedThisTurn.push i } }
    | none => pure ()
  | none => pure ()
  g := g.modifyPlayer p (fun pl => { pl with manaPool := addRestrictedMana pl.manaPool mana d.restriction })
  if d.damageYou > 0 then
    let before := (g.player p).life
    g := g.setLife p (before - (d.damageYou : Int))
      s!"{o.name} deals {d.damageYou} damage to {(g.player p).name}"
    let lost := (before - (g.player p).life).toNat
    g := g.afterLifeLost p lost
  -- Molten Tide: a triggered mana ability that resolves immediately (CR 605.4a).
  let extraRed :=
    if g.hasSubtype o "Mountain" && d.tap && !mana.isEmpty then
      (g.player p).mountainExtraRedThisTurn
    else 0
  if extraRed > 0 then
    g := (g.modifyPlayer p (fun pl =>
      { pl with manaPool := pl.manaPool.add (.colored .red) extraRed })).logMsg
      (s!"{(g.player p).name} adds an additional " ++ String.join (List.replicate extraRed "{R}"))
  let produced :=
    match mana[0]? with
    | some t =>
      if !mana.all (· == t) then String.intercalate ", " (mana.toList.map toString)
      else if mana.size == 1 then toString t
      else s!"{t} ×{mana.size}"
    | none => ""
  let verb := if d.tap then "taps" else "activates"
  g :=
    if mana.isEmpty then g.logMsg s!"{(g.player p).name} {verb} {o.name} but adds no mana"
    else g.logMsg s!"{(g.player p).name} {verb} {o.name} for {produced}{d.restriction.note}"
  if d.tap then
    g := match g.proposedSpell with
      | some prop =>
        let g := { g with proposedSpell := some { prop with tapped := prop.tapped.push id } }
        if o.printed.commanderIdentityScryCreature then
          { g with ancestryLandsTapped := g.ancestryLandsTapped.push id }
        else g
      | none => g
  if o.isCreature then
    g := g.putControlledTriggers p .youActivateCreatureAbility
  return { g with consecutivePasses := 0 }

/-- Index of the first mana ability of `o` that can add `mana` by tapping
alone, or with only mana and life costs when `plainOnly` is false. -/
def manaAbilityIndexFor (g : Game) (o : GameObject) (mana : ManaType) (plainOnly : Bool := true) :
    Option Nat :=
  let defs := g.manaAbilityDefs o
  (List.range defs.size).find? (fun i =>
    let d := defs[i]!
    (if plainOnly then d.isPlainTap else d.picks.isEmpty) && (d.output.withType mana).isSome)

/-- Tap `id` for `mana` with the first mana ability that can add it
(CR 605.3). Abilities that need other choices use `activateManaAbility`. -/
def tapForMana (g : Game) (p : PlayerId) (id : ObjectId) (mana : ManaType) : Except String Game := do
  let some o := g.findObject? id | throw "no such object"
  if o.printed.tapAddOneOfIfEnteredOrBasic.contains mana && !g.canUseEnteredOrBasicAdd o then
    throw s!"{o.nameWithToken}'s colored mana ability can be activated only if this land entered this turn or if you control a basic land"
  let some i := g.manaAbilityIndexFor o mana false
    | throw s!"{o.nameWithToken} cannot produce {mana}"
  let some d := (g.manaAbilityDefs o)[i]? | throw s!"{o.nameWithToken} cannot produce {mana}"
  let some added := d.output.withType mana | throw s!"{o.nameWithToken} cannot produce {mana}"
  g.activateManaAbility p id i added

/-- Mana `o` adds when tapped for `mana` with a plain `{T}` ability. -/
def manaFromTap (g : Game) (o : GameObject) (mana : ManaType) : Nat :=
  match g.manaAbilityIndexFor o mana with
  | some i =>
    match (g.manaAbilityDefs o)[i]? with
    | some d => ((d.output.withType mana).map (·.size)).getD 0
    | none => 0
  | none => 0

/-- Restriction on mana `o` adds when tapped for `mana` with a plain `{T}`
ability. -/
def tapRestrictionOf (g : Game) (o : GameObject) (mana : ManaType) : ManaRestriction :=
  match g.manaAbilityIndexFor o mana with
  | some i => ((g.manaAbilityDefs o)[i]?.map (·.restriction)).getD .none
  | none => .none

end Game
end Mtg.Engine
