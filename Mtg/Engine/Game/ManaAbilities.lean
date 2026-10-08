import Mtg.Engine.Game.ActivationCosts

/-!
# Mana abilities (CR 605)

Every mana ability of a permanent as one definition: its cost, the mana it
can add, and how that mana may be spent (CR 106.10). Activating one adds
the mana immediately, without using the stack (CR 605.3b).
-/

namespace Mtg.Engine
namespace Game

/-- How mana from a mana ability may be spent (CR 106.10). -/
inductive ManaRestriction where
  | none
  | elf
  | instantOrSorcery
  | hero
  | villain
  | cantNonartifact
  | creatureSource
  | fra (u : FraManaUse)
deriving DecidableEq, Repr, Inhabited, BEq

/-- The mana a mana ability adds (CR 106.1). -/
inductive ManaOutput where
  /-- Exactly these mana. -/
  | fixed (mana : Array ManaType)
  /-- `amount` mana of one type chosen from `types`. -/
  | oneOf (types : Array ManaType) (amount : Nat)
  /-- `amount` mana in any combination of `types`. -/
  | combination (types : Array ManaType) (amount : Nat)
  /-- One mana of a color among `allowed`; naming another color adds no mana
  (Mox Amber, Arcane Signet). -/
  | colorAmong (allowed : Array ManaType)
deriving DecidableEq, Repr, Inhabited, BEq

/-- One mana of each color. -/
def anyColorMana : Array ManaType := (Color.all.map ManaType.colored).toArray

namespace ManaOutput

/-- Mana types this output can include. -/
def types : ManaOutput → Array ManaType
  | .fixed m => m.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
  | .oneOf ts n | .combination ts n => if n == 0 then #[] else ts
  | .colorAmong _ => anyColorMana

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

/-- How much mana this output adds. -/
def amount : ManaOutput → Nat
  | .fixed m => m.size
  | .oneOf _ n | .combination _ n => n
  | .colorAmong allowed => if allowed.isEmpty then 0 else 1

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
    let identity :=
      if c.tapAddCommanderIdentity && (g.player p).hasCommander then
        ((g.player p).commanderColorIdentity.toList.map ManaType.colored).toArray
      else #[]
    let pain :=
      match c.tapAddOneOfDealsDamage with
      | some (ts, _) => ts
      | none => #[]
    let filter :=
      match c.filterMana with
      | some (_, ts) => ts
      | none => #[]
    let any :=
      if c.tapAddAnyColor || c.tapSacrificeAddAnyColor then anyColorMana else #[]
    let lantern :=
      if o.isOnBattlefield && c.isLand then
        match o.controller with
        | some q =>
          if (g.permanentsOf q).any (·.printed.grantLandsTapAnyColor) then anyColorMana
          else #[]
        | none => #[]
      else #[]
    uniqMana (c.simpleTapAddMana ++ c.tapAddOneOf ++ c.tapAddTogether ++
      pain ++ filter ++ identity ++ any ++ lantern ++ c.tapAddTwoAmong)

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
  let legendaryColors :=
    (g.permanentsOf p).foldl (fun acc x =>
      if x.isLegendary && (x.isCreature || x.printed.isPlaneswalker) then
        ColorSet.union acc x.printed.colors
      else acc) ColorSet.empty
  let pl := g.player p
  let identity := if pl.hasCommander then pl.commanderColorIdentity.toList else []
  simple ++
  (if c.tapAddOneOf.isEmpty then #[] else one (.oneOf c.tapAddOneOf 1)) ++
  c.tapAddManaForEach.map (fun a =>
    ({ output := .fixed (Array.replicate (count a.subtype) a.mana) } : ManaAbilityDef)) ++
  (if c.tapAddOneOfIfEnteredOrBasic.isEmpty || !g.canUseEnteredOrBasicAdd o then #[]
   else one (.oneOf c.tapAddOneOfIfEnteredOrBasic 1)) ++
  (if c.tapAddAnyColorEqualToPower then one (.oneOf anyColorMana power) .elf else #[]) ++
  (if c.tapAddAnyColorForInstantOrSorcery then
    one (.oneOf anyColorMana 1) .instantOrSorcery else #[]) ++
  (if c.tapAddAnyColor then one (.oneOf anyColorMana 1) else #[]) ++
  (if c.tapSacrificeAddAnyColor then
    #[{ output := .oneOf anyColorMana 1, sacrificeSelf := true }] else #[]) ++
  (if c.tapAddAnyColorForLegendary then
    one (.oneOf anyColorMana 1) (.fra .legendarySpell) else #[]) ++
  (if c.tapAddTwoAmong.size ≥ 2 then one (.combination c.tapAddTwoAmong 2) else #[]) ++
  (if c.tapAddAnyColorAmongLegendaries then
    one (.colorAmong (legendaryColors.toList.map ManaType.colored).toArray) else #[]) ++
  (if c.tapAddCommanderIdentity then
    one (.colorAmong (identity.map ManaType.colored).toArray) else #[]) ++
  (match c.tapAddRestricted with
   | some (ts, text) => one (.fixed ts) (restrictionOfText text)
   | none => #[]) ++
  (match c.tapPayLifeAddOneOf with
   | some (n, ts) => #[{ output := .oneOf ts 1, payLife := n }]
   | none => #[]) ++
  (if c.tapAddChosenColorPerDifferentPower then
    one (.oneOf anyColorMana ((g.creaturesControlledBy p).map (g.power ·)).toList.eraseDups.length)
   else #[]) ++
  (if c.tapAddTogether.isEmpty then #[] else #[{ output := .fixed c.tapAddTogether }]) ++
  (match c.tapAddOneOfDealsDamage with
   | some (ts, n) => #[{ output := .oneOf ts 1, damageYou := n }]
   | none => #[]) ++
  (match c.filterMana with
   | some (cost, ts) =>
     let types := ts.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
     #[{ output := .combination types 2, cost, tap := true }]
   | none => #[]) ++
  (if c.tapAddOppCouldProduce then
    let lands := g.livingOpponents p |>.foldl (fun acc pl =>
      acc ++ (g.permanentsOf pl.id).filter (·.printed.isLand)) #[]
    #[{ output := .colorAmong (g.landsCouldProduce lands) }]
   else #[]) ++
  (if c.tapAddYouCouldProduce then
    let lands := (g.permanentsOf p).filter (fun land => land.printed.isLand && land.id != o.id)
    #[{ output := .colorAmong (g.landsCouldProduce lands) }]
   else #[])

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
      | .addMana types => with_ (.fixed types)
      | .addAnyColor => with_ (.oneOf anyColorMana 1)
      | .addAnyColorSpendOnlySubtype s =>
        with_ (.oneOf anyColorMana 1)
          (if s == "Hero" then .hero else if s == "Villain" then .villain else .none)
      | .addAnyColorSpendOnlyArtifactSpell => with_ (.oneOf anyColorMana 1) (.fra .artifactSpell)
      | .addTwoAnyColorCreatureSources => with_ (.oneOf anyColorMana 2) .creatureSource
      | .addBlueCantNonartifact => with_ (.fixed #[.colored .blue]) .cantNonartifact
      | .addAnyColorEqualToSourcePower => with_ (.oneOf anyColorMana power)
      | .addFourAnyCombination => with_ (.combination anyColorMana 4)
      | .addTwoAnyColorEquipment => with_ (.oneOf anyColorMana 2) (.fra .equipmentOrEquip)
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
    | .fra .tapAddColorlessNotFromHand =>
      acc.push { output := .fixed #[.colorless], restriction := .fra .notSpellsFromHand }
    | .fra .tapAddAnyColorPlaneswalkerOnly =>
      acc.push { output := .oneOf anyColorMana 1, restriction := .fra .planeswalkerSpell }
    | .fra .tapSacrificeAddThreeOfOneColor =>
      acc.push { output := .oneOf anyColorMana 3, sacrificeSelf := true }
    | .fra .tapAddChosenColor =>
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
    | .elf => pool.add t (elfRestricted := true)
    | .instantOrSorcery => pool.add t (instRestricted := true)
    | .hero => pool.add t (heroRestricted := true)
    | .villain => pool.add t (villainRestricted := true)
    | .cantNonartifact => pool.add t (cantNonartifact := true)
    | .creatureSource => pool.add t (creatureRestricted := true)
    | .fra u => pool.add t (fra := some u)) pool

/-- A short note for the log describing `r`. -/
def ManaRestriction.note : ManaRestriction → String
  | .none | .fra .fromTreasure => ""
  | .elf => " (Elf spells and abilities)"
  | .instantOrSorcery => " (instant or sorcery spells)"
  | .hero => " (Hero spells and abilities)"
  | .villain => " (Villain spells and abilities)"
  | .cantNonartifact => " (not a nonartifact spell)"
  | .creatureSource => " (abilities of creature sources)"
  | .fra u => s!" ({u.label})"

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
    throw s!"{o.name}'s colored mana ability can be activated only if this land entered this turn or if you control a basic land"
  let some i := g.manaAbilityIndexFor o mana false
    | throw s!"{o.name} cannot produce {mana}"
  let some d := (g.manaAbilityDefs o)[i]? | throw s!"{o.name} cannot produce {mana}"
  let some added := d.output.withType mana | throw s!"{o.name} cannot produce {mana}"
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
