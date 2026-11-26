import Mtg.Engine.Game.ManaAbilities

/-!
# Playing lands and mana abilities (CR 305 / 605)

Land drops, mana sources and their producible types, tapping for mana
with spending restrictions (CR 106.6), and available-mana calculation.
-/

namespace Mtg.Engine
namespace Game

/-- Record that `p` has used a land play this turn, without putting a land
onto the battlefield. Tests use this when the drop itself is not the action. -/
def recordLandPlayed (g : Game) (p : PlayerId) : Game :=
  let snap : EventObject := { id := some ⟨Nat.pow 2 60⟩, controller := some p, owner := p, zone := .outside p }
  g.record (GameEvent.moved g.turnNumber snap (.outside p) (.outside p)
    (after := some snap) (verb := some .playLand) (actor := some p)
    (cause := .specialAction .playLand p))

/-- Put `id` onto the battlefield as `p`'s land play and run its enters
processing (CR 305.1). -/
def finishPlayLand (g : Game) (p : PlayerId) (id : ObjectId) (tapped : Bool := false) : Game :=
  match g.findObject? id with
  | none => g
  | some card =>
    let (g, newId) := g.putOntoBattlefield id p
      (tapped := tapped)
      (verb := some .playLand) (actor := some p)
      (cause := some (.specialAction .playLand p))
    let g := g.logMsg s!"{(g.player p).name} plays {g.name card}"
    if let .chooseReplacement .. := g.pending then
      g.chainPendingReplacement (.afterLastPermanentEnters (some id) (isPlayLand := true))
    else
      match g.findObject? newId with
      | some entered =>
        if !entered.isOnBattlefield then g
        else
          let g := if entered.status.tapped then g.logMsg s!"{g.name entered} enters tapped" else g
          g.afterLandEnters entered
      | none => g

def playLand (g : Game) (p : PlayerId) (id : ObjectId) : Except String Game := do
  if !g.canPlayLand p then
    throw "Can't play a land now (CR 116.2a / 305.3)"
  let some card := g.findObject? id | throw "no such object"
  if !g.mayPlay p card then
    throw (g.playZoneError p card)
  if !g.isLand card then
    throw s!"{g.name card} is not a land"
  let g := g.finishPlayLand p id
  if let .chooseReplacement .. := g.pending then
    return g.chainPendingReplacement (.receivePriority p)
  if g.pending != .none then
    return g
  return g.receivePriority p

def manaSources (g : Game) (p : PlayerId) : Array (GameObject × Array ManaType) :=
  g.permanentsOf p |>.filterMap (fun o =>
    let types := g.manaAbilitiesOf o
    if types.isEmpty || o.status.tapped then none
    else if g.hasSummoningSickness o &&
        !(g.isCreature o && g.activatesAsThoughHaste p) then none
    else some (o, types))

/-- Permanents `p` currently controls with this subtype. -/
def countSubtype (g : Game) (p : PlayerId) (subtype : CardSubtype) : Nat :=
  (g.permanentsOf p).filter (fun o => g.hasSubtype o subtype) |>.size

/-- Greatest mana value among permanents `p` controls matching `pred`. -/
def greatestManaValueAmong (g : Game) (p : PlayerId) (pred : GameObject → Bool) : Nat :=
  (g.permanentsOf p).foldl (fun acc o =>
    if pred o then max acc (g.objectManaValue o) else acc) 0

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
any source in `excludeIds` (used when `{T}` or tap-cost picks reserve those
permanents). Each source is counted as its first mana type (green for any color),
with its spending restriction (leaving `.mountainExtraRed` extra `{R}`
unrestricted). -/
def availableManaExceptIds (g : Game) (p : PlayerId) (excludeIds : Array ObjectId) : ManaPool :=
  (g.manaSources p).foldl
    (fun pool (src, types) =>
      if excludeIds.contains src.id then pool
      else
        let green := ManaType.colored .green
        let ordered :=
          if types.size ≥ 5 && types.contains green then
            #[green] ++ types.filter (· != green)
          else types
        let score (t : ManaType) : Nat × Nat × Nat :=
          let base := g.baseManaTypesFromTap src t
          let extra := g.extraMountainRedFromTap src base
          let isUnr := if (g.tapRestrictionOf src t).isNone then 1 else 0
          (isUnr, base.size + extra.size, extra.size)
        let best? :=
          ordered.foldl (fun (acc? : Option (ManaType × (Nat × Nat × Nat))) t =>
            let sc := score t
            match acc? with
            | none => some (t, sc)
            | some (_, bestSc) =>
              if sc.1 > bestSc.1 ||
                  (sc.1 == bestSc.1 && sc.2.1 > bestSc.2.1) ||
                  (sc.1 == bestSc.1 && sc.2.1 == bestSc.2.1 && sc.2.2 > bestSc.2.2) then
                some (t, sc)
              else acc?) none
        match best? with
        | some (t, _) => g.addTapManaToPool pool src t
        | none => pool)
    (g.player p).manaPool

/-- Mana in `p`'s pool plus mana from each of their untapped sources, skipping
`exclude` (used when that source's `{T}` is part of an activation cost).
Each source is counted as its best unrestricted/max-yield mana type (green for
five-color ties), with its spending restriction. -/
def availableManaExcept (g : Game) (p : PlayerId) (exclude : Option ObjectId) : ManaPool :=
  g.availableManaExceptIds p exclude.toArray

/-- Mana in `p`'s pool plus mana from each of their untapped sources. -/
def availableMana (g : Game) (p : PlayerId) : ManaPool :=
  g.availableManaExceptIds p #[]

/-- Mana types `src` can produce that may be spent on `prop` (CR 106.6). -/
def usableManaTypesForProposed (g : Game) (src : GameObject) (types : Array ManaType)
    (prop : ProposedSpell) : Array ManaType :=
  types.filter fun t =>
    g.restrictionAllowsProposed (g.tapRestrictionOf src t (prop? := some prop)) prop ||
      (!(g.extraMountainRedFromTap src (g.baseManaTypesFromTap src t (prop? := some prop))).isEmpty &&
        g.restrictionAllowsProposed none prop)

/-- Untapped mana sources `p` may activate while paying `prop` (CR 601.2g).
Sources reserved for `{T}` or another battlefield-source cost, or whose mana
cannot be spent on this spell or ability, are omitted. -/
def manaSourcesForProposed (g : Game) (p : PlayerId) (prop : ProposedSpell) :
    Array (GameObject × Array ManaType) :=
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  (g.manaSources p).filterMap (fun (src, types) =>
    if (prop.sourceId == some src.id && prop.tapSource &&
          !g.sourceTappedForCost src.id (some prop.spellId) sinceIdx) ||
        prop.teamworkCreatures.contains src.id then
      none
    else
      let usable := g.usableManaTypesForProposed src types prop
      if usable.isEmpty then none
      else some (src, usable))

/-- Pool after tapping `src` for `t`, including spending restrictions (and
leaving `.mountainExtraRed` extra `{R}` unrestricted). -/
def poolAfterTap (g : Game) (pool : ManaPool) (src : GameObject) (t : ManaType)
    (prop? : Option ProposedSpell := none) : ManaPool :=
  g.addTapManaToPool pool src t (prop? := prop?)

/-- Minimum number of mana units needed to pay `cost` (1 per colored,
colorless, hybrid, or twobrid symbol, plus generic; `{X}` is 0). -/
def minManaUnitsForCost (cost : ManaCost) : Nat :=
  cost.symbols.foldl
    (fun acc s =>
      match s with
      | .generic n => acc + n
      | .colored _ | .colorless | .hybrid _ _ | .twobrid _ => acc + 1
      | .x => acc)
    0

/-- Collapse multiple colored mana types on `src` that have zero symbols in
`cost` (`cost.symbolsIncludingColor c == 0`) and identical single-unit output
and restriction to a single representative, avoiding exponential branching on
any-color sources (CR 106.1 / 605). -/
def dedupZeroReqManaTypes (g : Game) (src : GameObject) (types : Array ManaType)
    (cost : ManaCost) (prop? : Option ProposedSpell := none) : Array ManaType :=
  if types.size ≤ 1 then types
  else Id.run do
    let mut out : Array ManaType := #[]
    let mut seenZero : Array (Option ManaSpendRestriction × Nat) := #[]
    for t in types do
      match t with
      | .colored c =>
        let base := g.baseManaTypesFromTap src t (prop? := prop?)
        let extra := g.extraMountainRedFromTap src base
        if cost.symbolsIncludingColor c == 0 && base == #[t] then
          let rn := (g.tapRestrictionOf src t (prop? := prop?), extra.size)
          if !seenZero.contains rn then
            seenZero := seenZero.push rn
            out := out.push t
        else
          out := out.push t
      | .colorless =>
        out := out.push t
    return out

/-- Whether some assignment of tap choices (including mixed-color
`ManaOutput.combination` tuples) from `sources` pays `cost`. -/
def canPayFromSources (g : Game) (pool : ManaPool) (cost : ManaCost)
    (sources : List (GameObject × Array ManaType))
    (spend : ManaSpend := {}) (prop? : Option ProposedSpell := none) : Bool :=
  let minUnits := minManaUnitsForCost cost
  let srcArr := sources.toArray.filterMap fun (src, types) =>
    let choices :=
      g.tapChoicesForSource src types cost
        (dedupSingleTypes := fun ts => dedupZeroReqManaTypes g src ts cost prop?)
        (prop? := prop?)
    if choices.isEmpty then none
    else
      let maxOut := choices.foldl (fun m (ch : TapManaChoice) => max m ch.totalSize) 0
      some (src, choices, maxOut)
  let sufMax : Array Nat := Id.run do
    let mut out := Array.replicate (srcArr.size + 1) 0
    let mut i := srcArr.size
    while i > 0 do
      i := i - 1
      out := out.set! i (srcArr[i]!.2.2 + out[i + 1]!)
    return out
  let rec go (curPool : ManaPool) (idx : Nat) : Bool :=
    if curPool.canPay cost spend then
      true
    else if idx ≥ srcArr.size then
      false
    else if curPool.total + sufMax[idx]! < minUnits then
      false
    else
      let (_, choices, _) := srcArr[idx]!
      choices.any (fun (ch : TapManaChoice) => go (ch.applyToPool curPool) (idx + 1))
  go pool 0

private def manaAbilityAllowsZeroOutput (d : ManaAbilityDef) : Bool :=
  d.extraEffect?.isSome ||
    (if d.modeChoices.isEmpty then d.output.allows #[]
     else d.modeChoices.any (fun m => m.output?.isNone || m.output?.any (·.allows #[])))

private def zeroOutputManaAbilityChangesState (o : GameObject) (d : ManaAbilityDef)
    (effCost : ManaCost) : Bool :=
  d.tap || d.removesSource || d.payLife > 0 || d.damageYou > 0 ||
    d.modeChoices.any (fun m => (m.output?.isNone || m.output?.any (·.allows #[])) && m.damageYou > 0) ||
    d.removeStoryCounter || d.removeIndestructibleCounter || d.putStunCounterOnSource ||
    !d.picks.isEmpty || d.crewPower?.isSome || d.exileManaSymbols?.isSome ||
    d.extraEffect?.isSome || d.modeChoices.any (·.output?.isNone) ||
    effCost.includesManaPayment || d.turnLimit?.isSome || d.lifetimeLimit?.isSome ||
    d.isBoast || d.isExhaust || d.isPowerUp ||
    (d.removeAnyNumberPlusOne && o.status.plusOnePlusOne > 0)

/-- Whether `p` currently controls a usable non-plain CR 605 mana ability
(`!isPlainTapManaAbilityDef`, such as Treasures, life/mana filter lands, or
counter-removal mana abilities). When `prop? = some prop`, also requires that
the source is not reserved for `prop`'s non-mana costs and that the ability can
produce mana covering `prop.cost` (or another usable mana ability's mana cost),
or spend pool mana when `includePoolSpending` is true. -/
def hasUsableNonPlainManaAbility (g : Game) (p : PlayerId)
    (prop? : Option ProposedSpell := none)
    (includePoolSpending : Bool := false) : Bool :=
  let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
  let perms := g.permanentsOf p
  let handManaObjs :=
    (g.player p).hand.filterMap fun id =>
      (g.findObject? id).bind fun o =>
        if !(g.baseCard o).allActivatedAbilities.isEmpty then some o else none
  let gyManaObjs :=
    (g.player p).graveyard.filterMap fun id =>
      (g.findObject? id).bind fun o =>
        if !(g.baseCard o).allActivatedAbilities.isEmpty then some o else none
  let manaObjs := perms ++ handManaObjs ++ gyManaObjs
  let plainManaSrcs := g.manaSources p
  let propTapReservedIds : Array ObjectId :=
    match prop? with
    | none => #[]
    | some prop =>
      let srcTap :=
        match prop.sourceId with
        | some sid =>
          if prop.tapSource && !g.sourceTappedForCost sid (some prop.spellId) sinceIdx then #[sid]
          else #[]
        | none => #[]
      srcTap ++ prop.teamworkCreatures
  let propBfSacReservedIds : Array ObjectId :=
    match prop? with
    | none => #[]
    | some prop =>
      let srcSac :=
        match prop.sourceId with
        | some sid => if g.proposedNeedsBattlefieldSource prop sinceIdx then #[sid] else #[]
        | none => #[]
      let sneakSac :=
        match prop.sneakAttacker with
        | some aid => if !g.sneakPaid prop.spellId then #[aid] else #[]
        | none => #[]
      srcSac ++ prop.teamworkCreatures ++ sneakSac
  let propRemoveReservedIds : Array ObjectId :=
    match prop? with
    | none => #[]
    | some prop =>
      let handOrGySrc :=
        match prop.sourceId with
        | some sid =>
          if prop.kind == .activatedAbility &&
              (prop.discardSource ||
                prop.activation.any (fun a =>
                  a.cost.discardSource || a.cost.exileSourceFromHand || a.isFromGraveyard)) then
            #[sid]
          else #[]
        | none => #[]
      propBfSacReservedIds ++ handOrGySrc
  let propPostManaPayableAfter (tappedIds removedIds : Array ObjectId) : Bool :=
    match prop? with
    | none => true
    | some prop =>
      let beholdOk :=
        match prop.needsBehold with
        | none => true
        | some quality =>
          perms.any (fun perm =>
            !removedIds.contains perm.id && g.hasSubtype perm quality) ||
            (g.player p).hand.any (fun id =>
              !removedIds.contains id &&
                (g.findObject? id).any (fun card => isDiscardableCard card && g.hasSubtype card quality))
      if !beholdOk then false
      else if prop.kind != .activatedAbility then
        let gSneak := g.probeAfterUnpaidSneak prop
        let sneakPerms := gSneak.permanentsOf p
        let excludeId := prop.sourceId.getD prop.spellId
        let src := gSneak.findObject? excludeId
        let isSpellSrc (s : GameObject) : Bool :=
          s.zone == .stack && (prop.spellId != excludeId || prop.kind == .spell)
        let pred? := src.bind fun s =>
          if isSpellSrc s then gSneak.spellSacrificeCostPredFor? s (gSneak.baseCard s) else none
        let sacOk :=
          !prop.needsSacrificeOther ||
            match pred? with
            | some pred =>
              let env : EvalEnv := { controller := p, sourceId := some excludeId }
              sneakPerms.any fun perm =>
                perm.id != excludeId && !removedIds.contains perm.id &&
                  !propBfSacReservedIds.contains perm.id &&
                  EvalExpr.evalObjectPred gSneak env (.live perm) pred
            | none =>
              sneakPerms.any fun perm =>
                perm.id != excludeId && !removedIds.contains perm.id &&
                  !propBfSacReservedIds.contains perm.id &&
                  (gSneak.isCreature perm || gSneak.isArtifact perm)
        let discardOk :=
          !prop.needsDiscardCard ||
            (gSneak.discardableHandIds p).any (fun id =>
              id != prop.spellId && !removedIds.contains id)
        sacOk && discardOk
      else
        match prop.sourceId, prop.activation with
        | some sid, some ab =>
          let sacSrc :=
            prop.sacrificeSource || ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield
          let discSrc :=
            prop.discardSource || ab.cost.discardSource || ab.cost.exileSourceFromHand
          let gySrc := ab.isFromGraveyard
          let srcZoneOk :=
            (!discSrc || !removedIds.contains sid) &&
              (!gySrc || !removedIds.contains sid)
          let allPicks :=
            costPicksWithSacrificeOther (costPicksOf ab)
              (prop.needsSacrificeOther || ab.cost.sacrificeAnotherCreatureOrArtifact)
          let zemoOk :=
            prop.choiceCostPaid || ab.cost.exileManaSymbols?.isNone ||
              (let col :=
                 match (g.findObject? sid).map g.evalLayer3 with
                 | some tcs => TextChange.applyColor tcs .black
                 | none => .black
               let remGy :=
                 (g.player p).graveyard.filter (fun id =>
                   !removedIds.contains id &&
                     (g.findObject? id).any (fun o => isDiscardableCard o && (g.colors o).contains col))
               g.canPayZemoBoast p remGy col)
          let crewOrPicksOk :=
            if !prop.choiceCostPaid then
              match ab.cost.crewPower? with
              | some n =>
                (g.firstPayableCrewSelection? p sid n allPicks
                  (tapSource := prop.tapSource)
                  (sacrificeOrExileSource := sacSrc)
                  (discardOrExileHandSource := discSrc)
                  (preTappedIds := propTapReservedIds ++ tappedIds)
                  (used := removedIds)
                  (sacReservedIds := propBfSacReservedIds)).isSome
              | none =>
                allPicks.isEmpty ||
                  g.costPicksPayable p (some sid) allPicks
                    (tapSource := prop.tapSource)
                    (sacrificeOrExileSource := sacSrc)
                    (discardOrExileHandSource := discSrc)
                    (used := removedIds)
                    (preTappedIds := propTapReservedIds ++ tappedIds)
                    (sacReservedIds := propBfSacReservedIds)
            else
              allPicks.isEmpty ||
                g.costPicksPayable p (some sid) allPicks
                  (tapSource := prop.tapSource)
                  (sacrificeOrExileSource := sacSrc)
                  (discardOrExileHandSource := discSrc)
                  (used := removedIds)
                  (preTappedIds := propTapReservedIds ++ tappedIds)
                  (sacReservedIds := propBfSacReservedIds)
          srcZoneOk && zemoOk && crewOrPicksOk
        | _, _ =>
          let excludeId := prop.sourceId.getD prop.spellId
          !prop.needsSacrificeOther ||
            perms.any (fun perm =>
              perm.id != excludeId && !removedIds.contains perm.id &&
                !propBfSacReservedIds.contains perm.id &&
                (g.isCreature perm || g.isArtifact perm))
  let rec chooseK : List ObjectId → Nat → Array ObjectId → (Array ObjectId → Bool) → Bool
    | _, 0, picked, k => k picked
    | [], _ + 1, _, _ => false
    | c :: rest, m + 1, picked, k =>
      if rest.length < m then false
      else chooseK rest m (picked.push c) k || chooseK rest (m + 1) picked k
  let rec existsValidDPicks (o : GameObject) (d : ManaAbilityDef)
      : List CostPick → Array ObjectId → Array ObjectId → Array ObjectId → Array ObjectId → Bool
    | [], _, dTap, dRem, extraEffTapped =>
      let totTapped := (if d.tap then #[o.id] else #[]) ++ dTap ++ extraEffTapped
      let totRemoved := (if d.removesSource then #[o.id] else #[]) ++ dRem
      propPostManaPayableAfter totTapped totRemoved
    | pick :: restPicks, usedD, dTap, dRem, extraEffTapped =>
      let isTapPick : Bool :=
        match pick with
        | .tapUntappedCreature | .tapTwoUntappedArtifacts | .custom (.tapObjects ..) => true
        | _ => false
      let laterSacAttachedEquip :=
        !isTapPick && restPicks.contains .sacrificeEquipmentAttachedToSource
      let cands :=
        (g.costPickCandidates p (some o.id) pick
          (tapSource := d.tap)
          (sacrificeOrExileSource := d.sacrificeSelf || d.exileSelf || laterSacAttachedEquip)
          (discardOrExileHandSource := d.discardSelf || d.exileSelfFromHand)).filter fun cid =>
            !usedD.contains cid &&
              !(isTapPick && (propTapReservedIds.contains cid || extraEffTapped.contains cid)) &&
              !(!isTapPick && propRemoveReservedIds.contains cid)
      if cands.size < pick.count then false
      else
        chooseK cands.toList pick.count #[] fun picked =>
          existsValidDPicks o d restPicks (usedD ++ picked)
            (if isTapPick then dTap ++ picked else dTap)
            (if isTapPick then dRem else dRem ++ picked)
            extraEffTapped
  let existsValidDCrewAndPicks (o : GameObject) (d : ManaAbilityDef)
      (extraEffTapped : Array ObjectId) : Bool :=
    match d.crewPower? with
    | none => existsValidDPicks o d d.picks.toList #[] #[] #[] extraEffTapped
    | some crewN =>
      if !o.isOnBattlefield then false
      else
        let cands :=
          (g.creaturesControlledBy p).filter fun c =>
            c.id != o.id && !c.status.tapped &&
              !propTapReservedIds.contains c.id && !extraEffTapped.contains c.id
        let okAfterCrew (picked : Array ObjectId) : Bool :=
          existsValidDPicks o d d.picks.toList #[] picked #[] (extraEffTapped ++ picked)
        if crewN == 0 then okAfterCrew #[]
        else
          let sufPow : Array Nat := Id.run do
            let mut out := Array.replicate (cands.size + 1) 0
            let mut i := cands.size
            while i > 0 do
              i := i - 1
              out := out.set! i (out[i + 1]! + (g.power cands[i]!).toNat)
            return out
          let rec searchCrew (idx : Nat) (curPow : Nat) (picked : Array ObjectId) : Bool :=
            if curPow ≥ crewN then okAfterCrew picked
            else if h : idx ≥ cands.size then false
            else if curPow + sufPow[idx]! < crewN then false
            else
              let c := cands[idx]!
              let pwr := (g.power c).toNat
              if pwr == 0 then searchCrew (idx + 1) curPow picked
              else
                searchCrew (idx + 1) (curPow + pwr) (picked.push c.id) ||
                  searchCrew (idx + 1) curPow picked
          termination_by cands.size - idx
          searchCrew 0 0 #[]
  let respectsPropReservations (o : GameObject) (d : ManaAbilityDef) : Bool :=
    match prop? with
    | none => true
    | some prop =>
      prop.cost.includesManaPayment &&
      (d.payLife == 0 || g.canPayLife p (prop.payLife + d.payLife)) &&
      (!d.tap || !propTapReservedIds.contains o.id) &&
      (!(d.sacrificeSelf || d.exileSelf) || !propBfSacReservedIds.contains o.id) &&
      (!(d.exileSelfFromHand || d.discardSelf || d.exileSelfFromGraveyard) ||
        !propRemoveReservedIds.contains o.id) &&
      (!d.removeStoryCounter ||
        !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeStoryCounter) &&
          !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .story) sinceIdx &&
          o.status.story ≤ 1)) &&
      (!d.removeIndestructibleCounter ||
        !(prop.sourceId == some o.id && prop.activation.any (·.cost.removeIndestructibleCounter) &&
          !g.sourceCounterCostPaidFor o.id (some prop.spellId) .removeCounters (some .indestructible) sinceIdx &&
          o.status.indestructibleCounters ≤ 1)) &&
      d.exileManaSymbols?.all (fun (col?, minSyms, pred) =>
        g.canPayExileManaSymbols p o.id col? minSyms pred
          (excludedIds := propRemoveReservedIds ++ (if d.exileSelfFromGraveyard then #[o.id] else #[]))) &&
      existsValidDCrewAndPicks o d #[]
  let canPayEffCost (o : GameObject) (d : ManaAbilityDef) (effCost : ManaCost) : Bool :=
    if !effCost.includesManaPayment then true
    else
      let spendEff := ManaSpend.forAbility (g.types o) (g.supertypes o) (g.subtypes o)
      let effSrcs :=
        plainManaSrcs.filter fun (src, _) =>
          !(d.tap && src.id == o.id) && !propTapReservedIds.contains src.id
      let picksOkWith (extraTapped : Array ObjectId) : Bool :=
        existsValidDCrewAndPicks o d extraTapped
      if picksOkWith (effSrcs.map (·.1.id)) then
        g.canPayFromSources (g.player p).manaPool effCost effSrcs.toList spendEff none
      else
        let propAllPicks : Array CostPick :=
          match prop? with
          | some prop =>
            if prop.kind != .activatedAbility then #[]
            else
              match prop.activation with
              | some ab =>
                costPicksWithSacrificeOther (costPicksOf ab)
                  (prop.needsSacrificeOther || ab.cost.sacrificeAnotherCreatureOrArtifact)
              | none => #[]
          | none => #[]
        let propSacSrc :=
          prop?.any fun prop =>
            prop.sacrificeSource ||
              prop.activation.any (fun ab => ab.cost.sacrificeSource || ab.cost.exileSourceFromBattlefield)
        let propDiscSrc :=
          prop?.any fun prop =>
            prop.discardSource ||
              prop.activation.any (fun ab => ab.cost.discardSource || ab.cost.exileSourceFromHand)
        let isCrit (s : GameObject) : Bool :=
          g.isCreature s || g.isArtifact s ||
            (d.tap && s.id == o.id) ||
            d.picks.any (fun pk =>
              match pk with
              | .custom (.tapObjects ..) | .custom (.or _) =>
                g.costPickAllows p (some o.id) pk s
                  (tapSource := d.tap)
                  (sacrificeOrExileSource := d.sacrificeSelf || d.exileSelf)
                  (discardOrExileHandSource := d.discardSelf || d.exileSelfFromHand)
              | _ => false) ||
            prop?.any (fun prop =>
              (prop.tapSource && prop.sourceId == some s.id) ||
                prop.teamworkCreatures.contains s.id ||
                propAllPicks.any fun pk =>
                  match pk with
                  | .custom (.tapObjects ..) | .custom (.or _) =>
                    g.costPickAllows p prop.sourceId pk s
                      (tapSource := prop.tapSource)
                      (sacrificeOrExileSource := propSacSrc)
                      (discardOrExileHandSource := propDiscSrc)
                  | _ => false)
        let freeOthers := (effSrcs.filter (fun (s, _) => !isCrit s)).toList
        let critRem := (effSrcs.filter (fun (s, _) => isCrit s)).toList
        let rec searchEff :
            List (GameObject × Array ManaType) → ManaPool → Array ObjectId → Bool
          | [], curPool, tappedIds =>
            picksOkWith tappedIds &&
              g.canPayFromSources curPool effCost freeOthers spendEff none
          | (s, ts) :: rest, curPool, tappedIds =>
            if !picksOkWith tappedIds then false
            else if g.canPayFromSources curPool effCost freeOthers spendEff none then true
            else if !g.canPayFromSources curPool effCost (((s, ts) :: rest) ++ freeOthers) spendEff none then false
            else
              let choices :=
                g.tapChoicesForSource s ts effCost
                  (dedupSingleTypes := fun xs => dedupZeroReqManaTypes g s xs effCost none)
                  (prop? := none)
              let rec tryChoices : List TapManaChoice → Bool
                | [] => false
                | ch :: chs =>
                  searchEff rest (ch.applyToPool curPool) (tappedIds.push s.id) || tryChoices chs
              tryChoices choices.toList || searchEff rest curPool tappedIds
        searchEff critRem (g.player p).manaPool #[]
  let hasProducibleChoice (o : GameObject) (d : ManaAbilityDef) (effCost : ManaCost) : Bool :=
    !(d.allChoicesFor (fun ts => if ts.size > 1 then #[ts[0]!] else ts)).isEmpty ||
      d.extraEffect?.isSome || d.modeChoices.any (·.output?.isNone) ||
      (prop?.isNone && manaAbilityAllowsZeroOutput d && zeroOutputManaAbilityChangesState o d effCost) ||
      (includePoolSpending && effCost.includesManaPayment &&
        (!(g.player p).manaPool.units.isEmpty || canPayEffCost o d effCost) &&
        manaAbilityAllowsZeroOutput d)
  let usableAbilityOn (o : GameObject) (d : ManaAbilityDef) (requireNonPlain : Bool) : Bool :=
    let effCost := g.manaAbilityEffectiveCost p o d
    (!requireNonPlain || !g.isPlainTapManaAbilityDef p o d) &&
      g.manaAbilityDefUsable p o d &&
      hasProducibleChoice o d effCost &&
      (!d.tap ||
        (!o.status.tapped &&
          !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p)))) &&
      respectsPropReservations o d &&
      canPayEffCost o d effCost
  match prop? with
  | none =>
    manaObjs.any (fun o => (g.manaAbilityDefs o).any (fun d => usableAbilityOn o d true))
  | some prop =>
    if !prop.cost.includesManaPayment then false
    else
      let spend := g.proposedManaSpend prop
      let otherManaCosts : Array (GameObject × ManaCost) :=
        manaObjs.foldl (fun acc o2 =>
          (g.manaAbilityDefs o2).foldl (fun acc d2 =>
            let eff2 := g.manaAbilityEffectiveCost p o2 d2
            if eff2.includesManaPayment && g.manaAbilityDefUsable p o2 d2 &&
                hasProducibleChoice o2 d2 eff2 &&
                (!d2.tap ||
                  (!o2.status.tapped &&
                    !(g.hasSummoningSickness o2 && !(g.isCreature o2 && g.activatesAsThoughHaste p)))) &&
                respectsPropReservations o2 d2 then
              acc.push (o2, eff2)
            else acc) acc) #[]
      manaObjs.any fun o =>
        (g.manaAbilityDefs o).any fun d =>
          let effCost := g.manaAbilityEffectiveCost p o d
          let poolSpendLaunder :=
            includePoolSpending && effCost.includesManaPayment &&
              (!(g.player p).manaPool.units.isEmpty || canPayEffCost o d effCost)
          usableAbilityOn o d true &&
            (poolSpendLaunder || d.extraEffect?.isSome || d.modeChoices.any (·.output?.isNone) ||
              let dedupForProp (ts : Array ManaType) : Array ManaType :=
                if ts.size ≤ 1 then ts
                else Id.run do
                  let mut acc : Array ManaType := #[]
                  let mut seenZero := false
                  for t in ts do
                    match t with
                    | .colored c =>
                      let req :=
                        prop.cost.symbolsIncludingColor c > 0 ||
                          otherManaCosts.any (fun (o2, c2) => o2.id != o.id && c2.symbolsIncludingColor c > 0)
                      if !req then
                        if !seenZero then
                          seenZero := true
                          acc := acc.push t
                      else
                        acc := acc.push t
                    | .colorless => acc := acc.push t
                  return acc
              let extra := if o.isOnBattlefield && d.tap then g.extraMountainRedFromTap o #[.colorless] else #[]
              (d.allChoicesFor dedupForProp).any fun (added, restr, riders) =>
                let simPool :=
                  addRestrictedMana (addRestrictedMana ManaPool.empty added restr riders) extra .none
                simPool.coveredMana prop.cost spend > 0 ||
                  otherManaCosts.any (fun (o2, eff2) =>
                    o2.id != o.id &&
                      simPool.coveredMana eff2
                        (ManaSpend.forAbility (g.types o2) (g.supertypes o2) (g.subtypes o2)) > 0))

/-- Whether `p` controls an untapped plain `{T}` mana ability whose output currently
produces 0 mana (`d.output.producibleTypes.isEmpty && d.output.allows #[]`) and can still be
legally activated to tap the permanent (CR 605.3a–b). -/
def hasUsableZeroOutputTapManaAbility (g : Game) (p : PlayerId) : Bool :=
  (g.permanentsOf p).any fun o =>
    (g.manaAbilityDefs o).any fun d =>
      g.isPlainTapManaAbilityDef p o d &&
        g.manaAbilityDefUsable p o d &&
        d.output.producibleTypes.isEmpty && d.output.allows #[] &&
        !o.status.tapped &&
        !(g.hasSummoningSickness o && !(g.isCreature o && g.activatesAsThoughHaste p))

end Game
end Mtg.Engine

