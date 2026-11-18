import Mtg.Engine.Game

/-!
# Demonstration agent

A deterministic heuristic used by `Mtg.Demo` and compile-time smoke tests
to exercise the engine without a human at the console.
-/

namespace Mtg.Engine.Agent

open Mtg.Engine
open Mtg.Engine.Game

/-- During CR 601.2g, tap sources until the locked-in cost is payable, then pay.
Only mana that can be spent on the pending payment is considered (CR 106.6).
Noncreatures are tapped before creatures when both help. Colorless is
preferred when it can be spent; otherwise colors meet unmet requirements.
Flexible sources such as Hidden Lair tap for `{U}` or `{B}` when that
color is needed and the rest of the board can still finish the cost. -/
def chooseManaPayment (g : Game) (p : PlayerId) : Option Action :=
  match g.proposedSpell with
  | none => some .pay
  | some prop =>
    let allowElf := g.proposedAllowsElfRestricted prop
    let allowInst := g.proposedAllowsInstRestricted prop
    let allowHero := g.proposedAllowsHeroRestricted prop
    let allowVillain := g.proposedAllowsVillainRestricted prop
    let allowCantNonartifact := g.proposedAllowsCantNonartifact prop
    let allowCreature := g.proposedAllowsCreatureRestricted prop
    let spend := g.proposedManaSpend prop
    if (g.player p).manaPool.canPay prop.cost
        (allowElfRestricted := allowElf)
        (allowInstRestricted := allowInst)
        (allowHeroRestricted := allowHero)
        (allowVillainRestricted := allowVillain)
        (allowCantNonartifact := allowCantNonartifact)
        (allowCreatureRestricted := allowCreature)
        (spend := spend) then
      some .pay
    else
      match g.preferredManaTapChoice p prop with
      | some (src, ch) =>
        match ch.singleTapType? with
        | some t => some (.tapForMana src.id t)
        | none => some (.activateManaAbility src.id ch.abilityIdx ch.baseAdded #[])
      | none => some .pay

/-- Discard the newest card in hand, or decline with an empty hand. -/
def discardBackOrDecline (g : Game) (p : PlayerId) : Option Action :=
  match (g.player p).hand.back? with
  | some id => some (.discard id)
  | none => some .decline

/-- Pay `{n}` from the pool if possible; otherwise tap the first mana source. -/
def payGenericOrTapFirstSource (g : Game) (p : PlayerId) (n : Nat) : Option Action :=
  let cost := ManaCost.ofGeneric n
  if (g.player p).manaPool.canPay cost (allowCantNonartifact := true) then
    some .payGeneric
  else
    let usable (r : ManaRestriction) : Bool :=
      match r with
      | .none | .cantNonartifact => true
      | .fra u => u.allows {}
      | _ => false
    let usableYield (src : GameObject) (t : ManaType) : Nat :=
      let base := g.baseManaTypesFromTap src t
      let extra := g.extraMountainRedFromTap src base
      (if usable (g.tapRestrictionOf src t) then base.size else 0) +
        (if usable .none then extra.size else 0)
    let usableSources := (g.manaSources p).filterMap fun (src, types) =>
      let best? :=
        types.foldl (fun (acc? : Option (ManaType × Nat)) t =>
          let y := usableYield src t
          if y == 0 then acc?
          else
            match acc? with
            | none => some (t, y)
            | some (_, bestY) => if y > bestY then some (t, y) else acc?) none
      best?.map (fun (t, _) => (src, t))
    let totalPool :=
      usableSources.foldl
        (fun pool (src, t) => g.addTapManaToPool pool src t)
        (g.player p).manaPool
    if !totalPool.canPay cost (allowCantNonartifact := true) then
      some .decline
    else
      match usableSources[0]? with
      | some (src, t) => some (.tapForMana src.id t)
      | none => some .decline

/-- Choose a single legal action for `actor`, or `none` if that player is not to act. -/
def choose (g : Game) (actor : PlayerId) : Option Action :=
  if g.over then none
  else if g.actor != some actor then none
  else
    let p := g.rawActor.getD actor
    match g.pending with
    | .declareAttackers =>
      let defaultDest := g.opponent p
      let opps := g.livingOpponents p
      let freeOpps := opps.filter (fun pl => g.attackTaxPerCreature pl.id == 0)
      let legalPwFor (plId : PlayerId) (usedTomik : Array ObjectId) : Option GameObject :=
        (g.permanentsOf plId).find? fun pw =>
          g.isPlaneswalker pw &&
            !(g.cantAttackJace p pw) &&
            !(g.planeswalkerAttackedByOneAtMost pw && usedTomik.contains pw.id)
      let pickDestFor (o : GameObject) (usedTomik : Array ObjectId) :
          Option (PlayerId × Option ObjectId) :=
        let maxSat :=
          if o.status.goadedBy.isEmpty then 0
          else
            freeOpps.foldl (fun best pl =>
              if g.hasFlying o && g.leftoverFlyingRestriction pl.id then best
              else max best (o.status.goadedBy.filter (· != pl.id)).size) 0
        let okPlayer (d : PlayerId) : Bool :=
          !(g.hasFlying o && g.leftoverFlyingRestriction d) &&
            (o.status.goadedBy.isEmpty ||
              (o.status.goadedBy.filter (· != d)).size >= maxSat)
        if maxSat > 0 then
          if freeOpps.any (·.id == defaultDest) && okPlayer defaultDest then
            some (defaultDest, none)
          else
            (freeOpps.find? (fun pl => okPlayer pl.id)).orElse
              (fun _ => opps.find? (fun pl => okPlayer pl.id))
              |>.map (fun pl => (pl.id, none))
        else if freeOpps.any (·.id == defaultDest) && okPlayer defaultDest then
          some (defaultDest, none)
        else
          match freeOpps.find? (fun pl => okPlayer pl.id) with
          | some pl => some (pl.id, none)
          | none =>
            match opps.findSome? (fun pl => (legalPwFor pl.id usedTomik).map (fun pw => (pl.id, some pw.id))) with
            | some res => some res
            | none =>
              if opps.any (·.id == defaultDest) && okPlayer defaultDest then
                some (defaultDest, none)
              else
                (opps.find? (fun pl => okPlayer pl.id)).map (fun pl => (pl.id, none))
      let allCands := g.battlefield.filter g.canAttack
      let ordered :=
        allCands.filter g.mustAttackIfAble ++
          allCands.filter (fun o => !g.mustAttackIfAble o)
      let (chosen, _, _) := ordered.foldl
        (fun (acc : Array (GameObject × PlayerId × Option ObjectId) × Nat × Array ObjectId) o =>
          let (cur, usedTax, usedTomik) := acc
          match pickDestFor o usedTomik with
          | none => acc
          | some (d, pw?) =>
            let addTax := if pw?.isSome then 0 else g.attackTaxPerCreature d
            let nextTax := usedTax + addTax
            if nextTax == 0 || (g.player p).manaPool.canPay (ManaCost.ofGeneric nextTax) (allowCantNonartifact := true) then
              let nextTomik :=
                match pw?.bind g.findObject? with
                | some pw =>
                  if g.planeswalkerAttackedByOneAtMost pw then usedTomik.push pw.id
                  else usedTomik
                | none => usedTomik
              (cur.push (o, d, pw?), nextTax, nextTomik)
            else acc) (#[], 0, #[])
      let ids := chosen.map (·.1.id)
      let pws := chosen.map (·.2.2)
      if pws.all (·.isNone) && chosen.all (·.2.1 == defaultDest) then
        some (.declareAttackers ids)
      else if pws.all (·.isNone) then
        some (.declareAttackers ids (each := chosen.map (some ·.2.1)))
      else
        some (.declareAttackers ids (each := chosen.map (some ·.2.1)) (planeswalkers := pws))
    | .declareBlockers =>
      -- Naive: don't block. The demo still exercises the declare-blockers step.
      some (.declareBlockers #[])
    | .activateManaAbilities _ =>
      chooseManaPayment g p
    | .chooseMode _ =>
      match g.proposedSpell with
      | some prop =>
        if prop.kind == .activatedAbility then
          chooseAbilityMode g p
        else
          chooseSpellMode g p
      | none => some .pass
    | .chooseX _ =>
      match g.proposedSpell with
      | some prop =>
        let sinceIdx := (g.targetProposalCheckpoint?.map (·.eventsSize)).getD g.events.size
        let selfTapExcl : Array ObjectId :=
          match prop.sourceId with
          | some sid =>
            if prop.tapSource && !g.sourceTappedForCost sid (some prop.spellId) sinceIdx then #[sid]
            else #[]
          | none => #[]
        let baseExcl := selfTapExcl ++ prop.teamworkCreatures
        let costForX (x : Nat) : ManaCost :=
          match prop.kind, prop.activation, prop.sourceId.bind g.findObject? with
          | .activatedAbility, some ab, src =>
            g.activationManaCost p ab (source := src) (chosenX := some x)
          | .spell, _, _ =>
            match g.findObject? prop.spellId with
            | none => prop.cost.substituteX x
            | some spell =>
              let preSpell :=
                { spell with
                  id := prop.original.id
                  zone := prop.original.zone
                  exiledBy := prop.original.exiledBy
                  controller := some p
                  chosenX := some x }
              let baseFace := g.baseCard spell
              let face :=
                match prop.sneakAttacker, baseFace.sneakCost with
                | some _, some sc => { baseFace with manaCost := sc }
                | _, _ => baseFace
              let upcomingAddGen : Nat :=
                if prop.resolutionCast || !baseFace.announcesAdditionalCost ||
                    prop.additionalGeneric > 0 || prop.needsBehold.isSome ||
                    prop.needsSacrificeOther || prop.needsDiscardCard ||
                    !g.additionalCostChoosesGeneric p prop then
                  0
                else
                  match baseFace.additionalCostBeholdOrPay with
                  | some (_, n) => n
                  | none =>
                    match baseFace.additionalCostOrPayGeneric,
                          baseFace.additionalCostDiscardOrPayGeneric with
                    | some n, _ => n
                    | none, some n => n
                    | none, none => 0
              let extraCost :=
                let baseExtra := ManaCost.ofGeneric (prop.additionalGeneric + upcomingAddGen)
                match if prop.kicked then baseFace.kicker else none with
                | some k => k.addCost baseExtra
                | none => baseExtra
              g.playManaCost preSpell face extraCost
                (origPerm := prop.origPerm)
                (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
                (explicitAltCost := prop.sneakAttacker.isSome)
                (useImplicitPermissions := false)
          | _, _, _ => prop.cost.substituteX x
        let xForExtraExcl (extraExcl : Array ObjectId) : Nat :=
          maxAffordableX g p prop.cost
            (allowElfRestricted := g.proposedAllowsElfRestricted prop)
            (allowInstRestricted := g.proposedAllowsInstRestricted prop)
            (allowHeroRestricted := g.proposedAllowsHeroRestricted prop)
            (allowVillainRestricted := g.proposedAllowsVillainRestricted prop)
            (allowCantNonartifact := g.proposedAllowsCantNonartifact prop)
            (allowCreatureRestricted := g.proposedAllowsCreatureRestricted prop)
            (spend := g.proposedManaSpend prop)
            (excludeIds := baseExcl ++ extraExcl)
            (costForX? := some costForX)
            (prop? := some prop)
        let manaBound? : Option Nat :=
          if !prop.cost.containsX then none
          else
            let upperX := xForExtraExcl #[]
            let (sid?, allPicks, sacSrc, discSrc, sacReservedIds, crewN?) :
                Option ObjectId × Array CostPick × Bool × Bool × Array ObjectId × Option Nat :=
              match prop.kind with
              | .activatedAbility =>
                let picks :=
                  match prop.activation with
                  | some ab =>
                    costPicksWithSacrificeOther (costPicksOf ab)
                      (prop.needsSacrificeOther || ab.cost.sacrificeAnotherCreatureOrArtifact)
                  | none =>
                    if prop.needsSacrificeOther then #[.sacrificeAnotherCreatureOrArtifact] else #[]
                let sSrc :=
                  prop.sacrificeSource ||
                    prop.activation.any (fun ab => ab.cost.sacrificeSource || ab.cost.fra == .exileSource)
                let dSrc :=
                  prop.discardSource ||
                    prop.activation.any (fun ab => ab.cost.discardSource || ab.cost.fra == .exileSourceFromHand)
                let cr? : Option Nat :=
                  if prop.fraCostPaid then none
                  else
                    prop.activation.bind fun ab =>
                      match ab.cost.fra with
                      | .crew n => some n
                      | _ => none
                (prop.sourceId, picks, sSrc, dSrc, #[], cr?)
              | .spell =>
                let spellFace := g.baseCard ((g.findObject? prop.spellId).getD prop.original)
                let unchosenAdd :=
                  !prop.resolutionCast && spellFace.announcesAdditionalCost &&
                    prop.additionalGeneric == 0 && prop.needsBehold.isNone &&
                    !prop.needsSacrificeOther && !prop.needsDiscardCard &&
                    !g.additionalCostChoosesGeneric p prop
                let willSacOther :=
                  prop.needsSacrificeOther ||
                    (unchosenAdd && spellFace.additionalCostBeholdOrPay.isNone &&
                      spellFace.additionalCostOrPayGeneric.isSome)
                let willDiscCard :=
                  prop.needsDiscardCard ||
                    (unchosenAdd && spellFace.additionalCostBeholdOrPay.isNone &&
                      spellFace.additionalCostOrPayGeneric.isNone &&
                      spellFace.additionalCostDiscardOrPayGeneric.isSome)
                let sacPick : Array CostPick :=
                  if !willSacOther then #[]
                  else if spellFace.additionalCostSacrificeCreatureOrPlaneswalker then
                    #[.sacrificeAnotherCreatureOrPlaneswalker]
                  else if spellFace.additionalCostSacrificeCreature then
                    #[.sacrificeAnotherCreature]
                  else
                    #[.sacrificeAnotherCreatureOrArtifact]
                let discPick : Array CostPick :=
                  if willDiscCard then #[.discardACard] else #[]
                (some prop.spellId, sacPick ++ discPick, false, false, prop.sneakAttacker.toArray, none)
              | .turnFaceUp =>
                let picks :=
                  (if prop.needsSacrificeOther then #[.sacrificeAnotherCreatureOrArtifact] else #[]) ++
                    (if prop.needsDiscardCard then #[.discardACard] else #[])
                (prop.sourceId, picks, false, false, #[], none)
            if allPicks.isEmpty && crewN?.isNone then
              some upperX
            else
              let greedyPicksForCrew (crewExcl : Array ObjectId) : Option (Array ObjectId) := Id.run do
                let mut usedPicks : Array ObjectId := #[]
                let mut tExcl : Array ObjectId := #[]
                for i in [0:allPicks.size] do
                  let pick := allPicks[i]!
                  match g.firstPayableCostPickSlice? p sid? (allPicks.extract i allPicks.size)
                      (tapSource := prop.tapSource)
                      (sacrificeOrExileSource := sacSrc)
                      (discardOrExileHandSource := discSrc)
                      (used := usedPicks)
                      (preTappedIds := crewExcl)
                      (sacReservedIds := sacReservedIds) with
                  | some chosen =>
                    if chosen.size != pick.count then
                      return none
                    usedPicks := usedPicks ++ chosen
                    if pick == .tapUntappedCreature || pick == .tapTwoUntappedArtifacts then
                      tExcl := tExcl ++ chosen
                  | none =>
                    return none
                return some tExcl
              let updateBest (best? : Option Nat) (cand : Nat) : Option Nat :=
                match best? with
                | none => some cand
                | some b => some (max b cand)
              let canBeatBest (best? : Option Nat) (curExcl : Array ObjectId) : Bool :=
                match best? with
                | none => true
                | some b => b < upperX && xForExtraExcl curExcl > b
              let rec chooseKMax :
                  List ObjectId → Nat → Array ObjectId → Option Nat →
                  (Array ObjectId → Option Nat → Option Nat) → Option Nat
                | _, 0, picked, best?, k => k picked best?
                | [], _ + 1, _, best?, _ => best?
                | c :: rest, m + 1, picked, best?, k =>
                  if rest.length < m || best? == some upperX then best?
                  else
                    let best1? := chooseKMax rest m (picked.push c) best? k
                    if best1? == some upperX then best1?
                    else chooseKMax rest (m + 1) picked best1? k
              let rec searchPicksMax :
                  List CostPick → Array ObjectId → Array ObjectId → Array ObjectId →
                  Option Nat → Option Nat
                | [], _, tapExcl, crewExcl, best? =>
                  updateBest best? (xForExtraExcl (crewExcl ++ tapExcl))
                | pick :: restPicks, usedPicks, tapExcl, crewExcl, best? =>
                  if !canBeatBest best? (crewExcl ++ tapExcl) then best?
                  else
                    let rem := (pick :: restPicks).toArray
                    let remHasTap :=
                      rem.any (fun pk => pk == .tapUntappedCreature || pk == .tapTwoUntappedArtifacts)
                    if !remHasTap then
                      if g.costPicksPayable p sid? rem
                          (tapSource := prop.tapSource)
                          (sacrificeOrExileSource := sacSrc)
                          (discardOrExileHandSource := discSrc)
                          (used := usedPicks)
                          (preTappedIds := crewExcl ++ tapExcl)
                          (sacReservedIds := sacReservedIds) then
                        updateBest best? (xForExtraExcl (crewExcl ++ tapExcl))
                      else best?
                    else
                      let isTapPick :=
                        pick == .tapUntappedCreature || pick == .tapTwoUntappedArtifacts
                      let isBfSacPick : Bool :=
                        match pick with
                        | .tapUntappedCreature | .tapTwoUntappedArtifacts
                        | .discardACard | .discardNonland | .discardLegendaryCard | .discardLegendarySameName
                        | .exileAnotherCreatureCardFromGraveyard => false
                        | _ => true
                      let laterSacAttachedEquip :=
                        isBfSacPick && restPicks.contains .sacrificeEquipmentAttachedToSource
                      let cands :=
                        (g.costPickCandidates p sid? pick
                          (tapSource := prop.tapSource)
                          (sacrificeOrExileSource := sacSrc || laterSacAttachedEquip)
                          (discardOrExileHandSource := discSrc)).filter fun cid =>
                            !usedPicks.contains cid &&
                              !(isBfSacPick && sacReservedIds.contains cid) &&
                              !(isTapPick && (crewExcl.contains cid || tapExcl.contains cid))
                      if cands.size < pick.count then best?
                      else
                        chooseKMax cands.toList pick.count #[] best? fun picked curBest? =>
                          let nextTap := if isTapPick then tapExcl ++ picked else tapExcl
                          searchPicksMax restPicks (usedPicks ++ picked) nextTap crewExcl curBest?
              let evalForCrew (crewExcl : Array ObjectId) (best? : Option Nat) : Option Nat :=
                if !canBeatBest best? crewExcl then best?
                else
                  let best1? :=
                    match greedyPicksForCrew crewExcl with
                    | some tExcl => updateBest best? (xForExtraExcl (crewExcl ++ tExcl))
                    | none => best?
                  if best1? == some upperX then best1?
                  else searchPicksMax allPicks.toList #[] #[] crewExcl best1?
              let bestX? : Option Nat :=
                match crewN?, sid? with
                | some n, some sid =>
                  let manaSrcs := g.manaSources p
                  let cands :=
                    ((g.creaturesControlledBy p).filter (fun c => c.id != sid && !c.status.tapped)).qsort
                      (fun a b =>
                        let aNonMana := !manaSrcs.any (·.1.id == a.id)
                        let bNonMana := !manaSrcs.any (·.1.id == b.id)
                        if aNonMana != bNonMana then aNonMana else g.power a > g.power b)
                  let initBest? :=
                    match g.firstPayableCrewSelection? p sid n allPicks
                        (tapSource := prop.tapSource)
                        (sacrificeOrExileSource := sacSrc)
                        (discardOrExileHandSource := discSrc)
                        (orderedCands? := some cands)
                        (disjointFromAllPicks := false) with
                    | some picked => evalForCrew picked none
                    | none => none
                  if initBest? == some upperX then initBest?
                  else if n == 0 then evalForCrew #[] initBest?
                  else
                    let candsWithSuf : List (GameObject × Nat) :=
                      cands.toList.foldr (fun c acc =>
                        let prev := match acc with | (_, s) :: _ => s | [] => 0
                        (c, Int.toNat (max 0 (g.power c)) + prev) :: acc) []
                    let rec searchCrewMax :
                        List (GameObject × Nat) → Nat → Array ObjectId → Option Nat → Option Nat
                      | [], accPow, picked, best? =>
                        if accPow ≥ n then evalForCrew picked best? else best?
                      | (c, suf) :: rest, accPow, picked, best? =>
                        if best? == some upperX || !canBeatBest best? picked then best?
                        else if accPow ≥ n then
                          evalForCrew picked best?
                        else if accPow + suf < n then
                          best?
                        else
                          let cPow := Int.toNat (max 0 (g.power c))
                          let best1? :=
                            if cPow > 0 then
                              searchCrewMax rest (accPow + cPow) (picked.push c.id) best?
                            else best?
                          if best1? == some upperX then best1?
                          else searchCrewMax rest accPow picked best1?
                    searchCrewMax candsWithSuf 0 #[] initBest?
                | _, _ => evalForCrew #[] none
              some (bestX?.getD 0)
        let minusLoyaltyBound? : Option Nat :=
          if prop.loyaltyX && prop.activation.bind (·.cost.loyalty) == some .minusX then
            -- Remove all but one loyalty counter so the planeswalker survives when loyalty > 0.
            let loyalty := ((prop.sourceId.bind g.findObject?).map (·.status.loyaltyCounters)).getD 0
            some (loyalty - 1)
          else none
        let plusOneBound? : Option Nat :=
          if prop.removePlusOneX then
            some (((prop.sourceId.bind g.findObject?).map (·.status.plusOnePlusOne)).getD 0)
          else none
        let bounds := #[manaBound?, minusLoyaltyBound?, plusOneBound?].filterMap id
        match bounds[0]? with
        | some b0 =>
          some (.chooseX (bounds.foldl min b0))
        | none =>
          if prop.loyaltyX && prop.activation.bind (·.cost.loyalty) == some .plusX then
            some (.chooseX 1)
          else
            some (.chooseX (xForExtraExcl #[]))
      | none => some (.chooseX 0)
    | .chooseTargets _ =>
      chooseSpellTarget g p
    | .sacrificePermanent _ sourceId =>
      match (g.sacrificeCreatureOrArtifactChoices p sourceId)[0]? with
      | some sac => some (.sacrifice sac.id)
      | none => some .decline
    | .discardForAdditionalCost _ =>
      match (g.player p).hand.back? with
      | some id => some (.discard id)
      | none => some .decline
    | .sacrificeCreature _ =>
      match (g.sacrificeCreatureChoices p)[0]? with
      | some sac => some (.sacrifice sac.id)
      | none => some .pass
    | .declareMulligan _ =>
      some .keep
    | .putOnBottom _ n =>
      some (.putOnBottom ((g.player p).hand.extract 0 n))
    | .scry _ n _ =>
      some (.scry (g.scryLookedIds p n) #[])
    | .surveil _ n _ =>
      some (.surveil (g.scryLookedIds p n) #[])
    | .mayDiscardDraw _ _ =>
      discardBackOrDecline g p
    | .chooseAdditionalCost _ =>
      match g.proposedSpell with
      | some prop =>
        some (.chooseAdditionalCost (g.additionalCostChoosesGeneric p prop))
      | none => some .pass
    | .chooseSacrificeCreature _ _ _ =>
      match (g.creaturesControlledBy p)[0]? with
      | some o => some (.sacrifice o.id)
      | none => some .pass
    | .chooseDiscardCard _ _ =>
      discardBackOrDecline g p
    | .assignCombatDamage _ _ =>
      some (.assignCombatDamage #[])
    | .chooseLegend q name ids =>
      let liveIds := g.validLegendChoiceIds q name ids
      some (.keepLegend (defaultLegendToKeep g (if liveIds.isEmpty then ids else liveIds)))
    | .chooseTriggerToStack q =>
      some (.stackTriggers (defaultTriggerSourceIds g q))
    | .mayPayGeneric _ n =>
      payGenericOrTapFirstSource g p n
    | .chooseLibraryPlacement _ _ =>
      some .chooseBottom
    | .mayAttachEquipment _ hostId _ =>
      match (g.permanentsOf p).find? (fun o =>
        g.isEquipment o && o.attachedTo != some hostId &&
          (g.findObject? hostId).any (g.canAttachEquipmentTo o)) with
      | some eq => some (.choosePermanents #[eq.id])
      | none => some .decline
    | .mayResolve _ =>
      match g.mayEffect with
      | some e =>
        match e.spellResolution with
        | .loseLife _ _ | .discard _ => some .decline
        | _ => some .accept
      | none => some .decline
    | .tapHumans _ =>
      let humans :=
        (g.permanentsOf p).filter (fun o =>
          g.hasSubtype o .human && !o.status.tapped)
      if humans.isEmpty then some .decline
      else some (.choosePermanents (humans.map (·.id)))
    | .payOrLetCounter _ n _ =>
      payGenericOrTapFirstSource g p n
    | .payWard _ _ cost =>
      match cost with
      | .genericMana n => payGenericOrTapFirstSource g p n
      | .discardOrPay n =>
        match (g.player p).hand.back? with
        | some id => some (.discard id)
        | none => payGenericOrTapFirstSource g p n
      | .discardEnchantmentInstantOrSorcery =>
        match (g.player p).hand.find? (fun id =>
          match g.findObject? id with
          | some o =>
            g.isEnchantment o || g.isInstantOrSorcery o
          | none => false) with
        | some id => some (.discard id)
        | none => some .decline
      | .sacrificeLegendary =>
        match (g.legendaryWardSacrificeChoices p)[0]? with
        | some o => some (.sacrifice o.id)
        | none => some .decline
      | .fivePoison => some .pay
      | .discardCard =>
        match (g.player p).hand.back? with
        | some id => some (.discard id)
        | none => some .decline
      | .sacrificePermanents left paid chosen =>
        let perms := (g.permanentsOf p).filter (fun o => !chosen.contains o.id)
        if paid == 0 && perms.size < left then some .decline
        else
          match perms[0]? with
          | some o => some (.sacrifice o.id)
          | none => some .decline
    | .recruitDiscard _ =>
      discardBackOrDecline g p
    | .chooseKicker _ =>
      match g.apply actor (.announceKicker false) with
      | .ok _ =>
        let preferAlt :=
          match g.proposedSpell with
          | some prop =>
            let spell := (g.findObject? prop.spellId).getD prop.original
            let face := { g.baseCard spell with keywords := g.currentKeywords spell }
            if !prop.alternativeCost &&
                (face.morph.isSome || face.impending.isSome) && face.kicker.isNone then
              let spellSacOk :=
                !prop.needsSacrificeOther ||
                  !(g.sacrificeCreatureOrArtifactChoices p (prop.sourceId.getD prop.spellId)).isEmpty
              let spellDiscardOk :=
                !prop.needsDiscardCard || (g.player p).hand.any (· != prop.spellId)
              let spellBeholdOk :=
                match prop.needsBehold with
                | none => true
                | some st =>
                  (g.permanentsOf p).any (g.hasSubtype · st) ||
                    (g.player p).hand.any (fun id =>
                      (g.findObject? id).any (g.hasSubtype · st))
              let frontAdditionalOk :=
                if face.morph.isSome then
                  g.canPayAnnouncedAdditionalFromSources p spell
                    (origPerm := prop.origPerm)
                    (explicitAltCost := prop.sneakAttacker.isSome)
                    (flashback := some (GameEvent.castWithFlashback g.events prop.spellId))
                    (useImplicitPermissions := false)
                    (fromHand := prop.original.zone == .hand p)
                else
                  spellSacOk && spellDiscardOk && spellBeholdOk
              let frontAffordable :=
                (!prop.origPerm.any (·.payLifeEqualManaValue) || g.canPayLife p prop.payLife) &&
                g.canPaySpellCostFromSources p spell prop.cost
                  (fromHand := prop.original.zone == .hand p) (prop? := some prop) &&
                frontAdditionalOk
              let altAffordable :=
                match g.apply actor (.announceKicker true) with
                | .error _ => false
                | .ok gAlt =>
                  match gAlt.proposedSpell with
                  | none => true
                  | some propAlt =>
                    let spellAlt := (gAlt.findObject? propAlt.spellId).getD propAlt.original
                    let altSacOk :=
                      !propAlt.needsSacrificeOther ||
                        !(gAlt.sacrificeCreatureOrArtifactChoices p
                          (propAlt.sourceId.getD propAlt.spellId)).isEmpty
                    let altDiscardOk :=
                      !propAlt.needsDiscardCard || (gAlt.player p).hand.any (· != propAlt.spellId)
                    let altBeholdOk :=
                      match propAlt.needsBehold with
                      | none => true
                      | some st =>
                        (gAlt.permanentsOf p).any (gAlt.hasSubtype · st) ||
                          (gAlt.player p).hand.any (fun id =>
                            (gAlt.findObject? id).any (gAlt.hasSubtype · st))
                    altSacOk && altDiscardOk && altBeholdOk &&
                      gAlt.canPaySpellCostFromSources p spellAlt propAlt.cost
                        (fromHand := propAlt.original.zone == .hand p) (prop? := some propAlt)
              !frontAffordable && altAffordable
            else false
          | none => false
        some (.announceKicker preferAlt)
      | .error _ => some (.announceKicker true)
    | .chooseGift _ =>
      some (.announceGift none)
    | .chooseTeamwork _ =>
      some (.announceTeamwork false)
    | .chooseTeamworkCreatures _ need =>
      let picked := g.pickTeamworkCreatures p need
      let total := picked.foldl (fun acc id => acc + ((g.findObject? id).map g.power |>.getD 0)) 0
      some (if total < (need : Int) then .decline else .choosePermanents picked)
    | .maySacrificeAnotherBolg _ bolgId =>
      match (g.permanentsOf p).find? (fun o => g.isCreature o && o.id != bolgId) with
      | some o => some (.sacrifice o.id)
      | none => some .decline
    | .mayCastFromLooked _ ids maxMv =>
      match ids.reverse.find? (fun id =>
        (g.mayCastFromLookedError p ids maxMv id).isNone) with
      | some id => some (.cast id)
      | none => some .decline
    | .mayPutLandFromHand _ =>
      match (g.player p).hand.findSome? (fun id =>
        match g.findObject? id with
        | some o => if g.isLand o then some id else none
        | none => none) with
      | some id => some (.cast id)
      | none => some .decline
    | .chooseTriggerOr _ =>
      some (.chooseMode 0)
    | .maySacArtifactOrDiscard _ _ =>
      match (g.permanentsOf p).find? (fun o => g.isArtifact o) with
      | some o => some (.sacrifice o.id)
      | none => discardBackOrDecline g p
    | .mayPutArtifactFromHand _ _ =>
      match (g.handObjects p).find? (fun o => g.isArtifact o) with
      | some o => some (.cast o.id)
      | none => some .decline
    | .mayHaveVillainConnive _ _ _ =>
      some .haveVillainConnive
    | .mayCastExiledElseDamage _ cardId .. =>
      match g.apply actor (.cast cardId) with
      | .error _ => some .decline
      | .ok gCast =>
        let affordable :=
          (g.findObject? cardId).any (fun o =>
            let face := { g.baseCard o with keywords := g.currentKeywords o }
            let origPerm : Option PlayPermission :=
              some ((g.paidResolutionOrigPerm? p o (face? := some face)).getD
                { player := p, ignoreTiming := true })
            let frontLegal :=
              match gCast.pending with
              | .chooseKicker _ => (gCast.apply actor (.announceKicker false)).isOk
              | _ => true
            let frontOk :=
              frontLegal &&
                (!origPerm.any (·.payLifeEqualManaValue) || g.canPayLife p (g.objectManaValue o)) &&
                g.canPaySpellCostFromSources p o
                  (g.playManaCost { o with controller := some p } face
                    (origPerm := origPerm) (flashback := some false)
                    (useImplicitPermissions := false)) &&
                g.canPayAnnouncedAdditionalFromSources p o (origPerm := origPerm)
                  (flashback := some false) (useImplicitPermissions := false)
            let morphOk :=
              face.morph.isSome && face.kicker.isNone &&
                (match gCast.pending with
                 | .chooseKicker _ => (gCast.apply actor (.announceKicker true)).isOk
                 | _ => false) &&
                (let morphObj :=
                   { o with
                     controller := some p
                     printed := morphSpellFace
                     adventurerCard := none
                     status := { o.status with faceDown := true } }
                 let morphPerm :=
                   origPerm.filter fun pm =>
                     !pm.withoutManaCost && !pm.payLifeEqualManaValue && pm.prepareSource.isNone
                 let morphCost :=
                   g.playManaCost { o with controller := some p } morphSpellFace
                     (origPerm := morphPerm) (flashback := some false)
                     (explicitAltCost := true) (useImplicitPermissions := false)
                 g.canPaySpellCostFromSources p morphObj morphCost (fromHand := false))
            let impendingOk :=
              match face.morph, face.impending, face.kicker with
              | none, some (_, alt), none =>
                let impFace := { face with manaCost := alt }
                match gCast.proposedSpell.bind (gCast.proposalAltCleanPerm? · impFace) with
                | none => false
                | some impPerm =>
                  (match gCast.pending with
                   | .chooseKicker _ => (gCast.apply actor (.announceKicker true)).isOk
                   | _ => true) &&
                  (let impCost :=
                     g.playManaCost { o with controller := some p } impFace
                       (origPerm := impPerm) (flashback := some false)
                       (explicitAltCost := true) (useImplicitPermissions := false)
                   g.canPaySpellCostFromSources p o impCost (fromHand := false) &&
                     g.canPayAnnouncedAdditionalFromSources p o (origPerm := impPerm)
                       (explicitAltCost := true) (flashback := some false)
                       (useImplicitPermissions := false) (fromHand := false)
                       (faceOverride? := some impFace))
              | _, _, _ => false
            frontOk || morphOk || impendingOk)
        some (if affordable then .cast cardId else .decline)
    | .fraChoice _ choice =>
      some (g.defaultFraAction p choice)
    | .chooseReplacement _ choices =>
      (g.defaultReplacementId p choices (payLifeIfSafe := true)).map Action.chooseReplacement
    | .chooseProliferate _ _ =>
      let own := (g.permanentsOf p).filter (·.status.hasCounters) |>.map (Target.permanent ·.id)
      let opps :=
        (g.livingOpponents p).filter (fun pl =>
          g.teamPoison pl.id > 0 || pl.counters.any (fun (_, c) => c > 0)) |>.map (Target.player ·.id)
      some (.targets (own ++ opps))
    | .resolveRandom _ =>
      -- Random results are supplied by the host (`--norandom`), never the heuristic.
      none
    | .none =>
      -- Play a land if possible (from hand or from exile under a permission).
      let lands :=
        (g.handObjects p).filter g.isLand ++
        (g.exiledPlayable p).filter g.isLand
      if g.canPlayLand p then
        match lands[0]? with
        | some land => some (.playLand land.id)
        | none =>
          chooseActivate g p
      else
        chooseActivate g p
where
  /-- During CR 601.2b, announce a legal mode for the proposed modal spell. -/
  chooseSpellMode (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell.bind (fun prop => g.findObject? prop.spellId) with
    | none => some .pass
    | some spell =>
      if !(g.chosenModesOf spell).isEmpty then some .decline else
      match g.defaultMode p spell with
      | some i => some (.chooseMode i)
      | none =>
        if Game.minModesFor (g.baseCard spell) == 0 then some .decline else some .pass
  /-- During CR 601.2c / 603.3d, announce a legal target for the current
  instance of the word “target” on the proposed spell, activated ability,
  or triggered ability. Optional “up to one” triggers may choose no target. -/
  chooseSpellTarget (g : Game) (p : PlayerId) : Option Action :=
    match g.objectAwaitingTargets with
    | none => some .pass
    | some spell =>
      let kind := (g.targetingOf spell).kind
      let reqCount : Nat :=
        if kind.spec.slots.isEmpty then (g.announcedTargetBounds spell).1
        else
          let curSlot := g.currentTargetSlot spell
          let (grpStart, grpEnd) := kind.instanceGroupBounds curSlot
          ((List.range grpEnd).drop grpStart).filter (!kind.isOptionalSlot ·) |>.length
      let legal := g.legalProposedTargets p spell
      if reqCount > 1 && legal.size >= reqCount then
        some (.targets (legal.extract 0 reqCount))
      else
        match g.defaultTarget p spell with
        | some t => some (.target t)
        | none =>
          if g.canSkipCurrentOptionalSlot spell then some .decline
          else if g.canFinishOptionalTargets spell then some .decline
          else
            match spell.triggeredAbility with
            | some ab =>
              if ab.allowsZeroTargets || spell.abilityEffect.any (·.allowsZeroTargets) then
                some .decline
              else some .pass
            | none =>
              if (g.currentSpellEffect spell).any (·.allowsZeroTargets) ||
                  spell.abilityEffect.any (·.allowsZeroTargets) then
                some .decline
              else some .pass
  /-- During CR 601.2b, announce a mode of a modal activated ability. -/
  chooseAbilityMode (g : Game) (p : PlayerId) : Option Action :=
    match g.proposedSpell with
    | none => some .pass
    | some prop =>
      match g.defaultAbilityMode p prop.abilityModes prop.sourceId with
      | some idx => some (.chooseMode idx)
      | none => some .pass
  /-- Largest `{X}` `p` can currently pay for `cost` (CR 107.3a / 106.6). -/
  maxAffordableX (g : Game) (p : PlayerId) (cost : ManaCost)
      (allowElfRestricted := false) (allowInstRestricted := false)
      (allowHeroRestricted := false) (allowVillainRestricted := false)
      (allowCantNonartifact := false) (allowCreatureRestricted := false)
      (spend : ManaSpend := {}) (exclude : Option ObjectId := none)
      (excludeIds : Array ObjectId := #[])
      (costForX? : Option (Nat → ManaCost) := none)
      (prop? : Option ProposedSpell := none) : Nat :=
    let ids :=
      match exclude with
      | some id => if excludeIds.contains id then excludeIds else excludeIds.push id
      | none => excludeIds
    let sources :=
      ((g.manaSources p).filter (fun (src, _) => !ids.contains src.id)).toList
    let pool := (g.player p).manaPool
    let maxPossibleMana :=
      sources.foldl
        (fun acc (src, types) =>
          acc +
            types.foldl (fun best t =>
              let base := g.baseManaTypesFromTap src t (prop? := prop?)
              let extra := g.extraMountainRedFromTap src base
              max best (base.size + extra.size)) 0)
        pool.total
    let costAt (x : Nat) : ManaCost :=
      match costForX? with
      | some f => f x
      | none => cost.substituteX x
    let allowances : ManaAllowances :=
      { hero := allowHeroRestricted
        villain := allowVillainRestricted
        cantNonartifact := allowCantNonartifact
        creature := allowCreatureRestricted
        spend := spend }
    let probeCap := maxPossibleMana + 4096
    if (costForX?.isNone && !cost.containsX) ||
        minManaUnitsForCost (costAt probeCap) ≤ minManaUnitsForCost (costAt 0) then
      0
    else Id.run do
      let mut best : Nat := 0
      for x in [0 : probeCap + 1] do
        let c := costAt x
        if minManaUnitsForCost c > maxPossibleMana then
          break
        if g.canPayFromSources pool c allowElfRestricted allowInstRestricted sources allowances
            (prop? := prop?) then
          best := x
      return best
  /-- Activate a non-mana ability if the available mana covers its cost. -/
  chooseActivate (g : Game) (p : PlayerId) : Option Action :=
    let shouldActivate (o : GameObject) (idx : Nat) (ab : ActivatedAbility) : Bool :=
      let isTurnFaceUp := o.status.faceDown && ab.effect.resolution == .frc .turnFaceUp
      let selfExcl : Array ObjectId :=
        if !isTurnFaceUp && ab.cost.tap then #[o.id] else #[]
      let allPicks :=
        costPicksWithSacrificeOther (costPicksOf ab) ab.cost.sacrificeAnotherCreatureOrArtifact
      let sacSrc := ab.cost.sacrificeSource || ab.cost.fra == .exileSource
      let discSrc := ab.cost.discardSource || ab.cost.fra == .exileSourceFromHand
      let manaCost := if isTurnFaceUp then ab.cost.mana else g.activationManaCost p ab (some o)
      let allowElf := !isTurnFaceUp && g.hasSubtype o .elf
      let allowHero := !isTurnFaceUp && g.hasSubtype o .hero
      let allowVillain := !isTurnFaceUp && g.hasSubtype o .villain
      let allowCreature := !isTurnFaceUp && g.isCreature o
      let actSpend : ManaSpend :=
        if isTurnFaceUp then {}
        else { equip := ab.isEquip, abilitySourceSubtypes := g.subtypes o }
      let costForX (x : Nat) : ManaCost :=
        if isTurnFaceUp then ab.cost.mana.substituteX x
        else g.activationManaCost p ab (some o) (chosenX := some x)
      let manaOkForExcl (excludeIds : Array ObjectId) : Bool :=
        g.canPayAbilityCostFromSources p o ab manaCost
          (isTurnFaceUp := isTurnFaceUp) (excludeIds := excludeIds) &&
        !(ab.effect == Effect.plusOneX &&
          maxAffordableX g p manaCost
            (allowElfRestricted := allowElf)
            (allowInstRestricted := false)
            (allowHeroRestricted := allowHero)
            (allowVillainRestricted := allowVillain)
            (allowCantNonartifact := true)
            (allowCreatureRestricted := allowCreature)
            (spend := actSpend)
            (excludeIds := excludeIds)
            (costForX? := some costForX) == 0)
      let greedyPicksForCrew (crewExcl : Array ObjectId) : Option (Array ObjectId) := Id.run do
        let mut usedPicks : Array ObjectId := #[]
        let mut tapExcl : Array ObjectId := #[]
        for i in [0:allPicks.size] do
          let pick := allPicks[i]!
          match g.firstPayableCostPickSlice? p (some o.id) (allPicks.extract i allPicks.size)
              (tapSource := ab.cost.tap)
              (sacrificeOrExileSource := sacSrc)
              (discardOrExileHandSource := discSrc)
              (used := usedPicks)
              (preTappedIds := crewExcl) with
          | some chosen =>
            if chosen.size != pick.count then
              return none
            usedPicks := usedPicks ++ chosen
            if pick == .tapUntappedCreature || pick == .tapTwoUntappedArtifacts then
              tapExcl := tapExcl ++ chosen
          | none =>
            return none
        return some tapExcl
      let rec chooseK : List ObjectId → Nat → Array ObjectId → (Array ObjectId → Bool) → Bool
        | _, 0, picked, k => k picked
        | [], _ + 1, _, _ => false
        | c :: rest, m + 1, picked, k =>
          if rest.length < m then false
          else chooseK rest m (picked.push c) k || chooseK rest (m + 1) picked k
      let rec searchPicksForCrew :
          List CostPick → Array ObjectId → Array ObjectId → Array ObjectId → Bool
        | [], _, tapExcl, crewExcl =>
          manaOkForExcl (selfExcl ++ crewExcl ++ tapExcl)
        | pick :: restPicks, usedPicks, tapExcl, crewExcl =>
          let rem := (pick :: restPicks).toArray
          let remHasTap :=
            rem.any (fun pk => pk == .tapUntappedCreature || pk == .tapTwoUntappedArtifacts)
          if !remHasTap then
            g.costPicksPayable p (some o.id) rem
              (tapSource := ab.cost.tap)
              (sacrificeOrExileSource := sacSrc)
              (discardOrExileHandSource := discSrc)
              (used := usedPicks)
              (preTappedIds := crewExcl ++ tapExcl) &&
            manaOkForExcl (selfExcl ++ crewExcl ++ tapExcl)
          else
            let isTapPick :=
              pick == .tapUntappedCreature || pick == .tapTwoUntappedArtifacts
            let isBfSacPick : Bool :=
              match pick with
              | .tapUntappedCreature | .tapTwoUntappedArtifacts
              | .discardACard | .discardNonland | .discardLegendaryCard | .discardLegendarySameName
              | .exileAnotherCreatureCardFromGraveyard => false
              | _ => true
            let laterSacAttachedEquip :=
              isBfSacPick && restPicks.contains .sacrificeEquipmentAttachedToSource
            let cands :=
              (g.costPickCandidates p (some o.id) pick
                (tapSource := ab.cost.tap)
                (sacrificeOrExileSource := sacSrc || laterSacAttachedEquip)
                (discardOrExileHandSource := discSrc)).filter fun cid =>
                  !usedPicks.contains cid &&
                    !(isTapPick && (crewExcl.contains cid || tapExcl.contains cid))
            if cands.size < pick.count then false
            else
              chooseK cands.toList pick.count #[] fun picked =>
                let nextTap := if isTapPick then tapExcl ++ picked else tapExcl
                searchPicksForCrew restPicks (usedPicks ++ picked) nextTap crewExcl
      let crewAndPicksAndManaOk : Bool :=
        if isTurnFaceUp then
          manaOkForExcl selfExcl
        else
          let checkWithCrew (crewExcl : Array ObjectId) : Bool :=
            (match greedyPicksForCrew crewExcl with
             | some tapExcl => manaOkForExcl (selfExcl ++ crewExcl ++ tapExcl)
             | none => false) ||
              searchPicksForCrew allPicks.toList #[] #[] crewExcl
          match ab.cost.fra with
          | .crew n =>
            let manaSrcs := g.manaSources p
            let cands :=
              ((g.creaturesControlledBy p).filter (fun c => c.id != o.id && !c.status.tapped)).qsort
                (fun a b =>
                  let aNonMana := !manaSrcs.any (·.1.id == a.id)
                  let bNonMana := !manaSrcs.any (·.1.id == b.id)
                  if aNonMana != bNonMana then aNonMana else g.power a > g.power b)
            let fastOk :=
              match g.firstPayableCrewSelection? p o.id n allPicks
                  (tapSource := ab.cost.tap)
                  (sacrificeOrExileSource := sacSrc)
                  (discardOrExileHandSource := discSrc)
                  (orderedCands? := some cands)
                  (disjointFromAllPicks := false) with
              | some picked => checkWithCrew picked
              | none => false
            if fastOk then true
            else if n == 0 then checkWithCrew #[]
            else
              let candsWithSuf : List (GameObject × Nat) :=
                cands.toList.foldr (fun c acc =>
                  let prev := match acc with | (_, s) :: _ => s | [] => 0
                  (c, Int.toNat (max 0 (g.power c)) + prev) :: acc) []
              let rec searchCrew : List (GameObject × Nat) → Nat → Array ObjectId → Bool
                | [], accPow, picked => accPow ≥ n && checkWithCrew picked
                | (c, suf) :: rest, accPow, picked =>
                  if accPow ≥ n then
                    checkWithCrew picked
                  else if accPow + suf < n then
                    false
                  else
                    let cPow := Int.toNat (max 0 (g.power c))
                    (cPow > 0 && searchCrew rest (accPow + cPow) (picked.push c.id)) ||
                      searchCrew rest accPow picked
              searchCrew candsWithSuf 0 #[]
          | _ => checkWithCrew #[]
      g.canActivate p o ab (idx? := some idx) &&
      -- Don't pay life that would reduce the player to 0 or less.
      (ab.cost.payLife == 0 || (g.player p).life > (ab.cost.payLife : Int)) &&
      -- Don't spend mana re-equipping a creature that is already equipped.
      !(ab.isEquip && o.attachedTo.isSome) &&
      -- Spend {4}{T} on Rogue's Passage only after attackers are declared.
      !(ab.effect == Effect.targetCantBeBlockedThisTurn &&
        !(g.permanentsOf p).any (fun c => g.isCreature c && c.status.attacking)) &&
      -- Don't typecycle a card you can currently afford to cast.
      !(ab.activateFromHand &&
        ((g.canCastFrontFace p o &&
          let face := { g.baseCard o with keywords := g.currentKeywords o }
          let perm? := g.playPermissionFor? p o (face? := some face)
          (!perm?.any (·.payLifeEqualManaValue) || g.canPayLife p (g.objectManaValue o)) &&
          g.canPaySpellCostFromSources p o
            (g.playManaCost { o with controller := some p } face
              (origPerm := perm?) (useImplicitPermissions := false)) &&
          g.canPayAnnouncedAdditionalFromSources p o
            (origPerm := perm?) (useImplicitPermissions := false)) ||
         g.canCastAndPayMorphFaceDown p o ||
         g.canCastAndPayImpending p o)) &&
      crewAndPicksAndManaOk
    let firstAbility (o : GameObject) : Option Nat :=
      let abs := g.activatedAbilitiesOf o
      (List.range abs.size).find? (fun idx => shouldActivate o idx abs[idx]!)
    let gy := (g.player p).graveyard.filterMap (fun id => g.findObject? id)
    let candidate :=
      (g.permanentsOf p).find? (fun o => (firstAbility o).isSome) <|>
        gy.find? (fun o => (firstAbility o).isSome) <|>
        (g.handObjects p).find? (fun o => (firstAbility o).isSome)
    match candidate with
    | some o =>
      match firstAbility o with
      | some idx => some (.activate o.id idx)
      | none => chooseCast g p
    | none => chooseCast g p
  chooseCast (g : Game) (p : PlayerId) : Option Action :=
    let selectBestPerm (o : GameObject) (face : CardDef) (mv : Nat)
        (asAdventure : Bool := false) : Option PlayPermission :=
      let raw :=
        g.playPermissionsFor p o ++
          (if o.zone == .exile && g.mayCastExiledBySource p o then
            #[{ player := p, anyMana := true }]
           else #[])
      let p1 := if asAdventure then raw.filter (!·.fromAdventure) else raw
      let baseTimingOk := g.timingAllowsCast p face
      let cands :=
        if !baseTimingOk && p1.any (·.ignoreTiming) then p1.filter (·.ignoreTiming)
        else p1
      let score (perm : PlayPermission) : Nat :=
        let lifeOk := !perm.payLifeEqualManaValue || g.canPayLife p mv
        (if lifeOk then 32 else 0) +
          (if perm.withoutManaCost then 16 else 0) +
          (if perm.payLifeEqualManaValue && lifeOk then 8 else 0) +
          (if perm.anyMana then 4 else 0) +
          (if perm.ignoreTiming then 2 else 0) +
          (if !perm.fromAdventure then 1 else 0)
      cands.foldl (fun best? perm =>
        match best? with
        | none => some perm
        | some b => if score perm >= score b then some perm else some b) none
    let candidates := g.handObjects p ++ g.exiledPlayable p
    let playable := candidates.filter (fun o =>
      let face := { g.baseCard o with keywords := g.currentKeywords o }
      let mv := g.objectManaValue o
      let perm? := selectBestPerm o face mv
      g.canCastFrontFace p o &&
        (!perm?.any (·.payLifeEqualManaValue) || g.canPayLife p mv) &&
        g.canPaySpellCostFromSources p o
          (g.playManaCost { o with controller := some p } face
            (origPerm := perm?) (useImplicitPermissions := false)) &&
        g.canPayAnnouncedAdditionalFromSources p o (origPerm := perm?)
          (useImplicitPermissions := false))
    let morphOnlyPlayable := candidates.filter (fun o =>
      !playable.any (·.id == o.id) &&
        (g.canCastAndPayMorphFaceDown p o || g.canCastAndPayImpending p o))
    let adventurePlayable := candidates.filter (fun o =>
      g.canCastAdventure p o &&
        match (g.baseCard o).adventure with
        | some adv =>
          let face := adv.toCardDef
          let advObj := { o with controller := some p, printed := face, adventurerCard := some o.printed }
          let perm? := selectBestPerm o face face.manaValue (asAdventure := true)
          (!perm?.any (·.payLifeEqualManaValue) || g.canPayLife p face.manaValue) &&
          g.canPaySpellCostFromSources p advObj
            (g.playManaCost { o with controller := some p } face
              (origPerm := perm?) (useImplicitPermissions := false))
            (fromHand := o.zone == .hand p) &&
          g.canPayAnnouncedAdditionalFromSources p advObj (origPerm := perm?)
            (useImplicitPermissions := false) (fromHand := o.zone == .hand p)
        | none => false)
    let oppHasCreature := !(g.creaturesControlledBy (g.opponent p)).isEmpty
    let ownCreature := (g.creaturesControlledBy p).back?
    let spellKind (o : GameObject) (k : SpellCastKind) : Bool :=
      (g.baseCard o).hasCastKind k
    let adventureKind (o : GameObject) (k : SpellCastKind) : Bool :=
      (g.baseCard o).adventure.any (fun a => a.hasCastKind k)
    let modeKind (o : GameObject) (k : SpellCastKind) : Bool :=
      (g.baseCard o).hasModeCastKind k
    let hasLegalKind (k : EffectTargetKind) : Bool :=
      !(g.legalTargetsForKind p k).isEmpty
    let adventureRemoval :=
      if oppHasCreature then
        adventurePlayable.find? (fun o =>
          adventureKind o .creatureDamage || adventureKind o .burn)
      else none
    let burn := playable.find? (fun o => spellKind o .burn)
    let creatureDamage :=
      if oppHasCreature then
        playable.find? (fun o => spellKind o .creatureDamage)
      else none
    let fight := playable.find? (fun o => spellKind o .fight)
    let draw := playable.find? (fun o =>
      (spellKind o .draw || modeKind o .draw) &&
        match (g.baseCard o).spellEffect with
        | some e =>
          match e.spellResolution with
          | .sequence [.draw (.fixed cards) .you, .loseLife (.fixed life) .you] =>
            (g.player p).life > life &&
              (g.player p).library.size >= cards.toNat
          | _ => true
        | none => true)
    let removal := playable.find? (fun o =>
      (oppHasCreature && (spellKind o .destroyCreature || modeKind o .destroyCreature)) ||
      (hasLegalKind .creatureWithFlying &&
        (spellKind o .destroyFlying || modeKind o .destroyFlying)) ||
      (hasLegalKind .creature &&
        (spellKind o .destroyCreature || modeKind o .destroyCreature)) ||
      (hasLegalKind .artifactOrLand && spellKind o .destroyArtifactOrLand))
    let massPump := playable.find? (fun o =>
      spellKind o .massPump || modeKind o .massPump)
    let creature := (playable.filter g.isCreature ++ morphOnlyPlayable)[0]?
    let artifact := playable.find? (fun o =>
      g.isArtifact o &&
        (!(g.baseCard o).activatedAbilities.isEmpty || g.isEquipment o))
    let pump :=
      if ownCreature.isSome then
        playable.find? (fun o =>
          spellKind o .pump ||
            (g.baseCard o).spellModes.any (fun e =>
              e.castKind == .pump && !(g.legalTargetsForKind p e.targetKind).isEmpty))
      else none
    let aura :=
      if ownCreature.isSome then
        playable.find? (fun o => g.isAura o)
      else none
    let extraLandAdventure :=
      adventurePlayable.find? (fun o => adventureKind o .extraLand)
    let isSpellCounter (o : GameObject) : Bool :=
      (g.baseCard o).spellEffect.any (fun e => e.targetKind.targetsStackSpell) ||
        (g.baseCard o).spellModes.any (fun e => e.targetKind.targetsStackSpell)
    let hasOppSpellTarget (o : GameObject) : Bool :=
      match (g.baseCard o).spellEffect with
      | some e => g.effectHasOppSpellTarget p e
      | none => (g.baseCard o).spellModes.any (g.effectHasOppSpellTarget p)
    -- Cast a counter only when an opponent's spell is a legal target.
    let counter :=
      playable.find? (fun o =>
        (spellKind o .counter || modeKind o .counter) &&
          if isSpellCounter o then hasOppSpellTarget o
          else !(g.stackSpells (fun _ => true)).isEmpty)
    if let some o := counter then
      some (.cast o.id)
    else if let some o := burn then
      some (.cast o.id)
    else if let some o := adventureRemoval then
      some (.castAdventure o.id)
    else if let some o := creatureDamage then
      some (.cast o.id)
    else if let some o := removal then
      some (.cast o.id)
    else if let some o := fight then
      some (.cast o.id)
    else if let some o := draw then
      some (.cast o.id)
    else if let some o := creature then
      some (.cast o.id)
    else if let some o := artifact then
      some (.cast o.id)
    else if let some o := pump then
      some (.cast o.id)
    else if let some o := aura then
      some (.cast o.id)
    else if let some o := extraLandAdventure then
      some (.castAdventure o.id)
    else if let some o := massPump then
      some (.cast o.id)
    else
      some .pass

/-- Apply the heuristic once. Returns `none` if no actor or the action failed. -/
def step (g : Game) : Except String Game := do
  match g.actor with
  | none => throw "No player has an action"
  | some p =>
    match choose g p with
    | none => g.apply p .pass
    | some a => g.apply p a

/-- Run the heuristic until the game ends or `fuel` actions have been taken. -/
def play (g : Game) (fuel : Nat := 400) (rng : Rng := Rng.ofSeed 1) : Game :=
  let (rng, g) := g.resolvePendingRandom rng
  match fuel with
  | 0 => g.logMsg "Stopped: action limit reached"
  | n + 1 =>
    if g.over then g
    else if !g.playersReceivePriority && g.pending == .none then
      -- Untap, or a cleanup with no CR 514.3a exception: recover by advancing.
      play (g.advanceStep) n rng
    else
      match step g with
      | .ok g' =>
        let (rng', g') := g'.resolvePendingRandom rng
        play g' n rng'
      | .error e => g.logMsg s!"Agent error: {e}"

end Mtg.Engine.Agent
